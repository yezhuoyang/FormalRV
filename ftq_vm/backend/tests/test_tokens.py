"""Token-ledger tests for the FTQ-VM simulator.

Covers: same-tick produce/consume ordering, availability/freshness errors,
double consume, explicit-id consumption, buffer overflow (incl. initial
inventory alone and the no-same-tick-rescue rule), FIFO oldest-fresh
selection, stats counters and the expired-tokens-occupy-space rule.

All models are built directly in Python (no YAML).
"""

from __future__ import annotations

from ftq_vm.backend.models import (
    BackendConfig,
    Op,
    Program,
    RunConfig,
    TokenConsume,
    TokenProduce,
    VMErrorKind,
)
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def run(ops, *, initial=None, capacity=None, ttl=None):
    """Run a program of `ops` on a minimal backend with token settings."""
    backend = BackendConfig(
        name="token-test-backend",
        token_initial_inventory=initial or {},
        token_buffer_capacity=capacity or {},
        token_ttl_us=ttl or {},
    )
    program = Program(name="token-test-program", ops=list(ops))
    return run_simulation(backend, program, RunConfig(seed=0))


def producer(op_id, at_us, duration_us=1, **produce_kwargs):
    """An op that produces one token (at op end unless at_us offset given)."""
    return Op(id=op_id, at_us=at_us, duration_us=duration_us,
              produces=[TokenProduce(**produce_kwargs)])


def consumer(op_id, at_us, **consume_kwargs):
    """An op of duration 1 that consumes at its start time."""
    return Op(id=op_id, at_us=at_us, duration_us=1,
              consumes=[TokenConsume(**consume_kwargs)])


def errors_of(result, kind):
    return [e for e in result.errors if e.kind == kind]


def token_stats(result, kind):
    matches = [t for t in result.stats.tokens if t.kind == kind]
    assert len(matches) == 1, f"expected one TokenStats for {kind!r}, got {matches}"
    return matches[0]


def consumed_by(result, op_id):
    return [t for t in result.tokens if t.consumer_op == op_id]


# --------------------------------------------------------------------------
# Same-tick ordering and availability
# --------------------------------------------------------------------------


def test_consume_after_produce_same_tick_succeeds():
    # Producer ends at t=5 (token appears at op end); consumer consumes at
    # t=5.  Productions are processed before consumptions at equal times.
    result = run([
        producer("prod", at_us=0, duration_us=5, kind="magic"),
        consumer("cons", at_us=5, kind="magic"),
    ])
    assert result.ok, [e.headline() for e in result.errors]
    [tok] = consumed_by(result, "cons")
    assert tok.kind == "magic"
    assert tok.produced_at_us == 5
    assert tok.consumed_at_us == 5


def test_consume_before_production_unavailable_with_delay_suggestion():
    # Token only appears at t=10, consume attempted at t=4.
    result = run([
        producer("prod", at_us=0, duration_us=10, kind="magic"),
        consumer("cons", at_us=4, kind="magic"),
    ])
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenUnavailable)
    assert err.op_ids == ["cons"]
    # Suggestion must mention the next production time and the needed delay.
    assert "t=10us" in err.suggestion
    assert "Delay the op by 6us" in err.suggestion


def test_never_produced_kind_is_unavailable_never_produced_flavor():
    result = run([consumer("cons", at_us=3, kind="ghost")])
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenUnavailable)
    assert err.kind == VMErrorKind.TokenUnavailable
    assert "no op produces" in err.message
    assert "no initial inventory" in err.message


def test_one_error_per_consume_request_on_shortfall():
    # Need 3, only 1 available: exactly ONE TokenUnavailable error (per
    # consume request, not per missing token); the one token IS consumed.
    result = run([
        producer("prod", at_us=0, duration_us=1, kind="magic"),
        consumer("cons", at_us=2, kind="magic", count=3),
    ])
    assert len(errors_of(result, VMErrorKind.TokenUnavailable)) == 1
    assert len(result.errors) == 1
    assert token_stats(result, "magic").consumed == 1


# --------------------------------------------------------------------------
# Freshness (ttl)
# --------------------------------------------------------------------------


def test_token_consumable_strictly_before_expiry():
    # ttl 10, produced at t=5 -> fresh while t < 15; consuming at t=14 is OK.
    result = run([
        producer("prod", at_us=0, duration_us=5, kind="magic"),
        consumer("cons", at_us=14, kind="magic"),
    ], ttl={"magic": 10})
    assert result.ok, [e.headline() for e in result.errors]
    [tok] = consumed_by(result, "cons")
    assert tok.expires_at_us == 15
    assert tok.consumed_at_us == 14


def test_consume_exactly_at_expiry_is_freshness_violation():
    # Same token, but consumed exactly at produced_at + ttl = 15: expired.
    # Stale tokens are present in the buffer -> TokenFreshnessViolation
    # (not TokenUnavailable).
    result = run([
        producer("prod", at_us=0, duration_us=5, kind="magic"),
        consumer("cons", at_us=15, kind="magic"),
    ], ttl={"magic": 10})
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenFreshnessViolation)
    assert err.op_ids == ["cons"]
    assert errors_of(result, VMErrorKind.TokenUnavailable) == []
    assert token_stats(result, "magic").consumed == 0


# --------------------------------------------------------------------------
# Explicit token ids
# --------------------------------------------------------------------------


def test_double_consume_via_explicit_token_id():
    result = run([
        producer("prod", at_us=0, duration_us=2, kind="magic", id="tok-1"),
        consumer("first", at_us=3, id="tok-1"),
        consumer("second", at_us=4, id="tok-1"),
    ])
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.DoubleConsume)
    assert err.token == "tok-1"
    assert set(err.op_ids) == {"second", "first"}
    # The first consume itself succeeded.
    [tok] = consumed_by(result, "first")
    assert tok.id == "tok-1" and tok.consumed_at_us == 3


def test_explicit_id_consumed_before_its_production_is_unavailable():
    result = run([
        producer("prod", at_us=0, duration_us=10, kind="magic", id="late"),
        consumer("cons", at_us=3, id="late"),
    ])
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenUnavailable)
    assert err.token == "late"
    assert "only produced at t=10us" in err.message
    assert errors_of(result, VMErrorKind.DoubleConsume) == []


# --------------------------------------------------------------------------
# Buffer capacity
# --------------------------------------------------------------------------


def test_buffer_overflow_on_exceeding_capacity():
    # Capacity 1; second production at t=2 pushes occupancy to 2.
    result = run([
        producer("p1", at_us=0, duration_us=1, kind="magic"),
        producer("p2", at_us=1, duration_us=1, kind="magic"),
    ], capacity={"magic": 1})
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenBufferOverflow)
    assert err.time_us == 2
    assert "exceeding capacity 1" in err.message
    assert len(result.errors) == 1


def test_buffer_overflow_from_initial_inventory_alone():
    # No ops at all: initial inventory 3 > capacity 2 overflows at t=0.
    result = run([], initial={"magic": 3}, capacity={"magic": 2})
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenBufferOverflow)
    assert err.time_us == 0
    assert len(result.errors) == 1


def test_same_tick_consumption_cannot_rescue_overflow():
    # Occupancy is checked after each production; a consumption at the very
    # same microsecond does not prevent the momentary overflow.
    result = run([
        producer("prod", at_us=0, duration_us=5, kind="magic"),  # token at t=5
        consumer("cons", at_us=5, kind="magic"),                 # consume at t=5
    ], initial={"magic": 1}, capacity={"magic": 1})
    [err] = errors_of(result, VMErrorKind.TokenBufferOverflow)
    assert err.time_us == 5
    # The consumption itself still succeeds (no availability errors).
    assert errors_of(result, VMErrorKind.TokenUnavailable) == []
    assert token_stats(result, "magic").consumed == 1


# --------------------------------------------------------------------------
# Initial inventory and FIFO selection
# --------------------------------------------------------------------------


def test_initial_inventory_available_at_t0():
    result = run([consumer("cons", at_us=0, kind="magic")],
                 initial={"magic": 1})
    assert result.ok, [e.headline() for e in result.errors]
    [tok] = consumed_by(result, "cons")
    assert tok.produced_at_us == 0
    assert tok.producer_op is None  # initial inventory has no producer op
    assert tok.consumed_at_us == 0


def test_fifo_takes_oldest_fresh_token():
    # Tokens produced at t=1 (by p1) and t=3 (by p2); kind-consume at t=5
    # must take the older one (p1's).
    result = run([
        producer("p1", at_us=0, duration_us=1, kind="magic"),
        producer("p2", at_us=2, duration_us=1, kind="magic"),
        consumer("cons", at_us=5, kind="magic"),
    ])
    assert result.ok
    [tok] = consumed_by(result, "cons")
    assert tok.producer_op == "p1"
    assert tok.produced_at_us == 1
    # p2's token is left in the buffer.
    assert token_stats(result, "magic").leftover == 1


def test_fifo_skips_expired_oldest_and_takes_oldest_fresh():
    # Oldest token (t=1, ttl 3 -> expires t=4) is stale at t=5; the consume
    # takes the next-oldest FRESH token (t=2, no ttl) and reports no error.
    result = run([
        producer("p_stale", at_us=0, duration_us=1, kind="magic", ttl_us=3),
        producer("p_fresh", at_us=1, duration_us=1, kind="magic"),
        consumer("cons", at_us=5, kind="magic"),
    ])
    assert result.ok, [e.headline() for e in result.errors]
    [tok] = consumed_by(result, "cons")
    assert tok.producer_op == "p_fresh"
    # The expired token is untouched and still in the buffer.
    [stale] = [t for t in result.tokens if t.producer_op == "p_stale"]
    assert stale.consumed_at_us is None
    assert stale.expires_at_us == 4


# --------------------------------------------------------------------------
# Stats and expired-token occupancy
# --------------------------------------------------------------------------


def test_stats_produced_consumed_counts_and_peak_occupancy():
    # initial 2 at t=0; +1 at t=3 (peak 3); -1 at t=4.
    result = run([
        producer("prod", at_us=0, duration_us=3, kind="magic"),
        consumer("cons", at_us=4, kind="magic"),
    ], initial={"magic": 2})
    assert result.ok
    ts = token_stats(result, "magic")
    assert ts.initial_inventory == 2
    assert ts.produced == 3  # produced count includes initial inventory
    assert ts.consumed == 1
    assert ts.peak_buffer == 3
    assert ts.leftover == 2


def test_expired_tokens_keep_occupying_the_buffer():
    # A token that expires at t=3 is never discarded: a fresh production at
    # t=10 brings occupancy to 2 > capacity 1 -> TokenBufferOverflow.
    result = run([
        producer("p_stale", at_us=0, duration_us=1, kind="magic", ttl_us=2),
        producer("p_new", at_us=9, duration_us=1, kind="magic"),
    ], capacity={"magic": 1})
    assert not result.ok
    [err] = errors_of(result, VMErrorKind.TokenBufferOverflow)
    assert err.time_us == 10
    # Occupancy series ends at 2: the expired token still takes a slot.
    assert result.token_occupancy_series["magic"][-1] == (10, 2)
    assert token_stats(result, "magic").peak_buffer == 2
