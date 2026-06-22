"""Tests for the factory layer (factory.py via run_simulation).

Covers: token production timing, p=0 failure, stochastic reproducibility,
deterministic_seed override, conservative-mode schedules, auto_retry chains,
batch-slot / output-port contention, explicit footprint reservation and
factory stats.
"""

from __future__ import annotations

import pytest

from ftq_vm.backend.models import (
    BackendConfig,
    EventKind,
    FactorySpec,
    Op,
    Program,
    ResourceSpec,
    RunConfig,
    VMErrorKind,
)
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def make_factory(**overrides) -> FactorySpec:
    spec = {"id": "F0", "produces": "T", "duration_us": 5,
            "success_probability": 1.0}
    spec.update(overrides)
    return FactorySpec(**spec)


def make_backend(factories, resources=()) -> BackendConfig:
    return BackendConfig(name="test-backend", resources=list(resources),
                         factories=list(factories))


def start_op(op_id: str = "start0", at_us: int = 0, factory: str = "F0") -> Op:
    return Op(id=op_id, kind="start_factory", at_us=at_us,
              metadata={"factory": factory})


def simulate(backend, ops, seed: int = 0, mode: str = "stochastic"):
    program = Program(name="test-program", ops=list(ops))
    return run_simulation(backend, program,
                          RunConfig(seed=seed, factory_mode=mode))


def events_of(result, kind: EventKind):
    return [e for e in result.events if e.kind == kind]


def factory_stats(result, fid: str = "F0"):
    return next(f for f in result.stats.factories if f.id == fid)


# --------------------------------------------------------------------------
# Basic success / failure semantics
# --------------------------------------------------------------------------


def test_p1_factory_produces_one_token_at_run_end():
    backend = make_backend([make_factory(duration_us=7)])
    result = simulate(backend, [start_op(at_us=3)])

    assert result.ok
    assert len(result.tokens) == 1
    token = result.tokens[0]
    assert token.kind == "T"
    assert token.produced_at_us == 3 + 7  # start + duration_us
    assert token.producer_op == "F0.run0"

    produced = events_of(result, EventKind.token_produced)
    assert [(e.time_us, e.token_kind) for e in produced] == [(10, "T")]
    succeeded = events_of(result, EventKind.factory_succeeded)
    assert [(e.time_us, e.factory) for e in succeeded] == [(10, "F0")]
    assert events_of(result, EventKind.factory_failed) == []


def test_marker_op_stays_and_run_op_is_generated():
    backend = make_backend([make_factory(duration_us=5)])
    result = simulate(backend, [start_op(at_us=2)])

    by_id = {iv["id"]: iv for iv in result.op_intervals}
    marker = by_id["start0"]
    assert marker["kind"] == "start_factory"
    assert marker["duration_us"] == 1
    assert marker["resources"] == []  # the marker itself holds nothing

    run = by_id["F0.run0"]
    assert run["kind"] == "factory_run"
    assert run["start_us"] == 2
    assert run["end_us"] == 7
    assert "F0.batch_slots" in run["resources"]
    assert run["produces"] == ["T"]


@pytest.mark.parametrize("mode", ["stochastic", "conservative"])
def test_p0_factory_produces_nothing_and_emits_factory_failed(mode):
    backend = make_backend([make_factory(success_probability=0.0)])
    result = simulate(backend, [start_op()], mode=mode)

    assert result.tokens == []
    assert events_of(result, EventKind.token_produced) == []
    assert events_of(result, EventKind.factory_succeeded) == []
    failed = events_of(result, EventKind.factory_failed)
    assert [(e.time_us, e.factory) for e in failed] == [(5, "F0")]

    stats = factory_stats(result)
    assert (stats.attempts, stats.successes, stats.failures) == (1, 0, 1)
    assert stats.tokens_produced == 0
    # a failed run is a warning, not a schedule violation
    assert result.ok


# --------------------------------------------------------------------------
# Reproducibility: seeds
# --------------------------------------------------------------------------


def test_same_seed_gives_identical_traces():
    def run_once():
        backend = make_backend(
            [make_factory(success_probability=0.5, max_parallel_batches=8)])
        ops = [start_op(f"s{i}", at_us=10 * i) for i in range(6)]
        return simulate(backend, ops, seed=42)

    r1, r2 = run_once(), run_once()

    tok1 = [(e.time_us, e.token_id, e.token_kind)
            for e in events_of(r1, EventKind.token_produced)]
    tok2 = [(e.time_us, e.token_id, e.token_kind)
            for e in events_of(r2, EventKind.token_produced)]
    assert tok1 == tok2
    assert r1.factory_runs == r2.factory_runs
    assert r1.trace_dict() == r2.trace_dict()
    assert factory_stats(r1).attempts == 6  # all six scheduled runs happened


def test_deterministic_seed_overrides_global_seed():
    def run_once(seed):
        backend = make_backend(
            [make_factory(success_probability=0.5, deterministic_seed=7,
                          max_parallel_batches=8)])
        ops = [start_op(f"s{i}", at_us=10 * i) for i in range(6)]
        return simulate(backend, ops, seed=seed)

    r1, r2 = run_once(0), run_once(999)
    # outcomes come from deterministic_seed, not from the global seed
    assert r1.factory_runs == r2.factory_runs
    assert ([e.time_us for e in events_of(r1, EventKind.token_produced)]
            == [e.time_us for e in events_of(r2, EventKind.token_produced)])


# --------------------------------------------------------------------------
# Conservative mode
# --------------------------------------------------------------------------


def test_conservative_p_half_alternates_fail_success():
    backend = make_backend([make_factory(success_probability=0.5)])
    ops = [start_op(f"s{i}", at_us=10 * i) for i in range(4)]
    result = simulate(backend, ops, mode="conservative")

    runs = result.factory_runs["F0"]
    assert [r["run_id"] for r in runs] == [f"F0.run{n}" for n in range(4)]
    # ceil(1/0.5) = 2: attempts 1..4 -> fail, success, fail, success
    assert [r["success"] for r in runs] == [False, True, False, True]
    # tokens appear exactly at the ends of the successful runs
    assert [t.produced_at_us for t in result.tokens] == [15, 35]
    assert factory_stats(result).successes == 2


# --------------------------------------------------------------------------
# auto_retry
# --------------------------------------------------------------------------


def test_auto_retry_retries_after_cooldown_until_max_retries():
    backend = make_backend([make_factory(
        success_probability=0.0, auto_retry=True, max_retries=2,
        cooldown_us=3, duration_us=5)])
    result = simulate(backend, [start_op(at_us=0)])

    runs = result.factory_runs["F0"]
    # 1 original attempt + at most max_retries=2 extra ones, then stop
    assert len(runs) == 3
    # each retry starts cooldown_us after the previous failed run's end
    assert [(r["start_us"], r["end_us"]) for r in runs] == [(0, 5), (8, 13), (16, 21)]
    assert [r["attempt"] for r in runs] == [1, 2, 3]
    assert [r["retry_of"] for r in runs] == [None, "F0.run0", "F0.run1"]
    assert all(not r["success"] for r in runs)

    retry_events = events_of(result, EventKind.factory_retry_scheduled)
    assert len(retry_events) == 2
    assert len(events_of(result, EventKind.factory_failed)) == 3
    assert result.tokens == []

    stats = factory_stats(result)
    assert (stats.attempts, stats.failures, stats.retries) == (3, 3, 2)
    assert stats.successes == 0
    assert stats.empirical_success_rate == 0.0


def test_auto_retry_stops_after_first_success():
    backend = make_backend([make_factory(
        success_probability=0.5, auto_retry=True, max_retries=5,
        cooldown_us=2, duration_us=5)])
    result = simulate(backend, [start_op(at_us=0)], mode="conservative")

    runs = result.factory_runs["F0"]
    # conservative p=0.5: attempt 1 fails, attempt 2 succeeds -> chain stops
    assert [(r["attempt"], r["success"]) for r in runs] == [(1, False), (2, True)]
    assert (runs[1]["start_us"], runs[1]["end_us"]) == (7, 12)  # 5 + cooldown 2
    assert [t.produced_at_us for t in result.tokens] == [12]
    assert result.tokens[0].producer_op == "F0.run1"

    stats = factory_stats(result)
    assert (stats.attempts, stats.successes, stats.failures, stats.retries) \
        == (2, 1, 1, 1)


# --------------------------------------------------------------------------
# Contention on the auto-resources
# --------------------------------------------------------------------------


def test_batch_slot_oversubscription_capacity_exceeded():
    backend = make_backend([make_factory(duration_us=10,
                                         max_parallel_batches=1)])
    # two runs [0, 10) and [5, 15) on a single batch slot
    result = simulate(backend, [start_op("s0", at_us=0), start_op("s1", at_us=5)])

    assert not result.ok
    assert len(result.errors) == 1
    err = result.errors[0]
    assert err.kind == VMErrorKind.CapacityExceeded
    assert err.resource == "F0.batch_slots"
    assert (err.interval.start_us, err.interval.end_us) == (5, 10)
    assert sorted(err.op_ids) == ["F0.run0", "F0.run1"]


def test_output_port_conflict_capacity_exceeded():
    backend = make_backend([make_factory(duration_us=10,
                                         max_parallel_batches=2,
                                         output_ports=1)])
    # two simultaneous successful runs: ports clash in the last microsecond
    result = simulate(backend, [start_op("s0", at_us=0), start_op("s1", at_us=0)])

    assert not result.ok
    assert len(result.errors) == 1
    err = result.errors[0]
    assert err.kind == VMErrorKind.CapacityExceeded
    assert err.resource == "F0.output_ports"
    assert (err.interval.start_us, err.interval.end_us) == (9, 10)
    # both tokens are still produced (outcomes are decided upstream)
    assert len(result.tokens) == 2


# --------------------------------------------------------------------------
# Explicit footprint reservation (physical_qubits is a stats annotation ONLY)
# --------------------------------------------------------------------------


def test_footprint_reserved_exclusively_and_annotations_charge_nothing():
    from ftq_vm.backend.models import FactoryFootprint, ZoneSpec

    resources = [ResourceSpec(id="qubits", kind="physical_qubit", capacity=1)]
    backend = BackendConfig(
        name="test-backend",
        zones=[ZoneSpec(id="fab", kind="factory_qubit", count=6)],
        resources=resources,
        factories=[make_factory(
            duration_us=5, physical_qubits=30, logical_slots=4,
            footprint=FactoryFootprint(qubits=["fab[0:4]"]))])
    result = simulate(backend, [start_op(at_us=0)])

    assert result.ok
    # the EXACT footprint qubits are held exclusively for the whole run
    # (exclusive usage shows as the full capacity, i.e. 1 per qubit)
    for i in range(4):
        assert result.resource_usage_series[f"fab[{i}]"] == [(0, 1), (5, 0)]
    # qubits outside the footprint are untouched
    assert result.resource_usage_series["fab[4]"] == [(0, 0)]
    # the physical_qubits/logical_slots ANNOTATIONS never charge any pool
    assert result.resource_usage_series["qubits"] == [(0, 0)]

    cert_resources = {r["id"]: r for r in result.certificate["resources"]}
    assert cert_resources["fab[0]"]["intervals"] == [
        {"op": "F0.run0", "mode": "exclusive", "amount": 1,
         "start_us": 0, "end_us": 5}]
    # annotations still surface in stats
    fstats = factory_stats(result)
    assert fstats.physical_qubits == 30
    assert fstats.logical_slots == 4


def test_workload_op_colliding_with_factory_footprint_is_caught():
    from ftq_vm.backend.models import FactoryFootprint, ResourceUse, UseMode, ZoneSpec

    backend = BackendConfig(
        name="test-backend",
        zones=[ZoneSpec(id="fab", kind="factory_qubit", count=6)],
        factories=[make_factory(
            duration_us=10,
            footprint=FactoryFootprint(qubits=["fab[0:4]"]))])
    rogue = Op(id="rogue_probe", at_us=3, duration_us=2,
               uses=[ResourceUse(resource="fab[2]", mode=UseMode.exclusive)])
    result = simulate(backend, [start_op(at_us=0), rogue])

    assert not result.ok
    conflicts = [e for e in result.errors
                 if e.kind == VMErrorKind.ResourceConflict]
    assert len(conflicts) == 1
    assert conflicts[0].resource == "fab[2]"
    assert set(conflicts[0].op_ids) == {"F0.run0", "rogue_probe"}
    assert (conflicts[0].interval.start_us, conflicts[0].interval.end_us) == (3, 5)


# --------------------------------------------------------------------------
# Factory stats
# --------------------------------------------------------------------------


def test_factory_stats_counters_and_utilization():
    backend = make_backend([make_factory(success_probability=0.5,
                                         duration_us=5)])
    ops = [start_op(f"s{i}", at_us=10 * i) for i in range(4)]
    result = simulate(backend, ops, mode="conservative")

    stats = factory_stats(result)
    assert stats.attempts == 4
    assert stats.successes == 2
    assert stats.failures == 2
    assert stats.retries == 0
    assert stats.empirical_success_rate == 0.5
    assert stats.tokens_produced == 2

    # utilization = busy batch-slot time / (max_parallel_batches * runtime)
    runtime = result.stats.total_runtime_us
    assert runtime == 35  # last run [30, 35) ends the trace
    assert stats.utilization == round(4 * 5 / (1 * runtime), 6)
