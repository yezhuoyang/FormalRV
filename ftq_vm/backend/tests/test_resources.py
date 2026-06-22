"""Resource and dependency checking tests for the FTQ-VM.

Covers the sweep-line resource checker (exclusive conflicts, capacity sums,
half-open intervals, merged violation intervals), static use validation
(UnknownResource, InvalidInterval, single-op AllocationError), resource
stats (peak_usage, utilization) and the dependency checker.

All models are built directly in Python; times are integer microseconds and
intervals are half-open [start_us, end_us).
"""

from __future__ import annotations

import pytest

from ftq_vm.backend.models import (
    BackendConfig,
    Op,
    Program,
    ResourceSpec,
    ResourceUse,
    UseMode,
    VMErrorKind,
)
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Small builders
# --------------------------------------------------------------------------


def res(rid: str, capacity: int = 1, kind: str = "zone") -> ResourceSpec:
    return ResourceSpec(id=rid, kind=kind, capacity=capacity)


def use(resource: str, mode: UseMode = UseMode.capacity, amount: int = 1,
        start: int = 0, end: int | None = None) -> ResourceUse:
    return ResourceUse(resource=resource, mode=mode, amount=amount,
                       start_us=start, end_us=end)


def op(oid: str, at: int, dur: int = 1, uses: list[ResourceUse] | None = None,
       deps: list[str] | None = None) -> Op:
    return Op(id=oid, at_us=at, duration_us=dur,
              uses=uses or [], deps=deps or [])


def run(resources: list[ResourceSpec], ops: list[Op]):
    backend = BackendConfig(name="test-backend", resources=resources)
    program = Program(name="test-program", ops=ops)
    return run_simulation(backend, program)


def errors_of(result, kind: VMErrorKind):
    return [e for e in result.errors if e.kind == kind]


# --------------------------------------------------------------------------
# Exclusive conflicts (ResourceConflict)
# --------------------------------------------------------------------------


def test_exclusive_vs_exclusive_overlap_conflicts():
    result = run(
        [res("z")],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("b", 5, 10, uses=[use("z", mode=UseMode.exclusive)])],
    )
    assert not result.ok
    conflicts = errors_of(result, VMErrorKind.ResourceConflict)
    assert len(conflicts) == 1
    err = conflicts[0]
    assert err.resource == "z"
    assert sorted(err.op_ids) == ["a", "b"]
    assert err.interval is not None
    assert (err.interval.start_us, err.interval.end_us) == (5, 10)


def test_exclusive_vs_capacity_overlap_conflicts():
    # The capacity use is well within capacity, but it overlaps an exclusive
    # hold, which conflicts with ANY other concurrent use.
    result = run(
        [res("z", capacity=4)],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("b", 5, 10, uses=[use("z", mode=UseMode.capacity, amount=1)])],
    )
    conflicts = errors_of(result, VMErrorKind.ResourceConflict)
    assert len(conflicts) == 1
    assert sorted(conflicts[0].op_ids) == ["a", "b"]
    assert (conflicts[0].interval.start_us, conflicts[0].interval.end_us) == (5, 10)
    # cap demand (1) never exceeds capacity (4): no CapacityExceeded on top.
    assert errors_of(result, VMErrorKind.CapacityExceeded) == []


def test_exclusive_vs_shared_overlap_conflicts():
    result = run(
        [res("z", capacity=2)],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("b", 3, 4, uses=[use("z", mode=UseMode.shared)])],
    )
    conflicts = errors_of(result, VMErrorKind.ResourceConflict)
    assert len(conflicts) == 1
    assert sorted(conflicts[0].op_ids) == ["a", "b"]
    assert (conflicts[0].interval.start_us, conflicts[0].interval.end_us) == (3, 7)


# --------------------------------------------------------------------------
# Capacity overuse (CapacityExceeded)
# --------------------------------------------------------------------------


def test_capacity_overuse_from_two_overlapping_ops():
    # capacity 3; demand 2 + 2 = 4 during the overlap [5, 10).
    result = run(
        [res("z", capacity=3)],
        [op("a", 0, 10, uses=[use("z", amount=2)]),
         op("b", 5, 10, uses=[use("z", amount=2)])],
    )
    assert not result.ok
    cap_errors = errors_of(result, VMErrorKind.CapacityExceeded)
    assert len(cap_errors) == 1
    err = cap_errors[0]
    assert err.resource == "z"
    assert sorted(err.op_ids) == ["a", "b"]
    assert (err.interval.start_us, err.interval.end_us) == (5, 10)
    assert "demand 4" in err.message
    # individually within capacity: no static AllocationError, no conflict.
    assert errors_of(result, VMErrorKind.AllocationError) == []
    assert errors_of(result, VMErrorKind.ResourceConflict) == []


# --------------------------------------------------------------------------
# Half-open boundaries and peaceful coexistence
# --------------------------------------------------------------------------


def test_half_open_boundary_end_equals_start_does_not_conflict():
    # b starts exactly when a ends; c (capacity) starts exactly when b ends.
    result = run(
        [res("z")],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("b", 10, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("c", 20, 5, uses=[use("z", amount=1)])],
    )
    assert result.ok
    assert result.errors == []


def test_shared_and_capacity_coexist_without_errors():
    # shared contributes nothing to usage, so a full-capacity capacity use
    # plus a concurrent shared use is fine.
    result = run(
        [res("z", capacity=2)],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.capacity, amount=2)]),
         op("b", 0, 10, uses=[use("z", mode=UseMode.shared)])],
    )
    assert result.ok
    assert result.errors == []
    z = next(s for s in result.stats.resources if s.id == "z")
    assert z.peak_usage == 2  # only the capacity amount counts


# --------------------------------------------------------------------------
# Static validation: AllocationError, UnknownResource, InvalidInterval
# --------------------------------------------------------------------------


def test_single_op_overrequest_is_allocation_error_not_capacity_exceeded():
    result = run(
        [res("z", capacity=3)],
        [op("a", 0, 10, uses=[use("z", amount=5)])],
    )
    assert not result.ok
    alloc = errors_of(result, VMErrorKind.AllocationError)
    assert len(alloc) == 1
    assert alloc[0].resource == "z"
    assert alloc[0].op_ids == ["a"]
    # no double-reporting: the invalid use is excluded from the sweep ...
    assert errors_of(result, VMErrorKind.CapacityExceeded) == []
    # ... so it never shows up in the usage accounting either.
    z = next(s for s in result.stats.resources if s.id == "z")
    assert z.peak_usage == 0


def test_unknown_resource_reported():
    result = run(
        [res("z")],
        [op("a", 0, 5, uses=[use("ghost_zone")])],
    )
    assert not result.ok
    unknown = errors_of(result, VMErrorKind.UnknownResource)
    assert len(unknown) == 1
    assert unknown[0].resource == "ghost_zone"
    assert unknown[0].op_ids == ["a"]


def test_invalid_interval_when_relative_end_exceeds_duration():
    # op runs for 5us, but the use claims the resource until offset 10.
    result = run(
        [res("z")],
        [op("a", 0, 5, uses=[use("z", end=10)])],
    )
    assert not result.ok
    invalid = errors_of(result, VMErrorKind.InvalidInterval)
    assert len(invalid) == 1
    assert invalid[0].resource == "z"
    assert invalid[0].op_ids == ["a"]
    # the bad use is excluded, so nothing else fires.
    assert len(result.errors) == 1


# --------------------------------------------------------------------------
# Merged violation intervals
# --------------------------------------------------------------------------


def test_contiguous_capacity_overload_merges_into_one_error():
    # capacity 1; a holds [0,10); b overloads [0,5) and c overloads [5,10):
    # the overload is contiguous over [0,10) -> exactly ONE merged error.
    result = run(
        [res("z", capacity=1)],
        [op("a", 0, 10, uses=[use("z")]),
         op("b", 0, 5, uses=[use("z")]),
         op("c", 5, 5, uses=[use("z")])],
    )
    cap_errors = errors_of(result, VMErrorKind.CapacityExceeded)
    assert len(cap_errors) == 1
    err = cap_errors[0]
    assert (err.interval.start_us, err.interval.end_us) == (0, 10)
    assert sorted(err.op_ids) == ["a", "b", "c"]


def test_contiguous_exclusive_conflict_merges_into_one_error():
    # exclusive a [0,10) overlaps b on [0,5) then c on [5,10): one merged
    # ResourceConflict spanning [0,10) naming all three ops.
    result = run(
        [res("z", capacity=2)],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)]),
         op("b", 0, 5, uses=[use("z", mode=UseMode.shared)]),
         op("c", 5, 5, uses=[use("z", mode=UseMode.capacity, amount=1)])],
    )
    conflicts = errors_of(result, VMErrorKind.ResourceConflict)
    assert len(conflicts) == 1
    assert (conflicts[0].interval.start_us, conflicts[0].interval.end_us) == (0, 10)
    assert sorted(conflicts[0].op_ids) == ["a", "b", "c"]


# --------------------------------------------------------------------------
# Stats: peak_usage and utilization
# --------------------------------------------------------------------------


def test_peak_usage_and_utilization():
    # capacity 4; usage 3 over [0,10) then 2 over [10,20).
    # busy area = 3*10 + 2*10 = 50; runtime = 20.
    # utilization = 50 / (4 * 20) = 0.625; peak = 3.
    result = run(
        [res("z", capacity=4)],
        [op("a", 0, 10, uses=[use("z", amount=3)]),
         op("b", 10, 10, uses=[use("z", amount=2)])],
    )
    assert result.ok
    z = next(s for s in result.stats.resources if s.id == "z")
    assert z.peak_usage == 3
    assert z.utilization == pytest.approx(0.625)
    assert result.stats.total_runtime_us == 20


def test_exclusive_use_counts_as_full_capacity_in_usage_series():
    # a lone exclusive hold owns the whole resource: the usage series shows
    # the full capacity and utilization is 1.0 while it runs.
    result = run(
        [res("z", capacity=4)],
        [op("a", 0, 10, uses=[use("z", mode=UseMode.exclusive)])],
    )
    assert result.ok
    z = next(s for s in result.stats.resources if s.id == "z")
    assert z.peak_usage == 4
    assert z.utilization == pytest.approx(1.0)
    assert result.resource_usage_series["z"] == [(0, 4), (10, 0)]


# --------------------------------------------------------------------------
# Dependencies
# --------------------------------------------------------------------------


def test_unknown_dependency():
    result = run([], [op("a", 0, 5, deps=["does_not_exist"])])
    assert not result.ok
    errs = errors_of(result, VMErrorKind.UnknownDependency)
    assert len(errs) == 1
    assert errs[0].op_ids == ["a"]
    assert "does_not_exist" in errs[0].message


def test_dependency_violation_when_dep_ends_after_start():
    # dep ends at t=10 but the dependent starts at t=5.
    result = run(
        [],
        [op("a", 0, 10),
         op("b", 5, 5, deps=["a"])],
    )
    assert not result.ok
    errs = errors_of(result, VMErrorKind.DependencyViolation)
    assert len(errs) == 1
    assert errs[0].op_ids == ["b", "a"]


def test_dependency_ending_exactly_at_start_passes():
    # half-open semantics: dep finishing at t is fine for an op starting at t.
    result = run(
        [],
        [op("a", 0, 10),
         op("b", 10, 5, deps=["a"])],
    )
    assert result.ok
    assert result.errors == []
