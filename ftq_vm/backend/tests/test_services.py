"""Tests for the service layer: FIFO multi-worker queues, overflow, deadlines,
bandwidth, default latencies, stats and event aggregation.

All scenarios build BackendConfig / Program models directly in Python and run
them through run_simulation.  Times are integer microseconds, intervals are
half-open [start_us, end_us).
"""

from __future__ import annotations

from ftq_vm.backend.models import (
    BackendConfig,
    EventKind,
    Op,
    Program,
    ServiceJobRequest,
    ServiceSpec,
    VMErrorKind,
)
from ftq_vm.backend.simulator import run_simulation


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def make_service(sid: str = "svc", *, workers: int = 1, max_latency_us: int = 10_000,
                 queue_capacity: int = 10_000, **kw) -> ServiceSpec:
    return ServiceSpec(id=sid, workers=workers, max_latency_us=max_latency_us,
                       queue_capacity=queue_capacity, **kw)


def make_backend(*services: ServiceSpec, defaults: dict | None = None) -> BackendConfig:
    return BackendConfig(name="test-backend", services=list(services),
                         default_latencies_us=defaults or {})


def job_op(op_id: str, at_us: int = 0, *, count: int = 1, pt: int | None = None,
           service: str = "svc", submit_at_us: int = 0, duration_us: int = 1) -> Op:
    """An op whose only effect is submitting one batch of service jobs."""
    return Op(id=op_id, at_us=at_us, duration_us=duration_us,
              service=[ServiceJobRequest(service=service, count=count,
                                         submit_at_us=submit_at_us,
                                         processing_time_us=pt)])


def run(backend: BackendConfig, *ops: Op):
    return run_simulation(backend, Program(name="test-program", ops=list(ops)))


def errors_of(result, kind: VMErrorKind):
    return [e for e in result.errors if e.kind == kind]


def stats_for(result, sid: str = "svc"):
    return next(s for s in result.stats.services if s.id == sid)


def job_events(result, kind: EventKind, sid: str = "svc"):
    return [e for e in result.events if e.kind == kind and e.service == sid]


# --------------------------------------------------------------------------
# FIFO multi-worker scheduling
# --------------------------------------------------------------------------


def test_fifo_two_workers_hand_computed_schedule():
    # 5 jobs at t=0, pt=10, 2 workers:
    #   jobs 0,1 start at 0; jobs 2,3 start at 10; job 4 starts at 20.
    backend = make_backend(make_service(workers=2))
    result = run(backend, job_op("a", 0, count=5, pt=10))

    assert result.ok
    records = result.job_records["svc"]
    assert [r.start_time_us for r in records] == [0, 0, 10, 10, 20]
    assert [r.complete_time_us for r in records] == [10, 10, 20, 20, 30]
    assert all(r.submit_time_us == 0 for r in records)

    (batch,) = result.service_batches["svc"]
    assert batch["count"] == 5
    assert batch["first_start_us"] == 0
    assert batch["last_complete_us"] == 30
    assert batch["max_latency_observed_us"] == 30
    assert batch["deadline_misses"] == 0


def test_fifo_orders_by_submit_time_across_ops():
    # Program lists the later-submitting op first; the earlier submission must
    # still be served first on the single worker.
    backend = make_backend(make_service(workers=1))
    result = run(backend,
                 job_op("late", 5, count=1, pt=10),
                 job_op("early", 0, count=1, pt=10))

    assert result.ok
    records = result.job_records["svc"]
    by_op = {r.op_id: r for r in records}
    assert by_op["early"].start_time_us == 0
    assert by_op["early"].complete_time_us == 10
    # late submits at t=5, waits for the worker, starts at t=10
    assert by_op["late"].submit_time_us == 5
    assert by_op["late"].start_time_us == 10
    assert by_op["late"].complete_time_us == 20
    # FIFO processing order: early's record is materialized first
    assert [r.op_id for r in records] == ["early", "late"]


def test_fifo_tie_break_by_program_order():
    # Equal submit times: program order decides who gets the single worker.
    backend = make_backend(make_service(workers=1))
    result = run(backend,
                 job_op("a", 0, count=1, pt=10),
                 job_op("b", 0, count=1, pt=10))

    assert result.ok
    by_op = {r.op_id: r for r in result.job_records["svc"]}
    assert by_op["a"].start_time_us == 0
    assert by_op["b"].start_time_us == 10


# --------------------------------------------------------------------------
# Queue overflow / queue accounting
# --------------------------------------------------------------------------


def test_queue_overflow_burst_one_merged_error():
    # 1 worker, pt=10, 5 jobs at t=0: one starts immediately, FOUR wait.
    # Queue: 4 at t=0, 3 at t=10, 2 at t=20 (back within capacity 2).
    backend = make_backend(make_service(workers=1, queue_capacity=2))
    result = run(backend, job_op("a", 0, count=5, pt=10))

    assert not result.ok
    overflows = errors_of(result, VMErrorKind.ServiceQueueOverflow)
    assert len(overflows) == 1  # contiguous violation merged into ONE error
    err = overflows[0]
    assert err.service == "svc"
    assert err.time_us == 0
    assert err.interval.start_us == 0
    assert err.interval.end_us == 20
    assert "queue length 4 exceeds capacity 2" in err.message
    assert stats_for(result).max_queue_length == 4


def test_queue_excludes_job_that_starts_at_submit():
    # Same burst, capacity 4: the queue peaks at 4 (NOT 5 -- the job that
    # starts at its submit time never counts as queued), so no overflow.
    backend = make_backend(make_service(workers=1, queue_capacity=4))
    result = run(backend, job_op("a", 0, count=5, pt=10))

    assert result.ok
    assert errors_of(result, VMErrorKind.ServiceQueueOverflow) == []
    assert stats_for(result).max_queue_length == 4


def test_jobs_starting_immediately_never_queued():
    # 2 workers, 2 jobs: both start at submit time; queue stays empty even
    # with queue_capacity=0.
    backend = make_backend(make_service(workers=2, queue_capacity=0))
    result = run(backend, job_op("a", 0, count=2, pt=10))

    assert result.ok
    assert errors_of(result, VMErrorKind.ServiceQueueOverflow) == []
    assert stats_for(result).max_queue_length == 0
    assert result.service_queue_series["svc"] == [(0, 0)]


# --------------------------------------------------------------------------
# Deadline misses
# --------------------------------------------------------------------------


def test_deadline_miss_single_error_per_batch_with_count():
    # 1 worker, pt=10, max_latency 15, 3 jobs at t=0: latencies 10, 20, 30.
    # Exactly 2 misses, aggregated into ONE error for the batch.
    backend = make_backend(make_service(workers=1, max_latency_us=15))
    result = run(backend, job_op("a", 0, count=3, pt=10))

    assert not result.ok
    misses = errors_of(result, VMErrorKind.DeadlineMiss)
    assert len(misses) == 1
    err = misses[0]
    assert err.service == "svc"
    assert err.op_ids == ["a"]
    assert err.time_us == 0
    assert err.interval.start_us == 0
    assert err.interval.end_us == 30
    assert "2 of 3 job(s)" in err.message
    assert "max_latency_us=15" in err.message
    assert stats_for(result).deadline_misses == 2
    (batch,) = result.service_batches["svc"]
    assert batch["deadline_misses"] == 2


def test_deadline_miss_one_error_per_batch_two_batches():
    # Two well-separated batches, each with 2 misses -> exactly 2 errors.
    backend = make_backend(make_service(workers=1, max_latency_us=5))
    result = run(backend,
                 job_op("a", 0, count=2, pt=10),
                 job_op("b", 100, count=2, pt=10))

    misses = errors_of(result, VMErrorKind.DeadlineMiss)
    assert len(misses) == 2
    assert sorted(e.op_ids[0] for e in misses) == ["a", "b"]
    for err in misses:
        assert "2 of 2 job(s)" in err.message
    assert stats_for(result).deadline_misses == 4


def test_latency_exactly_max_latency_is_not_a_miss():
    # latency == max_latency_us is on-time (strictly-greater is a miss).
    backend = make_backend(make_service(workers=1, max_latency_us=10))
    result = run(backend, job_op("a", 0, count=1, pt=10))

    assert result.ok
    assert errors_of(result, VMErrorKind.DeadlineMiss) == []
    (record,) = result.job_records["svc"]
    assert record.complete_time_us - record.submit_time_us == 10
    assert stats_for(result).deadline_misses == 0


# --------------------------------------------------------------------------
# Bandwidth limits
# --------------------------------------------------------------------------


def test_input_bandwidth_exceeded():
    # 3 jobs submitted in the same microsecond, input_bandwidth=2.
    backend = make_backend(make_service(workers=3, input_bandwidth=2))
    result = run(backend, job_op("a", 0, count=3, pt=1))

    assert not result.ok
    errs = errors_of(result, VMErrorKind.ServiceCapacityExceeded)
    assert len(errs) == 1
    assert errs[0].time_us == 0
    assert errs[0].service == "svc"
    assert "input bandwidth 2" in errs[0].message
    assert len(result.errors) == 1  # nothing else went wrong


def test_input_bandwidth_at_limit_is_ok():
    backend = make_backend(make_service(workers=3, input_bandwidth=3))
    result = run(backend, job_op("a", 0, count=3, pt=1))

    assert result.ok
    assert errors_of(result, VMErrorKind.ServiceCapacityExceeded) == []


def test_output_bandwidth_exceeded():
    # 2 workers finish 2 jobs in the same microsecond, output_bandwidth=1.
    backend = make_backend(make_service(workers=2, output_bandwidth=1))
    result = run(backend, job_op("a", 0, count=2, pt=5))

    assert not result.ok
    errs = errors_of(result, VMErrorKind.ServiceCapacityExceeded)
    assert len(errs) == 1
    assert errs[0].time_us == 5  # both jobs complete at t=5
    assert "output bandwidth 1" in errs[0].message


# --------------------------------------------------------------------------
# Default processing times
# --------------------------------------------------------------------------


def test_default_latencies_us_fallback():
    # No processing_time_us on the request -> backend default for the service.
    backend = make_backend(make_service(workers=1), defaults={"svc": 7})
    result = run(backend, job_op("a", 0, count=1, pt=None))

    assert result.ok
    (record,) = result.job_records["svc"]
    assert record.processing_time_us == 7
    assert record.complete_time_us == 7

    # No backend default either -> processing time defaults to 1.
    backend2 = make_backend(make_service(workers=1))
    result2 = run(backend2, job_op("a", 0, count=1, pt=None))
    (record2,) = result2.job_records["svc"]
    assert record2.processing_time_us == 1
    assert record2.complete_time_us == 1

    # An explicit processing_time_us beats the backend default.
    backend3 = make_backend(make_service(workers=1), defaults={"svc": 7})
    result3 = run(backend3, job_op("a", 0, count=1, pt=3))
    (record3,) = result3.job_records["svc"]
    assert record3.processing_time_us == 3
    assert record3.complete_time_us == 3


# --------------------------------------------------------------------------
# Stats
# --------------------------------------------------------------------------


def test_service_stats_queue_utilization_and_peak_busy():
    # 2 workers, 3 jobs pt=10 at t=0: completions at 10, 10, 20.
    # Runtime = 20 (last completion); busy area = 3*10 = 30;
    # utilization = 30 / (2 workers * 20) = 0.75.
    backend = make_backend(make_service(workers=2))
    result = run(backend, job_op("a", 0, count=3, pt=10))

    assert result.ok
    stats = stats_for(result)
    assert stats.total_jobs == 3
    assert stats.workers == 2
    assert stats.max_queue_length == 1     # only the third job ever waits
    assert stats.peak_busy_workers == 2
    assert stats.utilization == 0.75
    assert stats.deadline_misses == 0
    assert result.stats.total_runtime_us == 20


# --------------------------------------------------------------------------
# Event aggregation for large job counts
# --------------------------------------------------------------------------


def test_large_service_gets_batch_level_events():
    # 501 jobs > EVENT_DETAIL_LIMIT (500): per-job events collapse into one
    # submitted + one completed batch event; per-job records (limit 2000)
    # are still materialized.
    n = 501
    backend = make_backend(make_service(workers=n, queue_capacity=0))
    result = run(backend, job_op("a", 0, count=n, pt=1))

    assert result.ok
    submitted = job_events(result, EventKind.service_job_submitted)
    started = job_events(result, EventKind.service_job_started)
    completed = job_events(result, EventKind.service_job_completed)
    assert len(submitted) == 1
    assert submitted[0].amount == n
    assert submitted[0].job_id == "a/svc/0"  # the batch id, not a job id
    assert started == []                     # batch mode emits no started events
    assert len(completed) == 1
    assert completed[0].amount == n
    assert completed[0].time_us == 1
    assert len(result.job_records["svc"]) == n


def test_small_service_gets_per_job_events():
    # 2 jobs <= 500: one submitted/started/completed event PER JOB.
    backend = make_backend(make_service(workers=2))
    result = run(backend, job_op("a", 0, count=2, pt=5))

    assert result.ok
    submitted = job_events(result, EventKind.service_job_submitted)
    started = job_events(result, EventKind.service_job_started)
    completed = job_events(result, EventKind.service_job_completed)
    assert len(submitted) == 2
    assert len(started) == 2
    assert len(completed) == 2
    assert {e.job_id for e in submitted} == {"a/svc/0#0", "a/svc/0#1"}
    assert all(e.amount is None for e in submitted)  # per-job, not batch
