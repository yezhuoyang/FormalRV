/-
  scripts/EmitErrorCorpus.lean — generate the DIFFERENTIAL ERROR CORPUS:
  18 concrete DEVICE-PROGRAM examples over 6 hardware configurations,
  engineered so the triggered runtime errors RANGE OVER the whole shared
  error space.  Every schedule and every backend is generated from Lean
  definitions (the schedules below; the backends from
  `System/Params/HardwareCatalog.lean`).

  Companions:
    * scripts/CheckErrorCorpus.lean — runs the Lean diagnostic
      (`diagnoseDeviceProgram`) on every pair and asserts the expected
      failing conjuncts;
    * ftq_vm/backend/tests/test_error_corpus.py — runs the FTQ-VM on the
      same pairs and asserts the expected error kinds AND the
      agreement/divergence matrix between the two checkers.

  Run from the repo root:
      lake env lean --run scripts/EmitErrorCorpus.lean
-/
import FormalRV.Codegen.SysCallEmit
import FormalRV.System.Params.HardwareCatalog

open FormalRV.System.Architecture
open FormalRV.Codegen.SysCallEmit

namespace ErrorCorpus

/-- Shorthand SysCall builders. -/
def req (site b : Nat) : SysCall :=
  { kind := .RequestFreshAncilla site, begin_us := b, end_us := b + 1 }
def cnot (a c b : Nat) (dur : Nat := 1) : SysCall :=
  { kind := .Gate2q a c 0, begin_us := b, end_us := b + dur }
def meas (q b : Nat) : SysCall :=
  { kind := .Measure q 0, begin_us := b, end_us := b + 1 }
def dec (r b : Nat) (dur : Nat := 1) : SysCall :=
  { kind := .DecodeSyndrome r, begin_us := b, end_us := b + dur }
def pfu (c b : Nat) (dur : Nat := 1) : SysCall :=
  { kind := .PauliFrameUpdate c, begin_us := b, end_us := b + dur }

/-- One clean PPM round: request → 2 CNOTs → measure → decode → PFU. -/
def cleanBlock : List SysCall :=
  [ req 100 0, cnot 0 100 1, cnot 50 100 2, meas 100 3, dec 0 4, pfu 0 5 ]

/-- e01 clean baseline (std): PASS / PASS. -/
def e01 := cleanBlock

/-- e02 qubit conflict (dualRail so the CNOT cap doesn't also fire): two
    simultaneous CNOTs SHARING data qubit 0.  VM ResourceConflict ↔ Lean
    exclusivity. -/
def e02 : List SysCall :=
  [ req 100 0, req 101 0,
    cnot 0 100 1, cnot 0 101 1,
    meas 100 2, meas 101 2 ]

/-- e03 CNOT-cap violation (std, cap 1): two simultaneous CNOTs on
    DISJOINT qubits.  VM CapacityExceeded(gate.CNOT.parallel) ↔ Lean
    operation_capacity. -/
def e03 : List SysCall :=
  [ req 100 0, req 101 0,
    cnot 0 100 1, cnot 1 101 1,
    meas 100 2, meas 101 2 ]

/-- e04 = e03 on the dual-rail machine: PASS / PASS (reconfiguration). -/
def e04 := e03

/-- e05 slow decode (std): 20 µs decode vs the 10 µs budget.
    VM DeadlineMiss ↔ Lean decoder_react. -/
def e05 : List SysCall :=
  [ req 100 0, cnot 0 100 1, cnot 50 100 2, meas 100 3, dec 0 4 20 ]

/-- e06 feedforward before decode (std): the PFU fires before its decode
    completes.  VM TokenUnavailable ↔ Lean feedback_after_decode. -/
def e06 : List SysCall :=
  [ req 100 0, cnot 0 100 1, cnot 50 100 2, pfu 0 3, meas 100 3, dec 0 4 ]

/-- e07 ancilla reuse after measurement without reset (std).
    VM QubitReuseViolation ↔ Lean ancilla_freshness. -/
def e07 : List SysCall :=
  [ req 100 0, cnot 0 100 1, meas 100 2, cnot 1 100 3, meas 100 4 ]

/-- e08 ancilla used before ANY request (std).
    VM QubitReuseViolation (start-dirty) ↔ Lean ancilla_freshness. -/
def e08 : List SysCall :=
  [ cnot 0 100 0, meas 100 1 ]

/-- e09 unknown site (std): q[999] lies in no zone.
    VM load error ↔ Lean capacity_in_arch. -/
def e09 : List SysCall :=
  [ { kind := .Measure 999 0, begin_us := 0, end_us := 1 } ]

/-- e10 unsupported gate (std): SWAP (gate id 2) is not in the backend's
    gate table.  VM load error ↔ Lean gate_support. -/
def e10 : List SysCall :=
  [ { kind := .Gate2q 0 1 2, begin_us := 0, end_us := 1 } ]

/-- e11 wrong gate duration (std): a 5 µs CNOT on 1 µs hardware.
    VM load error ↔ Lean gate_support. -/
def e11 : List SysCall :=
  [ req 100 0, cnot 0 100 1 5, meas 100 6 ]

/-- e12 decoder burst (tinyQueue: 4 workers, 8-slot queue): 20 sequential
    measurements feed 20 SIMULTANEOUS decode calls.  VM
    ServiceQueueOverflow (16 queued > 8) ↔ Lean operation_capacity
    (20 active > 4 workers) — same verdict, different mechanism (queue
    dynamics vs concurrency cap).  The leading measures keep I6.a
    causality satisfied so the overload is the ONLY violation. -/
def e12 : List SysCall :=
  ((List.range 20).map fun k => meas k k)
  ++ ((List.range 20).map (fun r => dec r 20))

/-- e13 dangling Live ancilla (std): allocated, used, never measured.
    Lean ancilla_freshness (leak) — the VM has no end-of-schedule leak
    check: DIVERGENCE (Lean-stronger). -/
def e13 : List SysCall :=
  [ req 100 0, cnot 0 100 1 ]

/-- e14 double allocation (std): the same ancilla requested twice with no
    measurement between.  Lean ancilla_freshness (Live → Live) — the VM
    treats a re-reset as benign: DIVERGENCE (Lean-stronger). -/
def e14 : List SysCall :=
  [ req 100 0, req 100 2, meas 100 4 ]

/-- e15 magic-demand window (magicStock: ≤1 request / 12 000 µs, VM holds
    10 MagicState tokens): two requests to DISTINCT factories in one
    window (distinct, so only the demand window fires — not the
    factory-port conflict).  Lean window_throughput (I4) — the VM's causal
    token model is satisfied by the stock: DIVERGENCE (Lean-stronger). -/
def e15 : List SysCall :=
  [ { kind := .RequestMagicState 0, begin_us := 0,   end_us := 12000 }
  , { kind := .RequestMagicState 1, begin_us := 100, end_us := 12100 } ]

/-- e16 slow feedforward (std): a 5 µs PauliFrameUpdate vs the 1 µs cycle.
    Lean feedback_latency — the VM does not duration-check PFUs:
    DIVERGENCE (Lean-stronger). -/
def e16 : List SysCall :=
  [ req 100 0, cnot 0 100 1, cnot 50 100 2, meas 100 3, dec 0 4, pfu 0 5 5 ]

/-- e17 stale feedforward (staleDecode: decode tokens expire after 5 µs):
    the PFU consumes its decode result 35 µs late.  VM
    TokenFreshnessViolation — Lean's feedback_after_decode is order-only
    (no ttl): DIVERGENCE (VM-stronger). -/
def e17 : List SysCall :=
  [ req 100 0, cnot 0 100 1, cnot 50 100 2, meas 100 3, dec 0 4, pfu 0 40 ]

/-- e18 empty interval: `[3,3)us` is rejected by BOTH parsers. -/
def e18 : List SysCall :=
  [ { kind := .Measure 100 0, begin_us := 3, end_us := 3 } ]

/-- A surface-code syndrome-streaming workload on the `surface_d3_stream`
    machine: a 4×4 tile of d=3 patches, each read out once per round as
    ONE measure on its `syn` site (64 bits = 8 stabilizers × 8-bit soft
    data), plus one decode job per round.  `rounds` rounds at `cadence`
    µs. -/
def surfaceRounds (rounds cadence : Nat) : List SysCall :=
  (List.range rounds).flatMap fun r =>
    ((List.range 16).map fun p =>
      ({ kind := .Measure (16 + p) 0
         begin_us := r * cadence, end_us := r * cadence + 1 } : SysCall))
    ++ [ { kind := .DecodeSyndrome r
           begin_us := r * cadence + 1, end_us := r * cadence + 2 } ]

/-- e19 SYNDROME-STREAM FLOOD (surfacestream, 4 KB/ms link): 48 rounds at
    a 25 µs cadence → the first 1000 µs window carries 40 rounds × 16
    patches × 64 bits = 40960 bits > 32768.  Both checkers:
    SYNDROME_BANDWIDTH. -/
def e19 : List SysCall := surfaceRounds 48 25

/-- e20 the same workload PACED to the link: 30 rounds at a 40 µs cadence
    → any window carries ≤ 25 × 1024 = 25600 bits ≤ 32768.  PASS / PASS. -/
def e20 : List SysCall := surfaceRounds 30 40

/-- 1 ms decode calls at the given times, offset past a prefix of
    sequential measurements that causally feed them (strictDecoder
    machine: 2 workers, each OCCUPIED for the full decode latency and
    freed only when it finishes; no queue). -/
def decodesAt (times : List Nat) : List SysCall :=
  ((List.range times.length).map fun k => meas k k)
  ++ ((times.zipIdx).map fun (t, r) =>
    { kind := .DecodeSyndrome r
      begin_us := times.length + t, end_us := times.length + t + 1000 })

/-- e21 DECODER BANDWIDTH SUFFICIENT (strictdecode): 6 one-millisecond
    decodes through 2 workers, in back-to-back pairs.  Succeeds ONLY
    because each worker is freed at the END of its 1 ms latency
    (t = 1000, half-open) and immediately reused by the next decode.
    PASS / PASS — the positive latency-and-reuse test. -/
def e21 : List SysCall := decodesAt [0, 0, 1000, 1000, 2000, 2000]

/-- e22 DECODER OVERSUBSCRIBED (strictdecode): a third decode arrives at
    t = 500 while both workers are mid-decode (busy until 1000).  The
    decoder service is FINITE: Lean counts 3 active > 2 workers; the VM's
    zero-queue service overflows.  Both: DECODER_OVERLOAD. -/
def e22 : List SysCall := decodesAt [0, 0, 500]

/-- e23 PREMATURE REUSE (strictdecode): the third decode starts at
    t = 999 — 1 µs BEFORE a worker's 1 ms latency elapses.  Contrast with
    e21, where starting at exactly t = 1000 passes: the worker is freed
    only when the decode FINISHES.  Both: DECODER_OVERLOAD. -/
def e23 : List SysCall := decodesAt [0, 0, 999]

/-- e24 DECODE BEFORE MEASURE (std): the decoder is called at t = 2
    while the measurement still runs until t = 3 — the syndrome data
    does not exist yet.  Pure space-time causality (every resource is
    free).  Lean I6.a ↔ VM syndrome-token ledger: SYNDROME_CAUSALITY. -/
def e24 : List SysCall :=
  [ meas 0 2, dec 0 2 ]

/-- e25 MAGIC CONSUMED BEFORE PREPARED (magicscarce: ONE prepared state,
    no production): the second consumption has no state behind it.
    Lean I6.b ↔ VM token ledger: MAGIC_SUPPLY. -/
def e25 : List SysCall :=
  [ { kind := .RequestMagicState 0, begin_us := 0, end_us := 1 }
  , { kind := .RequestMagicState 1, begin_us := 5, end_us := 6 } ]

/-- (name, schedule, backend tag) — backends are catalog entries. -/
def corpus : List (String × List SysCall × String) :=
  [ ("e01_clean",            e01, "std")
  , ("e02_qubit_conflict",   e02, "dualrail")
  , ("e03_cnot_cap",         e03, "std")
  , ("e04_cap_reconfigured", e04, "dualrail")
  , ("e05_slow_decode",      e05, "std")
  , ("e06_pfu_before_decode", e06, "std")
  , ("e07_reuse_after_measure", e07, "std")
  , ("e08_use_before_request", e08, "std")
  , ("e09_unknown_site",     e09, "std")
  , ("e10_unsupported_gate", e10, "std")
  , ("e11_wrong_duration",   e11, "std")
  , ("e12_decoder_burst",    e12, "tinyqueue")
  , ("e13_dangling_live",    e13, "std")
  , ("e14_double_request",   e14, "std")
  , ("e15_magic_window",     e15, "magicstock")
  , ("e16_slow_feedforward", e16, "std")
  , ("e17_stale_feedforward", e17, "staledecode")
  , ("e18_empty_interval",   e18, "std")
  , ("e19_syndrome_flood",   e19, "surfacestream")
  , ("e20_syndrome_paced",   e20, "surfacestream")
  , ("e21_decoder_paced",    e21, "strictdecode")
  , ("e22_decoder_oversubscribed", e22, "strictdecode")
  , ("e23_decoder_premature_reuse", e23, "strictdecode")
  , ("e24_decode_before_measure", e24, "std")
  , ("e25_magic_unprepared", e25, "magicscarce") ]

end ErrorCorpus

def main : IO Unit := do
  let dir := "ftq_vm/backend/examples/corpus"
  IO.FS.createDirAll dir
  for (name, sched, backendTag) in ErrorCorpus.corpus do
    IO.FS.writeFile s!"{dir}/{name}.dp"
      (emitSchedule s!"{name} \{backend={backendTag}}" sched ++ "\n")
  let backends : List (String × FormalRV.System.HardwareCatalog.HardwareSpec) :=
    [ ("std",        FormalRV.System.HardwareCatalog.adder_d3)
    , ("dualrail",   FormalRV.System.HardwareCatalog.adder_d3_dualRail)
    , ("tinyqueue",  FormalRV.System.HardwareCatalog.adder_d3_tinyQueue)
    , ("magicstock", FormalRV.System.HardwareCatalog.adder_d3_magicStock)
    , ("staledecode", FormalRV.System.HardwareCatalog.adder_d3_staleDecode)
    , ("surfacestream", FormalRV.System.HardwareCatalog.surface_d3_stream)
    , ("strictdecode", FormalRV.System.HardwareCatalog.adder_d3_strictDecoder)
    , ("magicscarce", FormalRV.System.HardwareCatalog.adder_d3_magicScarce) ]
  for (tag, spec) in backends do
    IO.FS.writeFile s!"{dir}/backend_{tag}.json" spec.toBackendJson
  IO.println s!"wrote {ErrorCorpus.corpus.length} programs + {backends.length} backends to {dir}/"
