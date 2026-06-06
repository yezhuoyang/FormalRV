/-
  FormalRV.LatticeSurgery.SurfaceShorFullSchedule — the FULL detailed system-level
  schedule of a surface-code Shor fragment, with BOTH the resource-invariant
  check (A) AND the causal-dependency check (B) verified together.

  This is the system-layer capstone: a concrete, time-resolved `SysCall` schedule
  for two logical Toffolis of Shor's modular exponentiation, each compiled to a
  surface-code magic-injection lattice surgery (one |CCZ⟩ request + three M_ZZ
  merges) interleaved with syndrome extraction, decoding, and feed-forward Pauli
  corrections — and the two sub-circuits sequenced causally.

  We prove the schedule satisfies, by ONE uniform `checkAll`:
   • (A) RESOURCE conflict-freedom — capacity, exclusivity, latency, T-factory
         throughput, decoder reaction (`baseInvariants`); and
   • (B) CAUSAL dependencies — every producer finishes before its consumer starts
         (`causalityInv shorDeps`): magic→merge, merge+syndrome→decode,
         decode→feed-forward, and sub-circuit C₁→C₂ (qianxu App. E).
  Negative tests show each class independently rejects a violating schedule.

  Hardware-neutral: `moves := []`, so (per `SurfaceSystemCompile`) the schedule is
  valid on superconducting AND neutral-atom platforms.

  Connection to the verified circuit layer: the 2 `RequestMagicState` are the 2
  Toffolis' magic states (one each, `teleportCCX_one_magic`); the 6 merge
  `Measure`s are the 2×3 surgery merges of `cczInjectionSchedule`
  (`MagicInjectionSurgery`).  Qubit indices lie in disjoint layout patches
  (`SurfaceSystemCompile.patches_disjoint`).

  No `sorry`, no new `axiom`.
-/

import FormalRV.System.DependencyGraph
import FormalRV.LatticeSurgery.MagicInjectionSurgery

namespace FormalRV.LatticeSurgery.SurfaceShorFullSchedule

open FormalRV.Framework.Architecture
open FormalRV.Framework.InvariantFramework
open FormalRV.System.DependencyGraph

/-! ## The detailed schedule — two Toffolis, fully resolved in time

    Time units µs.  Zones (demoArch): Data [0,10), Workspace [10,20) (surgery
    merges), Factory [20,30), Routing [30,40).  Each Toffoli: factory makes the
    |CCZ⟩ while a syndrome round runs (concurrent), then three M_ZZ merges, then
    decode, then the feed-forward Pauli-frame update.  C₂ follows C₁. -/
def shorSched : List SysCall :=
  [ -- Toffoli 1 (sub-circuit C₁)
    { kind := SysCallKind.RequestMagicState 2, begin_us := 0,  end_us := 10 }   -- 0 |CCZ⟩ for T1
  , { kind := SysCallKind.Measure 5 0,         begin_us := 0,  end_us := 10 }   -- 1 syndrome round (Data)
  , { kind := SysCallKind.Measure 10 0,        begin_us := 10, end_us := 20 }   -- 2 merge M_ZZ #1
  , { kind := SysCallKind.Measure 11 0,        begin_us := 10, end_us := 20 }   -- 3 merge M_ZZ #2
  , { kind := SysCallKind.Measure 12 0,        begin_us := 10, end_us := 20 }   -- 4 merge M_ZZ #3
  , { kind := SysCallKind.DecodeSyndrome 0,    begin_us := 20, end_us := 25 }   -- 5 decode T1
  , { kind := SysCallKind.PauliFrameUpdate 0,  begin_us := 25, end_us := 26 }   -- 6 feed-forward T1
    -- Toffoli 2 (sub-circuit C₂, sequential after C₁)
  , { kind := SysCallKind.RequestMagicState 2, begin_us := 26, end_us := 36 }   -- 7 |CCZ⟩ for T2
  , { kind := SysCallKind.Measure 6 0,         begin_us := 26, end_us := 36 }   -- 8 syndrome round
  , { kind := SysCallKind.Measure 13 0,        begin_us := 36, end_us := 46 }   -- 9 merge M_ZZ #1
  , { kind := SysCallKind.Measure 14 0,        begin_us := 36, end_us := 46 }   -- 10 merge M_ZZ #2
  , { kind := SysCallKind.Measure 15 0,        begin_us := 36, end_us := 46 }   -- 11 merge M_ZZ #3
  , { kind := SysCallKind.DecodeSyndrome 1,    begin_us := 46, end_us := 51 }   -- 12 decode T2
  , { kind := SysCallKind.PauliFrameUpdate 1,  begin_us := 51, end_us := 52 } ] -- 13 feed-forward T2

/-! ## The causal dependency DAG (qianxu App. E producer→consumer edges) -/
def shorDeps : DepGraph :=
  { edges :=
    [ -- T1: magic → each merge
      ⟨0, 2⟩, ⟨0, 3⟩, ⟨0, 4⟩
      -- T1: merges + syndrome → decode
    , ⟨2, 5⟩, ⟨3, 5⟩, ⟨4, 5⟩, ⟨1, 5⟩
      -- T1: decode → feed-forward
    , ⟨5, 6⟩
      -- sub-circuit C₁ → C₂ (sequential): T1 feed-forward → T2 magic + syndrome
    , ⟨6, 7⟩, ⟨6, 8⟩
      -- T2: magic → each merge
    , ⟨7, 9⟩, ⟨7, 10⟩, ⟨7, 11⟩
      -- T2: merges + syndrome → decode
    , ⟨9, 12⟩, ⟨10, 12⟩, ⟨11, 12⟩, ⟨8, 12⟩
      -- T2: decode → feed-forward
    , ⟨12, 13⟩ ] }

/-! ## The system context (hardware-neutral) -/
def shorCtx : SystemCtx :=
  { arch := demoArch, sched := shorSched, moves := [],
    window_us := 26, max_per_window := 1, t_react_us := 10, distance_fn := demoDist }

/-! ## (A) Resource conflict-freedom -/

/-- The detailed two-Toffoli surface-code schedule passes every base invariant:
    capacity, exclusivity, latency, T-factory throughput (≤1 |CCZ⟩ per 26 µs
    window — one factory), and decoder reaction. -/
theorem shorCtx_resource_ok : checkAll baseInvariants shorCtx = true := by decide

/-! ## (B) Causal dependencies -/

/-- The schedule RESPECTS every causal edge — magic→merge, merge+syndrome→decode,
    decode→feed-forward, and the sequential C₁→C₂ ordering. -/
theorem shorCtx_causality_ok : respectsCausality shorSched shorDeps = true := by decide

/-! ## (A) ∧ (B): the unified check -/

/-- **FULL SYSTEM-LEVEL CORRECTNESS.**  The detailed surface-code Shor schedule
    satisfies RESOURCE conflict-freedom AND CAUSAL dependencies under one uniform
    `checkAll` — the "max parallelism subject to (A) and (B)" criterion, machine-
    checked on a fully time-resolved physical schedule. -/
theorem shorCtx_fully_valid :
    checkAll (baseInvariants ++ [causalityInv shorDeps]) shorCtx = true := by decide

/-! ## Negative tests — each class independently rejects a violation -/

/-- Putting T2's feed-forward (13) BEFORE its decode (12) breaks edge ⟨12,13⟩. -/
def badCausalSched : List SysCall :=
  shorSched.set 12 { kind := SysCallKind.DecodeSyndrome 1, begin_us := 55, end_us := 60 }

def badCausalCtx : SystemCtx := { shorCtx with sched := badCausalSched }

/-- It still passes the RESOURCE invariants (A)… -/
theorem badCausal_resource_ok : checkAll baseInvariants badCausalCtx = true := by decide
/-- …but FAILS causality (B): a correction cannot precede the decode producing it. -/
theorem badCausal_causality_fails :
    (causalityInv shorDeps).check badCausalCtx = false := by decide
/-- …so the unified check rejects it. -/
theorem badCausal_unified_fails :
    checkAll (baseInvariants ++ [causalityInv shorDeps]) badCausalCtx = false := by decide

/-- Asking BOTH Toffolis' |CCZ⟩ in the SAME window (T2 magic at 5 µs) exceeds the
    one-factory throughput — RESOURCE (A) rejects it, independently of causality. -/
def badThroughputSched : List SysCall :=
  shorSched.set 7 { kind := SysCallKind.RequestMagicState 2, begin_us := 5, end_us := 15 }
def badThroughputCtx : SystemCtx := { shorCtx with sched := badThroughputSched }
theorem badThroughput_resource_fails :
    checkAll baseInvariants badThroughputCtx = false := by decide

/-! ## Connection to the verified circuit layer (counts must line up) -/

/-- The schedule issues exactly 2 magic-state requests = 2 Toffolis, one |CCZ⟩
    each (`MagicInjectionSurgery.teleportCCX_one_magic`). -/
theorem two_magic_requests :
    (shorSched.filter (fun sc => match sc.kind with
      | SysCallKind.RequestMagicState _ => true | _ => false)).length = 2 := by decide

/-- The schedule issues exactly 6 merge measurements = 2 Toffolis × 3 M_ZZ merges
    (`MagicInjectionSurgery.cczInjectionSchedule` is a 3-merge schedule). -/
theorem six_merge_measurements :
    (shorSched.filter (fun sc => match sc.kind with
      | SysCallKind.Measure q _ => decide (10 ≤ q) | _ => false)).length = 6 := by decide

end FormalRV.LatticeSurgery.SurfaceShorFullSchedule
