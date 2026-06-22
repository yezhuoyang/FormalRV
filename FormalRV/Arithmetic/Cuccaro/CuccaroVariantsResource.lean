/-
  FormalRV.Arithmetic.Cuccaro.CuccaroVariantsResource
  ───────────────────────────────────────────────────
  THE time-resource (T-count) theorems for every DERIVED Cuccaro gadget —
  closing the audit gap "the variants have semantics + WellTyped but no count
  theorems" (arithmetic-gadget audit, 2026-06-10).

  Every theorem is ANCHORED: the left-hand side is the independent tree-walker
  `Gate.tcount` (= `Resource.countT` via the bridge in `Resource/GateCount.lean`)
  applied to THE SAME syntactic object the variant's semantic-correctness
  theorem verifies.  Nothing here can cheat — the counters live in their own
  world and the numbers are forced by the trees.

  Closed forms (per `bits`-bit gadget; preparations are X/CX-only, hence T-free):

    cuccaro_prepareConstRead              0
    cuccaro_addConstGate                  14·bits     (prepare ; adder ; prepare)
    cuccaro_subConstGate                  14·bits     (= addConst (2^bits − N))
    cuccaro_compareConstForwardGate        7·bits     (prepare ; MAJ chain)
    cuccaro_subConstForward/ReverseOnly    7·bits each
    cuccaro_maj_chain_inv                  7·bits
    sqir_prepareMaskedConstRead            0
    sqir_conditionalAdd/SubConstGate      14·bits
    sqir_style_compareConst_candidate     14·bits     (compute ; CX ; uncompute)
    sqir_controlledCompareConst           14·bits
    sqir_style_modAddConst_skeleton       28·bits
    sqir_style_modAddConst_dirtyFlag      42·bits
    sqir_style_modAddConst_clean_*        56·bits     (the ModularAdder/Cuccaro gate)
    sqir_style_controlledModAddConst_*    56·bits

  NOTE: the SQIR-chain prerequisite lemmas (prepare/conditional/comparator/
  controlled-candidate counts) are PRIVATE here because `ModMult/Internal/
  ToffoliCount.lean` declares public twins of the same names (it is in this
  file's downstream import closure via the ModularAdder umbrella).  Follow-up
  consolidation: make THIS file the canonical home and have ModMult import it.

  Cross-check: the proven ModMult composite `modmult_tcount = 112·bits²`
  is exactly `2 × bits × 56·bits` — `bits` controlled mod-adds at `56·bits`
  each, forward + uncompute.  The per-gadget counts here are the missing
  per-layer anchors beneath that composite.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroSubConst
import FormalRV.Arithmetic.Cuccaro.CuccaroModReduce
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRModAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRDirtyFlag.CuccaroModularAddDefinitions

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## §1. Preparations are T-free (X / CX / I only). -/

@[simp] private theorem tcount_cuccaro_prepareConstRead (n q_start c : Nat) :
    tcount (cuccaro_prepareConstRead n q_start c) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (cuccaro_prepareConstRead k q_start c)
                     (cond (c.testBit k) (Gate.X (q_start + 2 * k + 2)) Gate.I)) = 0
    cases c.testBit k <;> simp [tcount, ih]

@[simp] private theorem tcount_sqir_prepareMaskedConstRead (n q_start N flagPos : Nat) :
    tcount (sqir_prepareMaskedConstRead n q_start N flagPos) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (sqir_prepareMaskedConstRead k q_start N flagPos)
                     (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I)) = 0
    cases N.testBit k <;> simp [tcount, ih]

/-! ## §2. Add/sub-constant: the adder's `14·bits`, prepares free. -/

/-- **Add-constant T-count = 14·bits** — the same syntactic object verified by
`cuccaro_addConstGate_clean`. -/
theorem tcount_cuccaro_addConstGate (bits q_start c : Nat) :
    tcount (cuccaro_addConstGate bits q_start c) = 14 * bits := by
  show tcount (seq (cuccaro_prepareConstRead bits q_start c)
                   (seq (cuccaro_n_bit_adder_full bits q_start)
                        (cuccaro_prepareConstRead bits q_start c))) = 14 * bits
  simp [tcount, tcount_cuccaro_n_bit_adder_full]

/-- **Sub-constant T-count = 14·bits** — the object verified by
`cuccaro_subConstGate_clean` (two's-complement add). -/
theorem tcount_cuccaro_subConstGate (bits q_start N : Nat) :
    tcount (cuccaro_subConstGate bits q_start N) = 14 * bits :=
  tcount_cuccaro_addConstGate bits q_start (2 ^ bits - N)

/-! ## §3. Comparator / mod-reduce halves: one MAJ chain = `7·bits`. -/

/-- **Forward comparator T-count = 7·bits** — the object verified by
`cuccaro_compareConstGate_top_carry`. -/
theorem tcount_cuccaro_compareConstForwardGate (bits q_start N : Nat) :
    tcount (cuccaro_compareConstForwardGate bits q_start N) = 7 * bits := by
  show tcount (seq (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))
                   (cuccaro_maj_chain bits q_start)) = 7 * bits
  simp [tcount, tcount_cuccaro_maj_chain]

/-- Forward-only subtract half (= the forward comparator). -/
theorem tcount_cuccaro_subConstForwardOnlyGate (bits q_start N : Nat) :
    tcount (cuccaro_subConstForwardOnlyGate bits q_start N) = 7 * bits :=
  tcount_cuccaro_compareConstForwardGate bits q_start N

/-- Reverse-only subtract half: the reverse UMA chain (7·bits), prepare free. -/
theorem tcount_cuccaro_subConstReverseOnlyGate (bits q_start N : Nat) :
    tcount (cuccaro_subConstReverseOnlyGate bits q_start N) = 7 * bits := by
  show tcount (seq (cuccaro_uma_chain_reverse bits q_start)
                   (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))) = 7 * bits
  simp [tcount, tcount_cuccaro_uma_chain_reverse]

/-! ## §4. The inverse MAJ chain (used by the SQIR comparator's uncompute). -/

@[simp] private theorem tcount_cuccaro_MAJ_inv (a b c : Nat) :
    tcount (cuccaro_MAJ_inv a b c) = 7 := rfl

private theorem tcount_cuccaro_maj_chain_inv (n q_start : Nat) :
    tcount (cuccaro_maj_chain_inv n q_start) = 7 * n := by
  induction n generalizing q_start with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (cuccaro_maj_chain_inv k (q_start + 2))
                     (cuccaro_MAJ_inv q_start (q_start + 1) (q_start + 2))) = 7 * (k + 1)
    simp [tcount, ih]
    omega

/-! ## §5. The SQIR-style comparator: compute (7·bits) ; CX ; uncompute (7·bits). -/

/-- **SQIR comparator T-count = 14·bits** — the object verified by
`sqir_style_compareConst_candidate_flag` / `…_workspace_restored_at`. -/
private theorem tcount_sqir_style_compareConst_candidate (bits q_start N flagPos : Nat) :
    tcount (sqir_style_compareConst_candidate bits q_start N flagPos) = 14 * bits := by
  show tcount (seq (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))
                   (seq (cuccaro_maj_chain bits q_start)
                        (seq (Gate.CX (q_start + 2 * bits) flagPos)
                             (seq (cuccaro_maj_chain_inv bits q_start)
                                  (cuccaro_prepareConstRead bits q_start (2 ^ bits - N))))))
        = 14 * bits
  simp [tcount, tcount_cuccaro_maj_chain, tcount_cuccaro_maj_chain_inv]
  omega

/-- Controlled comparator (masked prepares): same `14·bits`. -/
private theorem tcount_sqir_controlledCompareConst (bits q_start c controlIdx flagPos : Nat) :
    tcount (sqir_controlledCompareConst bits q_start c controlIdx flagPos) = 14 * bits := by
  show tcount (seq (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - c) controlIdx)
                   (seq (cuccaro_maj_chain bits q_start)
                        (seq (Gate.CX (q_start + 2 * bits) flagPos)
                             (seq (cuccaro_maj_chain_inv bits q_start)
                                  (sqir_prepareMaskedConstRead bits q_start (2 ^ bits - c) controlIdx)))))
        = 14 * bits
  simp [tcount, tcount_cuccaro_maj_chain, tcount_cuccaro_maj_chain_inv]
  omega

/-! ## §6. Conditional (flag-controlled) add / sub: `14·bits`. -/

/-- **Conditional add-constant T-count = 14·bits** (masked prepare ; adder ;
masked unprepare) — the object whose WellTyped is
`sqir_conditionalAddConstGate_wellTyped`. -/
private theorem tcount_sqir_conditionalAddConstGate (bits q_start N flagPos : Nat) :
    tcount (sqir_conditionalAddConstGate bits q_start N flagPos) = 14 * bits := by
  show tcount (seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
                   (seq (cuccaro_n_bit_adder_full bits q_start)
                        (sqir_prepareMaskedConstRead bits q_start N flagPos))) = 14 * bits
  simp [tcount, tcount_cuccaro_n_bit_adder_full]

private theorem tcount_sqir_conditionalSubConstGate (bits q_start N flagPos : Nat) :
    tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 14 * bits :=
  tcount_sqir_conditionalAddConstGate bits q_start (2 ^ bits - N) flagPos

/-! ## §7. The modular-add pipelines. -/

/-- Skeleton (add ; compare): `14 + 14 = 28·bits`. -/
theorem tcount_sqir_style_modAddConst_skeleton (bits q_start N c flagPos : Nat) :
    tcount (sqir_style_modAddConst_skeleton bits q_start N c flagPos) = 28 * bits := by
  show tcount (seq (cuccaro_addConstGate bits q_start c)
                   (sqir_style_compareConst_candidate bits q_start N flagPos)) = 28 * bits
  simp [tcount, tcount_cuccaro_addConstGate, tcount_sqir_style_compareConst_candidate]
  omega

/-- Dirty-flag pipeline (add ; compare ; conditional-sub): `42·bits` —
the object verified by `sqir_style_modAddConst_dirtyFlag_clean_except_flag`. -/
theorem tcount_sqir_style_modAddConst_dirtyFlag_candidate
    (bits q_start N c flagPos : Nat) :
    tcount (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
      = 42 * bits := by
  show tcount (seq (cuccaro_addConstGate bits q_start c)
                   (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                        (sqir_conditionalSubConstGate bits q_start N flagPos))) = 42 * bits
  simp [tcount, tcount_cuccaro_addConstGate, tcount_sqir_style_compareConst_candidate,
        tcount_sqir_conditionalSubConstGate]
  omega

/-- Clean pipeline (dirty ; flag-uncompute compare ; X): `56·bits` —
the object verified by `sqir_style_modAddConst_clean_candidate_clean`. -/
theorem tcount_sqir_style_modAddConst_clean_candidate
    (bits q_start N c flagPos : Nat) :
    tcount (sqir_style_modAddConst_clean_candidate bits q_start N c flagPos)
      = 56 * bits := by
  show tcount (seq (sqir_style_modAddConst_dirtyFlag_candidate bits q_start N c flagPos)
                   (seq (sqir_style_compareConst_candidate bits q_start c flagPos)
                        (Gate.X flagPos))) = 56 * bits
  simp [tcount, tcount_sqir_style_modAddConst_dirtyFlag_candidate,
        tcount_sqir_style_compareConst_candidate]
  omega

/-- **THE clean modular add-constant gate (= `ModularAdder/Cuccaro`'s gate):
T-count = 56·bits** (0 in the dispatched `c = 0` identity case) — the object
verified by `sqir_style_modAddConst_clean_gate`'s correctness bundle. -/
theorem tcount_sqir_style_modAddConst_clean_gate (bits N c : Nat) :
    tcount (sqir_style_modAddConst_clean_gate bits N c)
      = if c = 0 then 0 else 56 * bits := by
  by_cases hc : c = 0 <;>
    simp [sqir_style_modAddConst_clean_gate, hc,
          tcount_sqir_style_modAddConst_clean_candidate, tcount]

/-! ## §8. The controlled modular-add pipeline (ModMult's per-bit primitive). -/

/-- Controlled candidate (cond-add ; compare ; cond-sub ; ctrl-compare ; CX):
`14·4 = 56·bits` — the object verified by
`sqir_style_controlledModAddConst_candidate_clean_qstart`. -/
private theorem tcount_sqir_style_controlledModAddConst_candidate
    (bits q_start N c controlIdx flagPos : Nat) :
    tcount (sqir_style_controlledModAddConst_candidate bits q_start N c controlIdx flagPos)
      = 56 * bits := by
  show tcount (seq (sqir_conditionalAddConstGate bits q_start c controlIdx)
                   (seq (sqir_style_compareConst_candidate bits q_start N flagPos)
                        (seq (sqir_conditionalSubConstGate bits q_start N flagPos)
                             (seq (sqir_controlledCompareConst bits q_start c controlIdx flagPos)
                                  (Gate.CX controlIdx flagPos))))) = 56 * bits
  simp [tcount, tcount_sqir_conditionalAddConstGate, tcount_sqir_style_compareConst_candidate,
        tcount_sqir_conditionalSubConstGate, tcount_sqir_controlledCompareConst]
  omega

/-- **THE controlled clean modular add-constant gate: T-count = 56·bits**
(0 for `c = 0`).  ModMult's `112·bits²` = `2 × bits ×` THIS count — the
per-layer anchor beneath the proven composite. -/
theorem tcount_sqir_style_controlledModAddConst_gate
    (bits q_start N c controlIdx flagPos : Nat) :
    tcount (sqir_style_controlledModAddConst_gate bits q_start N c controlIdx flagPos)
      = if c = 0 then 0 else 56 * bits := by
  by_cases hc : c = 0 <;>
    simp [sqir_style_controlledModAddConst_gate, hc,
          tcount_sqir_style_controlledModAddConst_candidate, tcount]

/-! ## §9. Smoke instances (third-party `#eval`-testable closed forms). -/

example : tcount (cuccaro_addConstGate 4 0 11) = 56 := by decide
example : tcount (cuccaro_compareConstForwardGate 4 0 11) = 28 := by decide
example : tcount (sqir_style_modAddConst_clean_gate 3 5 2) = 168 := by decide

end FormalRV.BQAlgo
