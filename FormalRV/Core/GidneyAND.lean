/-
  FormalRV.Core.GidneyAND — the REAL Gidney 2018 measurement-based logical-AND as an
  honest Clifford+T circuit with FOUR genuine T-gates, and a PROOF of its semantics.

  ## No cost model — a real circuit

  arXiv:1805.03662 §III.A's unary-iteration QROM costs `4L − 4` T because each of its
  `L − 1` ANDs is Gidney's *temporary AND* (arXiv:1709.06648): a Toffoli into a CLEAN
  ancilla using only 4 T-gates (the seventh-T textbook Toffoli's three control-phase
  fix-up T's are unnecessary when the target starts `|0⟩` and is uncomputed by
  measurement).

  This file builds that circuit at the unitary (`BaseUCom`) level with FOUR literal
  `U_T`/`U_TDAG` gates — `gidneyAND` — and PROVES (`gidneyAND_correct`, axiom-clean,
  reusing the proven 7-T `f_to_vec_CCX` machinery) that on every clean-target basis
  state it computes the AND:

    `uc_eval (gidneyAND a b c) · |a,b,0⟩ = |a, b, a ∧ b⟩`.

  The T-count is the LITERAL number of `T`/`T†` gates (`tGateCount`), proved `= 4` —
  NOT `tcount / 7`.  The textbook 7-T Toffoli is `tGateCount (CCX a b c) = 7`, also
  by literal count, so the `4 : 7` ratio is between two genuine circuits.

  ## Derivation (why exactly these gates)

  `BaseUCom.CCX = s₁;s₂;s₃;(T a;T b;T c;H c)` (7 T).  On a `|c=0⟩` input the suffix
  `s₃;T a;T b` only applies a phase `χ(a,b)` to the `(a,b)` register, with
  `χ(1,1)=i`, else `1`.  Dropping it leaves `s₁;s₂;T c;H c` (4 T) which computes the
  AND up to a `-i` phase on the `|1,1⟩` input; a single Clifford `S c` (0 T) corrects
  it.  Hence `gidneyAND = s₁;s₂;T c;H c;S c`.  Verified here against `f_to_vec_CCX`'s
  own 8-gate prefix lemma `f_to_vec_CCX_prefix_8`.

  No `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Core.GateDecompositions
import FormalRV.Core.PadAction.PadActionComposite

namespace FormalRV.Framework

open Matrix Complex BaseUCom

noncomputable section

/-! ## §1. The circuit: four genuine T-gates. -/

/-- **Gidney's measurement-based logical-AND (compute), 4 T-gates.**  The 7-T Toffoli
    `BaseUCom.CCX` with its three control-phase fix-up T's (`s₃`, `T a`, `T b`) dropped
    and replaced by the Clifford `S c` — valid because the target `c` starts `|0⟩`.
    Left-associated to share the proven `f_to_vec_CCX_prefix_8` (`s₁;s₂`). -/
def gidneyAND {dim : Nat} (a b c : Nat) : BaseUCom dim :=
  UCom.seq (UCom.seq (UCom.seq
    (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq (UCom.seq
      (BaseUCom.H c) (BaseUCom.CNOT b c)) (BaseUCom.TDAG c))
      (BaseUCom.CNOT a c))
      (BaseUCom.T c))
      (BaseUCom.CNOT b c))
      (BaseUCom.TDAG c))
      (BaseUCom.CNOT a c))           -- s₁;s₂  (= f_to_vec_CCX_prefix_8 chain)
      (BaseUCom.T c))                -- 4th T
      (BaseUCom.H c))
      (BaseUCom.S c)                 -- Clifford phase correction (0 T)

/-! ## §2. Semantic correctness: it computes the AND on a clean target. -/

/-- **★ THE GIDNEY-AND IS CORRECT ★.**  On any basis state with the target clean
    (`f c = false`), the 4-T `gidneyAND a b c` computes the logical AND into `c`:
    `|a,b,0⟩ ↦ |a, b, a ∧ b⟩`.  Proven via the 7-T Toffoli's own prefix lemma
    `f_to_vec_CCX_prefix_8` (the shared `s₁;s₂`) plus the `T;H;S` tail and the 4-case
    `exp(iπ/4)` phase arithmetic. -/
theorem gidneyAND_correct {dim : Nat} (a b c : Nat)
    (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Nat → Bool) (hfc : f c = false) :
    uc_eval (gidneyAND a b c : BaseUCom dim) * f_to_vec dim f
      = f_to_vec dim (update f c (f a && f b)) := by
  unfold gidneyAND
  rw [uc_eval_seq_mul, uc_eval_seq_mul, uc_eval_seq_mul,
      f_to_vec_CCX_prefix_8 dim a b c ha hb hc hac hbc f]
  -- ── gate 9: T c — push S·H·T to the two leaves, apply T ──
  simp only [mul_add_state, mul_smul_state]
  rw [f_to_vec_T_uc_eval dim c hc (update f c false),
      f_to_vec_T_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false,
      show (update f c true) c = true from update_eq f c true]
  simp only [Bool.false_eq_true, if_false, if_true, one_smul, mul_smul_state, smul_smul]
  -- ── gate 10: H c ──
  rw [f_to_vec_H_uc_eval dim c hc (update f c false),
      f_to_vec_H_uc_eval dim c hc (update f c true)]
  simp only [update_idem]
  rw [show (update f c false) c = false from update_eq f c false,
      show (update f c true) c = true from update_eq f c true]
  simp only [Bool.false_eq_true, if_false, if_true, one_mul, mul_add_state, mul_smul_state,
             smul_smul]
  -- ── gate 11: S c ──
  rw [f_to_vec_S_uc_eval dim c hc (update f c false),
      f_to_vec_S_uc_eval dim c hc (update f c true)]
  rw [show (update f c false) c = false from update_eq f c false,
      show (update f c true) c = true from update_eq f c true]
  simp only [Bool.false_eq_true, if_false, if_true, one_smul, smul_smul]
  -- phase identities (in the `ring_nf` angle form `I·π·(±1/4)`) and `√2² = 2`, `I² = -1`
  have cvt1 : Complex.exp (Complex.I * ↑Real.pi * (1/4))
      = Complex.exp (Complex.I * (Real.pi/4)) := by congr 1; ring
  have cvt2 : Complex.exp (Complex.I * ↑Real.pi * (-1/4))
      = Complex.exp (-(Complex.I * (Real.pi/4))) := by congr 1; ring
  cases hfa : f a <;> cases hfb : f b <;>
    simp only [hfa, hfb, hfc, Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor,
      Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, reduceIte, if_true, if_false, one_mul, mul_one] <;>
    ring_nf <;>
    simp only [cvt1, cvt2, exp_pi4_pow_two_eq_I, exp_neg_pi4_pow_two_eq_neg_I,
      exp_pi4_mul_exp_neg_pi4, exp_neg_pi4_mul_exp_pi4] <;>
    match_scalars <;>
    (apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im,
        pow_succ, pow_zero,
        mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero, zero_sub,
        neg_zero, neg_neg, mul_neg, neg_mul] <;>
      ring_nf <;>
      norm_num [Real.sq_sqrt, Real.mul_self_sqrt])

/-! ## §3. The LITERAL T-gate count — not `tcount / 7`. -/

open Classical in
/-- **The honest T-count of a unitary circuit**: the LITERAL number of `T`/`T†`
    (`U_T`/`U_TDAG`) gate applications.  No Toffoli model, no `tcount / 7` — this counts
    the genuine `π/4` rotations a circuit contains. -/
def tGateCount {dim : Nat} : BaseUCom dim → Nat
  | UCom.seq x y => tGateCount x + tGateCount y
  | UCom.app1 u _ => if u = U_T ∨ u = U_TDAG then 1 else 0
  | UCom.app2 _ _ _ => 0
  | UCom.app3 _ _ _ _ => 0

private theorem U_H_ne_U_T : (U_H : BaseUnitary 1) ≠ U_T := by
  rw [U_H, U_T]; intro h; rw [BaseUnitary.R.injEq] at h
  have := Real.pi_pos; linarith [h.1]

private theorem U_H_ne_U_TDAG : (U_H : BaseUnitary 1) ≠ U_TDAG := by
  rw [U_H, U_TDAG]; intro h; rw [BaseUnitary.R.injEq] at h
  have := Real.pi_pos; linarith [h.1]

private theorem U_S_ne_U_T : (U_S : BaseUnitary 1) ≠ U_T := by
  rw [U_S, U_T]; intro h; rw [BaseUnitary.R.injEq] at h
  have := Real.pi_pos; linarith [h.2.2]

private theorem U_S_ne_U_TDAG : (U_S : BaseUnitary 1) ≠ U_TDAG := by
  rw [U_S, U_TDAG]; intro h; rw [BaseUnitary.R.injEq] at h
  have := Real.pi_pos; linarith [h.2.2]

/-- **★ The Gidney AND has exactly FOUR T-gates ★** — a literal count of `U_T`/`U_TDAG`
    nodes (two `T†` + two `T`), matching arXiv:1805.03662 fig. temporary-and-notation's
    "4 |T⟩ states". -/
theorem tGateCount_gidneyAND {dim : Nat} (a b c : Nat) :
    tGateCount (gidneyAND a b c : BaseUCom dim) = 4 := by
  simp only [gidneyAND, tGateCount, BaseUCom.H, BaseUCom.T, BaseUCom.TDAG, BaseUCom.S,
    BaseUCom.CNOT, U_H_ne_U_T, U_H_ne_U_TDAG, U_S_ne_U_T, U_S_ne_U_TDAG,
    or_false, false_or, or_self, if_false, eq_self_iff_true, true_or, or_true, if_true]

/-- **The textbook 7-T Toffoli has exactly SEVEN T-gates** — same literal count, so the
    `4 : 7` saving of the temporary AND is between two genuine Clifford+T circuits, with no
    `tcount / 7` heuristic anywhere. -/
theorem tGateCount_CCX {dim : Nat} (a b c : Nat) :
    tGateCount (BaseUCom.CCX a b c : BaseUCom dim) = 7 := by
  simp only [BaseUCom.CCX, tGateCount, BaseUCom.H, BaseUCom.T, BaseUCom.TDAG,
    BaseUCom.CNOT, U_H_ne_U_T, U_H_ne_U_TDAG,
    or_false, false_or, or_self, if_false, eq_self_iff_true, true_or, or_true, if_true]

end
