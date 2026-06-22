/-
  FormalRV.QEC.Cultivation.TStateCheck
  ------------------------------------
  **The semantic CORE of magic-state cultivation's check step** — a faithful
  re-implementation of the "controlled-H check" of

    Gidney, Shutty, Jones, "Magic state cultivation: growing T states as cheap
    as CNOT gates", arXiv:2409.17595 (the cultivation stage, §Construction),
    following Chamberland-Noh's GHZ-controlled transversal-H check that it builds on.

  The cultivation check verifies that the encoded state is the magic state
  `|T⟩ = T|+⟩`.  The verification observable is `H_XY = (X+Y)/√2` (the magic
  state's stabilizer: `H_XY|T⟩ = |T⟩`).  The check is implemented as a
  *controlled-`H_XY`*: with the control in `|+⟩` and the target in `|T⟩`, phase
  kickback leaves the control in `|+⟩` (deterministic `+1`, NO detection — the
  check passes); on the orthogonal magic state `T|−⟩` (the `−1` eigenstate) the
  control flips to `|−⟩` (detection — the check has TEETH).

  Gidney's circuit-level trick (the "double cat check", `cat-check-d3`): apply
  `T†` to the data first, turning the `H_XY` check into a plain `X`-parity check,
  because `T·X·T† = H_XY` and `T†|T⟩ = |+⟩`.  Both halves are proved here on the
  real 2×2 / 4×4 matrices (NOT axiomatized).

  This file proves the semantic kernel; the stage/gadget scaffolding lives in
  `Cultivation.Stages`.  We do NOT claim full circuit-level fault-distance
  correctness (out of scope, per the brief).
-/
import Mathlib
import FormalRV.Core.UnitarySem

namespace FormalRV.QEC.Cultivation

open Matrix Complex
open FormalRV.Framework (σx σy σi)

noncomputable section

/-! ## §1. The T-phase `ω = e^{iπ/4} = (1+i)/√2` and its conjugate. -/

/-- `s = 1/√2` (written `√2/2`), as a complex scalar. -/
noncomputable def s : ℂ := (Real.sqrt 2 / 2 : ℝ)

/-- The `T`-phase `ω = e^{iπ/4} = (1+i)/√2`. -/
noncomputable def ω : ℂ := s * (1 + I)

/-- Its conjugate `ω* = e^{-iπ/4} = (1-i)/√2`. -/
noncomputable def cω : ℂ := s * (1 - I)

@[simp] lemma s_sq : s * s = 1 / 2 := by
  have h : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [s]
  rw [← Complex.ofReal_mul, h]; norm_num

/-- `ω · ω* = 1` (the phase has unit modulus). -/
@[simp] lemma omega_comega : ω * cω = 1 := by
  have h2 : (1 + I) * (1 - I) = 2 := by
    have h : (1 + I) * (1 - I) = 1 - I ^ 2 := by ring
    rw [h, Complex.I_sq]; ring
  have hsplit : ω * cω = (s * s) * ((1 + I) * (1 - I)) := by
    simp only [ω, cω]; ring
  rw [hsplit, h2, s_sq]; ring

@[simp] lemma comega_omega : cω * ω = 1 := by
  rw [mul_comm]; exact omega_comega

/-- `ω* = star ω` (so it really is the complex conjugate). -/
@[simp] lemma star_omega : star ω = cω := by
  simp only [ω, cω, s]
  rw [star_mul']
  simp [Complex.star_def, Complex.conj_ofReal]
  ring

/-- Faithfulness: `ω = e^{iπ/4}` matches the framework's `T`-gate phase. -/
lemma omega_eq_exp : ω = Complex.exp (↑(Real.pi / 4) * I) := by
  rw [Complex.exp_mul_I]
  have hc : Complex.cos (↑(Real.pi / 4)) = (Real.sqrt 2 / 2 : ℝ) := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hs : Complex.sin (↑(Real.pi / 4)) = (Real.sqrt 2 / 2 : ℝ) := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [hc, hs]; simp only [ω, s]; ring

/-! ## §2. The check observable `H_XY = (X+Y)/√2` and the magic state `|T⟩`. -/

/-- The check observable `H_XY = (X+Y)/√2 = !![0, ω*; ω, 0]`. -/
def hXY : Matrix (Fin 2) (Fin 2) ℂ := !![0, cω; ω, 0]

/-- Faithfulness: `H_XY` really is `(X+Y)/√2`. -/
lemma hXY_eq_sum : hXY = s • σx + s • σy := by
  simp only [hXY, cω, ω, FormalRV.Framework.σx, FormalRV.Framework.σy]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply] <;> ring

/-- The `T` gate `T = !![1,0; 0,ω]`. -/
def tGate : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, ω]

/-- The magic state `|T⟩ = T|+⟩ = (|0⟩ + ω|1⟩)/√2 = !![s; ω·s]`. -/
def magicT : Matrix (Fin 2) (Fin 1) ℂ := !![s; ω * s]

/-- The orthogonal magic state `T|−⟩ = (|0⟩ − ω|1⟩)/√2` (the `−1` eigenstate). -/
def magicTm : Matrix (Fin 2) (Fin 1) ℂ := !![s; -(ω * s)]

/-- `|+⟩ = !![s; s]`. -/
def plusKet : Matrix (Fin 2) (Fin 1) ℂ := !![s; s]

/-- Faithfulness: `|T⟩ = T|+⟩`. -/
lemma magicT_eq : magicT = tGate * plusKet := by
  simp only [magicT, tGate, plusKet]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ## §3. The semantic kernel of the check (all on real matrices). -/

/-- **`H_XY` is an involution** — it is a genuine reflection / measurable
parity observable (`H_XY² = I`). -/
@[simp] theorem hXY_involutive : hXY * hXY = σi := by
  simp only [hXY, FormalRV.Framework.σi]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`|T⟩` is the `+1` eigenstate of `H_XY`** — i.e. `H_XY` stabilizes the
magic state.  This is exactly the property the cultivation check verifies. -/
theorem hXY_stabilizes_magicT : hXY * magicT = magicT := by
  simp only [hXY, magicT]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two, ← mul_assoc, comega_omega]

/-- **The orthogonal magic state is the `−1` eigenstate** — so the check
genuinely discriminates `|T⟩` from `T|−⟩` (it is not vacuous). -/
theorem hXY_antistabilizes_magicTm : hXY * magicTm = -magicTm := by
  simp only [hXY, magicTm]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two, ← mul_assoc, comega_omega]

/-- **Gidney's `T†` trick: `T · X · T† = H_XY`.**  Conjugating by `T` turns the
plain `X`-parity check into the `H_XY` magic-state check — equivalently, applying
`T†` to the data first turns the `H_XY` check into an `X`-parity check (the form
actually measured by the "double cat check" circuit). -/
theorem tConj_X_eq_hXY : tGate * σx * tGateᴴ = hXY := by
  have hT : (tGateᴴ : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, cω] := by
    simp only [tGate]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, star_omega]
  rw [hT]
  simp only [tGate, hXY, FormalRV.Framework.σx]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## §4. The CONTROLLED-`H_XY` check (the actual cultivation cross-check).

  `ctrlHXY = |0⟩⟨0|⊗I + |1⟩⟨1|⊗H_XY` on (control, data).  With the control in
  `|+⟩`, phase kickback copies the `H_XY`-eigenvalue of the data onto the control:
  on `|T⟩` (eigenvalue `+1`) the control stays `|+⟩` (X-measurement `+1`, the
  check passes with no detection); on `T|−⟩` (eigenvalue `−1`) the control flips
  to `|−⟩` (X-measurement `−1`, the check fires). -/

/-- Controlled-`H_XY` on 2 qubits (control = high bit). -/
def ctrlHXY : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, cω;
     0, 0, ω, 0]

/-- `c = s² = 1/2`, the amplitude of each component of `|+⟩⊗|T⟩`. -/
noncomputable def c : ℂ := s * s

/-- `|+⟩ ⊗ |T⟩`. -/
def plusT  : Matrix (Fin 4) (Fin 1) ℂ := !![c; c * ω; c; c * ω]
/-- `|+⟩ ⊗ T|−⟩`. -/
def plusTm : Matrix (Fin 4) (Fin 1) ℂ := !![c; -(c * ω); c; -(c * ω)]
/-- `|−⟩ ⊗ T|−⟩`. -/
def minusTm : Matrix (Fin 4) (Fin 1) ℂ := !![c; -(c * ω); -c; c * ω]

/-- **★ THE CONTROLLED-H CHECK PASSES ON `|T⟩` ★** — controlled-`H_XY` leaves
`|+⟩⊗|T⟩` unchanged, so the control stays `|+⟩`: the `X`-basis measurement of the
control is deterministically `+1` and the check produces NO detection event.
This is the semantic correctness of the cultivation check on a good magic state. -/
theorem ctrlHXY_check_passes : ctrlHXY * plusT = plusT := by
  simp only [ctrlHXY, plusT]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
          mul_comm, mul_left_comm, mul_assoc]

/-- **★ THE CHECK HAS TEETH ★** — on the orthogonal magic state `T|−⟩`,
controlled-`H_XY` sends `|+⟩⊗T|−⟩ ↦ |−⟩⊗T|−⟩`: the control FLIPS to `|−⟩`, so the
`X`-measurement reads `−1` and the check FIRES.  The cultivation check therefore
genuinely discriminates `|T⟩` from its orthogonal partner (it is not a rubber
stamp). -/
theorem ctrlHXY_check_detects : ctrlHXY * plusTm = minusTm := by
  simp only [ctrlHXY, plusTm, minusTm]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four,
          mul_comm, mul_left_comm, mul_assoc]

end

end FormalRV.QEC.Cultivation
