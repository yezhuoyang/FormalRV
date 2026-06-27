/-
  FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone — closing gap-3 (2b)
  UNCONDITIONALLY.
  ════════════════════════════════════════════════════════════════════════════

  This module discharges the LAST open hypothesis of gap-3: the (2b) source spec

      runwayDataH_spec :
        uc_eval (runwayDataH w rest cm) * basis0 (cosetDim w (cm+rest))
          = doublyHWindowSource w rest cm

  for the concrete interior-H circuit `runwayDataH` (defined kernel-clean in
  `RunwayPrepClose` §E: `X` on the ctrl wire `0`, then `npar_H cm` on the a-block
  H-window `[aBase+rest, aBase+rest+cm)`, then `npar_H cm` on the b-block H-window
  `[bBase+rest, bBase+rest+cm)`).

  Feeding `runwayDataH_spec` (plus `runwayDataH_wellTyped`) into the §D headline
  `uc_eval_E2runwayInitPrep_eq_E2runwayInit` yields the UNCONDITIONAL literal headline
  `uc_eval_E2runwayInitPrep`.

  Kernel-clean: axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose

namespace FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore (basis0)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepFull
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepClose
open FormalRV.Framework (kron_vec kron_zeros kron_vec_combine)
open FormalRV.Framework.BaseUCom (npar_H npar_H_well_typed)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (aBase bBase scratchClean)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepSubBlock (genTwoReg winA genTwoReg_funboolNat)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat funboolEquiv extendBool)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow mem_cosetWindow)
open FormalRV.Shor.WindowedCircuit (decodeReg_lt_two_pow)
open FormalRV.Shor.GidneyInPlace.E2CosetSuccess (E2runwayInit)
open scoped Classical

/-! ## The (2b) source spec for `runwayDataH`. -/

open FormalRV.Framework (kron_vec_combine kron_vec_apply_combine
  kron_vec_smul_left kron_vec_smul_right)
open FormalRV.Framework.BaseUCom (npar H U_X)
open FormalRV.SQIRPort (kron_vec_sum_left kron_vec_sum_right kron_vec_basis_eq_basis_combine)
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (decodeReg_lt_two_pow decodeReg_testBit decodeReg_eq_mod_of_testBit decodeReg_eq_zero)
open FormalRV.Shor.GidneyInPlace.GatePerm (funbool_to_nat_agree)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg (scratchClean_congr_offBlocks)
open FormalRV.Shor.GidneyInPlace.CosetClass (mem_cosetWindow)
open FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepCore (fbn_testBit)

/-- **Source-dim irrelevance for `map_qubits` of `npar_H`.**  `map_qubits g (npar_H n)` does
    not depend on the SOURCE register dimension of `npar_H` — the recursion in `map_qubits`
    rebuilds the tree at the OUTPUT dimension `d'`, discarding the input index.  (For symbolic
    `n` the two are not `rfl`-defeq because `npar` is stuck, so we prove it by induction.) -/
theorem map_qubits_npar_H_dim_irrel (g : Nat → Nat) (n : Nat) (d1 d2 d' : Nat) :
    (map_qubits g (npar_H n : Framework.BaseUCom d1) : Framework.BaseUCom d')
      = (map_qubits g (npar_H n : Framework.BaseUCom d2) : Framework.BaseUCom d') := by
  show (map_qubits g (npar n (fun k => H k) : Framework.BaseUCom d1) : Framework.BaseUCom d')
    = (map_qubits g (npar n (fun k => H k) : Framework.BaseUCom d2) : Framework.BaseUCom d')
  induction n with
  | zero => rfl
  | succ k ih =>
      show Framework.UCom.seq (map_qubits g (npar k (fun k => H k))) (map_qubits g (H k))
        = Framework.UCom.seq (map_qubits g (npar k (fun k => H k))) (map_qubits g (H k))
      exact congrArg (fun c => Framework.UCom.seq c (map_qubits g (H k))) ih

/-- **`interior_npar_H`, transported to an arbitrary dimension `D = off + (cm + hi)`.**
    Same content as `interior_npar_H` but stated at a generic `D` (so it applies when the
    register is `cosetDim w (cm+rest)`, which is only PROPOSITIONALLY `off + (cm + hi)`).
    The dimension transport `hD ▸ ·` is discharged by `subst` plus `map_qubits_npar_H_dim_irrel`
    (the goal gate uses source dim `cm`; `interior_npar_H` uses `cm + hi`). -/
theorem interior_npar_H_at (off cm hi D : Nat) (hcm : 0 < cm) (hD : D = off + (cm + hi))
    (lo : Matrix (Fin (2 ^ off)) (Fin 1) ℂ) (hiv : Matrix (Fin (2 ^ hi)) (Fin 1) ℂ) :
    Framework.uc_eval
        (map_qubits (fun q => off + q) (npar_H cm : Framework.BaseUCom cm)
          : Framework.BaseUCom D)
        * ((hD.symm ▸ kron_vec lo (kron_vec (FormalRV.Framework.kron_zeros cm) hiv)
            : Matrix (Fin (2 ^ D)) (Fin 1) ℂ))
      = ((hD.symm ▸ (kron_vec lo
          (((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
            ∑ x : Fin (2 ^ cm),
            kron_vec (FormalRV.Framework.basis_vector (2 ^ cm) x.val) hiv))
          : Matrix (Fin (2 ^ D)) (Fin 1) ℂ)) := by
  subst hD
  rw [map_qubits_npar_H_dim_irrel (fun q => off + q) cm cm (cm + hi)]
  exact interior_npar_H off cm hi hcm lo hiv

/-- **The single-basis-vector interior-H step (index form).**  Applying `npar_H cm` on the
    interior `cm`-window block `[off, off+cm)` of a `D = off + (cm + hi)` register, to the basis
    vector whose window block is `0` (low part `lov`, high part `hiv`), produces the uniform
    superposition over the window-block values `x : Fin (2^cm)`.  Pure index bookkeeping: the
    register value of a clean-window state is `lov·2^(cm+hi) + hiv`, and writing `x` to the
    window gives `lov·2^(cm+hi) + x·2^hi + hiv`. -/
theorem hStep (off cm hi D lov hiv : Nat) (hcm : 0 < cm) (hD : D = off + (cm + hi))
    (hlov : lov < 2 ^ off) (hhiv : hiv < 2 ^ hi) :
    Framework.uc_eval
        (map_qubits (fun q => off + q) (npar_H cm : Framework.BaseUCom cm)
          : Framework.BaseUCom D)
        * FormalRV.Framework.basis_vector (2 ^ D) (lov * 2 ^ (cm + hi) + hiv)
      = ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
          ∑ x : Fin (2 ^ cm),
            FormalRV.Framework.basis_vector (2 ^ D) (lov * 2 ^ (cm + hi) + x.val * 2 ^ hi + hiv) := by
  subst hD
  have hhiv' : hiv < 2 ^ (cm + hi) := by
    calc hiv < 2 ^ hi := hhiv
      _ ≤ 2 ^ (cm + hi) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hin : (FormalRV.Framework.basis_vector (2 ^ (off + (cm + hi))) (lov * 2 ^ (cm + hi) + hiv))
      = (kron_vec (FormalRV.Framework.basis_vector (2 ^ off) lov)
            (kron_vec (FormalRV.Framework.kron_zeros cm)
              (FormalRV.Framework.basis_vector (2 ^ hi) hiv))) := by
    rw [show (FormalRV.Framework.kron_zeros cm : Matrix (Fin (2 ^ cm)) (Fin 1) ℂ)
          = FormalRV.Framework.basis_vector (2 ^ cm) 0 from rfl]
    have h1 : kron_vec (FormalRV.Framework.basis_vector (2 ^ cm) 0)
          (FormalRV.Framework.basis_vector (2 ^ hi) hiv)
        = FormalRV.Framework.basis_vector (2 ^ (cm + hi)) (0 * 2 ^ hi + hiv) := by
      have := kron_vec_basis_eq_basis_combine cm hi ⟨0, Nat.two_pow_pos cm⟩ ⟨hiv, hhiv⟩
      simpa [kron_vec_combine] using this
    have h2 : kron_vec (FormalRV.Framework.basis_vector (2 ^ off) lov)
          (FormalRV.Framework.basis_vector (2 ^ (cm + hi)) (0 * 2 ^ hi + hiv))
        = FormalRV.Framework.basis_vector (2 ^ (off + (cm + hi)))
            (lov * 2 ^ (cm + hi) + (0 * 2 ^ hi + hiv)) := by
      have := kron_vec_basis_eq_basis_combine off (cm + hi) ⟨lov, hlov⟩ ⟨0 * 2 ^ hi + hiv, by
        simpa using hhiv'⟩
      simpa [kron_vec_combine] using this
    rw [h1, h2]; congr 1; omega
  rw [hin, interior_npar_H_at off cm hi (off + (cm + hi)) hcm rfl
        (FormalRV.Framework.basis_vector (2 ^ off) lov)
        (FormalRV.Framework.basis_vector (2 ^ hi) hiv)]
  simp only [cast_eq]
  rw [kron_vec_smul_right]
  congr 1
  rw [kron_vec_sum_right]
  apply Finset.sum_congr rfl
  intro x _
  have h3 : kron_vec (FormalRV.Framework.basis_vector (2 ^ cm) x.val)
        (FormalRV.Framework.basis_vector (2 ^ hi) hiv)
      = FormalRV.Framework.basis_vector (2 ^ (cm + hi)) (x.val * 2 ^ hi + hiv) := by
    have := kron_vec_basis_eq_basis_combine cm hi ⟨x.val, x.isLt⟩ ⟨hiv, hhiv⟩
    simpa [kron_vec_combine] using this
  rw [h3]
  have h4 : kron_vec (FormalRV.Framework.basis_vector (2 ^ off) lov)
        (FormalRV.Framework.basis_vector (2 ^ (cm + hi)) (x.val * 2 ^ hi + hiv))
      = FormalRV.Framework.basis_vector (2 ^ (off + (cm + hi)))
          (lov * 2 ^ (cm + hi) + (x.val * 2 ^ hi + hiv)) := by
    have := kron_vec_basis_eq_basis_combine off (cm + hi) ⟨lov, hlov⟩ ⟨x.val * 2 ^ hi + hiv, by
      have : x.val * 2 ^ hi + hiv < 2 ^ cm * 2 ^ hi := by
        calc x.val * 2 ^ hi + hiv < x.val * 2 ^ hi + 2 ^ hi := by omega
          _ = (x.val + 1) * 2 ^ hi := by ring
          _ ≤ 2 ^ cm * 2 ^ hi := Nat.mul_le_mul_right _ x.isLt
      rw [pow_add]; exact this⟩
    simpa [kron_vec_combine] using this
  rw [h4]; congr 1; omega

/-- **The leading-wire `X` step (index form).**  `X` on wire `0` of a `D = 1 + d` register
    flips the all-zeros state `|0…0⟩` to the basis vector with the leading (MSB) bit set:
    index `1·2^d + 0 = 2^d`. -/
theorem xStep (D d : Nat) (hD : D = 1 + d) :
    Framework.uc_eval (Framework.UCom.app1 U_X 0 : Framework.BaseUCom D) * basis0 D
      = FormalRV.Framework.basis_vector (2 ^ D) (1 * 2 ^ d + 0) := by
  subst hD
  rw [uc_eval_X_basis0 d,
      show (FormalRV.Framework.kron_zeros d : Matrix (Fin (2 ^ d)) (Fin 1) ℂ)
        = FormalRV.Framework.basis_vector (2 ^ d) 0 from rfl]
  have := kron_vec_basis_eq_basis_combine 1 d ⟨1, by norm_num⟩ ⟨0, Nat.two_pow_pos d⟩
  simpa [kron_vec_combine] using this

/-! ### §F.1.  The entry-wise coordinate bridge: the double sum IS `doublyHWindowSource`.

The nested-kron uniform double sum produced by Steps X/aH/bH is, summand-by-summand, a single
basis vector `|Kab xa xb⟩` with
`Kab xa xb = 2^(cosetDim−1) + xa·2^hiA + xb·2^hiB` (ctrl=1, a-window=xa, b-window=xb, rest=0,
`hiA = 1+2cm+2rest`, `hiB = 1+cm+rest`).  We match this against `genTwoReg`'s
`decodeReg`/`scratchClean`/`funboolNat` indicator form ENTRY-WISE.  The bridge is the bit
function `gab` (ctrl=1, a/b-windows reading `xa`/`xb` big-endian, else 0) with
`Kab xa xb = funbool_to_nat (cosetDim) (gab …)`; then `funbool_to_nat`-uniqueness reduces the
match to wire-by-wire agreement, which reads off `scratchClean` and the window membership
(`∈ winA ⟺ the block's low-`rest` wires are clean`, since `winA` = multiples of `2^rest`). -/

/-- `(a + b·2^p).testBit i = a.testBit i` for `i < p` (low bitfield). -/
private theorem tb_low (a b p i : Nat) (hi : i < p) :
    (a + b * 2 ^ p).testBit i = a.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]; congr 2
  have key : b * 2 ^ p = (b * 2 ^ (p - i)) * 2 ^ i := by rw [mul_assoc, ← pow_add]; congr 2; omega
  rw [key, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
  obtain ⟨c, hc⟩ : 2 ∣ b * 2 ^ (p - i) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) b
  rw [hc, mul_comm 2 c, Nat.add_mul_mod_self_right]

/-- `(a + b·2^p).testBit i = b.testBit (i−p)` for `p ≤ i` and `a < 2^p` (high bitfield). -/
private theorem tb_high (a b p i : Nat) (ha : a < 2 ^ p) (hi : p ≤ i) :
    (a + b * 2 ^ p).testBit i = b.testBit (i - p) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = p + k := ⟨i - p, by omega⟩
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]; congr 2
  have hdiv : (a + b * 2 ^ p) / 2 ^ (p + k) = b / 2 ^ k := by
    rw [pow_add, ← Nat.div_div_eq_div_mul]; congr 1
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos p), Nat.div_eq_of_lt ha, Nat.zero_add]
  rw [show p + k - p = k from by omega, hdiv]

/-- The bit function whose `funbool_to_nat` value is `Kab xa xb`: ctrl bit set, the a-window
    `[1+2w+rest, 1+2w+rest+cm)` reading `xa` (big-endian), the b-window
    `[1+2w+cm+2rest, …+cm)` reading `xb`, everything else `false`. -/
private noncomputable def gab (w rest cm xa xb : Nat) : Nat → Bool := fun p =>
  if 1 + 2 * w + rest ≤ p ∧ p < 1 + 2 * w + rest + cm then xa.testBit (cm - 1 - (p - (1 + 2 * w + rest)))
  else if 1 + 2 * w + cm + 2 * rest ≤ p ∧ p < 1 + 2 * w + cm + 2 * rest + cm then
    xb.testBit (cm - 1 - (p - (1 + 2 * w + cm + 2 * rest)))
  else if p = 0 then true
  else false

/-- **`Kab xa xb = funbool_to_nat (cosetDim) (gab …)`.**  Bit-by-bit: the disjoint bitfields of
    `Kab = 2^(cd−1) + xa·2^hiA + xb·2^hiB` match the wire reads of `gab` (under the big-endian
    `funbool_to_nat` bit `i ↦ gab (cd−1−i)`). -/
private theorem Kab_eq_funbool (w rest cm xa xb : Nat) (hxa : xa < 2 ^ cm) (hxb : xb < 2 ^ cm) :
    2 ^ (cosetDim w (cm + rest) - 1) + xa * 2 ^ (1 + 2 * cm + 2 * rest) + xb * 2 ^ (1 + cm + rest)
      = FormalRV.Framework.funbool_to_nat (cosetDim w (cm + rest)) (gab w rest cm xa xb) := by
  have hcd0 : cosetDim w (cm + rest) = 2 + 2 * w + 3 * cm + 3 * rest := by unfold cosetDim; omega
  have hxbB : xb * 2 ^ (1 + cm + rest) < 2 ^ (1 + 2 * cm + 2 * rest) := by
    calc xb * 2 ^ (1 + cm + rest) < 2 ^ cm * 2 ^ (1 + cm + rest) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hxb
      _ = 2 ^ (cm + (1 + cm + rest)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (1 + 2 * cm + 2 * rest) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLB : xb * 2 ^ (1 + cm + rest) + xa * 2 ^ (1 + 2 * cm + 2 * rest)
      < 2 ^ (cosetDim w (cm + rest) - 1) := by
    calc xb * 2 ^ (1 + cm + rest) + xa * 2 ^ (1 + 2 * cm + 2 * rest)
        < 2 ^ (1 + 2 * cm + 2 * rest) + xa * 2 ^ (1 + 2 * cm + 2 * rest) := by omega
      _ = (1 + xa) * 2 ^ (1 + 2 * cm + 2 * rest) := by ring
      _ ≤ 2 ^ cm * 2 ^ (1 + 2 * cm + 2 * rest) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (cm + (1 + 2 * cm + 2 * rest)) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ (cosetDim w (cm + rest) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKlt : 2 ^ (cosetDim w (cm + rest) - 1) + xa * 2 ^ (1 + 2 * cm + 2 * rest)
        + xb * 2 ^ (1 + cm + rest) < 2 ^ cosetDim w (cm + rest) := by
    have h2 : 2 ^ (cosetDim w (cm + rest) - 1) + 2 ^ (cosetDim w (cm + rest) - 1)
        = 2 ^ cosetDim w (cm + rest) := by rw [← two_mul, ← pow_succ']; congr 1; omega
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hilt : i < cosetDim w (cm + rest)
  · rw [fbn_testBit (cosetDim w (cm + rest)) (gab w rest cm xa xb) i hilt]
    rw [show 2 ^ (cosetDim w (cm + rest) - 1) + xa * 2 ^ (1 + 2 * cm + 2 * rest)
            + xb * 2 ^ (1 + cm + rest)
          = (xb * 2 ^ (1 + cm + rest) + xa * 2 ^ (1 + 2 * cm + 2 * rest))
              + 1 * 2 ^ (cosetDim w (cm + rest) - 1) from by ring]
    have hLHS : ((xb * 2 ^ (1 + cm + rest) + xa * 2 ^ (1 + 2 * cm + 2 * rest))
          + 1 * 2 ^ (cosetDim w (cm + rest) - 1)).testBit i
        = (if i = cosetDim w (cm + rest) - 1 then true
           else if 1 + 2 * cm + 2 * rest ≤ i ∧ i < 1 + 3 * cm + 2 * rest then
             xa.testBit (i - (1 + 2 * cm + 2 * rest))
           else if 1 + cm + rest ≤ i ∧ i < 1 + 2 * cm + rest then xb.testBit (i - (1 + cm + rest))
           else false) := by
      by_cases hcd1 : i < cosetDim w (cm + rest) - 1
      · rw [tb_low _ 1 _ i hcd1, if_neg (by omega)]
        by_cases hA : 1 + 2 * cm + 2 * rest ≤ i
        · rw [tb_high (xb * 2 ^ (1 + cm + rest)) xa (1 + 2 * cm + 2 * rest) i hxbB hA]
          by_cases hAtop : i < 1 + 3 * cm + 2 * rest
          · rw [if_pos ⟨hA, hAtop⟩]
          · rw [if_neg (by omega), if_neg (by omega),
                Nat.testBit_lt_two_pow (lt_of_lt_of_le hxa (Nat.pow_le_pow_right (by norm_num) (by omega)))]
        · rw [tb_low (xb * 2 ^ (1 + cm + rest)) xa (1 + 2 * cm + 2 * rest) i (by omega), if_neg (by omega)]
          rw [show xb * 2 ^ (1 + cm + rest) = 0 + xb * 2 ^ (1 + cm + rest) from by ring]
          by_cases hB : 1 + cm + rest ≤ i
          · rw [tb_high 0 xb (1 + cm + rest) i (Nat.two_pow_pos _) hB]
            by_cases hBtop : i < 1 + 2 * cm + rest
            · rw [if_pos ⟨hB, hBtop⟩]
            · rw [if_neg (by omega),
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le hxb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
          · rw [tb_low 0 xb (1 + cm + rest) i (by omega), Nat.zero_testBit, if_neg (by omega)]
      · rw [tb_high _ 1 _ i hLB (by omega)]
        by_cases he : i = cosetDim w (cm + rest) - 1
        · rw [if_pos he, show i - (cosetDim w (cm + rest) - 1) = 0 from by omega]; rfl
        · rw [if_neg he, show (1 : Nat).testBit (i - (cosetDim w (cm + rest) - 1)) = false from by
                rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp; omega]
          rw [if_neg (by omega), if_neg (by omega)]
    rw [hLHS]
    clear hLB hxbB hKlt
    unfold gab
    rw [hcd0]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hKlt (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (FormalRV.Framework.funbool_to_nat_lt _ _)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- `gab` is scratch-clean (ctrl set, zero off both data blocks). -/
private theorem gab_scratchClean (w rest cm xa xb : Nat) :
    scratchClean w (cm + rest) (gab w rest cm xa xb) := by
  have hctrl0 : ulookup_ctrl_idx = 0 := by unfold ulookup_ctrl_idx; rfl
  refine ⟨?_, ?_⟩
  · show gab w rest cm xa xb ulookup_ctrl_idx = true
    rw [hctrl0]; unfold gab; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  · intro p hp hna hnb hnc
    rw [hctrl0] at hnc
    unfold gab
    rw [if_neg (by unfold aBase at hna; omega), if_neg (by unfold bBase at hnb; omega), if_neg (by omega)]

/-- `decodeReg idx (cm+rest) g % 2^rest = decodeReg idx rest g` — the low `rest` digits. -/
private theorem decodeReg_mod (idxf : Nat → Nat) (cm rest : Nat) (g : Nat → Bool) :
    decodeReg idxf (cm + rest) g % 2 ^ rest = decodeReg idxf rest g :=
  (decodeReg_eq_mod_of_testBit idxf rest (decodeReg idxf (cm + rest) g) g
    (fun i hi => (decodeReg_testBit idxf (cm + rest) g i (by omega)).symm)).symm

/-- A block's decode is a multiple of `2^rest` iff its low `rest` wires are clean. -/
private theorem lowrest_zero_iff (idxf : Nat → Nat) (cm rest : Nat) (g : Nat → Bool) :
    decodeReg idxf (cm + rest) g % 2 ^ rest = 0 ↔ ∀ i, i < rest → g (idxf i) = false := by
  rw [decodeReg_mod]
  constructor
  · intro h i hi
    have hb := decodeReg_testBit idxf rest g i hi
    rw [h, Nat.zero_testBit] at hb; exact hb.symm
  · intro h; exact decodeReg_eq_zero idxf rest g h

/-- `v ∈ winA rest cm (2^rest) 0 ↔ v % 2^rest = 0` (the H-window = multiples of `2^rest`). -/
private theorem mem_winA_iff_mod (cm rest v : Nat) (hv : v < 2 ^ (cm + rest)) :
    (⟨v, hv⟩ : Fin (2 ^ (cm + rest))) ∈ winA rest cm (2 ^ rest) 0 ↔ v % 2 ^ rest = 0 := by
  rw [show winA rest cm (2 ^ rest) 0 = cosetWindow (2 ^ (cm + rest)) (2 ^ rest) cm 0 from rfl,
      mem_cosetWindow _ _ _ _ (Nat.two_pow_pos rest)]
  constructor
  · rintro ⟨j, _, hjeq⟩; simp only [Nat.zero_add] at hjeq; rw [hjeq]; exact Nat.mul_mod_left j (2 ^ rest)
  · intro hmod
    refine ⟨v / 2 ^ rest, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos rest), ← pow_add]; exact hv
    · simp only [Nat.zero_add]; rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)]

/-- Big-endian read of the `cm` wires at offset `base`. -/
private noncomputable def Xwin (cd base cm : Nat) (f : Fin cd → Bool) : Nat :=
  FormalRV.Framework.funbool_to_nat cm (fun m => extendBool cd f (base + m))

private theorem Xwin_lt (cd base cm : Nat) (f : Fin cd → Bool) : Xwin cd base cm f < 2 ^ cm :=
  FormalRV.Framework.funbool_to_nat_lt cm _

/-- On the a-window wires, `gab` with `xa = Xwin` reproduces `f`. -/
private theorem gab_aWin_eq (w rest cm : Nat) (f : Fin (cosetDim w (cm + rest)) → Bool)
    (k : Nat) (hk : k < cm) :
    gab w rest cm (Xwin (cosetDim w (cm + rest)) (1 + 2 * w + rest) cm f)
        (Xwin (cosetDim w (cm + rest)) (1 + 2 * w + cm + 2 * rest) cm f) (1 + 2 * w + rest + k)
      = extendBool (cosetDim w (cm + rest)) f (1 + 2 * w + rest + k) := by
  unfold gab
  rw [if_pos (by omega), show 1 + 2 * w + rest + k - (1 + 2 * w + rest) = k from by omega]
  unfold Xwin
  rw [fbn_testBit cm _ (cm - 1 - k) (by omega)]
  congr 1; omega

/-- On the b-window wires, `gab` with `xb = Xwin` reproduces `f`. -/
private theorem gab_bWin_eq (w rest cm : Nat) (f : Fin (cosetDim w (cm + rest)) → Bool)
    (k : Nat) (hk : k < cm) :
    gab w rest cm (Xwin (cosetDim w (cm + rest)) (1 + 2 * w + rest) cm f)
        (Xwin (cosetDim w (cm + rest)) (1 + 2 * w + cm + 2 * rest) cm f) (1 + 2 * w + cm + 2 * rest + k)
      = extendBool (cosetDim w (cm + rest)) f (1 + 2 * w + cm + 2 * rest + k) := by
  unfold gab
  rw [if_neg (by omega), if_pos (by omega),
      show 1 + 2 * w + cm + 2 * rest + k - (1 + 2 * w + cm + 2 * rest) = k from by omega]
  unfold Xwin
  rw [fbn_testBit cm _ (cm - 1 - k) (by omega)]
  congr 1; omega

/-- `(Xwin … base) .testBit k = f (base + (cm−1−k))` for `k < cm` (big-endian window read). -/
private theorem Xwin_testBit (cd base cm : Nat) (f : Fin cd → Bool) (k : Nat) (hk : k < cm) :
    (Xwin cd base cm f).testBit k = extendBool cd f (base + (cm - 1 - k)) := by
  unfold Xwin; rw [fbn_testBit cm _ k hk]

/-- **The agreement characterization.**  `extendBool f` agrees wire-by-wire with `gab xa xb`
    on `[0, cosetDim)` IFF `xa`/`xb` are the (big-endian) values of `f`'s a/b-windows AND `f`
    is scratch-clean with both blocks' low-`rest` wires clean (i.e. both block decodes are
    multiples of `2^rest`, the `winA` membership condition).  This is the bridge between the
    LHS basis index `gab` and the RHS `decodeReg`/`scratchClean` reads. -/
private theorem agree_iff (w rest cm : Nat)
    (f : Fin (cosetDim w (cm + rest)) → Bool) (xa xb : Nat) (hxa : xa < 2 ^ cm) (hxb : xb < 2 ^ cm) :
    (∀ p, p < cosetDim w (cm + rest) → extendBool (cosetDim w (cm + rest)) f p = gab w rest cm xa xb p)
      ↔ (xa = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + rest) cm f
          ∧ xb = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + cm + 2 * rest) cm f
          ∧ scratchClean w (cm + rest) (extendBool (cosetDim w (cm + rest)) f)
          ∧ decodeReg (fun i => aBase w + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0
          ∧ decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
              (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0) := by
  have hcd0 : cosetDim w (cm + rest) = 2 + 2 * w + 3 * cm + 3 * rest := by unfold cosetDim; omega
  have hctrl0 : ulookup_ctrl_idx = 0 := by unfold ulookup_ctrl_idx; rfl
  constructor
  · intro hag
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < cm
      · rw [Xwin_testBit _ (1 + 2 * w + rest) cm f k hk]
        have := hag ((1 + 2 * w + rest) + (cm - 1 - k)) (by rw [hcd0]; omega)
        rw [show gab w rest cm xa xb ((1 + 2 * w + rest) + (cm - 1 - k))
              = xa.testBit (cm - 1 - ((1 + 2 * w + rest) + (cm - 1 - k) - (1 + 2 * w + rest))) from by
              unfold gab; rw [if_pos (by omega)],
            show cm - 1 - ((1 + 2 * w + rest) + (cm - 1 - k) - (1 + 2 * w + rest)) = k from by omega] at this
        rw [← this]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hxa (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (Xwin_lt _ (1 + 2 * w + rest) cm f)
              (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < cm
      · rw [Xwin_testBit _ (1 + 2 * w + cm + 2 * rest) cm f k hk]
        have := hag ((1 + 2 * w + cm + 2 * rest) + (cm - 1 - k)) (by rw [hcd0]; omega)
        rw [show gab w rest cm xa xb ((1 + 2 * w + cm + 2 * rest) + (cm - 1 - k))
              = xb.testBit (cm - 1 - ((1 + 2 * w + cm + 2 * rest) + (cm - 1 - k) - (1 + 2 * w + cm + 2 * rest))) from by
              unfold gab; rw [if_neg (by omega), if_pos (by omega)],
            show cm - 1 - ((1 + 2 * w + cm + 2 * rest) + (cm - 1 - k) - (1 + 2 * w + cm + 2 * rest)) = k from by omega] at this
        rw [← this]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hxb (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (Xwin_lt _ (1 + 2 * w + cm + 2 * rest) cm f)
              (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · refine ⟨?_, ?_⟩
      · rw [hctrl0, hag 0 (by rw [hcd0]; omega)]
        unfold gab; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      · intro p hp hna hnb hnc
        rw [hag p hp]; rw [hctrl0] at hnc
        unfold gab
        rw [if_neg (by unfold aBase at hna; omega), if_neg (by unfold bBase at hnb; omega), if_neg (by omega)]
    · rw [lowrest_zero_iff]
      intro i hi
      rw [hag (aBase w + i) (by unfold aBase; rw [hcd0]; omega)]
      unfold gab aBase; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [lowrest_zero_iff]
      intro i hi
      rw [hag (bBase w (cm + rest) + i) (by unfold bBase; rw [hcd0]; omega)]
      unfold gab bBase; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rintro ⟨hxaE, hxbE, hsc, haL, hbL⟩ p hp
    rw [lowrest_zero_iff] at haL hbL
    by_cases hAw : 1 + 2 * w + rest ≤ p ∧ p < 1 + 2 * w + rest + cm
    · rw [show gab w rest cm xa xb p = xa.testBit (cm - 1 - (p - (1 + 2 * w + rest))) from by
            unfold gab; rw [if_pos hAw]]
      rw [hxaE, Xwin_testBit _ (1 + 2 * w + rest) cm f (cm - 1 - (p - (1 + 2 * w + rest))) (by omega)]
      congr 1; omega
    · by_cases hBw : 1 + 2 * w + cm + 2 * rest ≤ p ∧ p < 1 + 2 * w + cm + 2 * rest + cm
      · rw [show gab w rest cm xa xb p = xb.testBit (cm - 1 - (p - (1 + 2 * w + cm + 2 * rest))) from by
              unfold gab; rw [if_neg hAw, if_pos hBw]]
        rw [hxbE, Xwin_testBit _ (1 + 2 * w + cm + 2 * rest) cm f
              (cm - 1 - (p - (1 + 2 * w + cm + 2 * rest))) (by omega)]
        congr 1; omega
      · rw [show gab w rest cm xa xb p = (if p = 0 then true else false) from by
              unfold gab; rw [if_neg hAw, if_neg hBw]]
        by_cases hp0 : p = 0
        · rw [if_pos hp0, hp0]; exact hsc.1
        · rw [if_neg hp0]
          by_cases haLR : aBase w ≤ p ∧ p < aBase w + rest
          · obtain ⟨i, hi, rfl⟩ : ∃ i, i < rest ∧ aBase w + i = p :=
              ⟨p - aBase w, by unfold aBase at haLR ⊢; omega, by unfold aBase at haLR ⊢; omega⟩
            exact haL i hi
          · by_cases hbLR : bBase w (cm + rest) ≤ p ∧ p < bBase w (cm + rest) + rest
            · obtain ⟨i, hi, rfl⟩ : ∃ i, i < rest ∧ bBase w (cm + rest) + i = p :=
                ⟨p - bBase w (cm + rest), by omega, by omega⟩
              exact hbL i hi
            · refine hsc.2 p hp ?_ ?_ (by rw [hctrl0]; omega)
              · unfold aBase at haLR ⊢; omega
              · unfold bBase at hbLR ⊢; omega

/-- **Double-sum collapse (abstract).**  A uniform double sum of indicators selecting the
    UNIQUE pair `(Xa, Xb)` (gated by a pair-independent predicate `G`) collapses to
    `if G then c·c else 0`. -/
private theorem collapse_abs (cm : Nat) (c : ℂ) (Xa Xb : Nat) (hXa : Xa < 2 ^ cm)
    (hXb : Xb < 2 ^ cm) (G : Prop) [Decidable G] :
    c * ∑ xa : Fin (2 ^ cm), c * ∑ xb : Fin (2 ^ cm),
        (if (xa.val = Xa ∧ xb.val = Xb ∧ G) then (1 : ℂ) else 0)
      = (if G then c * c else 0) := by
  by_cases hG : G
  · rw [if_pos hG, Finset.sum_eq_single (⟨Xa, hXa⟩ : Fin (2 ^ cm))]
    · rw [Finset.sum_eq_single (⟨Xb, hXb⟩ : Fin (2 ^ cm))]
      · rw [if_pos ⟨rfl, rfl, hG⟩]; ring
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h.2.1))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun d _ => ?_))
      rw [if_neg (fun h => hb (Fin.ext h.1))]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hG]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun xa _ => ?_))
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun xb _ => ?_))
    rw [if_neg (fun h => hG h.2.2)]

/-- **THE (2b) SOURCE SPEC (the last open hypothesis of gap-3).**  The concrete interior-H
    circuit `runwayDataH` carries `|0…0⟩` to the doubly-H-window `genTwoReg`
    (`doublyHWindowSource`).  Opening (`X` on ctrl, two interior `npar_H` windows) + the
    entry-wise coordinate bridge (§F.1) between the nested-kron uniform double sum and the
    `decodeReg`/`scratchClean`/`funboolNat` indicator layout of `genTwoReg`. -/
theorem runwayDataH_spec (w rest cm : Nat) (hcm : 0 < cm) :
    Framework.uc_eval (runwayDataH w rest cm) * basis0 (cosetDim w (cm + rest))
      = RunwayPrepFull.doublyHWindowSource w rest cm := by
  rw [runwayDataH, uc_eval_seq_mul, uc_eval_seq_mul]
  -- The two interior H windows: a-window at offset aH, b-window at offset bH.
  -- Layout: cosetDim = aH + (cm + hiA) = bH + (cm + hiB).
  set D := cosetDim w (cm + rest) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; unfold cosetDim; omega
  -- a-window: off_a = aBase w + rest, hi_a = 1 + 2*cm + 2*rest
  have hDa : D = (aBase w + rest) + (cm + (1 + 2 * cm + 2 * rest)) := by
    rw [hDdef]; unfold cosetDim aBase; omega
  -- b-window: off_b = bBase w (cm+rest) + rest, hi_b = 1 + cm + rest
  have hDb : D = (bBase w (cm + rest) + rest) + (cm + (1 + cm + rest)) := by
    rw [hDdef]; unfold cosetDim bBase; omega
  -- Step X: ctrl wire 0 set to 1.
  rw [xStep D (D - 1) (by omega)]
  -- Rewrite the ctrl index into the a-window split form: lovA · 2^(cm+hiA) + 0.
  have hxa : 1 * 2 ^ (D - 1) + 0
      = 2 ^ (aBase w + rest - 1) * 2 ^ (cm + (1 + 2 * cm + 2 * rest)) + 0 := by
    rw [Nat.add_zero, Nat.add_zero, one_mul, ← pow_add]
    congr 1
    rw [hDdef]; unfold cosetDim aBase; omega
  rw [hxa]
  -- Step a-H: uniform superposition on the a-window.
  rw [hStep (aBase w + rest) cm (1 + 2 * cm + 2 * rest) D (2 ^ (aBase w + rest - 1)) 0 hcm hDa
        (by exact Nat.pow_lt_pow_right (by norm_num) (by unfold aBase; omega)) (Nat.two_pow_pos _)]
  -- Distribute the b-H over the a-sum by linearity.
  rw [Matrix.mul_smul, Matrix.mul_sum]
  -- Apply the b-H step to each a-summand.
  have hbstep : ∀ x : Fin (2 ^ cm),
      Framework.uc_eval (map_qubits (fun q => bBase w (cm + rest) + rest + q)
            (npar_H cm : Framework.BaseUCom cm) : Framework.BaseUCom D)
          * FormalRV.Framework.basis_vector (2 ^ D)
              (2 ^ (aBase w + rest - 1) * 2 ^ (cm + (1 + 2 * cm + 2 * rest))
                + x.val * 2 ^ (1 + 2 * cm + 2 * rest) + 0)
        = ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) •
            ∑ y : Fin (2 ^ cm),
              FormalRV.Framework.basis_vector (2 ^ D)
                ((2 ^ (bBase w (cm + rest) + rest - 1) + x.val * 2 ^ rest) * 2 ^ (cm + (1 + cm + rest))
                  + y.val * 2 ^ (1 + cm + rest) + 0) := by
    intro x
    -- rewrite the a-summand index into the b-window split form lovB · 2^(cm+hiB) + 0
    have hidx : 2 ^ (aBase w + rest - 1) * 2 ^ (cm + (1 + 2 * cm + 2 * rest))
          + x.val * 2 ^ (1 + 2 * cm + 2 * rest) + 0
        = (2 ^ (bBase w (cm + rest) + rest - 1) + x.val * 2 ^ rest) * 2 ^ (cm + (1 + cm + rest)) + 0 := by
      rw [Nat.add_zero, Nat.add_zero, ← pow_add, add_mul, ← pow_add, mul_assoc, ← pow_add]
      congr 2
      · unfold aBase bBase; omega
      · congr 1; omega
    rw [hidx,
        hStep (bBase w (cm + rest) + rest) cm (1 + cm + rest) D
          (2 ^ (bBase w (cm + rest) + rest - 1) + x.val * 2 ^ rest) 0 hcm hDb
          (by
            -- 2^(bH-1) + xa·2^rest < 2^bH = 2·2^(bH-1), since xa·2^rest < 2^cm·2^rest ≤ 2^(bH-1)
            have hxr : x.val * 2 ^ rest < 2 ^ (bBase w (cm + rest) + rest - 1) := by
              calc x.val * 2 ^ rest < 2 ^ cm * 2 ^ rest :=
                    (Nat.mul_lt_mul_right (Nat.two_pow_pos rest)).mpr x.isLt
                _ = 2 ^ (cm + rest) := (pow_add 2 cm rest).symm
                _ ≤ 2 ^ (bBase w (cm + rest) + rest - 1) :=
                    Nat.pow_le_pow_right (by norm_num) (by unfold bBase; omega)
            have hbh : 2 ^ (bBase w (cm + rest) + rest)
                = 2 * 2 ^ (bBase w (cm + rest) + rest - 1) := by
              rw [← pow_succ']; congr 1; unfold bBase; omega
            rw [hbh]; omega)
          (Nat.two_pow_pos _)]
  rw [Finset.sum_congr rfl (fun x _ => hbstep x)]
  -- Normalise each summand index to the clean disjoint-bitfield form
  -- `2^(D-1) + xa·2^hiA + xb·2^hiB`, `hiA = 1+2cm+2rest`, `hiB = 1+cm+rest`.
  have hidxNorm : ∀ x y : Fin (2 ^ cm),
      (2 ^ (bBase w (cm + rest) + rest - 1) + x.val * 2 ^ rest) * 2 ^ (cm + (1 + cm + rest))
          + y.val * 2 ^ (1 + cm + rest) + 0
        = 2 ^ (D - 1) + x.val * 2 ^ (1 + 2 * cm + 2 * rest) + y.val * 2 ^ (1 + cm + rest) := by
    intro x y
    have he1 : (2 ^ (bBase w (cm + rest) + rest - 1)) * 2 ^ (cm + (1 + cm + rest)) = 2 ^ (D - 1) := by
      rw [← pow_add]; congr 1; rw [hDdef]; unfold cosetDim bBase; omega
    have he2 : 2 ^ rest * 2 ^ (cm + (1 + cm + rest)) = 2 ^ (1 + 2 * cm + 2 * rest) := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.add_zero, add_mul, he1, mul_assoc, he2]
  simp only [hidxNorm]
  -- Unfold the target and match entry-wise.
  show _ = RunwayPrepFull.doublyHWindowSource w rest cm
  rw [RunwayPrepFull.doublyHWindowSource]
  funext idx col
  obtain rfl : col = 0 := Subsingleton.elim col 0
  obtain ⟨f, rfl⟩ : ∃ f, funboolNat (cosetDim w (cm + rest)) f = idx :=
    ⟨(funboolEquiv (cosetDim w (cm + rest))).symm idx,
      Equiv.apply_symm_apply (funboolEquiv (cosetDim w (cm + rest))) idx⟩
  rw [genTwoReg_funboolNat]
  simp only [hDdef, Matrix.smul_apply, Matrix.sum_apply, FormalRV.Framework.basis_vector_apply,
    smul_eq_mul]
  -- Indicator rewrite: each LHS term is the `agree_iff` predicate.
  have hind : ∀ xa xb : Fin (2 ^ cm),
      (if (funboolNat (cosetDim w (cm + rest)) f).val
            = 2 ^ (cosetDim w (cm + rest) - 1) + xa.val * 2 ^ (1 + 2 * cm + 2 * rest)
                + xb.val * 2 ^ (1 + cm + rest) then (1 : ℂ) else 0)
        = (if (xa.val = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + rest) cm f
              ∧ xb.val = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + cm + 2 * rest) cm f
              ∧ scratchClean w (cm + rest) (extendBool (cosetDim w (cm + rest)) f)
              ∧ decodeReg (fun i => aBase w + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0
              ∧ decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
                  (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0)
            then (1 : ℂ) else 0) := by
    intro xa xb
    congr 1
    rw [Kab_eq_funbool w rest cm xa.val xb.val xa.isLt xb.isLt,
        show (funboolNat (cosetDim w (cm + rest)) f).val
          = FormalRV.Framework.funbool_to_nat (cosetDim w (cm + rest)) (extendBool (cosetDim w (cm + rest)) f) from rfl]
    apply propext
    constructor
    · intro heq
      exact (agree_iff w rest cm f xa.val xb.val xa.isLt xb.isLt).mp
        (fun p hp => funbool_to_nat_agree (cosetDim w (cm + rest)) _ _ heq p hp)
    · intro hgood
      have hwire := (agree_iff w rest cm f xa.val xb.val xa.isLt xb.isLt).mpr hgood
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < cosetDim w (cm + rest)
      · rw [fbn_testBit _ _ i hi, fbn_testBit _ _ i hi,
            hwire (cosetDim w (cm + rest) - 1 - i) (by omega)]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (FormalRV.Framework.funbool_to_nat_lt _ _)
              (Nat.pow_le_pow_right (by norm_num) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (FormalRV.Framework.funbool_to_nat_lt _ _)
              (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp only [hind]
  -- Collapse the LHS double sum to `if Good3 then c·c else 0` via `collapse_abs`.
  classical
  set G : Prop := scratchClean w (cm + rest) (extendBool (cosetDim w (cm + rest)) f)
      ∧ decodeReg (fun i => aBase w + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0
      ∧ decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
          (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0 with hGdef
  have hLHS : (((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) * ∑ xa : Fin (2 ^ cm),
        ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) * ∑ xb : Fin (2 ^ cm),
          (if (xa.val = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + rest) cm f
                ∧ xb.val = Xwin (cosetDim w (cm + rest)) (1 + 2 * w + cm + 2 * rest) cm f ∧ G)
            then (1 : ℂ) else 0))
        = if G then ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) * ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) else 0 :=
    collapse_abs cm ((1 : ℂ) / Real.sqrt (2 ^ cm : ℝ)) _ _ (Xwin_lt _ _ _ _) (Xwin_lt _ _ _ _) G
  rw [hLHS]
  -- the a-decode/b-decode ∈ winA ⟺ low-rest clean.
  have hawin := mem_winA_iff_mod cm rest
    (decodeReg (fun i => aBase w + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f))
    (decodeReg_lt_two_pow _ _ _)
  have hbwin := mem_winA_iff_mod cm rest
    (decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f))
    (decodeReg_lt_two_pow _ _ _)
  by_cases hG : G
  · obtain ⟨hGsc, hGaL, hGbL⟩ := hG
    rw [if_pos hGsc, if_pos (hawin.mpr hGaL), if_pos (hbwin.mpr hGbL),
        if_pos (show G from ⟨hGsc, hGaL, hGbL⟩)]
    push_cast; ring
  · rw [if_neg hG]
    by_cases hsc' : scratchClean w (cm + rest) (extendBool (cosetDim w (cm + rest)) f)
    · rw [if_pos hsc']
      by_cases haL' : decodeReg (fun i => aBase w + i) (cm + rest) (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0
      · rw [if_pos (hawin.mpr haL')]
        by_cases hbL' : decodeReg (fun i => bBase w (cm + rest) + i) (cm + rest)
            (extendBool (cosetDim w (cm + rest)) f) % 2 ^ rest = 0
        · exact absurd ⟨hsc', haL', hbL'⟩ hG
        · rw [if_neg (fun h => hbL' (hbwin.mp h)), mul_zero]
      · rw [if_neg (fun h => haL' (hawin.mp h)), zero_mul]
    · rw [if_neg hsc']

/-! ## The UNCONDITIONAL closure of gap-3. -/

theorem uc_eval_E2runwayInitPrep (m w rest cm N : Nat) (hm : 0 < m) (hN : 0 < N) (h1N : 1 < N)
    (hcm : 0 < cm) (hbudget : 2 ^ cm * N ≤ 2 ^ (cm + rest)) :
    FormalRV.SQIRPort.QState.cast (RunwayPrepClose.kronDim_eq m w (cm + rest))
        (Framework.uc_eval
            (RunwayPrepFull.E2runwayInitPrep m w rest cm N hN h1N hbudget
              (runwayDataH w rest cm))
          * basis0 (m + cosetDim w (cm + rest)))
      = E2runwayInit m w (cm + rest) N cm :=
  RunwayPrepClose.uc_eval_E2runwayInitPrep_eq_E2runwayInit m w rest cm N hm hN h1N hbudget
    (runwayDataH w rest cm) (runwayDataH_wellTyped w rest cm) (runwayDataH_spec w rest cm hcm)

-- Kernel-cleanliness checks (axioms ⊆ {propext, Classical.choice, Quot.sound};
-- no `sorry`, no `native_decide`).
#print axioms runwayDataH_spec
#print axioms uc_eval_E2runwayInitPrep

end FormalRV.Shor.GidneyInPlace.Capstone.RunwayPrepDone
