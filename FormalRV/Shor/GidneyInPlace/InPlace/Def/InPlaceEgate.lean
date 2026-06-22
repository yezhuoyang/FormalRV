/-
  FormalRV.Shor.GidneyInPlace.InPlaceEgate
  ────────────────────────────────────────────
  BRICK 1 of the two-register in-place coset-multiplier DYNAMICS transport:
  the CONTIGUOUS-ACCUMULATOR product equiv `eGid` (control × data factorization of
  the `cosetDim`-register, with the DATA factor at the CONTIGUOUS accumulator block
  `[accBase, accBase+bits)`), plus its injectivity/bijectivity.

  WHY a fresh equiv (not the existing `ReducedLookupEgate.e_gate`):  the existing
  `e_gate` hard-wires its data factor to Cuccaro's INTERLEAVED augend positions
  `augendIdx (1+2w) i = 1+2w+2i+1` (`assembleE`/`compIdx`).  The in-place passes
  (`gidneyProductAddTOf`) accumulate into a CONTIGUOUS block `accBase+i`
  (`ProductAddArith.gidneyProductAddTOf_state` decodes via `fun i => accBase+i`), with
  the addend in a SEPARATE temp block.  No single register relabel maps the whole
  interleaved circuit to the relocated one at the `uc_eval`/`branchOfE` level, so the
  coset dynamics needs its own factorization.  This file builds it by MIRRORING the
  `assembleE`/`eFun`/`e_gate` construction verbatim, replacing the interleaved augend
  index with the contiguous `fun i => accBase+i` (whose injectivity is the trivial
  `Nat.add_left_cancel`) and the 3-region `compIdx` with the 2-region `compIdxGid`
  (below the block / above the block).

  PARAMETERIZED by `accBase` so the SINGLE equiv serves BOTH passes: pass-1
  accumulator `b @ accBase = 1+2w+bits`, pass-2 accumulator `a @ accBase = 1+2w`.
  All that is needed of the layout is `accBase + bits ≤ cosetDim w bits` (both passes
  satisfy it).  NO dynamics / `uc_eval` / `cosetState` reasoning here — purely the
  structural factorization (the single hard blocker the dynamics map identified).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.ReducedLookup.Def.ReducedLookupEgate

namespace FormalRV.Shor.GidneyInPlace.InPlaceEgate

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat funboolNat_injective)
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate
open FormalRV.Shor.GidneyInPlace.ReducedLookupEgate (comp_add_bits bits_le_cosetDim)

/-! ## §1. The contiguous complement enumerator `compIdxGid`.

    Data factor = the contiguous accumulator block `[accBase, accBase+bits)`.  The
    complement is `[0, accBase) ∪ [accBase+bits, cosetDim)`, enumerated by:
      `j < accBase`            ↦ `j`                       (below the block)
      `accBase ≤ j`            ↦ `accBase + bits + (j - accBase)`  (above the block)
    a strictly simpler (2-region, both contiguous) map than `compIdx`. -/

/-- The contiguous complement-position enumerator: a bijection
    `[0, cosetDim-bits) → (non-accumulator positions of [0, cosetDim))`. -/
def compIdxGid (bits accBase : Nat) (j : Nat) : Nat :=
  if j < accBase then j else accBase + bits + (j - accBase)

/-- `compIdxGid` is bounded by `cosetDim` on `[0, cosetDim-bits)`. -/
theorem compIdxGid_lt (w bits accBase j : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) (hj : j < cosetDim w bits - bits) :
    compIdxGid bits accBase j < cosetDim w bits := by
  unfold compIdxGid; split <;> omega

/-- `compIdxGid` is injective (its branch conditions are on the input). -/
theorem compIdxGid_inj (bits accBase i j : Nat)
    (h : compIdxGid bits accBase i = compIdxGid bits accBase j) : i = j := by
  unfold compIdxGid at h; split_ifs at h <;> omega

/-- `compIdxGid` images avoid the accumulator block `[accBase, accBase+bits)`. -/
theorem compIdxGid_ne_data (bits accBase j i : Nat) (hi : i < bits) :
    compIdxGid bits accBase j ≠ accBase + i := by
  unfold compIdxGid; split <;> omega

/-- `compIdxGid` images lie strictly OUTSIDE the accumulator block `[accBase,
    accBase+bits)` (below it or above it) — the membership-negation form. -/
theorem compIdxGid_off_block (bits accBase j : Nat) :
    ¬ (accBase ≤ compIdxGid bits accBase j ∧ compIdxGid bits accBase j < accBase + bits) := by
  unfold compIdxGid; split <;> omega

/-- **Coverage.**  Every position `< cosetDim` is EITHER an accumulator position (for
    a unique `i < bits`) OR a complement position (for a unique `j < cosetDim-bits`). -/
theorem coverGid (w bits accBase p : Nat) (haccfit : accBase + bits ≤ cosetDim w bits)
    (hp : p < cosetDim w bits) :
    (∃ i, i < bits ∧ p = accBase + i)
      ∨ (∃ j, j < cosetDim w bits - bits ∧ p = compIdxGid bits accBase j) := by
  unfold compIdxGid
  by_cases h0 : p < accBase
  · right; exact ⟨p, by omega, by rw [if_pos h0]⟩
  by_cases hblk : p < accBase + bits
  · left; exact ⟨p - accBase, by omega, by omega⟩
  · right
    refine ⟨p - bits, by omega, ?_⟩
    rw [if_neg (by omega)]; omega

/-! ## §2. The assembled bit-function and the named equiv `eGid`. -/

/-- Assemble a `cosetDim`-bit function from a control value `x` (at the complement
    positions) and a data value `z` (at the contiguous accumulator positions
    `accBase+i`, little-endian). -/
def assembleEGid (w bits accBase : Nat) (x z : Nat) : Nat → Bool :=
  writeReg (fun i => accBase + i) bits z
    (writeReg (compIdxGid bits accBase) (cosetDim w bits - bits) x (fun _ => false))

/-- At an accumulator position, `assembleEGid` reads bit `i` of the data value `z`. -/
theorem assembleEGid_data (w bits accBase x z i : Nat) (hi : i < bits) :
    assembleEGid w bits accBase x z (accBase + i) = z.testBit i := by
  unfold assembleEGid
  exact writeReg_at _ bits z _ (fun a b _ _ h => Nat.add_left_cancel h) i hi

/-- At a complement position, `assembleEGid` reads bit `j` of the control value `x`. -/
theorem assembleEGid_comp (w bits accBase x z j : Nat) (hj : j < cosetDim w bits - bits) :
    assembleEGid w bits accBase x z (compIdxGid bits accBase j) = x.testBit j := by
  unfold assembleEGid
  rw [writeReg_frame _ bits z _ _
        (fun i hi => compIdxGid_ne_data bits accBase j i hi)]
  exact writeReg_at _ (cosetDim w bits - bits) x _
    (fun a b _ _ h => compIdxGid_inj bits accBase a b h) j hj

/-- **`assembleEGid` is injective in the value pair** (over the relevant value
    ranges), on `[0, cosetDim)`: recover `z` at accumulator positions, `x` at
    complement positions. -/
theorem assembleEGid_inj (w bits accBase x z x' z' : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits)
    (hx : x < 2 ^ (cosetDim w bits - bits)) (hx' : x' < 2 ^ (cosetDim w bits - bits))
    (hz : z < 2 ^ bits) (hz' : z' < 2 ^ bits)
    (h : (fun p : Fin (cosetDim w bits) => assembleEGid w bits accBase x z p.val)
       = (fun p : Fin (cosetDim w bits) => assembleEGid w bits accBase x' z' p.val)) :
    x = x' ∧ z = z' := by
  have key : ∀ p, p < cosetDim w bits →
      assembleEGid w bits accBase x z p = assembleEGid w bits accBase x' z' p :=
    fun p hp => congrFun h ⟨p, hp⟩
  refine ⟨Nat.eq_of_testBit_eq (fun j => ?_), Nat.eq_of_testBit_eq (fun i => ?_)⟩
  · -- compare bit j of x vs x'
    by_cases hj : j < cosetDim w bits - bits
    · have := key (compIdxGid bits accBase j) (compIdxGid_lt w bits accBase j haccfit hj)
      rw [assembleEGid_comp w bits accBase x z j hj,
          assembleEGid_comp w bits accBase x' z' j hj] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by omega) (by omega)))]
  · -- compare bit i of z vs z'
    by_cases hi : i < bits
    · have := key (accBase + i) (by omega)
      rw [assembleEGid_data w bits accBase x z i hi,
          assembleEGid_data w bits accBase x' z' i hi] at this
      exact this
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hz' (Nat.pow_le_pow_right (by omega) (by omega)))]

/-- The forward map of `eGid`: `(x, z) ↦ funboolNat (assembleEGid x.val z.val)`. -/
noncomputable def eFunGid (w bits accBase : Nat) :
    Fin (2 ^ (cosetDim w bits - bits)) × Fin (2 ^ bits) → Fin (2 ^ cosetDim w bits) :=
  fun p => funboolNat (cosetDim w bits) (fun i => assembleEGid w bits accBase p.1.val p.2.val i.val)

theorem eFunGid_injective (w bits accBase : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) :
    Function.Injective (eFunGid w bits accBase) := by
  rintro ⟨x, z⟩ ⟨x', z'⟩ h
  unfold eFunGid at h
  have hassemble := funboolNat_injective (cosetDim w bits) h
  obtain ⟨hxx, hzz⟩ := assembleEGid_inj w bits accBase x.val z.val x'.val z'.val
    haccfit x.isLt x'.isLt z.isLt z'.isLt hassemble
  exact Prod.ext (Fin.ext hxx) (Fin.ext hzz)

theorem eFunGid_bijective (w bits accBase : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) :
    Function.Bijective (eFunGid w bits accBase) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨eFunGid_injective w bits accBase haccfit, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      ← pow_add, comp_add_bits]

/-- **BRICK 1 — the contiguous-accumulator product equiv `eGid`.**  Factors the
    in-place coset-multiplier register `Fin (2^cosetDim)` into control
    `Fin (2^(cosetDim-bits))` × data `Fin (2^bits)`, with the data slice carrying the
    accumulator VALUE at the CONTIGUOUS block `[accBase, accBase+bits)`.  Serves both
    passes via `accBase` (pass-1 `b @ 1+2w+bits`, pass-2 `a @ 1+2w`). -/
noncomputable def eGid (w bits accBase : Nat) (haccfit : accBase + bits ≤ cosetDim w bits) :
    Fin (2 ^ (cosetDim w bits - bits)) × Fin (2 ^ bits) ≃ Fin (2 ^ cosetDim w bits) :=
  Equiv.ofBijective (eFunGid w bits accBase) (eFunGid_bijective w bits accBase haccfit)

/-- The two in-place accumulator blocks both fit: `accBase + bits ≤ cosetDim w bits`
    for pass-1 (`accBase = 1+2w+bits`) and pass-2 (`accBase = 1+2w`). -/
theorem pass1_accfit (w bits : Nat) : (1 + 2 * w + bits) + bits ≤ cosetDim w bits := by
  unfold cosetDim; omega

theorem pass2_accfit (w bits : Nat) : (1 + 2 * w) + bits ≤ cosetDim w bits := by
  unfold cosetDim; omega

end FormalRV.Shor.GidneyInPlace.InPlaceEgate
