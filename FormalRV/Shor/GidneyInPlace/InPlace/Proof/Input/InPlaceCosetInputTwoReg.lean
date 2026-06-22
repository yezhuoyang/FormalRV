/-
  FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
  ──────────────────────────────────────────────────────
  The TWO-REGISTER coset input for the in-place Gidney multiplier, and its
  `branchOfE` projections under BOTH `eGid` factorizations (pass-1 data = b-block,
  pass-2 data = a-block).  NO gate dynamics, NO `uc_eval`, NO `normSqDist`,
  NO bad-set — purely the state object plus its two control×data projections.

  THE OBJECT.  On `Fin (2 ^ cosetDim w bits)` (`cosetDim w bits = 2 + 2w + 3·bits`):
   • register a @ block `[1+2w, 1+2w+bits)`        holds `cosetState (2^bits) N cm xa`;
   • register b @ block `[1+2w+bits, 1+2w+2·bits)` holds `cosetState (2^bits) N cm xb`;
   • scratch (ctrl @0; address/AND lookup zone `[1,1+2w]`; temp `[1+2w+2·bits, …]`;
     carry @ `1+2w+3·bits`) is CLEAN (ctrl bit `true`, the rest `false`).
  It is the PRODUCT of the two block coset states times a clean-scratch indicator.
  For the actual gate input one takes `xa = x`, `xb = 0`.

  DESIGN — BLOCK-NEUTRAL.  The two `eGid` factorizations (`eGid … bBase` reads the
  b-block as the data factor, `eGid … aBase` reads the a-block) are DIFFERENT
  equivs, and we must prove each projection INDEPENDENTLY (we never relate the two —
  that refactor is a separate future step).  So we DO NOT define the state through
  either `eGid`; we define it block-neutrally on the index's bit-function (extracted
  by `nat_to_funbool`), reading BOTH block values + the scratch directly.  Then each
  projection is obtained by evaluating the single funbool-value lemma
  `cosetInputTwoReg_funboolNat` at that `eGid`'s assembled bit-function
  (`assembleEGid …`), discharging the per-position reads with `assembleEGid_data`
  (own data block) and `assembleEGid_comp` (the other block + scratch, which lie in
  the complement region — using `compIdxGid bits bBase j = j` for `j < bBase`, and
  symmetrically for the a-pass).

  AUDIT.  Branch indices are RAW `Fin (2^bits)` register values, NEVER residues mod N
  (`cosetState (2^bits) N cm ·` assigns the amplitude as a function of the raw index's
  window membership).  The control weights `β_b`/`β_a` are the OTHER block's coset
  amplitude (`1/√2^cm` when that block's value is in its window AND scratch clean,
  else `0`).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.InPlace.Proof.Input.InPlaceCosetInputGid

namespace FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.SQIRPort
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.GidneyInPlace.ReducedLookupCosetGate (cosetDim)
open FormalRV.Shor.GidneyInPlace.GatePerm (funboolNat funbool_to_nat_agree)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState)
open FormalRV.Shor.GidneyInPlace.CosetClass (cosetWindow)
open FormalRV.Shor.GidneyInPlace.BranchFactor (branchOfE)
open FormalRV.Shor.GidneyInPlace.InPlaceEgate

/-! ## §0. Layout abbreviations. -/

/-- a-register base: block `[aBase, aBase+bits)`. -/
def aBase (w : Nat) : Nat := 1 + 2 * w
/-- b-register base: block `[bBase, bBase+bits)`. -/
def bBase (w bits : Nat) : Nat := 1 + 2 * w + bits

/-! ## §1. The clean-scratch predicate and the block-neutral coset input. -/

/-- The clean-scratch indicator on a bit-function `g` for the two-register layout:
    ctrl bit set, and every NON-block position (the lookup zone `[1, 1+2w]`, the temp
    block `[1+2w+2·bits, 1+2w+3·bits)`, the carry `@ 1+2w+3·bits`) reads `false`.
    Equivalently: `g` is `false` everywhere outside the two data blocks and the ctrl
    bit, and `true` at the ctrl bit.  We phrase it as: `g p = true ↔ p = 0` for every
    NON-data position `p < cosetDim`. -/
def scratchClean (w bits : Nat) (g : Nat → Bool) : Prop :=
  g ulookup_ctrl_idx = true ∧
  (∀ p, p < cosetDim w bits →
    ¬ (aBase w ≤ p ∧ p < aBase w + bits) →
    ¬ (bBase w bits ≤ p ∧ p < bBase w bits + bits) →
    p ≠ ulookup_ctrl_idx → g p = false)

open Classical in
/-- The two-register coset input, defined block-neutrally on the index's bit-function
    `nat_to_funbool (cosetDim) idx.val`:
      amplitude = (a-block coset amplitude at `xa`)·(b-block coset amplitude at `xb`)
      when the scratch is clean, else `0`.
    The block values are the raw register decodes `decodeReg (aBase+·)`/`(bBase+·)`;
    membership in `cosetWindow (2^bits) N cm xa`/`xb` gates the per-block amplitude. -/
noncomputable def cosetInputTwoReg (w bits N cm xa xb : Nat) :
    QState (2 ^ cosetDim w bits) :=
  fun idx _ =>
    let g := nat_to_funbool (cosetDim w bits) idx.val
    let va := decodeReg (fun i => aBase w + i) bits g
    let vb := decodeReg (fun i => bBase w bits + i) bits g
    if scratchClean w bits g then
      (if (⟨va, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
        then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
      * (if (⟨vb, decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
        then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
    else 0

/-! ## §2. The funbool↔index bridge: `nat_to_funbool ∘ funboolNat` agrees on `[0,dim)`. -/

/-- **The funbool round-trip (agreement form).**  The bit-function recovered from the
    index `funboolNat dim f` (via `nat_to_funbool dim ·.val`) agrees with `extendBool
    dim f` — hence with `f` — on every position `< dim`.  Composes the value round-trip
    `funbool_to_nat_nat_to_funbool` with the digit-uniqueness `funbool_to_nat_agree`. -/
theorem nat_to_funbool_funboolNat_agree (dim : Nat) (f : Fin dim → Bool)
    (p : Nat) (hp : p < dim) :
    nat_to_funbool dim (funboolNat dim f).val p = GatePerm.extendBool dim f p := by
  have hval : funbool_to_nat dim (nat_to_funbool dim (funboolNat dim f).val)
      = funbool_to_nat dim (GatePerm.extendBool dim f) := by
    show funbool_to_nat dim (nat_to_funbool dim (funbool_to_nat dim (GatePerm.extendBool dim f)))
        = funbool_to_nat dim (GatePerm.extendBool dim f)
    exact funbool_to_nat_nat_to_funbool dim _ (funbool_to_nat_lt dim _)
  exact funbool_to_nat_agree dim _ _ hval p hp

/-- `scratchClean` depends only on the bit-function's values OFF BOTH data blocks —
    because every position it reads (ctrl `@0`, lookup zone, temp, carry) lies outside
    both `[aBase, aBase+bits)` and `[bBase, bBase+bits)`.  This is the form the
    projections need: `gz` agrees with the control function off the OWN data block, hence
    in particular off both blocks (the OTHER block sits in the control region too). -/
theorem scratchClean_congr_offBlocks (w bits : Nat) (g h : Nat → Bool)
    (hgh : ∀ p, p < cosetDim w bits →
      ¬ (aBase w ≤ p ∧ p < aBase w + bits) →
      ¬ (bBase w bits ≤ p ∧ p < bBase w bits + bits) → g p = h p) :
    scratchClean w bits g ↔ scratchClean w bits h := by
  have hctrl : ulookup_ctrl_idx < cosetDim w bits := by
    unfold ulookup_ctrl_idx cosetDim; omega
  have hctrla : ¬ (aBase w ≤ ulookup_ctrl_idx ∧ ulookup_ctrl_idx < aBase w + bits) := by
    unfold ulookup_ctrl_idx aBase; omega
  have hctrlb : ¬ (bBase w bits ≤ ulookup_ctrl_idx ∧ ulookup_ctrl_idx < bBase w bits + bits) := by
    unfold ulookup_ctrl_idx bBase; omega
  unfold scratchClean
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← hgh _ hctrl hctrla hctrlb]; exact h1, fun p hp hna hnb hnc => ?_⟩
    rw [← hgh p hp hna hnb]; exact h2 p hp hna hnb hnc
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [hgh _ hctrl hctrla hctrlb]; exact h1, fun p hp hna hnb hnc => ?_⟩
    rw [hgh p hp hna hnb]; exact h2 p hp hna hnb hnc

/-! ## §3. The funbool-value lemma: the amplitude at a basis index in terms of its bits. -/

open Classical in
/-- **The funbool-value lemma.**  The amplitude of `cosetInputTwoReg` at the basis index
    `funboolNat (cosetDim) f` is the predicate on `f`'s bits: gated by `scratchClean` of
    `extendBool … f`, the product of the a-block and b-block coset amplitudes (decoding
    the blocks via `decodeReg` of `extendBool … f`).  This is the SINGLE bridge both
    projections evaluate (each at its own `eGid`'s assembled bit-function). -/
theorem cosetInputTwoReg_funboolNat (w bits N cm xa xb : Nat)
    (f : Fin (cosetDim w bits) → Bool) :
    cosetInputTwoReg w bits N cm xa xb (funboolNat (cosetDim w bits) f) 0
      = if scratchClean w bits (GatePerm.extendBool (cosetDim w bits) f) then
          (if (⟨decodeReg (fun i => aBase w + i) bits (GatePerm.extendBool (cosetDim w bits) f),
                decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
              ∈ cosetWindow (2 ^ bits) N cm xa
            then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
          * (if (⟨decodeReg (fun i => bBase w bits + i) bits (GatePerm.extendBool (cosetDim w bits) f),
                  decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits))
              ∈ cosetWindow (2 ^ bits) N cm xb
              then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
        else 0 := by
  have hagree : ∀ p, p < cosetDim w bits →
      nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val p
        = GatePerm.extendBool (cosetDim w bits) f p :=
    fun p hp => nat_to_funbool_funboolNat_agree (cosetDim w bits) f p hp
  have hda : decodeReg (fun i => aBase w + i) bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      = decodeReg (fun i => aBase w + i) bits (GatePerm.extendBool (cosetDim w bits) f) :=
    decodeReg_ext _ _ _ _ (fun i hi => hagree (aBase w + i) (by unfold aBase cosetDim; omega))
  have hdb : decodeReg (fun i => bBase w bits + i) bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      = decodeReg (fun i => bBase w bits + i) bits (GatePerm.extendBool (cosetDim w bits) f) :=
    decodeReg_ext _ _ _ _ (fun i hi => hagree (bBase w bits + i) (by unfold bBase cosetDim; omega))
  have hsc : scratchClean w bits
        (nat_to_funbool (cosetDim w bits) (funboolNat (cosetDim w bits) f).val)
      ↔ scratchClean w bits (GatePerm.extendBool (cosetDim w bits) f) :=
    scratchClean_congr_offBlocks w bits _ _ (fun p hp _ _ => hagree p hp)
  unfold cosetInputTwoReg
  simp only []
  by_cases hcl : scratchClean w bits (GatePerm.extendBool (cosetDim w bits) f)
  · rw [if_pos (hsc.mpr hcl), if_pos hcl]
    congr 1
    · congr 2
      exact Fin.ext hda
    · congr 2
      exact Fin.ext hdb
  · rw [if_neg (fun hc => hcl (hsc.mp hc)), if_neg hcl]

/-! ## §4. The pass-B projection (data factor = b-block, `accBase = bBase`). -/

/-- The complement (control) bit-function for the pass-B `eGid` (`accBase = bBase`):
    the assembled bit-function with the b-data factor set to `0`.  The scratch and
    a-block of the actual input lie in the COMPLEMENT region, so they are read from
    `ctrl` alone, independent of the b-data value `z` — this function captures exactly
    that control content. -/
noncomputable def ctrlFunB (w bits ctrl : Nat) : Nat → Bool :=
  fun i => assembleEGid w bits (bBase w bits) ctrl 0 i

open Classical in
/-- The pass-B control weight `β_b`: the a-block coset amplitude (at `xa`), gated by the
    scratch being clean — both read from the control value `ctrl` (via `ctrlFunB`, i.e.
    independent of the b-data branch). -/
noncomputable def betaB (w bits N cm xa ctrl : Nat) : ℂ :=
  if scratchClean w bits (ctrlFunB w bits ctrl) then
    (if (⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xa
      then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
  else 0

/-- The complement (control) bit-function for the pass-A `eGid` (`accBase = aBase`):
    the assembled bit-function with the a-data factor set to `0`.  The scratch and
    b-block of the actual input lie in the COMPLEMENT region, read from `ctrl` alone. -/
noncomputable def ctrlFunA (w bits ctrl : Nat) : Nat → Bool :=
  fun i => assembleEGid w bits (aBase w) ctrl 0 i

open Classical in
/-- The pass-A control weight `β_a`: the b-block coset amplitude (at `xb`), gated by the
    scratch being clean — both read from the control value `ctrl` (via `ctrlFunA`, i.e.
    independent of the a-data branch). -/
noncomputable def betaA (w bits N cm xb ctrl : Nat) : ℂ :=
  if scratchClean w bits (ctrlFunA w bits ctrl) then
    (if (⟨decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl),
          decodeReg_lt_two_pow _ _ _⟩ : Fin (2 ^ bits)) ∈ cosetWindow (2 ^ bits) N cm xb
      then ((1 / Real.sqrt (2 ^ cm) : ℝ) : ℂ) else 0)
  else 0

/-- **`assembleEGid` is independent of the data value off the data block.**  At a
    position `p < cosetDim` outside the accumulator block `[accBase, accBase+bits)`,
    `assembleEGid` reads the CONTROL value `x` (via the complement enumerator), so the
    data value `z` is irrelevant — it agrees with `z = 0`.  (By `coverGid`: such a `p`
    is a complement position `compIdxGid j`, where `assembleEGid_comp` gives `x.testBit
    j` for both.) -/
theorem assembleEGid_off_block_zindep (w bits accBase x z p : Nat)
    (haccfit : accBase + bits ≤ cosetDim w bits) (hp : p < cosetDim w bits)
    (hoff : ¬ (accBase ≤ p ∧ p < accBase + bits)) :
    assembleEGid w bits accBase x z p = assembleEGid w bits accBase x 0 p := by
  rcases coverGid w bits accBase p haccfit hp with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact absurd ⟨Nat.le_add_right _ _, by omega⟩ hoff
  · rw [assembleEGid_comp w bits accBase x z j hj,
        assembleEGid_comp w bits accBase x 0 j hj]

/-- **Pass-B projection.**  Under the `eGid` factorization with `accBase = bBase` (the
    b-block is the data factor), the `branchOfE` data substate of `cosetInputTwoReg` in
    control branch `ctrl` is the b-register coset state `cosetState (2^bits) N cm xb`
    scaled by the control weight `betaB` (the a-coset amplitude × scratch-clean
    indicator, read from `ctrl` only).  Branch index `z` (inside `cosetState`) is a RAW
    `Fin (2^bits)` register value, NOT a residue. -/
theorem branchOfE_cosetInputTwoReg_passB (w bits N cm xa xb : Nat)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits))) :
    branchOfE (eGid w bits (bBase w bits) (pass1_accfit w bits))
        (cosetInputTwoReg w bits N cm xa xb) ctrl
      = fun i z => (betaB w bits N cm xa ctrl.val) * cosetState (2 ^ bits) N cm xb i z := by
  funext z hz
  have h0 : hz = 0 := Subsingleton.elim hz 0
  subst h0
  -- Reduce the LHS to a funbool index, then to the value lemma.
  show cosetInputTwoReg w bits N cm xa xb
      (eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, z)) 0
    = (betaB w bits N cm xa ctrl.val) * cosetState (2 ^ bits) N cm xb z 0
  -- The eGid image is the funbool index of the assembled bit-function.
  have hImg : eGid w bits (bBase w bits) (pass1_accfit w bits) (ctrl, z)
      = funboolNat (cosetDim w bits)
          (fun i => assembleEGid w bits (bBase w bits) ctrl.val z.val i.val) := by
    show eFunGid w bits (bBase w bits) (ctrl, z) = _
    rfl
  rw [hImg, cosetInputTwoReg_funboolNat w bits N cm xa xb _]
  -- Abbreviations for the z-assembled and 0-assembled (control) bit-functions.
  set gz : Nat → Bool :=
    GatePerm.extendBool (cosetDim w bits)
      (fun i => assembleEGid w bits (bBase w bits) ctrl.val z.val i.val) with hgz
  -- `gz p = assembleEGid … z.val p` on `[0,dim)`.
  have hgzval : ∀ p, p < cosetDim w bits →
      gz p = assembleEGid w bits (bBase w bits) ctrl.val z.val p := by
    intro p hp
    rw [hgz]; simp only [GatePerm.extendBool, dif_pos hp]
  -- `gz` agrees with the control function `ctrlFunB` off the b-block.
  have hgz_ctrl : ∀ p, p < cosetDim w bits →
      ¬ (bBase w bits ≤ p ∧ p < bBase w bits + bits) →
      gz p = ctrlFunB w bits ctrl.val p := by
    intro p hp hoff
    rw [hgzval p hp, ctrlFunB]
    exact assembleEGid_off_block_zindep w bits (bBase w bits) ctrl.val z.val p
      (pass1_accfit w bits) hp hoff
  -- b-block decodes to the raw data value `z`.
  have hbdec : decodeReg (fun i => bBase w bits + i) bits gz = z.val := by
    rw [decodeReg_eq_mod_of_testBit (fun i => bBase w bits + i) bits z.val gz
          (fun i hi => by
            rw [hgzval (bBase w bits + i) (by unfold bBase cosetDim; omega)]
            exact assembleEGid_data w bits (bBase w bits) ctrl.val z.val i hi)]
    exact Nat.mod_eq_of_lt z.isLt
  -- a-block decode equals the control function's a-block decode (z-independent).
  have hadec : decodeReg (fun i => aBase w + i) bits gz
      = decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val) :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hgz_ctrl (aBase w + i) (by unfold aBase cosetDim; omega)
        (by unfold aBase bBase; omega))
  -- scratch-clean is z-independent.
  have hscl : scratchClean w bits gz ↔ scratchClean w bits (ctrlFunB w bits ctrl.val) :=
    scratchClean_congr_offBlocks w bits _ _ (fun p hp _ hnb => hgz_ctrl p hp hnb)
  -- Assemble.
  rw [betaB, cosetState]
  by_cases hcl : scratchClean w bits (ctrlFunB w bits ctrl.val)
  · rw [if_pos (hscl.mpr hcl), if_pos hcl]
    -- match the b-amp to the coset window, the a-amp to betaB's a-amp.
    have hbeq : (⟨decodeReg (fun i => bBase w bits + i) bits gz, decodeReg_lt_two_pow _ _ _⟩
        : Fin (2 ^ bits)) = z := Fin.ext hbdec
    have haeq : (⟨decodeReg (fun i => aBase w + i) bits gz, decodeReg_lt_two_pow _ _ _⟩
        : Fin (2 ^ bits))
      = ⟨decodeReg (fun i => aBase w + i) bits (ctrlFunB w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ := Fin.ext hadec
    rw [hbeq, haeq]
  · rw [if_neg (fun hc => hcl (hscl.mp hc)), if_neg hcl, zero_mul]

/-! ## §5. The pass-A projection (data factor = a-block, `accBase = aBase`). -/

/-- **Pass-A projection.**  Under the `eGid` factorization with `accBase = aBase` (the
    a-block is the data factor), the `branchOfE` data substate of `cosetInputTwoReg` in
    control branch `ctrl` is the a-register coset state `cosetState (2^bits) N cm xa`
    scaled by the control weight `betaA` (the b-coset amplitude × scratch-clean
    indicator, read from `ctrl` only).  Proven INDEPENDENTLY of pass-B, via this
    factorization's own `assembleEGid_data`/`assembleEGid_comp`.  Branch index `z` is a
    RAW `Fin (2^bits)` register value, NOT a residue. -/
theorem branchOfE_cosetInputTwoReg_passA (w bits N cm xa xb : Nat)
    (ctrl : Fin (2 ^ (cosetDim w bits - bits))) :
    branchOfE (eGid w bits (aBase w) (pass2_accfit w bits))
        (cosetInputTwoReg w bits N cm xa xb) ctrl
      = fun i z => (betaA w bits N cm xb ctrl.val) * cosetState (2 ^ bits) N cm xa i z := by
  funext z hz
  have h0 : hz = 0 := Subsingleton.elim hz 0
  subst h0
  show cosetInputTwoReg w bits N cm xa xb
      (eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, z)) 0
    = (betaA w bits N cm xb ctrl.val) * cosetState (2 ^ bits) N cm xa z 0
  have hImg : eGid w bits (aBase w) (pass2_accfit w bits) (ctrl, z)
      = funboolNat (cosetDim w bits)
          (fun i => assembleEGid w bits (aBase w) ctrl.val z.val i.val) := by
    show eFunGid w bits (aBase w) (ctrl, z) = _
    rfl
  rw [hImg, cosetInputTwoReg_funboolNat w bits N cm xa xb _]
  set gz : Nat → Bool :=
    GatePerm.extendBool (cosetDim w bits)
      (fun i => assembleEGid w bits (aBase w) ctrl.val z.val i.val) with hgz
  have hgzval : ∀ p, p < cosetDim w bits →
      gz p = assembleEGid w bits (aBase w) ctrl.val z.val p := by
    intro p hp
    rw [hgz]; simp only [GatePerm.extendBool, dif_pos hp]
  have hgz_ctrl : ∀ p, p < cosetDim w bits →
      ¬ (aBase w ≤ p ∧ p < aBase w + bits) →
      gz p = ctrlFunA w bits ctrl.val p := by
    intro p hp hoff
    rw [hgzval p hp, ctrlFunA]
    exact assembleEGid_off_block_zindep w bits (aBase w) ctrl.val z.val p
      (pass2_accfit w bits) hp hoff
  -- a-block decodes to the raw data value `z`.
  have hadec : decodeReg (fun i => aBase w + i) bits gz = z.val := by
    rw [decodeReg_eq_mod_of_testBit (fun i => aBase w + i) bits z.val gz
          (fun i hi => by
            rw [hgzval (aBase w + i) (by unfold aBase cosetDim; omega)]
            exact assembleEGid_data w bits (aBase w) ctrl.val z.val i hi)]
    exact Nat.mod_eq_of_lt z.isLt
  -- b-block decode equals the control function's b-block decode (z-independent).
  have hbdec : decodeReg (fun i => bBase w bits + i) bits gz
      = decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val) :=
    decodeReg_ext _ _ _ _ (fun i hi =>
      hgz_ctrl (bBase w bits + i) (by unfold bBase cosetDim; omega)
        (by unfold aBase bBase; omega))
  -- scratch-clean is z-independent.
  have hscl : scratchClean w bits gz ↔ scratchClean w bits (ctrlFunA w bits ctrl.val) :=
    scratchClean_congr_offBlocks w bits _ _ (fun p hp hna _ => hgz_ctrl p hp hna)
  rw [betaA, cosetState]
  by_cases hcl : scratchClean w bits (ctrlFunA w bits ctrl.val)
  · rw [if_pos (hscl.mpr hcl), if_pos hcl]
    have haeq : (⟨decodeReg (fun i => aBase w + i) bits gz, decodeReg_lt_two_pow _ _ _⟩
        : Fin (2 ^ bits)) = z := Fin.ext hadec
    have hbeq : (⟨decodeReg (fun i => bBase w bits + i) bits gz, decodeReg_lt_two_pow _ _ _⟩
        : Fin (2 ^ bits))
      = ⟨decodeReg (fun i => bBase w bits + i) bits (ctrlFunA w bits ctrl.val),
          decodeReg_lt_two_pow _ _ _⟩ := Fin.ext hbdec
    rw [haeq, hbeq]
    ring
  · rw [if_neg (fun hc => hcl (hscl.mp hc)), if_neg hcl, zero_mul]

end FormalRV.Shor.GidneyInPlace.InPlaceCosetInputTwoReg
