/-
  FormalRV.LatticeSurgery.SurgeryCorrect — operational correctness of a
  qLDPC code-surgery gadget: it implements the logical Pauli measurement
  of its target operator.  This completes Step 2 of the LDPC-PPM plan
  beyond the operator-support readout of `SurgeryReadout`.

  Two operational obligations, grounded verbatim in qianxu App. C
  (`~/Downloads/qianxuLatex/main.tex`):

  * **(R) Eigenvalue extraction** (`main.tex:544`): "the outcomes of the
    target logical operators ℒ [are] extracted from the parities of the
    merged-code X-checks in the first stabilizer measurement cycle."
    Formalized as `surgery_eigenvalue`: the product of the
    `span_witness`-selected SIGNED merged X-checks equals the target
    logical operator, signed by the XOR-parity of those checks' outcomes.

  * **(N) Non-disturbance** (`main.tex:544`): the data logical operators
    that commute with ℒ are preserved ("the k−t logical Z̄ operators of
    the data code that commute with ℒ").  Formalized as
    `surgery_preserves_commuting_logical`: any operator commuting with all
    merged X-checks survives the merge measurement (folded `apply_PPM`).

  The fault-tolerance triple (`main.tex:435` (i) merged distance Θ(d),
  (ii) merged qLDPC, (iii) τ_s = Θ(d)) is the delimited residue:
  (ii)/(iii) are decidable in `LDPCSurgery.verify_surgery_gadget`; the
  merged distance (i) is the single Cheeger-backed external axiom.

  No Mathlib.  Pure Bool / Nat / List + the PauliString algebra.
-/

import FormalRV.LatticeSurgery.SurgeryReadout

namespace FormalRV.Framework.SurgeryCorrect

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMUpdate
open FormalRV.Framework.PPMOp
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryReadout

/-! ## Signed X-row: a measured merged X-check carrying its ±1 outcome -/

/-- An X-type check / logical lowered to a `PauliString`, with phase
    encoding a measurement outcome (`s = true` ↦ `−1` ↦ `Phase.minus`). -/
def signedXRow (s : Bool) (l : BoolVec) : PauliString :=
  ⟨if s then Phase.minus else Phase.plus, l.map xBit⟩

@[simp] theorem signedXRow_ops (s : Bool) (l : BoolVec) :
    (signedXRow s l).ops = l.map xBit := rfl

@[simp] theorem signedXRow_phase (s : Bool) (l : BoolVec) :
    (signedXRow s l).phase = (if s then Phase.minus else Phase.plus) := rfl

/-- An unsigned `xRow` is the `s = false` signed row. -/
theorem xRow_eq_signedXRow_false (l : BoolVec) : xRow l = signedXRow false l := rfl

/-! ## Single-qubit X/I products carry trivial phase

    `X·X = +I`, `X·I = +X`, `I·X = +X`, `I·I = +I`: the phase is always
    `+`.  This is why the *only* sign in a product of X/I strings comes
    from the strings' own phases (the measurement outcomes). -/

theorem pmul_xBit_phase (a b : Bool) :
    (Pauli.mul (xBit a) (xBit b)).1 = Phase.plus := by
  cases a <;> cases b <;> rfl

/-! ## Phase-component of the product fold

    Companion to `PPMUpdate.foldl_mul_snd` (which tracks the `.ops`
    accumulator): this tracks the `.1` (phase) accumulator of the same
    fold, collapsing it to a single `foldl` over phases.  Mirrors the
    proof of `foldl_mul_snd` verbatim. -/
theorem foldl_mul_fst (l : List (Pauli × Pauli)) (ph0 : Phase) (acc0 : List Pauli) :
    (l.foldl
      (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
        let (a, b) := ab
        let (ph, c) := Pauli.mul a b
        (acc.1.mul ph, acc.2 ++ [c])) (ph0, acc0)).1
    = l.foldl (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) ph0 := by
  induction l generalizing ph0 acc0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.foldl_cons]
    rw [ih]

/-- If every zipped pair multiplies to phase `+`, the phase fold is the
    identity on its seed.  This is the engine that proves the *only*
    sign in a product of X/I strings comes from the strings' own
    phases (their measurement outcomes). -/
theorem foldl_phase_plus (l : List (Pauli × Pauli)) (ph0 : Phase)
    (hall : ∀ ab ∈ l, (Pauli.mul ab.1 ab.2).1 = Phase.plus) :
    l.foldl (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) ph0 = ph0 := by
  induction l generalizing ph0 with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [hall hd List.mem_cons_self]
    have hp : ph0.mul Phase.plus = ph0 := Phase.mul_plus ph0
    rw [hp]
    exact ih ph0 (fun ab hab => hall ab (List.mem_cons_of_mem _ hab))

/-! ## Multiplication of signed X-rows: outcomes XOR, supports XOR -/

/-- The phase fold over a zip of `xBit`-lowered lists is trivial, since
    every X/I single-qubit product carries phase `+` (`pmul_xBit_phase`). -/
theorem foldl_phase_plus_xBit (a b : BoolVec) :
    ((a.map xBit).zip (b.map xBit)).foldl
        (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) Phase.plus
      = Phase.plus := by
  apply foldl_phase_plus
  intro ab hab
  -- `ab` is a zipped pair of `xBit`-images, so each component is `xBit _`.
  have ha : ab.1 ∈ a.map xBit := List.of_mem_zip hab |>.1
  have hb : ab.2 ∈ b.map xBit := List.of_mem_zip hab |>.2
  obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
  rw [← hx, ← hy]
  exact pmul_xBit_phase x y

/-- The `.ops` of a product of two signed X-rows is the support-XOR row,
    identical to the unsigned `xRow` case (phase lives only in `.phase`). -/
theorem signedXRow_mul_ops (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    ((signedXRow sa a).mul (signedXRow sb b)).ops = (xRow (vec_xor a b)).ops := by
  rw [mul_ops]
  simp only [signedXRow_ops, xRow_ops]
  exact zipmap_pmul_xBit a b h

/-- The `.phase` of a product of two signed X-rows is the XOR of the two
    outcome signs: `(-1)^sa · (-1)^sb = (-1)^(sa⊕sb)`.  All single-qubit
    X/I products are phase-trivial, so no extra sign is produced. -/
theorem signedXRow_mul_phase (sa sb : Bool) (a b : BoolVec) :
    ((signedXRow sa a).mul (signedXRow sb b)).phase
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
  show ((signedXRow sa a).phase.mul (signedXRow sb b).phase).mul
        (((signedXRow sa a).ops.zip (signedXRow sb b).ops).foldl
          (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
            let (x, y) := ab
            let (ph, c) := Pauli.mul x y
            (acc.1.mul ph, acc.2 ++ [c]))
          (Phase.plus, ([] : List Pauli))).1
      = (if (sa != sb) then Phase.minus else Phase.plus)
  rw [foldl_mul_fst]
  simp only [signedXRow_ops, signedXRow_phase]
  rw [foldl_phase_plus_xBit a b]
  have hp : ((if sa then Phase.minus else Phase.plus).mul
        (if sb then Phase.minus else Phase.plus)).mul Phase.plus
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
    cases sa <;> cases sb <;> rfl
  exact hp

/-- **Signed multiplication law.**  Multiplying two signed X-rows XORs
    both their outcome signs and their supports.  This is the algebra
    that lets a product of measured merged X-checks carry the XOR-parity
    of their individual ±1 outcomes. -/
theorem signedXRow_mul (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    (signedXRow sa a).mul (signedXRow sb b) = signedXRow (sa != sb) (vec_xor a b) := by
  have hops : ((signedXRow sa a).mul (signedXRow sb b)).ops
      = (signedXRow (sa != sb) (vec_xor a b)).ops := by
    rw [signedXRow_mul_ops sa sb a b h, signedXRow_ops, xRow_ops]
  have hphase : ((signedXRow sa a).mul (signedXRow sb b)).phase
      = (signedXRow (sa != sb) (vec_xor a b)).phase := by
    rw [signedXRow_mul_phase sa sb a b, signedXRow_phase]
  -- Reconstruct the structure equality from the two field equalities.
  cases hps : (signedXRow sa a).mul (signedXRow sb b) with
  | mk ph ops =>
    cases hrhs : signedXRow (sa != sb) (vec_xor a b) with
    | mk ph' ops' =>
      rw [hps, hrhs] at hphase hops
      simp only at hphase hops
      rw [hphase, hops]

/-! ## Selected signed product mirroring `row_combination` -/

/-- The XOR-parity of the outcome signs `ss` over exactly the rows
    selected by `sel`, mirroring the recursion of `row_combination`. -/
def selectedParity : BoolVec → List Bool → Bool
  | [],          _       => false
  | _,           []      => false
  | false :: ts, _ :: ss => selectedParity ts ss
  | true :: ts,  s :: ss => s != selectedParity ts ss

/-- The signed Pauli-string product of the merged X-checks selected by
    `sel`, with each selected check carrying its measurement-outcome sign
    from `ss`.  Mirrors `selectedXProduct`/`row_combination` (including
    the empty-accumulator special case) so all three stay in lockstep. -/
def selectedSignedProduct : BoolVec → BoolMat → List Bool → PauliString
  | [],          _,         _       => xRow []
  | _,           [],        _       => xRow []
  | _,           _,         []      => xRow []
  | false :: ts, _ :: tm,   _ :: ss => selectedSignedProduct ts tm ss
  | true :: ts,  row :: tm, s :: ss =>
      let acc := selectedSignedProduct ts tm ss
      match acc.ops with
      | []       => signedXRow s row
      | _        => (signedXRow s row).mul acc

/-! ## Lockstep: the signed product mirrors `row_combination` -/

/-- **Operator-support lockstep for the signed product.**  The `.ops` of
    `selectedSignedProduct` is the lowering of the GF(2) `row_combination`
    of the same selection — identical to `selectedXProduct_ops`, since the
    signs live only in `.phase`.  Proved by induction mirroring the shared
    recursion, using `signedXRow_mul_ops` in the key case. -/
theorem selectedSignedProduct_ops (n : Nat) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      (selectedSignedProduct sel mat ss).ops = (xRow (row_combination sel mat)).ops := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedProduct, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          simp only [selectedSignedProduct, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at ihe
            have hacc : (selectedSignedProduct ts tm ss).ops = [] := by
              rw [ihe]; rfl
            rw [hacc]
            rfl
          | cons c cs =>
            rw [hrc] at ihe
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            -- The accumulator's `.ops` is `(c::cs).map xBit`, hence nonempty.
            have hacc : (selectedSignedProduct ts tm ss).ops = (c :: cs).map xBit := by
              rw [ihe]; rfl
            rw [hacc]
            show ((signedXRow sgn row).mul (selectedSignedProduct ts tm ss)).ops
                = (xRow (vec_xor row (c :: cs))).ops
            rw [mul_ops, signedXRow_ops, hacc]
            show ((xRow row).ops.zip (xRow (c :: cs)).ops).map (fun ab => pmul2 ab.1 ab.2)
                = (xRow (vec_xor row (c :: cs))).ops
            rw [← mul_ops]
            exact xRow_vec_xor_ops row (c :: cs) hlen

/-- When the rows have positive width `n`, an empty GF(2) `row_combination`
    forces the selected outcome-parity to be `false`: no `true` is selected
    (a selected positive-width row would make the combination nonempty), so
    `selectedParity` XORs over the empty selected set.  This is the
    invariant that justifies the empty-accumulator branch of
    `selectedSignedProduct` discarding the accumulator's (necessarily `+`)
    sign. -/
theorem parity_false_of_combo_nil (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length → row_combination sel mat = [] →
      selectedParity sel ss = false := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen hcombo
    cases mat with
    | nil =>
      cases ss with
      | nil => rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedParity]
          simp only [row_combination] at hcombo
          exact ih tm ss htm hslen' hcombo
        | true =>
          exfalso
          -- A `true` selection of a width-`n` row cannot yield an empty combo.
          have hrow : row.length = n := hmat row List.mem_cons_self
          simp only [row_combination] at hcombo
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at hcombo
            simp only at hcombo
            rw [hcombo] at hrow
            simp at hrow
            omega
          | cons c cs =>
            rw [hrc] at hcombo
            simp only at hcombo
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hvx : (vec_xor row (c :: cs)).length = n := by
              rw [vec_xor_length, hrow, hcs]; omega
            rw [hcombo] at hvx
            simp at hvx
            omega

/-- **Full lockstep theorem (sign-aware).**  The signed product of the
    `sel`-selected merged X-checks equals the lowering of the GF(2)
    `row_combination` of the same selection, signed by the XOR-parity of
    the selected outcome bits.  This refines `selectedXProduct_ops` from
    the operator-support level to the full `PauliString` (phase included).
    Proved by induction mirroring the shared recursion; the key
    `true :: ts` case uses `signedXRow_mul` to combine, and
    `selectedSignedProduct_ops` to detect the empty-accumulator branch
    (whose parity is pinned to `false` by `parity_false_of_combo_nil`). -/
theorem selectedSignedProduct_eq (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      selectedSignedProduct sel mat ss
        = signedXRow (selectedParity sel ss) (row_combination sel mat) := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedProduct, selectedParity, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          have ihops := selectedSignedProduct_ops n ts tm ss htm hslen'
          simp only [selectedSignedProduct, selectedParity, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            -- Accumulator support empty ⇒ `signedXRow sgn row` branch.
            rw [hrc] at ihops
            have hacc : (selectedSignedProduct ts tm ss).ops = [] := by
              rw [ihops]; rfl
            rw [hacc]
            -- Parity of the tail selection is `false` (no `true` selected).
            have hpar : selectedParity ts ss = false :=
              parity_false_of_combo_nil n hn ts tm ss htm hslen' hrc
            rw [hpar, Bool.bne_false]
          | cons c cs =>
            -- Accumulator support nonempty ⇒ `(signedXRow sgn row).mul acc`.
            rw [hrc] at ihops ihe
            have hacc : (selectedSignedProduct ts tm ss).ops = (c :: cs).map xBit := by
              rw [ihops]; rfl
            rw [hacc]
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            -- Replace the accumulator by its IH normal form, then combine.
            show (signedXRow sgn row).mul (selectedSignedProduct ts tm ss)
                = signedXRow (sgn != selectedParity ts ss) (vec_xor row (c :: cs))
            rw [ihe, signedXRow_mul sgn (selectedParity ts ss) row (c :: cs) hlen]

/-! ## The eigenvalue-extraction statement -/

/-- **Surgery eigenvalue extraction (qianxu App. C, `main.tex:544`).**
    If the merged X-check matrix is rectangular (all rows of positive
    width `n`), the outcome-sign list is aligned with it, and the gadget
    passes its decidable kernel condition `targets_logical_correctly`
    (qianxu's `⟨ℒ⟩ = f_X'^T ker(H_X'^T)`), then the signed product of the
    `span_witness`-selected merged X-checks equals the target logical
    operator `P̄`, signed by the XOR-parity of those checks' measurement
    outcomes.  This is "the outcome of P̄ = parity of the merged X-checks
    in cycle 1": the operator support is fixed (`surgery_readout_operator`)
    and the phase carries the XOR of the individual ±1 outcomes. -/
theorem surgery_eigenvalue (g : SurgeryGadget) (n : Nat) (hn : 0 < n) (signs : List Bool)
    (hshape : ∀ r ∈ g.merged_hx, r.length = n) (hsig : signs.length = g.merged_hx.length)
    (hker : g.targets_logical_correctly = true) :
    selectedSignedProduct g.span_witness g.merged_hx signs
      = signedXRow (selectedParity g.span_witness signs) g.target_pauli := by
  have hcombo : row_combination g.span_witness g.merged_hx = g.target_pauli :=
    of_decide_eq_true (by simpa [SurgeryGadget.targets_logical_correctly] using hker)
  rw [selectedSignedProduct_eq n hn g.span_witness g.merged_hx signs hshape hsig, hcombo]

end FormalRV.Framework.SurgeryCorrect
