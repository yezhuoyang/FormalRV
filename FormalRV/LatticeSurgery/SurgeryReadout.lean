/-
  FormalRV.Framework.SurgeryReadout — Step 2 of the LDPC-PPM
  correctness plan (`notes/topic-ldpc-ppm-correctness.md`): the
  READOUT bridge from the decidable kernel condition of a qLDPC
  code-surgery gadget to the Pauli-operator statement "the product
  of the measured merged X-checks equals the target logical Pauli".

  ## Where this sits

  `LDPCSurgery.SurgeryGadget` carries the merged-code parity matrices
  `merged_hx`/`merged_hz` (qianxu App. C, `main.tex:425`) and the
  decidable structural verifier `verify_surgery_gadget`, whose
  load-bearing clause is the kernel condition
     `targets_logical_correctly : row_combination span_witness merged_hx
                                   = target_pauli`
  (i.e. qianxu's `⟨ℒ⟩ = f_X'^T ker(H_X'^T)`, restated as a GF(2)
  row-span identity).  That clause is a fact about *bit vectors*.

  This file lifts it to a fact about *Pauli operators*: under the
  lowering `xRow` (X-support bitvector ↦ X-type PauliString), GF(2)
  addition of supports IS Pauli multiplication (`xRow_vec_xor_ops`),
  so the row-span identity says exactly that the product of the
  `span_witness`-selected merged X-checks acts as the target logical
  X-operator `P̄`.  This is the "back-end realization obligation"
  that the QMeas measurement language (sibling paper) takes as the
  axiom `transversal_X_is_logical_X` — here PROVED for the qLDPC
  merged-code construction, code-generally (any data code).

  Scope of THIS slice: the operator-support (`.ops`) statement —
  i.e. *which* logical Pauli is measured.  The eigenvalue-extraction
  (folding `apply_PPM` over the merged stabilizers, using the
  `PPMUpdateInvariants` lemmas) and non-disturbance are the next
  slice.  Phase/sign is +1 for X-type CSS checks; tracked separately.

  No Mathlib.  Pure Bool / Nat / List + the PauliString algebra.
-/

import FormalRV.PPM.PPMUpdateInvariants
import FormalRV.LatticeSurgery.LDPCSurgery

namespace FormalRV.Framework.SurgeryReadout

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMUpdate
open FormalRV.Framework.LDPC

/-! ## Lowering X-support bitvectors to Pauli strings -/

/-- An X-support bit lowered to a single-qubit Pauli (`true ↦ X`). -/
@[inline] def xBit (b : Bool) : Pauli := if b then Pauli.X else Pauli.I

/-- Lower an X-type check / logical support vector to a `PauliString`
    (phase `+`; `true ↦ X`, `false ↦ I`). -/
def xRow (l : List Bool) : PauliString := ⟨Phase.plus, l.map xBit⟩

@[simp] theorem xRow_ops (l : List Bool) : (xRow l).ops = l.map xBit := rfl

/-! ## The GF(2)→Pauli homomorphism (operator-support level) -/

/-- Pointwise: the X/I product (dropping phase) of two X-support bits
    is the XOR of the bits.  `X·X = I`, `X·I = X`, `I·X = X`, `I·I = I`. -/
theorem pmul2_xBit (a b : Bool) : pmul2 (xBit a) (xBit b) = xBit (a != b) := by
  cases a <;> cases b <;> rfl

/-- Pure-list core of the homomorphism: zipping two X-support lists and
    taking pointwise products equals XOR-ing then lowering. -/
theorem zipmap_pmul_xBit (a b : List Bool) (h : a.length = b.length) :
    ((a.map xBit).zip (b.map xBit)).map (fun p => pmul2 p.1 p.2)
      = (vec_xor a b).map xBit := by
  induction a generalizing b with
  | nil => simp [vec_xor]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.zip_cons_cons, vec_xor, pmul2_xBit,
        ih ys (by simpa using h)]

/-- **Key homomorphism.**  GF(2) addition of X-supports = Pauli
    multiplication of the corresponding X-strings, at the operator
    (`ops`) level.  This is what makes the kernel condition a
    statement about the measured logical operator. -/
theorem xRow_vec_xor_ops (a b : List Bool) (h : a.length = b.length) :
    ((xRow a).mul (xRow b)).ops = (xRow (vec_xor a b)).ops := by
  rw [mul_ops, xRow_ops]
  simp only [xRow_ops]
  exact zipmap_pmul_xBit a b h

/-! ## Merged-code X-stabilizers as Pauli strings -/

/-- The X-type stabilizers of the merged code, lowered to Pauli
    strings.  These are the operators measured during the surgery
    merge (qianxu App. C step 2). -/
def merged_stabilizers_X (g : SurgeryGadget) : List PauliString :=
  g.merged_hx.map xRow

/-! ## Selected product mirroring `row_combination` -/

/-- The Pauli-string product of the merged X-checks selected by `sel`,
    mirroring the recursion of `LDPC.row_combination` (including its
    empty-accumulator special case) so the two stay in lockstep. -/
def selectedXProduct (sel : List Bool) (mat : BoolMat) : PauliString :=
  match sel, mat with
  | [],          _         => xRow []
  | _,           []        => xRow []
  | false :: ts, _ :: tm   => selectedXProduct ts tm
  | true :: ts,  row :: tm =>
      let acc := selectedXProduct ts tm
      match acc.ops with
      | []       => xRow row
      | _        => (xRow row).mul acc

/-! ## Length bookkeeping for `row_combination` -/

/-- Componentwise XOR truncates to the shorter operand, so its length is
    the `min` of the two input lengths.  Needed below to discharge the
    `length`-equality side condition of `zipmap_pmul_xBit`. -/
theorem vec_xor_length (a b : BoolVec) :
    (vec_xor a b).length = min a.length b.length := by
  induction a generalizing b with
  | nil => simp [vec_xor]
  | cons x xs ih =>
    cases b with
    | nil => simp [vec_xor]
    | cons y ys => simp [vec_xor, ih ys]

/-- A `row_combination` over a rectangular matrix (every row of length
    `n`) is either empty (no rows selected, or empty selection/matrix)
    or itself of length `n`.  This is the shape invariant that lets the
    `selectedXProduct`/`row_combination` lockstep proof feed a
    `length`-matched pair into the GF(2)→Pauli homomorphism. -/
theorem row_combination_length (n : Nat) :
    ∀ (sel : List Bool) (mat : BoolMat), (∀ r ∈ mat, r.length = n) →
      (row_combination sel mat = [] ∨ (row_combination sel mat).length = n) := by
  intro sel
  induction sel with
  | nil => intro mat _; left; rfl
  | cons s ts ih =>
    intro mat hmat
    cases mat with
    | nil => left; rfl
    | cons row tm =>
      have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
      cases s with
      | false => simp only [row_combination]; exact ih tm htm
      | true =>
        simp only [row_combination]
        cases hrc : row_combination ts tm with
        | nil => right; exact hmat row List.mem_cons_self
        | cons c cs =>
          right
          have hrow : row.length = n := hmat row List.mem_cons_self
          have hcs : (c :: cs).length = n := by
            have := (ih tm htm).resolve_left (by rw [hrc]; simp)
            rw [hrc] at this; exact this
          rw [vec_xor_length, hrow, hcs]; omega

/-! ## `selectedXProduct` mirrors `row_combination` at the operator level -/

/-- **Lockstep theorem.**  The operator support of the
    `sel`-selected product of merged X-checks equals the lowering of the
    GF(2) `row_combination` of the same selection.  Proved by induction
    mirroring the shared recursion of `selectedXProduct` and
    `row_combination`; the key `true :: ts, row :: tm` case uses the
    GF(2)→Pauli homomorphism `xRow_vec_xor_ops` together with the
    `row_combination_length` shape invariant to discharge the
    `length`-matched side condition. -/
theorem selectedXProduct_ops (n : Nat) :
    ∀ (sel : List Bool) (mat : BoolMat), (∀ r ∈ mat, r.length = n) →
      (selectedXProduct sel mat).ops = (xRow (row_combination sel mat)).ops := by
  intro sel
  induction sel with
  | nil => intro mat _; rfl
  | cons s ts ih =>
    intro mat hmat
    cases mat with
    | nil =>
      cases s <;> rfl
    | cons row tm =>
      have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
      cases s with
      | false =>
        simp only [selectedXProduct, row_combination]
        exact ih tm htm
      | true =>
        have ihe := ih tm htm
        simp only [selectedXProduct, row_combination]
        cases hrc : row_combination ts tm with
        | nil =>
          rw [hrc] at ihe
          have hacc : (selectedXProduct ts tm).ops = [] := by
            rw [ihe]; rfl
          rw [hacc]
        | cons c cs =>
          rw [hrc] at ihe
          have hrow : row.length = n := hmat row List.mem_cons_self
          have hcs : (c :: cs).length = n := by
            have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
            rw [hrc] at this; exact this
          have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
          rw [ihe]
          show ((xRow row).mul (selectedXProduct ts tm)).ops
              = (xRow (vec_xor row (c :: cs))).ops
          rw [mul_ops, ihe, ← mul_ops]
          exact xRow_vec_xor_ops row (c :: cs) hlen

/-! ## The readout statement -/

/-- **Surgery readout operator.**  If the merged X-check matrix is
    rectangular (all rows of width `n`) and the gadget passes its
    decidable kernel condition `targets_logical_correctly` (qianxu's
    `⟨ℒ⟩ = f_X'^T ker(H_X'^T)`, restated as a GF(2) row-span identity),
    then the product of the `span_witness`-selected merged X-checks acts,
    at the operator-support level, as exactly the target logical
    X-operator `P̄`.

    This is the "back-end realization obligation" that the QMeas
    measurement language axiomatizes as `transversal_X_is_logical_X`;
    here it is PROVED for the qLDPC merged-code construction, code
    generally (for any data code, any rectangular merged `H_X`). -/
theorem surgery_readout_operator (g : SurgeryGadget) (n : Nat)
    (hshape : ∀ r ∈ g.merged_hx, r.length = n)
    (hker : g.targets_logical_correctly = true) :
    (selectedXProduct g.span_witness g.merged_hx).ops = (xRow g.target_pauli).ops := by
  have hcombo : row_combination g.span_witness g.merged_hx = g.target_pauli :=
    of_decide_eq_true (by simpa [SurgeryGadget.targets_logical_correctly] using hker)
  rw [selectedXProduct_ops n g.span_witness g.merged_hx hshape, hcombo]

/-! ## Concrete smoke test (exercises the math directly, no full gadget) -/

/-- GF(2) selection of both rows of a 2×3 X-check matrix: the row span
    of `[[X·X], …]` selected by `[true,true]` is the componentwise XOR
    `vec_xor [T,F,T] [F,T,T] = [T,T,F]`. -/
example : row_combination [true, true] [[true, false, true], [false, true, true]]
    = [true, true, false] := by decide

/-- The Pauli-string product computed by `selectedXProduct` over the same
    selection has exactly the operator support of the lowered XOR vector
    `xRow [T,T,F] = X⊗X⊗I`.  Demonstrates `selectedXProduct` realizes the
    row-span product correctly on a concrete instance. -/
example : (selectedXProduct [true, true] [[true, false, true], [false, true, true]]).ops
    = (xRow [true, true, false]).ops := by decide

end FormalRV.Framework.SurgeryReadout
