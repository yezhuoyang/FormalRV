/-
  FormalRV.Framework.CliffordConj — the GATE-LEVEL rung of the
  QEC verification stack.

  ## What this file is

  The physical realization of a single stabilizer measurement
  (a Pauli-Product Measurement, PPM) is a *gate* circuit:

      prepare ancilla `a` in |0⟩  (stabilized by Z_a)
      apply CNOT(data_i → a) for each i in the stabilizer support
      measure Z_a

  This file proves — from the single-qubit CNOT conjugation
  rules, by `decide` on the symplectic (x,z)-bit table — that
  this gate circuit measures exactly the intended stabilizer.

  ## The Heisenberg (Gottesman) picture

  A Clifford gate `C` conjugates a Pauli `P ↦ C P C†`.  Measuring
  an observable `M` *after* `C` is the same as measuring `C† M C`
  *before* `C`.  So to find what the final `measure Z_a` measures
  on the input data, we conjugate the ancilla observable `Z_a`
  back through the gadget's CNOTs.

  For a Z-type stabilizer `S = ∏_{i∈supp} Z_i`, conjugating `Z_a`
  back through `CNOT(data_i → a)` for each `i∈supp` yields
  `(∏_{i∈supp} Z_i) · Z_a = S · Z_a`.  Hence measuring `Z_a`
  measures `S` on the data register.  Everything is Z-type, so no
  `Y` arises and the global phase stays `+1` throughout.

  ## The CNOT symplectic rule

  On per-qubit (x,z) bits, `CNOT(control=c, target=t)` acts by

      x_t ↦ x_t ⊕ x_c        (control X spreads to target)
      z_c ↦ z_c ⊕ z_t        (target Z spreads to control)

  with `x_c`, `z_t` unchanged.  Equivalently the transfer table:
  `X_c ↦ X_c X_t`, `Z_t ↦ Z_c Z_t`, `X_t` and `Z_c` fixed.

  ## Where this fits in the stack

  This is the GATE-LEVEL rung: the physical ancilla+CNOT+measure
  circuit realizes one stabilizer measurement (PPM).  The full
  Hilbert-space faithfulness of the Heisenberg/Pauli-conjugation
  picture is the once-proven Gottesman–Knill bridge (cited
  residue — we work in the symplectic Pauli algebra, which that
  bridge certifies is faithful to the state action).

  Rungs above this one:
    * `QEC.CSSCode.syndrome_circuit_implements_code`
        — the code (many stabilizers measured together)
    * `SurgeryCorrect.surgery_implements_logical_measurement`
        — logical PPM via lattice surgery
    * `Corpus.ShorPPMEndToEnd`
        — Shor's algorithm end-to-end

  No Mathlib.  Pure Bool / Nat / List.  Decidable everywhere.
-/
import FormalRV.PPM.PauliSemantics

namespace FormalRV.Framework.CliffordConj

open FormalRV.Framework.PauliSem

/-! ## (1) Single-qubit symplectic encode/decode -/

/-- `(x,z)` symplectic bits of a single-qubit Pauli:
    `I = (F,F)`, `X = (T,F)`, `Z = (F,T)`, `Y = (T,T)`. -/
def toSym : Pauli → Bool × Bool
  | .I => (false, false)
  | .X => (true,  false)
  | .Z => (false, true)
  | .Y => (true,  true)

/-- Inverse of `toSym`. -/
def ofSym : Bool × Bool → Pauli
  | (false, false) => .I
  | (true,  false) => .X
  | (false, true)  => .Z
  | (true,  true)  => .Y

/-- `ofSym` is a left inverse of `toSym` — the symplectic
    encoding is lossless. -/
theorem ofSym_toSym (p : Pauli) : ofSym (toSym p) = p := by
  cases p <;> rfl

/-! ## (2) CNOT conjugation on a `PauliString`

    We operate on positions `c` (control) and `t` (target) of
    `p.ops`.  Because the Z-type measurement gadget never
    produces a `Y`, no extra `±i` factors are introduced, so we
    keep the phase as `p.phase`.  Correctness of the
    sign tracking is therefore documented for the Y-free /
    Z-only case used by the gadget below. -/

/-- Conjugate `p` by `CNOT(control=c, target=t)`: read the
    `(x,z)` bits at positions `c` and `t`, update them by
    `x_t ⊕= x_c` and `z_c ⊕= z_t` (with `x_c`, `z_t` fixed),
    and write the new Paulis back.

    Implemented via `List.getD`/`List.set` over `p.ops`.  Out-of-
    range indices read as `I` (getD default) and writes are
    no-ops, so the definition is total. -/
def cnotConj (c t : Nat) (p : PauliString) : PauliString :=
  let pc := p.ops.getD c .I
  let pt := p.ops.getD t .I
  let (xc, zc) := toSym pc
  let (xt, zt) := toSym pt
  let pc' := ofSym (xc, xor zc zt)   -- z_c ⊕= z_t
  let pt' := ofSym (xor xt xc, zt)   -- x_t ⊕= x_c
  { phase := p.phase
    ops   := (p.ops.set c pc').set t pt' }

/-! ## (3) Single- / 2-qubit conjugation correctness by `decide`

    The standard CNOT conjugation table on `c=0, t=1`:
      `X⊗I ↦ X⊗X`,  `I⊗Z ↦ Z⊗Z`,  `Z⊗I ↦ Z⊗I`,  `I⊗X ↦ I⊗X`. -/

/-- `X⊗I ↦ X⊗X` (control X spreads to target). -/
example : cnotConj 0 1 ⟨Phase.plus, [Pauli.X, Pauli.I]⟩
    = ⟨Phase.plus, [Pauli.X, Pauli.X]⟩ := by decide

/-- `I⊗Z ↦ Z⊗Z` (target Z spreads to control). -/
example : cnotConj 0 1 ⟨Phase.plus, [Pauli.I, Pauli.Z]⟩
    = ⟨Phase.plus, [Pauli.Z, Pauli.Z]⟩ := by decide

/-- `Z⊗I ↦ Z⊗I` (control Z fixed). -/
example : cnotConj 0 1 ⟨Phase.plus, [Pauli.Z, Pauli.I]⟩
    = ⟨Phase.plus, [Pauli.Z, Pauli.I]⟩ := by decide

/-- `I⊗X ↦ I⊗X` (target X fixed). -/
example : cnotConj 0 1 ⟨Phase.plus, [Pauli.I, Pauli.X]⟩
    = ⟨Phase.plus, [Pauli.I, Pauli.X]⟩ := by decide

/-! ## (4) The Z-stabilizer-measurement GADGET theorem -/

/-- Conjugate the ancilla observable `Z_a` back through the
    gadget's CNOTs `CNOT(data_i → a)` for each `i` in `supp`.
    In the Heisenberg picture the result is the observable that
    `measure Z_a` actually measures on the input register, namely
    `(∏_{i∈supp} Z_i) · Z_a`. -/
def measGadgetConj (supp : List Nat) (a : Nat) (p : PauliString) : PauliString :=
  supp.foldl (fun q i => cnotConj i a q) p

/-- GATE-LEVEL gadget: the ancilla+CNOT(0→2)+CNOT(1→2)+measure-Z₂
    circuit measures the stabilizer `Z₀Z₁`.  In the Heisenberg
    picture the measured `Z₂` becomes `Z₀Z₁Z₂` — the `Z₀Z₁` part
    is the stabilizer measured on the 2-qubit data register; the
    trailing `Z₂` is the ancilla's own observable. -/
theorem measGadget_measures_Z0Z1 :
    measGadgetConj [0, 1] 2 ⟨Phase.plus, [Pauli.I, Pauli.I, Pauli.Z]⟩
      = ⟨Phase.plus, [Pauli.Z, Pauli.Z, Pauli.Z]⟩ := by decide

/-- GATE-LEVEL gadget (3-body): the ancilla+CNOT(0→3)+CNOT(1→3)
    +CNOT(2→3)+measure-Z₃ circuit measures the stabilizer
    `Z₀Z₁Z₂`.  The measured `Z₃` becomes `Z₀Z₁Z₂Z₃`. -/
theorem measGadget_measures_Z0Z1Z2 :
    measGadgetConj [0, 1, 2] 3
        ⟨Phase.plus, [Pauli.I, Pauli.I, Pauli.I, Pauli.Z]⟩
      = ⟨Phase.plus, [Pauli.Z, Pauli.Z, Pauli.Z, Pauli.Z]⟩ := by decide

/-! ## Per-qubit CNOT-conjugation lemmas (reusable building blocks)

    These characterize how a single `cnotConj i a` step acts on
    a Z-type canonical state (control reads `I`, ancilla reads
    `Z`).  They are the per-qubit transfer rules from the file
    header, packaged for the parametric induction below. -/

/-- `CNOT(i → a)` turns a control reading `I` into `Z` when the
    ancilla `a` reads `Z` (control Z spreads back from the target,
    since the target Z is mirrored onto the control). -/
theorem cnot_ctrl (p : PauliString) (i a : Nat) (hi : i < p.ops.length)
    (hci : p.ops.getD i .I = Pauli.I) (hca : p.ops.getD a .I = Pauli.Z) :
    (cnotConj i a p).ops.getD i .I = Pauli.Z := by
  by_cases hia : i = a
  · subst hia; simp only [hci] at hca; cases hca
  · simp only [cnotConj, hci, hca, toSym, ofSym, Bool.xor_false, Bool.false_xor]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simpa using hi)]
    rfl

/-- `CNOT(i → a)` leaves the ancilla reading `Z` when the control
    reads `I` (the control X part that would spread to the target
    is absent, so the ancilla's Z is untouched). -/
theorem cnot_anc (p : PauliString) (i a : Nat) (ha : a < p.ops.length)
    (hci : p.ops.getD i .I = Pauli.I) (hca : p.ops.getD a .I = Pauli.Z) :
    (cnotConj i a p).ops.getD a .I = Pauli.Z := by
  simp only [cnotConj, hci, hca, toSym, ofSym, Bool.xor_false, Bool.false_xor]
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_set_self (by simp [List.length_set]; omega)]
  rfl

/-- `CNOT(c → t)` leaves every position other than `c` and `t`
    untouched. -/
theorem cnot_other (p : PauliString) (c t j : Nat) (hjc : j ≠ c) (hjt : j ≠ t) :
    (cnotConj c t p).ops.getD j .I = p.ops.getD j .I := by
  simp only [cnotConj]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]

/-- `cnotConj` preserves the register length. -/
theorem cnot_len (p : PauliString) (c t : Nat) :
    (cnotConj c t p).ops.length = p.ops.length := by
  simp [cnotConj, List.length_set]

/-- `cnotConj` preserves the global phase (Z-type / sign-free). -/
theorem cnot_phase (p : PauliString) (c t : Nat) :
    (cnotConj c t p).phase = p.phase := by
  simp [cnotConj]

/-! ## The parametric gadget characterization

    Below, the gadget is run on a *canonical* Z-type input: every
    data position reads `I` and the ancilla `a` reads `Z`.  Under
    the natural hypotheses — `a` not in the support, the support
    `Nodup` (one CNOT per data qubit), and all indices in range —
    we prove the full per-position characterization of the
    conjugated observable:

      * the ancilla stays `Z`             (`gadget_anc`),
      * every support qubit becomes `Z`   (`gadget_ctrl`),
      * everything else is untouched      (`gadget_untouched`).

    Together (`measGadget_characterization`) this says the
    conjugated `Z_a` is exactly `(∏_{i∈supp} Z_i) · Z_a`, i.e. the
    gate circuit measures the Z-type stabilizer on the support. -/

/-- The gadget preserves the register length. -/
theorem gadget_len (supp : List Nat) (a : Nat) (p : PauliString) :
    (measGadgetConj supp a p).ops.length = p.ops.length := by
  unfold measGadgetConj
  induction supp generalizing p with
  | nil => rfl
  | cons i rest ih => simp only [List.foldl_cons]; rw [ih]; exact cnot_len p i a

/-- The gadget preserves the global phase (everything is Z-type, so
    no `±i` factor ever arises). -/
theorem gadget_phase (supp : List Nat) (a : Nat) (p : PauliString) :
    (measGadgetConj supp a p).phase = p.phase := by
  unfold measGadgetConj
  induction supp generalizing p with
  | nil => rfl
  | cons i rest ih => simp only [List.foldl_cons]; rw [ih]; exact cnot_phase p i a

/-- Positions outside the support and `≠ a` are untouched by the
    whole gadget. -/
theorem gadget_untouched (supp : List Nat) (a : Nat) (j : Nat) (hja : j ≠ a) :
    ∀ (p : PauliString), j ∉ supp →
      (measGadgetConj supp a p).ops.getD j .I = p.ops.getD j .I := by
  unfold measGadgetConj
  induction supp with
  | nil => intro p _; rfl
  | cons i rest ih =>
    intro p hjs
    simp only [List.foldl_cons]
    have hji : j ≠ i := fun h => hjs (h ▸ List.mem_cons_self ..)
    rw [ih (cnotConj i a p) (fun h => hjs (List.mem_cons_of_mem _ h))]
    exact cnot_other p i a j hji hja

/-- The ancilla observable stays `Z` through the whole gadget. -/
theorem gadget_anc (supp : List Nat) (a : Nat) :
    ∀ (p : PauliString), a < p.ops.length → a ∉ supp → supp.Nodup →
      p.ops.getD a .I = Pauli.Z → (∀ i ∈ supp, p.ops.getD i .I = Pauli.I) →
      (measGadgetConj supp a p).ops.getD a .I = Pauli.Z := by
  unfold measGadgetConj
  induction supp with
  | nil => intro p _ _ _ hca _; simpa using hca
  | cons i rest ih =>
    intro p ha hanc hnd hca hctrl
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    have hia : i ≠ a := fun h => hanc (h ▸ List.mem_cons_self ..)
    have hci : p.ops.getD i .I = Pauli.I := hctrl i (List.mem_cons_self ..)
    apply ih (cnotConj i a p)
    · rw [cnot_len]; exact ha
    · exact fun h => hanc (List.mem_cons_of_mem _ h)
    · exact hnd.2
    · exact cnot_anc p i a ha hci hca
    · intro j hj
      have hji : j ≠ i := fun h => hnd.1 (h ▸ hj)
      have hja : j ≠ a := fun h => hanc (h ▸ List.mem_cons_of_mem _ hj)
      rw [cnot_other p i a j hji hja]
      exact hctrl j (List.mem_cons_of_mem _ hj)

/-- Every support qubit `k ∈ supp` ends up reading `Z`. -/
theorem gadget_ctrl (supp : List Nat) (a : Nat) :
    ∀ (p : PauliString), a < p.ops.length → a ∉ supp → supp.Nodup →
      p.ops.getD a .I = Pauli.Z → (∀ i ∈ supp, i < p.ops.length) →
      (∀ i ∈ supp, p.ops.getD i .I = Pauli.I) →
      ∀ k ∈ supp, (measGadgetConj supp a p).ops.getD k .I = Pauli.Z := by
  unfold measGadgetConj
  induction supp with
  | nil => intro p _ _ _ _ _ _ k hk; cases hk
  | cons i rest ih =>
    intro p ha hanc hnd hca hrange hctrl
    simp only [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    have hia : i ≠ a := fun h => hanc (h ▸ List.mem_cons_self ..)
    have hci : p.ops.getD i .I = Pauli.I := hctrl i (List.mem_cons_self ..)
    have hir : i < p.ops.length := hrange i (List.mem_cons_self ..)
    have hci' : (cnotConj i a p).ops.getD i .I = Pauli.Z := cnot_ctrl p i a hir hci hca
    have hca' : (cnotConj i a p).ops.getD a .I = Pauli.Z := cnot_anc p i a ha hci hca
    intro k hk
    rcases List.mem_cons.mp hk with hk | hk
    · subst hk
      rw [show rest.foldl (fun q j => cnotConj j a q) (cnotConj k a p)
            = measGadgetConj rest a (cnotConj k a p) from rfl]
      rw [gadget_untouched rest a k hia (cnotConj k a p) hnd.1]
      exact hci'
    · apply ih (cnotConj i a p)
      · rw [cnot_len]; exact ha
      · exact fun h => hanc (List.mem_cons_of_mem _ h)
      · exact hnd.2
      · exact hca'
      · intro j hj; rw [cnot_len]; exact hrange j (List.mem_cons_of_mem _ hj)
      · intro j hj
        have hji : j ≠ i := fun h => hnd.1 (h ▸ hj)
        have hja : j ≠ a := fun h => hanc (h ▸ List.mem_cons_of_mem _ hj)
        rw [cnot_other p i a j hji hja]
        exact hctrl j (List.mem_cons_of_mem _ hj)
      · exact hk

/-- **Parametric gate-level gadget theorem.**  Running the
    ancilla+CNOT(data_i→a for i∈supp)+measure-Zₐ circuit and
    conjugating the measured `Z_a` back through it yields, on the
    canonical Z-type input, an observable that reads `Z` on every
    support qubit and on the ancilla, and is untouched elsewhere.

    Concretely, for any `j`:
      * if `j = a` or `j ∈ supp`, the conjugated observable reads `Z`;
      * otherwise it equals the input's reading at `j`.

    This is the general statement instantiated by the concrete
    `measGadget_measures_Z0Z1` / `..._Z0Z1Z2` `decide` theorems
    above: the gate circuit measures exactly the Z-type stabilizer
    `∏_{i∈supp} Z_i` on the data register. -/
theorem measGadget_characterization
    (supp : List Nat) (a : Nat) (p : PauliString)
    (ha : a < p.ops.length) (hanc : a ∉ supp) (hnd : supp.Nodup)
    (hca : p.ops.getD a .I = Pauli.Z)
    (hrange : ∀ i ∈ supp, i < p.ops.length)
    (hctrl : ∀ i ∈ supp, p.ops.getD i .I = Pauli.I) :
    (∀ k ∈ supp, (measGadgetConj supp a p).ops.getD k .I = Pauli.Z)
    ∧ (measGadgetConj supp a p).ops.getD a .I = Pauli.Z
    ∧ (∀ j, j ≠ a → j ∉ supp →
        (measGadgetConj supp a p).ops.getD j .I = p.ops.getD j .I) := by
  refine ⟨gadget_ctrl supp a p ha hanc hnd hca hrange hctrl,
          gadget_anc supp a p ha hanc hnd hca hctrl, ?_⟩
  intro j hja hjs
  exact gadget_untouched supp a j hja p hjs

-- Axiom audit: the headline gate-level gadget theorem depends only
-- on Lean's core axioms (`propext`; no `sorry`, no project `axiom`).
#print axioms measGadget_measures_Z0Z1

end FormalRV.Framework.CliffordConj
