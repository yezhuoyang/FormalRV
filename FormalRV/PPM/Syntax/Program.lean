/-
  FormalRV.PPM.Syntax.Program
  ───────────────────────────
  THE PPM program syntax (John's notation, 2026-06-10):

      c2 = Measure X[0]Z[1]X[3]              -- outcome-binding measurement
      if c2 == 1 then X[0]Z[2] else skip      -- explicit Pauli-frame correction
      frame Z[4]                              -- unconditional frame update
      useT / useCCZ                           -- magic-state consumption

  A PPM program is a SYNTAX TREE: a list of statements over sparse Pauli
  products (`X[0]Z[1]X[3]` = the Pauli with X on qubit 0, Z on qubit 1, X on
  qubit 3, identity elsewhere — identity factors are unrepresentable by
  construction).  Measurements bind their ±1 outcome to classical slots
  `c0, c1, …` in program order; corrections fire on the XOR-parity of bound
  slots (covering both single-outcome `if c2 == 1` and the multi-outcome
  parity corrections lattice surgery needs).

  This file is the LEAF IR: **zero imports**, pure `Nat`/`List`/`Bool` data —
  the honest-resource discipline requires the `Resource/` counters to walk
  exactly this tree, so it must not depend on any semantics, compiler, or
  gadget builder.  (Human-readable `ppm! { … }` notation: `Notation.lean`;
  semantics: `PPM/Semantics/ProgramSemantics.lean`, Phase C; the
  `Gate → PPMProg` compiler: Phase D.)
-/

namespace FormalRV.PPM.Prog

/-! ## §1. Sparse Pauli products. -/

/-- A non-identity single-qubit Pauli kind (sparse products never mention `I`). -/
inductive PKind where
  | x | y | z
  deriving Repr, DecidableEq

/-- One factor of a sparse Pauli product: `X[3]` = `⟨3, .x⟩`. -/
structure PFactor where
  qubit : Nat
  kind  : PKind
  deriving Repr, DecidableEq

/-- A sparse logical Pauli product, e.g. `X[0]Z[1]X[3]`.  Implicit identity on
unmentioned qubits.  Well-formed products list qubits in strictly increasing
order (`sortedStrict`), so each product has a unique representation. -/
abbrev PauliProduct := List PFactor

/-- Strictly-increasing qubit indices (canonical sparse representation). -/
def sortedStrict : PauliProduct → Bool
  | []           => true
  | [_]          => true
  | a :: b :: t  => decide (a.qubit < b.qubit) && sortedStrict (b :: t)

/-- SPACE of a product: the largest qubit index it touches, plus one. -/
def PauliProduct.width : PauliProduct → Nat
  | []      => 0
  | f :: t  => max (f.qubit + 1) (PauliProduct.width t)

/-! ## §2. Statements and programs. -/

/-- A classical outcome slot (`c0, c1, …`): the index of the measurement whose
±1 outcome it holds (numbered in program order). -/
abbrev CVar := Nat


/-- One PPM statement. -/
inductive PPMStmt where
  /-- `c<dst> = Measure P` — measure the Pauli product `P`, binding the ±1
  outcome to classical slot `dst` (well-formedness forces `dst` to be the
  next unbound slot). -/
  | measure (dst : CVar) (P : PauliProduct)
  /-- `c<dst> = MeasureIf (c_{i₁} ^^ … ^^ c_{iₖ}) then P₁ else P₀` —
  SELECTIVE-DESTRUCTION measurement (Litinski): measure `P₁` if the
  XOR-parity of the listed outcomes is `1`, else `P₀`, binding the ±1
  outcome to slot `dst`.  The branch products are MEASUREMENT AXES — the
  selected projector acts on the state immediately; Pauli corrections stay
  exclusively in `correct`.  This is the ONE adaptive primitive the π/8
  teleport block requires (its two first-outcome branches need corrections
  differing by a π/4 rotation, which no outcome-affine Pauli frame can
  express). -/
  | measureSel (sel : List CVar) (dst : CVar) (Pthen Pels : PauliProduct)
  /-- `c<dst> = MeasureSel2 (par₁; par₂) P00 P01 P10 P11` — FOUR-WAY
  selective destruction: the measured axis is selected by TWO outcome
  parities (`P_{s₁s₂}` for selector values `(s₁, s₂)`).  This is the
  twisted-basis primitive the CCZ-state teleport block requires: each
  resource-ancilla destruction basis is the plain `X` twisted by `Z`s on
  the other two ancillas according to two first-round outcomes (the
  conditional-CZ corrections absorbed as CZ-conjugated bases). -/
  | measureSel2 (sel1 sel2 : List CVar) (dst : CVar)
      (P00 P01 P10 P11 : PauliProduct)
  /-- `frame P` — unconditional Pauli-frame update by `P`. -/
  | frame (P : PauliProduct)
  /-- `if c_{i₁} ^^ … ^^ c_{iₖ} == 1 then thn else els` — conditional
  Pauli-frame correction on the XOR-parity of the listed outcomes
  (`els = []` renders as `skip`). -/
  | correct (parity : List CVar) (thn els : PauliProduct)
  /-- `if Σ⊕ (c_{i₁}·…·c_{iₖ}) == 1 then thn else els` — conditional
  Pauli-frame correction on an XOR of AND-MONOMIALS of outcomes
  (singleton monomials recover `correct`).  Degree-2 monomials are
  REQUIRED by degree-3 phase-gate injection: the CCZ-block's residual
  Pauli fires on `b_i ^^ (m_j ∧ m_k)`, and no outcome-affine (XOR-only)
  frame can express it — classical AND logic in the decoder is intrinsic
  to CCZ teleportation. -/
  | correctQ (mons : List (List CVar)) (thn els : PauliProduct)
  /-- `useT[q]` — inject (consume) one T magic state on logical qubit `q`. -/
  | useT (q : Nat)
  /-- `useCCZ[a,b,c]` — inject one CCZ magic state on logical qubits `a,b,c`. -/
  | useCCZ (a b c : Nat)
  deriving Repr, DecidableEq

/-- A PPM program: a list of statements, executed in order. -/
abbrev PPMProg := List PPMStmt

/-! ## §3. Well-formedness (decidable). -/

/-- How many classical slots a statement binds. -/
def PPMStmt.binds : PPMStmt → Nat
  | .measure ..     => 1
  | .measureSel ..  => 1
  | .measureSel2 .. => 1
  | _               => 0

/-- Statement well-formedness given `bound` already-bound slots: a measurement
binds exactly the next slot over a canonical nonempty product; corrections
reference only bound slots and have a nonempty then-branch. -/
def PPMStmt.wfAt (bound : Nat) : PPMStmt → Bool
  | .measure dst P       => decide (dst = bound) && sortedStrict P && !P.isEmpty
  | .measureSel sel dst Pt Pe =>
      decide (dst = bound) && !sel.isEmpty
        && sel.all (fun c => decide (c < bound))
        && sortedStrict Pt && !Pt.isEmpty && sortedStrict Pe && !Pe.isEmpty
  | .measureSel2 sel1 sel2 dst P00 P01 P10 P11 =>
      decide (dst = bound) && !sel1.isEmpty && !sel2.isEmpty
        && sel1.all (fun c => decide (c < bound))
        && sel2.all (fun c => decide (c < bound))
        && sortedStrict P00 && !P00.isEmpty
        && sortedStrict P01 && !P01.isEmpty
        && sortedStrict P10 && !P10.isEmpty
        && sortedStrict P11 && !P11.isEmpty
  | .frame P             => sortedStrict P && !P.isEmpty
  | .correct par thn els =>
      !par.isEmpty && par.all (fun c => decide (c < bound))
        && sortedStrict thn && !thn.isEmpty && sortedStrict els
  | .correctQ mons thn els =>
      !mons.isEmpty
        && mons.all (fun mon =>
            !mon.isEmpty && mon.all (fun c => decide (c < bound)))
        && sortedStrict thn && !thn.isEmpty && sortedStrict els
  | .useT _              => true
  | .useCCZ a b c        => decide (a ≠ b) && decide (a ≠ c) && decide (b ≠ c)

/-- Program well-formedness from a starting slot count. -/
def PPMProg.wfFrom : Nat → PPMProg → Bool
  | _,     []     => true
  | bound, s :: p => s.wfAt bound && PPMProg.wfFrom (bound + s.binds) p

/-- **Program well-formedness**: slots bind sequentially from `c0`, every
correction references only already-bound outcomes, every product is canonical. -/
def PPMProg.wf (p : PPMProg) : Bool := PPMProg.wfFrom 0 p

/-! ## §4. Space dimensions of a program (the honest SPACE readouts). -/

/-- Quantum width of a statement. -/
def PPMStmt.width : PPMStmt → Nat
  | .measure _ P       => P.width
  | .measureSel _ _ Pt Pe => max Pt.width Pe.width
  | .measureSel2 _ _ _ P00 P01 P10 P11 =>
      max (max P00.width P01.width) (max P10.width P11.width)
  | .frame P           => P.width
  | .correct _ thn els => max thn.width els.width
  | .correctQ _ thn els => max thn.width els.width
  | .useT q            => q + 1
  | .useCCZ a b c      => max (a + 1) (max (b + 1) (c + 1))

/-- **Quantum width** of a program: the number of qubits it touches. -/
def PPMProg.width : PPMProg → Nat
  | []     => 0
  | s :: p => max s.width (PPMProg.width p)

/-- **Classical width** of a program: the number of outcome slots it binds. -/
def PPMProg.cwidth : PPMProg → Nat
  | []     => 0
  | s :: p => s.binds + PPMProg.cwidth p

/-! ## §5. Structural laws. -/

theorem PPMProg.wfFrom_append (b : Nat) (p q : PPMProg) :
    PPMProg.wfFrom b (p ++ q)
      = (PPMProg.wfFrom b p && PPMProg.wfFrom (b + PPMProg.cwidth p) q) := by
  induction p generalizing b with
  | nil => simp [PPMProg.wfFrom, PPMProg.cwidth]
  | cons s t ih =>
      show (s.wfAt b && PPMProg.wfFrom (b + s.binds) (t ++ q)) = _
      rw [ih]
      show (s.wfAt b && (PPMProg.wfFrom (b + s.binds) t
              && PPMProg.wfFrom (b + s.binds + PPMProg.cwidth t) q)) = _
      have h : b + s.binds + PPMProg.cwidth t
          = b + PPMProg.cwidth (s :: t) := by
        show _ = b + (s.binds + PPMProg.cwidth t); omega
      rw [h, ← Bool.and_assoc]
      rfl

theorem PPMProg.width_append (p q : PPMProg) :
    PPMProg.width (p ++ q) = max (PPMProg.width p) (PPMProg.width q) := by
  induction p with
  | nil => simp [PPMProg.width]
  | cons s t ih =>
      show max s.width (PPMProg.width (t ++ q)) = _
      rw [ih]
      show max s.width (max (PPMProg.width t) (PPMProg.width q))
          = max (max s.width (PPMProg.width t)) (PPMProg.width q)
      omega

theorem PPMProg.cwidth_append (p q : PPMProg) :
    PPMProg.cwidth (p ++ q) = PPMProg.cwidth p + PPMProg.cwidth q := by
  induction p with
  | nil => simp [PPMProg.cwidth]
  | cons s t ih =>
      show s.binds + PPMProg.cwidth (t ++ q) = _
      rw [ih]
      show s.binds + (PPMProg.cwidth t + PPMProg.cwidth q)
          = s.binds + PPMProg.cwidth t + PPMProg.cwidth q
      omega

/-! ## §6. Smoke checks. -/

example : sortedStrict [⟨0, .x⟩, ⟨1, .z⟩, ⟨3, .x⟩] = true := by decide
example : sortedStrict [⟨1, .x⟩, ⟨1, .z⟩] = false := by decide
example :
    PPMProg.wf [.measure 0 [⟨0, .z⟩, ⟨1, .z⟩],
                .correct [0] [⟨1, .x⟩] []] = true := by decide
example :  -- forward reference to an unbound outcome is rejected
    PPMProg.wf [.correct [0] [⟨1, .x⟩] []] = false := by decide
example :  -- slots must bind sequentially
    PPMProg.wf [.measure 1 [⟨0, .z⟩]] = false := by decide
example :
    PPMProg.width [.measure 0 [⟨0, .x⟩, ⟨3, .x⟩], .frame [⟨5, .z⟩]] = 6 := by decide
example :
    PPMProg.cwidth [.measure 0 [⟨0, .x⟩], .useT 1,
                    .measure 1 [⟨1, .z⟩]] = 2 := by decide
example :  -- magic injection counts toward quantum width
    PPMProg.width [.useT 4] = 5 := by decide
example :  -- CCZ injection requires three distinct qubits
    PPMProg.wf [.useCCZ 0 0 2] = false := by decide

end FormalRV.PPM.Prog
