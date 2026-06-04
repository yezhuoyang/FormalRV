/-
  FormalRV.QEC.CSSCode — the unified CSS-code pivot type, and the
  level's SEMANTIC-CORRECTNESS theorem:
  **the stabilizer-measurement circuit implements the specified code.**

  Design: `notes/topic-qec-code-framework.md`.  The pivot representation
  is the GF(2) check-matrix pair `(hx, hz)` (`BoolMat`), reusing the
  `FormalRV.Framework.LDPC` toolbox + `GF2Linear`.  A code can be built
  in three "languages" (algebraic / check-matrix / stabilizer); they all
  lower to this `(hx, hz)` pair.

  ## The semantic-correctness goal of this level

  A CSS code is *specified* by its check matrices.  Its stabilizer-
  measurement circuit measures, for each row, the Pauli operator obtained
  by lowering that row (X-rows ↦ X/I strings via `xStab`, Z-rows ↦ Z/I
  strings via `zStab`).  "This circuit implements the specified code"
  means exactly: those measured operators form a *valid stabilizer code*
  (a pairwise-commuting generating set) and they ARE the code's
  stabilizers.  The headline theorem `syndrome_circuit_implements_code`
  proves this holds IFF the CSS commutation condition `H_X H_Z^T = 0`:

      valid (toStabilizers c) c.n  ↔  c.css_condition

  i.e. the construction yields a genuine stabilizer code precisely when
  the CSS condition holds — the circuit implements the code.

  Note (layering / future unification): `xStab`/`zStab` here are the
  canonical check-matrix→Pauli lowering; the surgery layer's
  `SurgeryReadout.xRow` / `SurgeryCorrect.zRow` are definitionally the
  same and should later be re-pointed to import these (kept separate now
  to avoid a QEC→LatticeSurgery import inversion / touching committed
  files).

  No Mathlib.  Pure Bool / Nat / List.
-/

import FormalRV.QEC.GF2Linear
import FormalRV.PPM.PPMOperational
import FormalRV.PPM.PPMUpdateInvariants
import FormalRV.Framework.L4_QECCode

namespace FormalRV.QEC

open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.PPMUpdate

/-! ## The pivot type -/

/-- A CSS code as its GF(2) check-matrix pair.  Mirrors `bposd.css_code`.
    `hx`/`hz` are the X- and Z-stabilizer parity matrices, rows of length `n`. -/
structure CSSCode where
  n  : Nat
  hx : BoolMat
  hz : BoolMat
  deriving Inhabited, Repr

namespace CSSCode

/-- Every row of `hx` and `hz` has length `n`. -/
def well_shaped (c : CSSCode) : Bool :=
  matrix_has_n_cols c.hx c.n && matrix_has_n_cols c.hz c.n

/-- CSS commutation: `H_X · H_Z^T = 0` over GF(2). -/
def css_condition (c : CSSCode) : Bool := orthogonal c.hx c.hz

/-- All structural invariants of a CSS code. -/
def valid (c : CSSCode) : Bool := c.well_shaped && c.css_condition

/-- qLDPC degree bound on both check matrices. -/
def is_qldpc_code (c : CSSCode) (Δ : Nat) : Bool :=
  is_qldpc c.hx c.n Δ && is_qldpc c.hz c.n Δ

/-! ## Canonical check-matrix → Pauli-string lowering -/

/-- Lower an X-support bit to a single-qubit Pauli (`true ↦ X`). -/
@[inline] def xbit (b : Bool) : Pauli := if b then Pauli.X else Pauli.I
/-- Lower a Z-support bit to a single-qubit Pauli (`true ↦ Z`). -/
@[inline] def zbit (b : Bool) : Pauli := if b then Pauli.Z else Pauli.I

/-- An X-type check row lowered to an X/I `PauliString`. -/
def xStab (l : BoolVec) : PauliString := ⟨Phase.plus, l.map xbit⟩
/-- A Z-type check row lowered to a Z/I `PauliString`. -/
def zStab (l : BoolVec) : PauliString := ⟨Phase.plus, l.map zbit⟩

@[simp] theorem xStab_ops (l : BoolVec) : (xStab l).ops = l.map xbit := rfl
@[simp] theorem zStab_ops (l : BoolVec) : (zStab l).ops = l.map zbit := rfl

/-- **The stabilizer-measurement circuit of the code**: the X-checks
    lowered via `xStab`, then the Z-checks via `zStab`.  This is the
    sequence of Pauli measurements that the syndrome-extraction circuit
    performs (each ancilla+CNOT+measure gadget realises one of these). -/
def toStabilizers (c : CSSCode) : StabilizerState :=
  c.hx.map xStab ++ c.hz.map zStab

/-! ## Adapter to the flat resource container `Framework.QECCode` -/

/-- Project to the flat L4 resource container.  `k` and `d` are supplied
    separately (distance is NOT derived — honest residue; `k` derivation
    needs GF(2) rank, a later module). -/
def toQECCode (c : CSSCode) (k d : Nat) : Framework.QECCode :=
  { n := c.n, k := k, d := d, hx := c.hx, hz := c.hz }

@[simp] theorem toQECCode_hx (c : CSSCode) (k d : Nat) : (c.toQECCode k d).hx = c.hx := rfl
@[simp] theorem toQECCode_hz (c : CSSCode) (k d : Nat) : (c.toQECCode k d).hz = c.hz := rfl
@[simp] theorem toQECCode_n  (c : CSSCode) (k d : Nat) : (c.toQECCode k d).n  = c.n  := rfl

/-- Smart constructor from a `QECCode` carrying matrices, checking the CSS
    invariants. -/
def ofQECCodeChecked (q : Framework.QECCode) : Option CSSCode :=
  let c : CSSCode := { n := q.n, hx := q.hx, hz := q.hz }
  if c.valid then some c else none

/-! ## Commutation lemmas for the lowered stabilizers -/

/-- Single-qubit X/I operators always commute. -/
theorem xbit_commutes (x y : Bool) : Pauli.commutes (xbit x) (xbit y) = true := by
  cases x <;> cases y <;> rfl

/-- Single-qubit Z/I operators always commute. -/
theorem zbit_commutes (x y : Bool) : Pauli.commutes (zbit x) (zbit y) = true := by
  cases x <;> cases y <;> rfl

/-- Any two X/I strings commute. -/
theorem xStab_commutes (a b : BoolVec) : (xStab a).commutes (xStab b) = true := by
  simp only [PauliString.commutes, xStab_ops]
  rw [Nat.beq_eq_true_eq]
  have hzero : ((a.map xbit).zip (b.map xbit)).countP
      (fun p => ! (Pauli.commutes p.1 p.2)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    have h1 : p.1 ∈ a.map xbit := List.of_mem_zip hp |>.1
    have h2 : p.2 ∈ b.map xbit := List.of_mem_zip hp |>.2
    obtain ⟨x, _, hx⟩ := List.mem_map.mp h1
    obtain ⟨y, _, hy⟩ := List.mem_map.mp h2
    rw [← hx, ← hy, xbit_commutes]
    decide
  rw [hzero]

/-- Any two Z/I strings commute. -/
theorem zStab_commutes (a b : BoolVec) : (zStab a).commutes (zStab b) = true := by
  simp only [PauliString.commutes, zStab_ops]
  rw [Nat.beq_eq_true_eq]
  have hzero : ((a.map zbit).zip (b.map zbit)).countP
      (fun p => ! (Pauli.commutes p.1 p.2)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    have h1 : p.1 ∈ a.map zbit := List.of_mem_zip hp |>.1
    have h2 : p.2 ∈ b.map zbit := List.of_mem_zip hp |>.2
    obtain ⟨x, _, hx⟩ := List.mem_map.mp h1
    obtain ⟨y, _, hy⟩ := List.mem_map.mp h2
    rw [← hx, ← hy, zbit_commutes]
    decide
  rw [hzero]

/-- At each position the X-vs-Z anticommutation indicator equals the GF(2)
    overlap bit, so the symplectic anticommuting-position count over the
    lowered strings equals the overlap count over the raw supports. -/
theorem xz_anti_count (a b : BoolVec) :
    ((a.map xbit).zip (b.map zbit)).countP (fun p => ! p.1.commutes p.2)
      = (a.zip b).countP (fun p => p.1 && p.2) := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons, List.zip_cons_cons, List.countP_cons]
      rw [ih]
      have hhead : (! (xbit x).commutes (zbit y)) = (x && y) := by
        cases x <;> cases y <;> rfl
      rw [hhead]

/-- An X-row stabilizer commutes with a Z-row stabilizer IFF their supports
    are GF(2)-orthogonal (even overlap) — the symplectic pairing equals the
    GF(2) inner product `dotBit`. -/
theorem xStab_zStab_commutes (a b : BoolVec) :
    (xStab a).commutes (zStab b) = ! dotBit a b := by
  simp only [PauliString.commutes, xStab_ops, zStab_ops, dotBit]
  rw [xz_anti_count]
  generalize (a.zip b).countP (fun p => p.1 && p.2) = m
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> decide

/-! ## SEMANTIC CORRECTNESS: the circuit implements the code -/

/-- **The stabilizer-measurement circuit implements the specified code.**
    For a well-shaped CSS code, the lowered measured operators
    `toStabilizers c` form a valid (pairwise-commuting) stabilizer code IFF
    the CSS commutation condition `H_X · H_Z^T = 0` holds.  Equivalently:
    the syndrome-extraction circuit realises a genuine stabilizer code
    exactly when the specified check matrices are a valid CSS code, and the
    measured stabilizer group is exactly `{xStab(hxᵢ)} ∪ {zStab(hzⱼ)}`. -/
theorem syndrome_circuit_implements_code (c : CSSCode) (hws : c.well_shaped = true) :
    StabilizerState.valid (c.toStabilizers) c.n = true ↔ c.css_condition = true := by
  -- Row-length facts extracted from well-shapedness.
  rw [well_shaped, Bool.and_eq_true, matrix_has_n_cols, matrix_has_n_cols,
      List.all_eq_true, List.all_eq_true] at hws
  obtain ⟨hwx, hwz⟩ := hws
  have hxlen : ∀ row ∈ c.hx, row.length = c.n := by
    intro row hr; have := hwx row hr; simpa using this
  have hzlen : ∀ row ∈ c.hz, row.length = c.n := by
    intro row hr; have := hwz row hr; simpa using this
  -- Length validity always holds for a well-shaped code.
  have hlen : StabilizerState.valid_length (c.toStabilizers) c.n = true := by
    rw [StabilizerState.valid_length, List.all_eq_true]
    intro g hg
    rw [toStabilizers, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨row, hrow, hgr⟩ := List.mem_map.mp hg
      subst hgr
      simp only [decide_eq_true_eq, xStab_ops, List.length_map]
      exact hxlen row hrow
    · obtain ⟨row, hrow, hgr⟩ := List.mem_map.mp hg
      subst hgr
      simp only [decide_eq_true_eq, zStab_ops, List.length_map]
      exact hzlen row hrow
  -- Commutation validity holds IFF the CSS condition holds.
  have hcomm : StabilizerState.valid_commuting (c.toStabilizers) = true
      ↔ c.css_condition = true := by
    rw [StabilizerState.valid_commuting, List.all_eq_true]
    constructor
    · -- valid_commuting → css_condition
      intro h
      rw [css_condition, orthogonal_iff]
      intro ra hra rb hrb
      have hg1 : xStab ra ∈ c.toStabilizers := by
        rw [toStabilizers, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨ra, hra, rfl⟩)
      have hg2 : zStab rb ∈ c.toStabilizers := by
        rw [toStabilizers, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨rb, hrb, rfl⟩)
      have hc := h (xStab ra) hg1
      rw [List.all_eq_true] at hc
      have := hc (zStab rb) hg2
      rw [xStab_zStab_commutes] at this
      cases hd : dotBit ra rb with
      | false => rfl
      | true => rw [hd] at this; simp at this
    · -- css_condition → valid_commuting
      intro h
      rw [css_condition, orthogonal_iff] at h
      intro g1 hg1
      rw [List.all_eq_true]
      intro g2 hg2
      rw [toStabilizers, List.mem_append] at hg1 hg2
      rcases hg1 with hg1 | hg1 <;> rcases hg2 with hg2 | hg2
      · -- (xs, xs)
        obtain ⟨a, _, ha⟩ := List.mem_map.mp hg1
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hg2
        subst ha hb; exact xStab_commutes a b
      · -- (xs, zs)
        obtain ⟨a, ha, hga⟩ := List.mem_map.mp hg1
        obtain ⟨b, hb, hgb⟩ := List.mem_map.mp hg2
        subst hga hgb
        rw [xStab_zStab_commutes, h a ha b hb]; rfl
      · -- (zs, xs)
        obtain ⟨a, ha, hga⟩ := List.mem_map.mp hg1
        obtain ⟨b, hb, hgb⟩ := List.mem_map.mp hg2
        subst hga hgb
        rw [commutes_symm (zStab a) (xStab b)
              (by rw [zStab_ops, xStab_ops, List.length_map, List.length_map,
                      hzlen a ha, hxlen b hb])]
        rw [xStab_zStab_commutes, h b hb a ha]; rfl
      · -- (zs, zs)
        obtain ⟨a, _, ha⟩ := List.mem_map.mp hg1
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hg2
        subst ha hb; exact zStab_commutes a b
  -- Combine: valid = valid_length && valid_commuting, length always true.
  rw [StabilizerState.valid, hlen, Bool.true_and]
  exact hcomm

end CSSCode
end FormalRV.QEC
