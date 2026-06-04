/-
  FormalRV.QEC.LogicalValidity — the NON-TRIVIALITY / independence layer
  that closes the one RESIDUE flagged in `Logical.lean`.

  `LogicalBasis.valid` (in `Logical.lean`) checks that a declared logical
  basis COMMUTES with every stabilizer and realises the symplectic δ_ij
  pairing.  But commuting with the stabilizers is necessary, NOT sufficient,
  for being a genuine logical operator: a stabilizer itself commutes with
  every stabilizer.  A genuine logical lies in N(S)\S — it must ALSO lie
  OUTSIDE the stabilizer group, i.e. it is not a product of stabilizers.

  This file adds that GF(2)-rank condition using `GF2Rank.inRowspace` /
  `GF2Rank.rank`:

    * `outsideStabZ` / `outsideStabX` — every declared logical is NOT in the
      rowspace of the corresponding check matrix (not a product of checks).
    * `independentModStabZ` / `independentModStabX` — the `k` logical
      supports raise the stabilizer rank by exactly `k` (they are mutually
      independent modulo the stabilizers).
    * `is_logical_basis` — the COMPLETE N(S)\S condition: `valid` ∧ outside ∧
      independent.

  DISCRIMINATING DEMO: a declared "logical Z" that is actually a row of `hz`
  (a stabilizer) passes `valid` (it commutes with everything) but is
  correctly REJECTED by `outsideStabZ` / `is_logical_basis`.

  All verification here is `decide` at the worked Steane instance.
  No Mathlib.  Pure Bool / Nat / List + `decide`.
-/

import FormalRV.QEC.GF2Rank
import FormalRV.QEC.Logical

namespace FormalRV.QEC

open FormalRV.Framework.LDPC

namespace LogicalBasis

/-! ## Outside-the-stabilizer-group conditions -/

/-- Every Z̄_i is OUTSIDE the Z-stabilizer group: `lz i` is not in the GF(2)
    rowspace of `hz` (not a product of Z-checks). -/
def outsideStabZ {c k} (L : LogicalBasis c k) : Bool :=
  (List.finRange k).all (fun i => ! inRowspace c.hz (L.lz i))

/-- Every X̄_j is OUTSIDE the X-stabilizer group: `lx j` is not in the GF(2)
    rowspace of `hx` (not a product of X-checks). -/
def outsideStabX {c k} (L : LogicalBasis c k) : Bool :=
  (List.finRange k).all (fun j => ! inRowspace c.hx (L.lx j))

/-! ## Independence-modulo-stabilizers conditions -/

/-- The `k` logical-Z supports raise the Z-stabilizer rank by exactly `k`:
    they are mutually independent modulo the stabilizers (a basis-level
    strengthening of `outsideStabZ`). -/
def independentModStabZ {c k} (L : LogicalBasis c k) : Bool :=
  decide (rank (c.hz ++ (List.finRange k).map L.lz) = rank c.hz + k)

/-- The `k` logical-X supports raise the X-stabilizer rank by exactly `k`. -/
def independentModStabX {c k} (L : LogicalBasis c k) : Bool :=
  decide (rank (c.hx ++ (List.finRange k).map L.lx) = rank c.hx + k)

/-! ## The complete N(S)\S condition -/

/-- A GENUINE logical basis: `valid` (commute with all stabilizers + δ_ij
    symplectic pairing) AND every declared logical is OUTSIDE the stabilizer
    group AND the logicals are mutually independent modulo stabilizers.
    Together these are the complete `N(S)\S` membership condition — they
    rule out a "logical" that is secretly a stabilizer (commutes, but acts
    trivially on the code space). -/
def is_logical_basis {c k} (L : LogicalBasis c k) : Bool :=
  L.valid && L.outsideStabZ && L.outsideStabX && L.independentModStabZ && L.independentModStabX

end LogicalBasis

/-! ## POSITIVE demo: the all-ones Steane logical is genuine -/

/-- The all-ones Steane Z̄ is OUTSIDE the Z-stabilizer group (weight 7, odd —
    not in the even-weight Hamming rowspace). -/
theorem steaneLogical_outsideStabZ : steaneLogical.outsideStabZ = true := by decide

/-- The all-ones Steane X̄ is OUTSIDE the X-stabilizer group. -/
theorem steaneLogical_outsideStabX : steaneLogical.outsideStabX = true := by decide

/-- The single Steane Z̄ is independent modulo the Z-stabilizers: appending it
    raises the rank from 3 to 4. -/
theorem steaneLogical_independentModStabZ : steaneLogical.independentModStabZ = true := by decide

/-- The single Steane X̄ is independent modulo the X-stabilizers. -/
theorem steaneLogical_independentModStabX : steaneLogical.independentModStabX = true := by decide

/-- **HEADLINE (positive)**: the all-ones Steane logical basis is a GENUINE
    logical operator — it satisfies the complete N(S)\S condition. -/
theorem steaneLogical_is_logical_basis : steaneLogical.is_logical_basis = true := by decide

/-! ## NEGATIVE demo: a stabilizer is correctly REJECTED -/

/-- A FAKE logical basis whose declared "logical Z" is actually the FIRST ROW
    of the Steane `hz` — i.e. a genuine Z-STABILIZER, not a logical.  Its X̄ is
    kept as the real all-ones logical (so only the Z side is the trap). -/
def fakeLogical : LogicalBasis steaneCSS 1 :=
  { lx := steaneLogical.lx
    lz := fun _ => [false, false, false, true, true, true, true] }

/-- The fake "logical Z" still COMMUTES with every X-stabilizer (it IS a
    Z-check row, so it lies in the kernel of every X-check — even overlap).
    This is exactly the commutation test that is "already checked elsewhere":
    it is FOOLED by a stabilizer, returning `true`. -/
theorem fakeLogical_z_in_ker_hx : fakeLogical.z_in_ker_hx = true := by decide

/-- The full `valid` predicate happens to also reject THIS particular fake via
    its δ-pairing clause: a weight-4 Z-stabilizer cannot anticommute with the
    weight-7 all-ones X̄ (even overlap ⇒ they commute), so `pairs_delta` — and
    hence `valid` — is `false`.  The whole point of this file is that even
    WITHOUT relying on that δ accident, the GF(2)-rank layer independently
    rejects the fake (next theorem). -/
theorem fakeLogical_valid_false : fakeLogical.valid = false := by decide

/-- The discriminating rejection: the fake "logical Z" is a row of `hz`, hence
    INSIDE the stabilizer rowspace, so `outsideStabZ` correctly returns
    `false` — independently of the commutation/δ checks. -/
theorem fakeLogical_outsideStabZ_false : fakeLogical.outsideStabZ = false := by decide

/-- It is also NOT independent modulo the stabilizers (appending a stabilizer
    row does not raise the rank). -/
theorem fakeLogical_independentModStabZ_false :
    fakeLogical.independentModStabZ = false := by decide

/-- **HEADLINE (negative)**: a stabilizer masquerading as a logical is
    correctly REJECTED by the complete condition.  This is the discriminating
    test: `valid` alone (commute-with-stabilizers) is FOOLED, but
    `is_logical_basis` (which enforces N(S)\S via the GF(2)-rank layer) is
    NOT. -/
theorem fakeLogical_is_logical_basis_false :
    fakeLogical.is_logical_basis = false := by decide

end FormalRV.QEC
