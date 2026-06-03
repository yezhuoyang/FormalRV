/-
  FormalRV.QEC.LogicalFinder — DETERMINE the logical operators of a CSS code from its
  check matrices, DEFINING its logical qubits.

  John (2026-06-03): "the first thing we must solve is to determine all Logical Z of
  these codes, otherwise the logical qubits/index is not even defined and there is no
  way to compile [a PPM]."  Right — `LogicalBasis` was hand-filled; there was no
  algorithm to FIND the logicals.  This module adds the missing GF(2) NULLSPACE
  (`GF2Rank` had only rank / rowspace-membership) and the logical-operator finder:

      logical Z of a CSS code = ker(H_X) / rowspace(H_Z)   (k = n − rank H_X − rank H_Z)
      logical X of a CSS code = ker(H_Z) / rowspace(H_X)

  Each computed logical Z commutes with every X-check (in ker H_X) and is NOT a
  Z-stabilizer (outside rowspace H_Z) — a genuine element of N(S)\S.  The k logical Z
  operators ARE the k logical-qubit names: logical qubit `i` is the one measured by
  `logicalZ c |>.get i`.  General (any CSS code), `decide`-verified on a real
  bivariate-bicycle code (qianxu's LP family) at 18 qubits + Steane + [[4,2,2]].

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.GF2Rank
import FormalRV.QEC.Instances

namespace FormalRV.QEC.LogicalFinder

open FormalRV.Framework.LDPC
open FormalRV.QEC.Instances
open FormalRV.QEC.Algebraic

/-! ## §1. GF(2) reduced row echelon form + nullspace (kernel) -/

/-- Reduced row echelon form: echelon-reduce, then back-substitute each pivot against
    the others (clears bits above pivots), giving distinct pivot columns each set in
    exactly one row. -/
def rref (mat : BoolMat) : BoolMat :=
  let ech := rowReduce mat
  ech.map (fun p => reduceVec (ech.filter (· != p)) p)

/-- A basis of the GF(2) KERNEL of `mat` over `n` columns: one null vector per FREE
    (non-pivot) column.  `kernelBasis` has dimension `n − rank mat`. -/
def kernelBasis (mat : BoolMat) (n : Nat) : List BoolVec :=
  let R := rref mat
  let pivots := R.filterMap leadIdx
  ((List.range n).filter (fun c => ! pivots.contains c)).map (fun c =>
    (List.range n).map (fun i =>
      if i = c then true
      else if pivots.contains i then
        (match R.find? (fun r => leadIdx r == some i) with | some r => r.getD c false | none => false)
      else false))

/-- GF(2) inner product (parity of the overlap). -/
def gf2dot (u v : BoolVec) : Bool := ((u.zip v).filter (fun p => p.1 && p.2)).length % 2 == 1

/-! ## §2. The logical-operator finder -/

/-- Logical operators: a basis of `ker(stab)` reduced MODULO `rowspace(coStab)` — the
    `k` generators of N(S)\S in this sector. -/
def logicalBasis (stab coStab : BoolMat) (n : Nat) : List BoolVec :=
  (kernelBasis stab n).foldl (fun taken v =>
    if (reduceVec (rowReduce (coStab ++ taken)) v).any id then taken ++ [v] else taken) []

/-- The logical Z operators of a CSS code = ker(H_X) / rowspace(H_Z).  These DEFINE
    the logical qubits: logical qubit `i` is named by `(logicalZ c).get i`. -/
def logicalZ (c : FormalRV.QEC.CSSCode) : List BoolVec := logicalBasis c.hx c.hz c.n

/-- The logical X operators of a CSS code = ker(H_Z) / rowspace(H_X). -/
def logicalX (c : FormalRV.QEC.CSSCode) : List BoolVec := logicalBasis c.hz c.hx c.n

/-- The number of logical qubits, DERIVED as the count of logical Z operators found. -/
def numLogicals (c : FormalRV.QEC.CSSCode) : Nat := (logicalZ c).length

/-- Every computed logical Z is GENUINE: it commutes with all X-checks (in ker H_X)
    and is not a Z-stabilizer (outside rowspace H_Z). -/
def logicalZ_genuine (c : FormalRV.QEC.CSSCode) : Bool :=
  (logicalZ c).all (fun v => c.hx.all (fun r => ! gf2dot r v) && ! inRowspace c.hz v)

/-- Every computed logical X is genuine (in ker H_Z, outside rowspace H_X). -/
def logicalX_genuine (c : FormalRV.QEC.CSSCode) : Bool :=
  (logicalX c).all (fun v => c.hz.all (fun r => ! gf2dot r v) && ! inRowspace c.hx v)

/-! ## §3. A real bivariate-bicycle (qianxu LP-family) code: its logical qubits DEFINED -/

/-- A small bivariate-bicycle code `[[18, 2, d]]` (qianxu's LP family, l=m=3): genuine
    BB structure, k=2 (high-rate), `decide`-tractable. -/
def bbSmall : FormalRV.QEC.CSSCode := bivariateBicycle 3 3 [(1,0),(0,1)] [(1,0),(0,2)]

/-- **The BB code has exactly 2 logical qubits, DETERMINED from its matrices** — its
    two logical Z operators are computed, not asserted. -/
theorem bbSmall_2_logical_qubits : numLogicals bbSmall = 2 := by decide

/-- **Every computed logical Z of the BB code is genuine** (commutes with all
    X-checks, is not a Z-stabilizer) — so the 2 logical qubits are well-defined. -/
theorem bbSmall_logicalZ_genuine : logicalZ_genuine bbSmall = true := by decide

/-- …and likewise the logical X operators. -/
theorem bbSmall_logicalX_genuine : logicalX_genuine bbSmall = true := by decide

/-! ## §4. Cross-checks on known codes -/

/-- Steane [[7,1,3]]: the finder returns exactly 1 logical qubit, genuine. -/
theorem steane_1_logical : numLogicals FormalRV.QEC.steaneCSS = 1 ∧ logicalZ_genuine FormalRV.QEC.steaneCSS = true := by
  decide

/-- [[4,2,2]]: the finder returns exactly 2 logical qubits, genuine. -/
theorem code422_2_logical : numLogicals code422 = 2 ∧ logicalZ_genuine code422 = true := by decide

end FormalRV.QEC.LogicalFinder
