/-
  FormalRV.QEC.FrontendAlgebraic -- the ALGEBRAIC frontend of the QEC
  code-construction framework.

  Builds CSS qLDPC codes from polynomial / product data and lowers each
  construction to the unified CSSCode pivot (hx, hz).  Every constructor
  produces an honest GF(2) check-matrix pair; the CSS commutation condition
  H_X * H_Z^T = 0 is then derived (by decide) on concrete smoke instances.

  Constructions: identMat, kron, hypergraphProduct, repCode, surfaceHGP,
  shiftMat, shiftPow, matXor, biCirculant, bivariateBicycle, circulant,
  circDagger.  Capstone: surfaceHGP3_circuit_implements instantiates
  CSSCode.syndrome_circuit_implements_code on the distance-3 surface code.

  No Mathlib.  Pure Bool / Nat / List + decide / native_decide.
-/

import FormalRV.QEC.CSSCode

namespace FormalRV.QEC.Algebraic

open FormalRV.Framework.LDPC
open FormalRV.Framework.PPMOp
open FormalRV.QEC

/-! ## (1) GF(2) identity and Kronecker product -/

/-- The n x n GF(2) identity matrix. -/
def identMat (n : Nat) : BoolMat :=
  (List.range n).map (fun i => (List.range n).map (fun j => decide (i = j)))

/-- Kronecker product of two GF(2) matrices.  If A is rA x cA and B is
    rB x cB, the result is (rA*rB) x (cA*cB), block (i,k),(j,l) = A i j and B k l. -/
def kron (A B : BoolMat) : BoolMat :=
  A.flatMap (fun arow => B.map (fun brow =>
    arow.flatMap (fun a => brow.map (fun b => a && b))))

/-! ### Smoke checks for (1) -/

example : kron [[true]] (identMat 3) = identMat 3 := by decide
example : (kron (identMat 2) (identMat 3)).length = 2 * 3 := by decide
example : kron (identMat 2) (identMat 2) = identMat 4 := by decide

/-! ## (2) Hypergraph product (standard CSS HGP) -/

/-- The CSS hypergraph product of classical parity-check matrices
    h1 : m1 x n1 and h2 : m2 x n2.

      n  = n1*n2 + m1*m2
      hx = [ h1 (x) I_n2 | I_m1 (x) h2^T ]
      hz = [ I_n1 (x) h2 | h1^T (x) I_m2 ]

    CSS condition hx*hz^T = 0 holds since
    (h1(x)I)(I(x)h2^T) + (I(x)h2^T)(h1(x)I) = h1(x)h2^T + h1(x)h2^T = 0
    over GF(2).  Dimensions are passed explicitly to avoid re-deriving them. -/
def hypergraphProduct (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : CSSCode :=
  { n := n1 * n2 + m1 * m2,
    hx := hcat (kron h1 (identMat n2)) (kron (identMat m1) (transpose h2 n2)),
    hz := hcat (kron (identMat n1) h2) (kron (transpose h1 n1) (identMat m2)) }

/-! ## (3) Repetition code + surface code as HGP -/

/-- The (d-1) x d consecutive-ones parity check of the distance-d repetition
    code: row i (for 0 <= i < d-1) has 1s at columns i and i+1. -/
def repCode (d : Nat) : BoolMat :=
  (List.range (d - 1)).map (fun i =>
    (List.range d).map (fun j => decide (j = i) || decide (j = i + 1)))

/-- The unrotated surface code at distance d = HGP(repCode d, repCode d).
    Parameters [[d^2 + (d-1)^2, 1, d]].  Here repCode d is (d-1) x d, so
    m1 = m2 = d-1 and n1 = n2 = d. -/
def surfaceHGP (d : Nat) : CSSCode :=
  hypergraphProduct (repCode d) (repCode d) (d - 1) d (d - 1) d

/-! ### Smoke checks for (3) -/

example : (surfaceHGP 3).n = 13 := by decide
example : (surfaceHGP 3).well_shaped = true := by decide
example : (surfaceHGP 3).css_condition = true := by decide

/-! ## (4) Bivariate-bicycle codes -/

/-- The l x l cyclic shift matrix S_l: row i has a 1 at column (i+1) mod l. -/
def shiftMat (l : Nat) : BoolMat :=
  (List.range l).map (fun i => (List.range l).map (fun j => decide (j = (i + 1) % l)))

/-- S_l^k as a matrix: entry (i, (i+k) mod l) is 1. -/
def shiftPow (l k : Nat) : BoolMat :=
  (List.range l).map (fun i => (List.range l).map (fun j => decide (j = (i + k) % l)))

/-- Entrywise GF(2) sum (XOR) of two equal-shape matrices. -/
def matXor (A B : BoolMat) : BoolMat :=
  (A.zip B).map (fun p => (p.1.zip p.2).map (fun q => xor q.1 q.2))

/-- A bivariate monomial sum over F2[x,y]/(x^l+1, y^m+1) as a list of (i,j)
    exponent pairs.  Monomial x^i y^j lowers to shiftPow l i (x) shiftPow m j
    (an lm x lm matrix); the sum is GF(2) XOR over all terms. -/
def biCirculant (l m : Nat) (terms : List (Nat × Nat)) : BoolMat :=
  terms.foldl (fun acc t => matXor acc (kron (shiftPow l t.1) (shiftPow m t.2)))
    ((List.range (l * m)).map (fun _ => (List.range (l * m)).map (fun _ => false)))

/-- A bivariate-bicycle (BB) code, a.k.a. LP(a, b) (Bravyi et al. 2024).
      A = biCirculant l m a,  B = biCirculant l m b
      hx = [ A | B ],  hz = [ B^T | A^T ],  n = 2*l*m
    CSS condition holds since A and B are circulants over the same commutative
    ring, so A*B = B*A, hence A*B + B*A = 0 over GF(2), which is hx*hz^T. -/
def bivariateBicycle (l m : Nat) (a b : List (Nat × Nat)) : CSSCode :=
  let A := biCirculant l m a
  let B := biCirculant l m b
  { n := 2 * l * m,
    hx := hcat A B,
    hz := hcat (transpose B (l * m)) (transpose A (l * m)) }

/-! ### Smoke checks for (4) -/

example : (bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]).n = 18 := by decide
example : (bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]).well_shaped = true := by decide
example : (bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]).css_condition = true := by decide

example : (bivariateBicycle 6 6 [(3, 0), (0, 1), (0, 2)] [(0, 3), (1, 0), (2, 0)]).n = 72 := by decide
example : (bivariateBicycle 6 6 [(3, 0), (0, 1), (0, 2)] [(0, 3), (1, 0), (2, 0)]).well_shaped = true := by
  native_decide
example : (bivariateBicycle 6 6 [(3, 0), (0, 1), (0, 2)] [(0, 3), (1, 0), (2, 0)]).css_condition = true := by
  native_decide

/-! ## (5) Lifted product (qianxu LP) -- circulant ring primitives -/

/-- A ring element of F2[x]/(x^l+1), represented by its exponent support. -/
abbrev Circ := List Nat

/-- The l x l circulant matrix of a Circ: entry (i, j) is 1 iff
    (j - i) mod l is a member of the support. -/
def circulant (l : Nat) (p : Circ) : BoolMat :=
  (List.range l).map (fun i =>
    (List.range l).map (fun j => p.contains ((j + l - i % l) % l)))

/-- The conjugate p(x) to p(x_inv) on Circ: e to (l - e) mod l. -/
def circDagger (l : Nat) (p : Circ) : Circ := p.map (fun e => (l - e % l) % l)

/-! ### Smoke checks for (5) -/

example : circulant 3 [1] = shiftMat 3 := by decide
example : circDagger 3 [1] = [2] := by decide

/-! ## (6) Pipeline capstone -/

/-- The constructed distance-3 surface code syndrome circuit implements it.
    Instantiating CSSCode.syndrome_circuit_implements_code on the HGP-built
    surface code: because the construction is CSS (css_condition = true), the
    measured stabilizer group toStabilizers is a valid (pairwise-commuting)
    stabilizer code.  Closes the ALGEBRAIC -> check-matrix ->
    circuit-implements-code chain end-to-end. -/
theorem surfaceHGP3_circuit_implements :
    StabilizerState.valid ((surfaceHGP 3).toStabilizers) (surfaceHGP 3).n = true := by
  rw [CSSCode.syndrome_circuit_implements_code (surfaceHGP 3) (by decide)]
  decide

/-- The same end-to-end chain for the tiny bivariate-bicycle code:
    its syndrome circuit implements the constructed [[18, *, *]] BB code. -/
theorem tinyBB_circuit_implements :
    StabilizerState.valid
      ((bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]).toStabilizers)
      (bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]).n = true := by
  rw [CSSCode.syndrome_circuit_implements_code
        (bivariateBicycle 3 3 [(0, 0), (1, 0)] [(0, 0), (0, 1)]) (by decide)]
  decide

end FormalRV.QEC.Algebraic
