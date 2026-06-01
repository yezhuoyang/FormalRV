/-
  FormalRV.Corpus.CainXu — Phase-C corpus paper #1: Cain–Xu et al.
  2026 (qianxu).

  Phase C first slice. Cain–Xu et al. 2026 (the "qianxu" paper in our
  corpus) propose a fault-tolerant Shor implementation on a
  reconfigurable neutral-atom array, using a lifted-product (LP)
  qLDPC code stack. This file plants the paper's parametric tuple
  into the framework — no semantic verification yet; that arrives in
  later Phase-C ticks.

  Parametric tuple bound here:
    L1 ShorAlgorithm     : N = (2048-bit composite, placeholder),
                           q_A = 33  (qianxu p. 5)
    L4 QECCode           : (n, k, d) = (144, 12, 12)  (qianxu Sec. 3:
                           bivariate-bicycle LP qLDPC instance)
    HW QualtranPhysical  : physical_error = 1e-3,
                           cycle_time = 1 μs  (Bluvstein 2024 baseline)

  The Lean tuple type-checks against the four-layer framework on this
  one paper — first cross-paper test of the parametric interface.
-/

import FormalRV.Framework.L1_Algorithm
import FormalRV.Framework.L4_QECCode
import FormalRV.Qualtran.Bridge

namespace FormalRV.Corpus.CainXu

open FormalRV.Framework FormalRV.Qualtran

/-- The Cain–Xu Shor instance: factor an RSA-2048 modulus with
`q_A = 33` Ekerå–Håstad windows (qianxu p. 5). The `N` literal is
placeholder — the parametric review applies to any 2048-bit composite
the paper instantiates. -/
def cainxu_shor : ShorAlgorithm :=
  { N := 0, q_A := 33 }

/-- The Cain–Xu LP qLDPC code: bivariate-bicycle `[[144, 12, 12]]`
instance (qianxu Sec. 3). Parity-check matrices are placeholder `[]`
here — the explicit matrix encoding is a later Phase-C tick. -/
def cainxu_code : QECCode :=
  { n := 144, k := 12, d := 12, hx := [], hz := [] }

/-- The Cain–Xu neutral-atom hardware baseline: physical error 1e-3,
cycle time 1 μs (Bluvstein 2024-style numbers, encoded in our Nat
units as 1/1000 and 1/10 μs respectively). -/
def cainxu_hw : QualtranPhysicalParameters :=
  { physical_error_thousandths := 1, cycle_time_us_tenths := 10 }

/-- The full parametric tuple for the Cain–Xu corpus instance. -/
def cainxu_instance : ShorAlgorithm × QECCode × QualtranPhysicalParameters :=
  (cainxu_shor, cainxu_code, cainxu_hw)

/-- Smoke: paper-stated parameters read back correctly through the
tuple. q_A = 33 (qianxu p. 5); (n,k,d) = (144,12,12) (qianxu Sec. 3);
physical_error = 1e-3 (Bluvstein). -/
example : cainxu_instance.1.q_A = 33 := by rfl
example : cainxu_instance.2.1.n = 144 ∧
          cainxu_instance.2.1.k = 12 ∧
          cainxu_instance.2.1.d = 12 := by exact ⟨rfl, rfl, rfl⟩
example : cainxu_instance.2.2.physical_error_thousandths = 1 := by rfl

/-- Helper: build a `length-n` `Bool` vector from a list of non-zero
positions. -/
def makeRow (positions : List Nat) (n : Nat) : List Bool :=
  (List.range n).map (fun i => positions.contains i)

/-- The first X-type stabilizer of the BB `[[144, 12, 12]]` code with
the Bravyi-style choice `A = x³ + y + y²` (on the L-block, indices
0..71 with `(i, j) ↦ 6 i + j`, `l = 12`, `m = 6`) and `B = y³ + x + x²`
(on the R-block, offset 72). The first X-check is at `(i, j) = (0, 0)`,
giving non-zero positions `{1, 2, 18}` on the L-block and `{75, 78, 84}`
on the R-block — weight 6 total.

Exact (A, B) follows the Bravyi–Cross–Gambetta-style BB construction
(qianxu Sec. 3 cites this family); the specific polynomial choice may
differ from qianxu's stated one (which the paper does not give in
machine-readable form). The encoding shows the framework can carry
real parity-check matrix rows. -/
def bb_first_x_check : List Bool :=
  makeRow [1, 2, 18, 75, 78, 84] 144

/-- Smoke: first X-check has length 144 and stabilizer weight 6. -/
example : bb_first_x_check.length = 144 := by native_decide
example : (bb_first_x_check.filter id).length = 6 := by native_decide

end FormalRV.Corpus.CainXu
