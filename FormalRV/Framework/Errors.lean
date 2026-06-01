/-
  FormalRV.Framework.Errors — three error-mechanism definitions.

  Phase A.7 of the paper plan (`PAPER_PLAN.md`). The paper §2 splits
  end-to-end error into three mechanisms:

  (i)  Logical (random): physical Pauli errors that escape the L4
       decoder, producing an undetected logical Pauli on the protected
       data.  Bounded by `logical_error_budget`.

  (ii) Approximation (deterministic): finite-precision synthesis of
       continuous rotations (T-decompositions of `R_z(θ)`, Solovay–
       Kitaev tails) and finite truncation of QFT phase registers.
       Bounded by `approximation_error`.

  (iii) Algorithmic uncertainty: even with perfect logical gates, the
        Ekerå–Håstad post-processor only succeeds with the lattice-
        good-region probability bound.  Lower-bounded by
        `algorithmic_success_prob`.

  All three are Nat-valued placeholders in this tick (numerators per
  10^k; the k is encoded by the caller).  A later tick refines to
  `Real` once mathlib is imported.
-/

namespace FormalRV.Framework

/-- Total logical-Pauli error budget across `n_cycles` cycles on an
L4 code of distance `d`.  Placeholder: returns `n_cycles` directly,
which a future tick will refine to `a · n_cycles · (p_g / p_star)^{(d+1)/2}`
once mathlib supplies `Real.pow`. -/
def logical_error_budget (n_cycles : Nat) (d : Nat) : Nat :=
  let _ := d
  n_cycles

/-- Deterministic synthesis-and-truncation error budget for an algorithm
of `n_rotations` continuous rotations, each compiled at synthesis
precision `eps_thousandths` (per 1000).  Placeholder: returns the
product; future tick refines to `n_rotations · eps`. -/
def approximation_error (n_rotations : Nat) (eps_thousandths : Nat) : Nat :=
  n_rotations * eps_thousandths

/-- Lower bound on Ekerå–Håstad post-processing success probability,
in 1/1000-of-100% units (so a "success probability of 0.99" reads as
99/100, or the Nat value 99 in this stand-in).

Placeholder formula: `q_A · 100 / (q_A + 1)`.  This is monotone in
`q_A` (more windows ⇒ higher success bound), gives 0 at `q_A = 0`
(no measurement ⇒ no signal), 50 at `q_A = 1` (single-window ⇒ 50%
ceiling under this placeholder), and approaches 100 as `q_A → ∞`.
A faithful Ekerå–Håstad lattice-good-region bound will replace this
once mathlib `Real` enters the project. -/
def algorithmic_success_prob (q_A : Nat) (precision_thousandths : Nat) : Nat :=
  let _ := precision_thousandths
  q_A * 100 / (q_A + 1)

/-- Smoke checks: each `def` is callable. -/
example : logical_error_budget 100 5 = 100 := by rfl
example : approximation_error 2 3 = 6 := by rfl
/-- Monotonicity is visible: 0 windows ⇒ 0; 1 window ⇒ 50; 3 ⇒ 75;
33 ⇒ 97. -/
example : algorithmic_success_prob 0 0 = 0 := by rfl
example : algorithmic_success_prob 1 0 = 50 := by rfl
example : algorithmic_success_prob 3 0 = 75 := by rfl
example : algorithmic_success_prob 33 999 = 97 := by rfl

end FormalRV.Framework
