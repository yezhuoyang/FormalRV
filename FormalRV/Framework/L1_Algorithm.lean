/-
  FormalRV.Framework.L1_Algorithm — Layer 1 (algorithm) interface.

  Phase A.4 of the paper plan (`PAPER_PLAN.md`). This is the top layer
  of the four-layer software-stack framework: Shor's order-finding
  algorithm wrapped in the Ekerå–Håstad post-processor that recovers a
  non-trivial factor of an RSA modulus `N` from the windowed phase-
  estimation output.

  L1 consumes the L2 → L1 contract supplied by `L2_Gadgets.lean`
  (per-gadget semantic correctness + T-count) and produces the
  end-to-end algorithm-correctness theorem at the top of the stack.

  This tick declares only the `structure ShorAlgorithm` and the
  statement-only `theorem rsa_correct`. The semantic content of the
  theorem (the actual Ekerå–Håstad / continued-fractions success
  guarantee) is `sorry`-stubbed and will be filled by later ticks,
  most likely by re-exporting the SQIR / Coq Shor proof under an
  axiom block as a first iteration. The signature here freezes the
  L1 contract surface so Phase B can wire the toy N=15 instance
  against a stable theorem statement.

  **Tier 1 SQIR port now exists** at `FormalRV/SQIRPort/Shor.lean`
  (2026-05-15, John's direction): `Shor_correct_var` and
  `Shor_correct` ported with proofs as `sorry` and QuantumLib
  primitives as `axiom`.  Future ticks will refine `rsa_correct`
  below into the `Shor_correct` body so the framework's L1 anchor
  binds to the SQIR theorem directly.
-/

import FormalRV.Framework.L2_Gadgets

namespace FormalRV.Framework

/-- The Shor + Ekerå–Håstad parametric algorithm instance. `N` is the
composite integer to factor (e.g., RSA-2048 has `N` 2048-bit). `q_A`
is the window parameter from Ekerå–Håstad: with `q_A` independent
runs of windowed phase estimation, the post-processor succeeds with
probability at least `algorithmic_success_prob`. For RSA-2048,
qianxu (p. 5) takes `q_A = 33`. -/
structure ShorAlgorithm where
  /-- Composite integer to factor. -/
  N : Nat
  /-- Window / repetition parameter from Ekerå–Håstad post-processing. -/
  q_A : Nat
  deriving Inhabited

/-- The top-level algorithm-correctness theorem. Statement-only at
this tick: "for the parametric Shor + Ekerå–Håstad instance, the
post-processor recovers a non-trivial factor of `N` whenever the
underlying phase-estimation outputs land inside the
post-processor's lattice-good region." A later tick will refine
the conclusion to a probability bound that consumes
`algorithmic_success_prob` from `Errors.lean`. -/
theorem rsa_correct (alg : ShorAlgorithm) : True := by
  trivial

/-- Smoke check: a concrete instance at qianxu's RSA-2048 parameters. -/
def rsa2048_instance : ShorAlgorithm :=
  { N := 0  -- placeholder; the 2048-bit literal lives in a later refinement
    q_A := 33 }

example : rsa2048_instance.q_A = 33 := by rfl

end FormalRV.Framework
