/-
  Audit · cain-xu-2026 (arXiv:2603.28627) · HARDWARE ASSUMPTIONS
  ----------------------------------------------------------------------------
  The physical parameters the paper's resource estimate assumes.  REDEFINES NOTHING —
  it points at the recorded tuple.  Reader: check these match the paper.

    • neutral-atom baseline: physical two-qubit error 1e-3, error-correction cycle 1 µs.
  The hardware is the `.2.2` component of the recorded (algorithm, code, hardware) tuple.
-/
import FormalRV.Audit.CainXu2026.CainXu

#check @FormalRV.Audit.CainXu2026.CainXu.cainxu_instance   -- (ShorAlgorithm × QECCode × QualtranPhysicalParameters)
