/-
  FormalRV — formally-verified resource estimation for fault-tolerant
  Shor's algorithm.

  This root imports the whole library, organized by concern.  Start at
  `FormalRV.Shor.Main` for the headline theorem; see `README.md` for the
  four-layer architecture and the verification status of each part.
-/

-- ★ The main theorem (Shor order-finding success probability), re-exported.
import FormalRV.Shor.Main

-- Definitions: Gate IR + classical/quantum semantics.
import FormalRV.Core
-- L2 logical arithmetic gadgets + correctness.
import FormalRV.Arithmetic
-- L1 algorithm: Shor order finding + QPE.
import FormalRV.Shor
-- Classical number theory: the order→factoring reduction that makes Shor actually factor.
import FormalRV.NumberTheory
-- Quantum phase estimation + quantum Fourier transform (general; siblings of Shor).
import FormalRV.QPE
import FormalRV.QFT
-- Separate, independent resource-counting system (Time: gates/depth; Space: qubits).
import FormalRV.Resource
-- L4 QEC codes.
import FormalRV.QEC
-- Pauli-rotation IR: circuits → ±{π, π/2, π/4, π/8} rotations → parallel layers → PPM.
import FormalRV.PauliRotation
-- L3 Pauli-product measurement + magic factories.
import FormalRV.PPM
-- Lowering the measurement-augmented IR (EGate, Gidney/Berry measured uncompute) to PPM.
import FormalRV.Shor.EGatePPMLowering
-- Lattice surgery.
-- System invariants / scheduling / architecture.
import FormalRV.System
-- The four inter-layer contract interfaces.
import FormalRV.Framework
-- Per-paper reader-facing audit (import-only; #check + #print axioms).
import FormalRV.Audit
-- Teaching entry point: standard textbook Shor + surface-code lattice surgery (START HERE).
import FormalRV.Shor.StandardShor
-- Qualtran physical-parameter bridge.
import FormalRV.Qualtran
-- The verifier: airtight Shor-on-LP-code obligation + the #verify_clean enforcement gate.
import FormalRV.Verifier
-- Code emission: device-program / QASM serializers (library modules; demos are standalone).
import FormalRV.Codegen
