/-
  FormalRV.QPE.QPEDef
  ───────────────────
  THE definition of Quantum Phase Estimation (QPE), as a concrete `BaseUCom`
  unitary circuit over an ABSTRACT (black-box) oracle.  **Definitions only — no
  proofs.**

  THE circuit is `Framework.BaseUCom.QPE k n c` (QPE.lean): on `k + n` qubits,

      QPE k n c  =  npar_H k ; controlled_powers c k ; QFTinv k

  i.e. (1) Hadamards on the `k` measurement qubits, (2) the controlled-powers
  ladder of the oracle, and (3) the inverse QFT on the measurement register.

  ## The black box

  `c : Nat → BaseUCom (k+n)` is a BLACK-BOX oracle family: `c i` is "apply the
  unitary `U` to the power `2^i`, controlled on measurement qubit `i`".  QPE
  knows `U` ONLY through this abstract family and an eigenvalue hypothesis — it
  does NOT know how `U` is built.  Modular exponentiation (`U = ×a mod N`) is one
  instantiation, supplied by Shor; QPE itself is oracle-generic.  The Shor-facing
  wrappers `QPE_var m anc f` / `QPE_var_lsb m anc f` (in
  `Shor/MainAlgorithm/.../QuantumPrimitives.lean`) lift a data-register family
  `f : Nat → BaseUCom anc` into this shape via `map_qubits (· + m)`.

  ## The ideal output and the eigenvalue hypothesis

  On a data-register eigenstate `ψ` of `U` with phase `θ` (`U|ψ⟩ = e^{2πiθ}|ψ⟩`),
  QPE produces `qpe_phase_state m θ ⊗ ψ` (QPEAmplitude.lean), the phase-register
  state peaked at the `m`-bit approximation of `θ`.  The per-oracle eigenvalue
  weight is `qpeEigenvalue m i θ = exp(2πi · 2^(m-i-1) · θ)` (MSB-first;
  PhaseKickback.lean), or `exp(2πi · 2^i · θ)` LSB-first.

  Where to look next:
    • Semantic correctness (THE main theorem) : `QPECorrectness.lean`
    • Resource / measurement-basis compilation : `QPEResource.lean`
    • Worked example + QASM emission           : `QPEExample.lean`
    • Heavy machinery (phase kickback, cascade): `PhaseKickback.lean`,
      `ControlledGates.lean`; amplitude/peak analysis: `QPEAmplitude.lean`.

  Refs: Nielsen–Chuang §5.2 (phase estimation); SQIR `QPEGeneral.v`.
-/
import FormalRV.QPE.QPE
import FormalRV.QPE.QPEAmplitude
import FormalRV.QPE.PhaseKickback

namespace FormalRV.Framework.BaseUCom

open FormalRV.Framework

/-! ## THE QPE circuit (re-surfaced as the spine's single "Definition" entry).

`QPE k n c` and its 3-stage composition are defined in `QPE.lean`; the smoke
checks below pin the structure the correctness theorem runs on. -/

/-- Smoke: THE QPE circuit is exactly `npar_H k ; controlled_powers c k ; QFTinv k`. -/
example (k n : Nat) (c : Nat → BaseUCom (k + n)) :
    QPE k n c
      = UCom.seq (npar_H k) (UCom.seq (controlled_powers c k) (QFTinv k)) :=
  QPE_def_unfold c

/-- Smoke: the controlled-powers ladder is `control i (c i)` over `i ∈ [0,k)`
(the black-box oracle is applied once per measurement qubit). -/
example (d k : Nat) (c : Nat → BaseUCom d) :
    controlled_powers c (k + 1)
      = UCom.seq (controlled_powers c k) (control k (c k)) :=
  controlled_powers_succ c k

end FormalRV.Framework.BaseUCom
