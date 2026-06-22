/-
  FormalRV.QPE.QPEResource
  ────────────────────────
  THE "resource" account for Quantum Phase Estimation.

  QPE adds only TWO things on top of its `k` black-box controlled-oracle calls:
    1. `k` Hadamards on the measurement register (`npar_H k`), and
    2. one `k`-qubit INVERSE QFT as the measurement basis (`QFTinv k`).
  The oracle (`controlled_powers c k`) is a BLACK BOX — its cost belongs to the
  instantiation (for Shor, the modular-exponentiation ladder, which dominates).
  So the QPE-specific resource is exactly the measurement-basis cost, which is
  the inverse-QFT cost: continuous controlled phases, hence governed by
  Clifford+T COMPILATION (the approximate / banded QFT), not an exact T-count.

  Headlines (re-surfaced from `QFT/IQFTResource.lean`, now phrased about QPE's
  measurement basis):
    • `qpe_measurement_basis_isCliffordT`  — the banded measurement basis is
      exactly Clifford+T (cutoff `c ≤ 2`).
    • `qpe_measurement_basis_error_budget` — its derived `≤ 2π/2^c` error budget.
    • `qpe_circuit_resource_decomp`        — the QPE unitary factors as
      `QFTinv k · controlled_powers c k · npar_H k` (so the only QPE overhead is
      the H-layer + the inverse QFT).

  EXACT GATE/QUBIT COUNTS (the `Resource/` counters walking THE circuit's
  syntax tree, with the oracle a BLACK BOX — see `QPECount.lean`, imported below):
    • `Resource.cnotCountU_QPE` / `oneQCountU_QPE` — QPE's counts = the
      controlled-oracle calls (parametric in the oracle's own counts) + the
      inverse-QFT basis `3·⌊k/2⌋ + k·(k−1)`  (TIME)
    • `Resource.cnotCountU_QPE_var_lsb`            — same through the Shor-facing
      wrapper (counts invariant under lifting + LSB reversal)
    • `Resource.widthU_QPE_decomp`                 — the space decomposition
    • `SQIRPort.qpe_verified_with_resources`       — black-box semantics + count,
      about the SAME syntactic object.
-/
import FormalRV.QPE.QPE
import FormalRV.QPE.QPECount
import FormalRV.QFT.IQFTResource

namespace FormalRV.Framework.BaseUCom

open FormalRV.Framework
open FormalRV.Framework.AQFTCompile

/-- **QPE measurement basis is Clifford+T (THE gate-set resource).**  The QPE
measurement-basis inverse QFT, compiled at cutoff `c ≤ 2` (banded), emits only
Clifford+T gates. -/
theorem qpe_measurement_basis_isCliffordT {dim : Nat} (c : Nat) (hc : c ≤ 2)
    (rs : List PhaseRot) :
    FormalRV.Framework.CliffordTRotations.IsCliffordT
      (compileLadder c rs : BaseUCom dim) :=
  iqft_banded_isCliffordT c hc rs

/-- **QPE measurement basis error budget (THE approximation resource).**  The
total cost of the cutoff-`c` measurement-basis compilation is the derived
geometric tail `≤ 2π/2^c`. -/
theorem qpe_measurement_basis_error_budget (c n : ℕ) (hcn : c ≤ n) :
    ∑ m ∈ Finset.Ico c n, (Real.pi / 2 ^ m) ≤ 2 * Real.pi / 2 ^ c :=
  iqft_banded_error_budget c n hcn

/-- **QPE resource decomposition.**  The QPE unitary is the right-to-left
product `QFTinv k · controlled_powers c k · npar_H k`: beyond the `k`
black-box controlled-oracle calls, the only overhead is the `k`-Hadamard
preparation and the `k`-qubit inverse QFT (the measurement basis). -/
theorem qpe_circuit_resource_decomp {k n : Nat} (c : Nat → BaseUCom (k + n)) :
    uc_eval (QPE k n c)
      = uc_eval (QFTinv k) * uc_eval (controlled_powers c k) * uc_eval (npar_H k) :=
  uc_eval_QPE c

end FormalRV.Framework.BaseUCom
