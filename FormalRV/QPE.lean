/-
  FormalRV.QPE — Quantum Phase Estimation, over an ABSTRACT (black-box) oracle.
  Extracted from Shor/ as a general, oracle-generic component (sibling of QFT/).

  ## The spine (read these four)
    • `QPEDef`         — THE definition: `QPE k n c` (= npar_H ; controlled_powers
                         c ; QFTinv) with `c` a BLACK-BOX oracle family; `qpe_phase_state`.
    • `QPECorrectness` — THE main theorem: `qpe_on_eigenstate_correct` — QPE on an
                         eigenstate of the abstract oracle yields the phase state
                         (relocated here out of QFT/; modexp-free, oracle-generic).
    • `QPEResource`    — the only QPE overhead is the H-layer + the inverse-QFT
                         measurement basis (Clifford+T compilation + error budget).
    • `QPEExample`     — worked phase-oracle example + uniform `emitQASM`
                         (`QPEPhaseGadget`); kept OFF the default build path (#evals).

  Supporting machinery (imported by the spine; read only when auditing proofs):
  `PhaseKickback` (the phase-kickback cascade + pre-QFT Fourier form),
  `ControlledGates` (controlled-gate semantics + the `control` decomposition),
  `QPEAmplitude` (Dirichlet-kernel amplitude analysis + the 4/π² peak bound),
  and `QPE` (the circuit definitions).

  Modular exponentiation is NOT QPE's job — it is a black-box oracle here; its
  instantiation lives in Shor (`Shor/PostQFT/QPEModmultEigenstate.lean`).

  See `README.md` for the qubit layout, the worked example, and the diagram.
-/
import FormalRV.QPE.QPEAmplitude
import FormalRV.QPE.PhaseKickback
import FormalRV.QPE.QPE
import FormalRV.QPE.ControlledGates
import FormalRV.QPE.QPEDef
import FormalRV.QPE.QPECorrectness
import FormalRV.QPE.QPEResource
