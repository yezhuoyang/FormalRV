/-
  FormalRV.QFT — the inverse Quantum Fourier Transform (IQFT), the
  measurement-basis transform of QPE / Shor, as a VERIFIED `BaseUCom` circuit.
  Extracted from Shor/ as a general, Shor-agnostic component (sibling of QPE/).

  ## The spine (read these four)
    • `IQFTDef`         — THE definition: `IQFT n` (= `real_QFTinv_layer n` =
                          framework `BaseUCom.QFTinv n`) + the ideal `IQFT_matrix`.
    • `IQFTCorrectness` — THE main theorem: `uc_eval (IQFT n) = IQFT_matrix n`
                          for all `n ≥ 1` (`iqft_correct`), + the framework bridge.
    • `IQFTResource`    — the cost/compilation story: banded (approximate) QFT
                          is exactly Clifford+T, with the derived `≤ 2π/2^c`
                          error budget.
    • `IQFTExample`     — worked 2- and 3-qubit example + uniform `emitQASM`
                          (`IQFTGadget`); kept OFF the default build path (#evals).

  Supporting proofs (imported by the spine; read only when auditing the proofs):
  `IQFTRecursiveArbitrary` (arbitrary-n column induction), `IQFTCircuitCorrectness`
  (1- and 2-qubit base cases + lemmas), `AQFTCompile` / `AQFTCompileSemantics` (the
  Clifford+T compiler), and `IQFTDefinitions` (the helper defs the proofs run on).

  See `README.md` for the qubit layout, the worked example, and the diagram.
-/
import FormalRV.QFT.IQFTDef
import FormalRV.QFT.IQFTCorrectness
import FormalRV.QFT.IQFTResource
-- Reusable two-register QFT measurement model (Ekerå–Håstad / general-DLP circuit shape).
import FormalRV.QFT.TwoRegisterQFT.Basic
