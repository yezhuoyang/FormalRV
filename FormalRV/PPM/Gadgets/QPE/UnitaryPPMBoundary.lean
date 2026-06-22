/-
  FormalRV.PPM.Gadgets.QPE.UnitaryPPMBoundary — WHERE the unitary QPE layer
  meets the PPM layer, as a theorem.

  QPE itself (Hadamards, controlled-powers, inverse QFT, measurement) is
  verified at the Hilbert-space level (`QPE_var_on_eigenstate_from_real_QFTinv`,
  `qpe_prob_peak_bound`) and STAYS unitary — its phase rotations are outside
  the Clifford+CCX `Gate` IR (the honest boundary, unchanged here).  What
  QPE consumes from below is the modexp ORACLE, which IS a `Gate` and IS
  compiled to PPM by this folder's modules.

  The keystone seam theorem here: for ANY contract compiler and ANY
  well-typed oracle gate, the bits the compiled PPM program observes are
  EXACTLY the unitary semantics' computational-basis action of the very
  `BaseUCom` circuit QPE is proven against (`uc_eval_toUCom_acts_on_basis`,
  proven for ALL gates incl. Toffoli).  So the PPM-observed oracle and the
  QPE-assumed oracle are THE SAME map — the two layers compose without a
  faithfulness gap on the Boolean fragment.

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.Gadgets.CompilerContract
import FormalRV.Arithmetic.Correctness

namespace FormalRV.PPM.Gadgets.QPEPPM

open FormalRV.Framework
open FormalRV.BQAlgo

/-- **The unitary↔PPM seam, per gadget**: any contract compiler's observed
    output bits for a well-typed gate are exactly the computational-basis
    action of the unitary (`uc_eval`) of the SAME gate's `BaseUCom` lift —
    the circuit shape QPE's Hilbert-space theorems quantify over. -/
theorem observes_unitary_basis_action (S : PPMCompilerSpec)
    (dim : Nat) (g : Gate) (h_wt : Gate.WellTyped dim g) (f : Nat → Bool) :
    S.Observes (S.compile g) f (Gate.applyNat g f)
    ∧ uc_eval (Gate.toUCom dim g) * f_to_vec dim f
        = f_to_vec dim (Gate.applyNat g f) :=
  ⟨S.compile_observes g f, uc_eval_toUCom_acts_on_basis dim g h_wt f⟩

end FormalRV.PPM.Gadgets.QPEPPM
