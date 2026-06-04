import FormalRV.Verifier.ProofGate
import FormalRV.Verifier.ShorSpec

/-!
# FormalRV.Verifier

The verifier: an airtight, user-fixed specification of a correct Shor implementation on a
user-supplied LP code, plus the `#verify_clean` enforcement gate that REJECTS any submission
which is incomplete (`sorry`) or leans on an extra axiom.  Set the spec first; build the
construction second; the gate decides acceptance.
-/
