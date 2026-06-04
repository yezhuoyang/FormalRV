/-
  FormalRV.Verifier.ProofGate — the anti-cheat ENFORCEMENT of the verifier.

  `#verify_clean foo` is a hard build-time check: it succeeds iff `foo` is fully proved using
  ONLY the standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) — NO `sorryAx`,
  NO custom `axiom`s.  If `foo`'s proof is incomplete or leans on any extra axiom, `#verify_clean`
  raises an ELABORATION ERROR and the build FAILS.

  This is the "Lean verifier rejects the implementer's submission unless the whole thing is
  proved" mechanism: the user (spec-setter) writes `#verify_clean <submission>` at the bottom of
  the obligation; the implementer cannot land a submission that hides a `sorry` or sneaks in an
  axiom, because the kernel's transitive axiom set is inspected and the build is gated on it.
-/
import Lean

open Lean Elab Command

namespace FormalRV.Verifier

/-- The ONLY axioms a verification-clean proof may transitively depend on.
    These are the standard classical-logic kernel axioms; everything else — most importantly
    `sorryAx` and any project `axiom` — is rejected. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#verify_clean foo`: ACCEPT iff `foo` depends only on `allowedAxioms`; otherwise a hard
    error (build fails).  The verifier rejects incomplete / cheating submissions. -/
elab "#verify_clean " name:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let axs ← collectAxioms declName
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  if bad.isEmpty then
    logInfo m!"✓ verifier ACCEPTS `{declName}`  (axioms: {axs.toList})"
  else
    throwError m!"✗ verifier REJECTS `{declName}`: depends on disallowed axiom(s) {bad.toList}.\n\
      A complete, sorry-free, axiom-free proof of the WHOLE obligation is required — \
      the verifier does not accept partial or hand-wavy submissions."

/-- `#verify_rejects foo`: the DUAL regression check — succeeds iff `foo` WOULD be rejected
    (depends on a disallowed axiom / `sorryAx`), errors if `foo` is actually clean.  Lets the
    verifier's rejection behaviour be tested without failing the build. -/
elab "#verify_rejects " name:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let axs ← collectAxioms declName
  let bad := axs.filter (fun a => !allowedAxioms.contains a)
  if bad.isEmpty then
    throwError m!"#verify_rejects FAILED: `{declName}` is verification-clean (would be ACCEPTED)."
  else
    logInfo m!"✓ verifier correctly REJECTS `{declName}`  (disallowed: {bad.toList})"

end FormalRV.Verifier

/-! ## Self-tests: the gate accepts a clean proof and rejects an unproven one. -/

namespace FormalRV.Verifier.SelfTest

theorem clean_example : 1 + 1 = 2 := rfl
#verify_clean clean_example          -- ✓ accepted (axiom-free)

/-- Test fixture (unused anywhere): a claim asserted as an `axiom` instead of proved — the kind
    of "cheat" the verifier must reject. -/
private axiom unproven_fixture : (2 : Nat) + 2 = 4
#verify_rejects unproven_fixture     -- ✓ correctly rejected (a real proof is required)

end FormalRV.Verifier.SelfTest
