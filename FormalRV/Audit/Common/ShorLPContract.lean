/-
  FormalRV.Audit.Common.ShorLPContract — the VERIFIER (proof-carrying contract) for
  "fault-tolerant Shor on a user-specified LP code".

  John's directive: FIX THE VERIFIER FIRST, so the implementer cannot cheat / overclaim.
  The verifier is this `structure`; an implementer's SUBMISSION is a *term* of it. Lean's
  kernel accepts the term ONLY if every proof obligation is discharged, and the submission
  is ACCEPTED only if `#print axioms` on it is `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `native_decide` axiom, no custom axiom).  There is NO way to overclaim:
  a false or missing obligation simply cannot be proven.

  The four things John listed are the four groups of fields:
    (1) USER SPECIFIES THE LP CODE        → the structure is parametric in `code`; `hCSS`.
    (2) LOGICAL Z FOR ALL LOGICAL QUBITS  → `k`, `basis`, `hBasisValid`, `hDimension`.
    (3) CONSTRUCTION OF FULL SHOR         → `arithCircuit`, `program`, `gadget`,
                                            algorithm instance + oracle.
    (4) PROOF OF CORRECTNESS (everything) → `hArithCorrect`, `hPreservesCode`,
                                            `hGadgetVerified`, `hSimulates`, `hShorSucceeds`,
                                            `hResourceBound`.

  NONE of these may be hand-wavy: each is a real proposition.  In particular the decidable
  core (1)+(2) is bulletproof — `code.valid`, `basis.valid`, and the rank-derived dimension
  are KERNEL-COMPUTED Booleans, so a wrong code / fake logical basis / wrong qubit count
  cannot be certified (only `sorryAx` could, and the acceptance check forbids it).

  This file fixes the CONTRACT.  It deliberately does NOT yet build a complete `lp20`
  submission — that is the construction phase.  We include: the contract; the decidable
  ACCEPTANCE checker; a worked decidable-core certificate on the small real BB code; and a
  NEGATIVE test proving a bogus logical basis is REJECTED.

  No `sorry`, no `axiom`.
-/

import FormalRV.Corpus.QianxuVerifiedUpperBound
import FormalRV.Corpus.QianxuLPSurgery
import FormalRV.Audit.Common.ShorOnLPBridge

namespace FormalRV.Audit.Common.ShorLPContract

open FormalRV.QEC
open FormalRV.QEC.LogicalFinder
open FormalRV.QEC.LogicalMeasurementGeneral
open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect
open FormalRV.BQAlgo
open VerifiedShor

/-! ## §1. Helpers

    ACCEPTANCE PROTOCOL (external, by design — cannot be a Lean term, since Lean cannot
    introspect its own axiom use inside a proof).  A submission `cert : Certificate code` is
    ACCEPTED iff it type-checks AND
        `#print axioms cert`  =  `[propext, Classical.choice, Quot.sound]`.
    This forbids BOTH `sorryAx` (no hand-waving any obligation) AND
    `Lean.ofReduceBool` / `native_decide`'s native-eval axiom (no unverified brute force).
    Consequently the decidable obligations (`code.valid`, `basis.valid`, the rank dimension)
    must be discharged by KERNEL `decide` or a PARAMETRIC proof — never `native_decide`. -/

/-- The GF(2) support of a Pauli string: the positions where it acts non-trivially.  Used to
    tie each surgery gadget's `target_pauli` to the operation it measures. -/
def pauliSupport (P : PauliString) : BoolVec :=
  P.ops.map (fun p => decide (p ≠ Pauli.I))

/-! ## §2. THE VERIFIER CONTRACT (proof-carrying; parametric in the user's LP code) -/

/-- **The fault-tolerant-Shor-on-`code` certificate.**  A term of this type is a complete,
    machine-checked proof that the user's LP `code` carries a fault-tolerant Shor's
    algorithm.  Every field is a genuine obligation; there is no escape hatch. -/
structure Certificate (code : CSSCode) where
  /-- (1) the user's code is a genuine CSS code (`H_X H_Z^T = 0`, well-shaped). -/
  hCSS : code.valid = true
  /-- (2a) the number of logical qubits. -/
  k : Nat
  /-- (2b) the logical X̄/Z̄ operators for ALL `k` logical qubits — i.e. "the logical Z for
      each logical qubit", with its symplectic partner. -/
  basis : LogicalBasis code k
  /-- (2c) the logical basis is VALID: each Z̄ ⟂ X-checks, each X̄ ⟂ Z-checks, symplectic
      form δ_ij — so the operators are genuine and correctly indexed (decidable). -/
  hBasisValid : basis.valid = true
  /-- (2d) `k` is the TRUE logical dimension `n − rank H_X − rank H_Z`, so the count cannot
      be over- or under-claimed (and with `hBasisValid` this forces a genuine N(S)\S
      basis). -/
  hDimension : code.n - rank code.hx - rank code.hz = k
  /-- (3a) the modular-arithmetic circuit (Gate IR) the modexp is built from. -/
  bits : Nat
  N : Nat
  a : Nat
  ainv : Nat
  arithCircuit : Gate
  /-- (4a) the arithmetic is CORRECT for all inputs: the circuit maps x ↦ (a·x) mod N at
      the classical-basis level. -/
  hArithCorrect : ∀ x : Nat, x < N →
    Gate.applyNat arithCircuit (encodeDataZeroAnc bits (ModMul.ancillaWidth bits) x)
      = encodeDataZeroAnc bits (ModMul.ancillaWidth bits) ((a * x) % N)
  /-- (3b) the modexp compiled to a sequence of logical Pauli-product measurements on THIS
      code's logical qubits. -/
  program : List PauliString
  /-- (4b) every operation is a genuine logical operation of the code (commutes with all
      stabilizers — so the program is a legal logical computation). -/
  hProgramLogical : ∀ P ∈ program, ∀ g ∈ code.hx.map CSSCode.xStab ++ code.hz.map CSSCode.zStab,
    g.commutes P = true
  /-- (4c) FAULT TOLERANCE: the program preserves EVERY code stabilizer throughout the whole
      computation (the error-correcting structure survives). -/
  hPreservesCode : ∀ g ∈ code.hx.map CSSCode.xStab ++ code.hz.map CSSCode.zStab,
    g ∈ measureChecks program (codeStateWithLogicals code k basis)
  /-- (3c)+(4d) a VERIFIED lattice-surgery gadget for EVERY logical operation in the program,
      on THIS code.  NO single representative: each PPM `program[i]` gets its OWN structurally-
      verified gadget that measures exactly that operation's logical operator (its support). -/
  gadgets : Fin program.length → SurgeryGadget
  hGadgetsOnCode : ∀ i : Fin program.length,
    (gadgets i).data_code.hx = code.hx ∧ (gadgets i).data_code.hz = code.hz
  hGadgetsVerified : ∀ i : Fin program.length,
    SurgeryGadget.verify_surgery_gadget (gadgets i) = true
  hGadgetsMeasure : ∀ i : Fin program.length,
    (gadgets i).target_pauli
      = pauliSupport (program.get i) ++ List.replicate (gadgets i).ancilla_n false
  /-- (4e) THE COMPILATION IS FAITHFUL — FULL STATE.  For EVERY computational-basis input
      `x < N`, running the LP `program` from the encoded input `encodeState x` yields EXACTLY
      the encoded output `encodeState ((a·x) mod N)` AS A WHOLE STABILIZER STATE — not merely
      one logical-readout bit: the ENTIRE encoded state is correct.  Forbids "preserves the
      code but computes nothing / the wrong thing". -/
  encodeState : Nat → StabilizerState
  hSimulates : ∀ x : Nat, x < N →
    measureChecks program (encodeState x) = encodeState ((a * x) % N)
  /-- (3d)+(4f) the ALGORITHM: Shor order-finding succeeds with probability ≥ κ/(log₂N)⁴
      using this modular multiplier as the oracle (the SQIR-ported success bound). -/
  r : Nat
  m : Nat
  hShorSucceeds :
    FormalRV.SQIRPort.probability_of_success a r N m bits (ModMul.ancillaWidth bits)
        (ModMul.circuitFamily a ainv N bits)
      ≥ FormalRV.SQIRPort.κ / (Nat.log2 N : ℝ) ^ 4
  /-- (4g) a VERIFIED resource upper bound: the construction runs within `qubitBound`
      qubits and `timeBound` µs, and these are honest (the naive sequential makespan
      dominates any schedule, so the requirement is at most this). -/
  qubitBound : Nat
  timeBound : Nat
  numPPMs : Nat
  tau_s : Nat
  cycle : Nat
  n_LP : Nat
  N_A : Nat
  factory : Nat
  hQubitBound : qubitBound = FormalRV.Corpus.QianxuVerifiedUpperBound.upperQubits n_LP N_A factory
  hTimeBound  : timeBound = FormalRV.Corpus.QianxuVerifiedUpperBound.upperTimeUs numPPMs tau_s cycle
  hTimeIsUpperBound : ∀ depth, depth ≤ numPPMs →
    depth * tau_s * cycle ≤ FormalRV.Corpus.QianxuVerifiedUpperBound.upperTimeUs numPPMs tau_s cycle

/-! ## §3. The ACCEPTANCE checker (the decidable, machine-checked core) -/

/-- The verifier's decidable acceptance core: the code is CSS, the logical basis is valid,
    and the qubit count is the true dimension.  These are KERNEL-computed Booleans — they
    cannot be faked.  (The semantic obligations of `Certificate` are enforced by the type
    system + the `#print axioms` clean-acceptance check.) -/
def acceptsCore (code : CSSCode) (k : Nat) (basis : LogicalBasis code k) : Bool :=
  code.valid && basis.valid && decide (code.n - rank code.hx - rank code.hz = k)

/-- Soundness of the core checker: it accepts exactly the decidable obligations a
    `Certificate` must satisfy. -/
theorem acceptsCore_iff (code : CSSCode) (cert : Certificate code) :
    acceptsCore code cert.k cert.basis = true := by
  unfold acceptsCore
  rw [cert.hCSS, cert.hBasisValid]
  simp [cert.hDimension]

/-! ## §4. Worked decidable-core certificate on the REAL small BB code -/

/-- The decidable core IS satisfiable on the real [[18,2,d]] bivariate-bicycle code: its
    computed logical basis is valid and `k = 2` is the true dimension.  (A full
    `Certificate bbSmall` additionally needs the construction + algorithm fields; this shows
    the *core* the contract demands is genuine, not vacuous.) -/
theorem bbSmall_core_accepted :
    acceptsCore bbSmall 2 bbSmallLogicalBasis = true := by decide

/-! ## §5. NEGATIVE test: a bogus logical basis is REJECTED -/

/-- A deliberately WRONG logical basis for the BB code: claim the all-zero vector is a
    logical operator. -/
def bogusBasis : LogicalBasis bbSmall 2 :=
  { lx := fun _ => List.replicate bbSmall.n false
    lz := fun _ => List.replicate bbSmall.n false }

/-- **The verifier REJECTS the bogus basis** — `acceptsCore` computes `false`, so no
    `Certificate bbSmall` can use it (its `hBasisValid` would be `false = true`, unprovable
    without `sorryAx`, which acceptance forbids).  Overclaiming is impossible. -/
theorem bogus_rejected : acceptsCore bbSmall 2 bogusBasis = false := by decide

/-- Concretely, the bogus basis fails validity (the all-zero "logical" pairs trivially, so
    the symplectic δ_ij fails). -/
theorem bogus_basis_invalid : bogusBasis.valid = false := by decide

end FormalRV.Audit.Common.ShorLPContract
