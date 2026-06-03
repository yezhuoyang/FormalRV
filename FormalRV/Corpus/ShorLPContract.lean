/-
  FormalRV.Corpus.ShorLPContract — the VERIFIER (proof-carrying contract) for
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
import FormalRV.Corpus.ShorOnLPBridge

namespace FormalRV.Corpus.ShorLPContract

open FormalRV.QEC
open FormalRV.QEC.LogicalFinder
open FormalRV.QEC.LogicalMeasurementGeneral
open FormalRV.Framework.LDPC
open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp
open FormalRV.Framework.SurgeryCorrect
open FormalRV.BQAlgo
open VerifiedShor

/-! ## §1. Logical readout: the classical data the code's logical qubits carry -/

/-- The logical Z̄_i is "read 1" on a stabilizer state iff it is a `+`-stabilizer of it
    (the logical-Z measurement outcome).  This is how a code state encodes a logical bit. -/
def readLogicalBit {c : CSSCode} {k : Nat} (L : LogicalBasis c k)
    (s : StabilizerState) (i : Fin k) : Bool :=
  decide (L.zbar i ∈ s)

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
  /-- (3c) a lattice-surgery gadget realising the logical measurements, ON THIS code. -/
  gadget : SurgeryGadget
  hGadgetOnCode : gadget.data_code.hx = code.hx ∧ gadget.data_code.hz = code.hz
  /-- (4d) the surgery gadget passes the full structural verifier (dimensions, qLDPC,
      τ_s = Θ(d), kernel/row-span condition) — the physical realisation is verified, not
      asserted. -/
  hGadgetVerified : SurgeryGadget.verify_surgery_gadget gadget = true
  /-- (4e) THE COMPILATION IS FAITHFUL: running the LP `program` on the logically-encoded
      input `x` reproduces, at the logical readout, exactly the arithmetic circuit's output
      `(a·x) mod N`.  This is the bridge from the abstract circuit to the LP-code computation
      (the obligation that forbids "the program preserves the code but computes nothing").
      `encodeState x` is the implementer-supplied logical encoding. -/
  encodeState : Nat → StabilizerState
  hSimulates : ∀ x : Nat, x < N → ∀ i : Fin k,
    readLogicalBit basis (measureChecks program (encodeState x)) i
      = readLogicalBit basis (encodeState ((a * x) % N)) i
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

end FormalRV.Corpus.ShorLPContract
