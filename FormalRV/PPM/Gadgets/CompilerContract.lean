/-
  FormalRV.PPM.Gadgets.CompilerContract — the COMPILER-AGNOSTIC contract that
  every per-gadget "compiled to PPM, semantically correct" theorem is stated
  against (John's modularization directive, 2026-06-10).

  ## The modular split

  The project is accumulating per-gadget PPM correctness theorems (adders,
  modular adders, both modular multipliers, both modexps, windowed arithmetic,
  …) AND has more than one Gate→PPM compiler in flight:

    * the PROVEN magic-factory compiler `compileArithmeticGateToMagicPPM`
      (old `MagicPPMProgram` IR, `QECBridge/CircuitToPPMFactoryProvision`);
    * the NEW program syntax `PPMProg` (`PPM/Syntax/Program.lean` —
      `c = Measure P` / `frame P` / parity corrections / `useT` / `useCCZ`)
      whose `compilePPM : Gate → PPMProg` keystone (Phase D) is being built
      in a separate lane.

  Proving each gadget against each compiler would be quadratic and would have
  to be redone when Phase D lands.  Instead: a gadget theorem is proven ONCE
  against `PPMCompilerSpec` — anything that compiles a `Gate` and OBSERVES its
  `Gate.applyNat` action — and each compiler discharges the contract once.

      gadget theorems  (per gadget, this folder)      compilers (per IR)
            \                                            /
             ──────────  PPMCompilerSpec  ──────────────
                 compile_observes / compile_magicDemand

  ## Instances

  * `magicFactoryCompiler F` (THIS FILE, proven): the existing magic-aware
    compiler, run on a factory-provisioned certified-T pool — its
    `compile_observes` is exactly `compileToMagicPPM_provisioned_run_observe`,
    and its magic demand equals the Toffoli count
    (`shorMagicDemand_eq_ccxCount`).
  * the NEW-SYNTAX instance (PENDING, do not build here): when Phase D's
    `compilePPM : Gate → PPMProg` + `compilePPM_correct` land
    (`PPM/Syntax/Program.lean` lane), instantiate
    `Prog := PPMProg`, `Observes := (run-based observation)`,
    `magicDemand := countMagicCCZ` (or the T-scheme count) — every gadget
    theorem in `PPM/Gadgets/` then holds for the new syntax with no rework.

  ## Honesty boundary (inherited, unchanged)

  `Observes` is SUCCESS-BRANCH observation: for the factory instance this is
  the named-contract boundary of `ShorModMulPPMFactoryE2E` (abstract
  `teleportCCXRel`, `TFactoryContract`, no per-request failure probability).

  No `sorry`, no `axiom`.
-/
import FormalRV.PPM.QECBridge.CircuitToPPMFactoryProvision

namespace FormalRV.PPM.Gadgets

open FormalRV.Framework
open FormalRV.BQAlgo
open FormalRV.Framework.CircuitToPPMMagicFactory
open FormalRV.Framework.CircuitToPPMToffoliMagic
open FormalRV.Framework.CircuitToPPMFactoryProvision

/-- **The compiler contract.**  A PPM compiler is anything that takes a
    `Gate` (the Clifford+CCX arithmetic IR) to a PPM program in SOME target
    IR `Prog`, together with an observation relation `Observes p input out`
    ("some run of `p` from encoded `input` observes output bits `out`")
    such that the compiled program always observes the gate's verified
    Boolean action, and whose magic demand is the gate's Toffoli count. -/
structure PPMCompilerSpec where
  /-- The target PPM IR (`MagicPPMProgram` today; `PPMProg` once Phase D lands). -/
  Prog : Type
  /-- The compiler. -/
  compile : Gate → Prog
  /-- `Observes p input out`: a (success-branch) run of `p` from encoded
      `input` ends observing output bits `out`. -/
  Observes : Prog → (Nat → Bool) → (Nat → Bool) → Prop
  /-- **Compiler correctness**: the compiled program observes exactly the
      gate's `applyNat` action — the single fact every per-gadget PPM
      theorem composes with the gadget's arithmetic correctness. -/
  compile_observes : ∀ (g : Gate) (input : Nat → Bool),
      Observes (compile g) input (Gate.applyNat g input)
  /-- The magic accounting of the target IR. -/
  magicDemand : Prog → Nat
  /-- **Honest magic accounting**: compiled magic demand = Toffoli count. -/
  compile_magicDemand : ∀ g : Gate, magicDemand (compile g) = gateCCXCount g
  /-- SYNTACTIC sequencing of target programs (list append for both the
      magic-factory IR and the new `PPMProg` syntax). -/
  seqProg : Prog → Prog → Prog
  /-- **Compositionality of the compiler**: compiling a sequenced gate IS
      the syntactic sequencing of the compiled programs — gadget programs
      are CONCRETE syntax objects that compose by concatenation. -/
  compile_seq : ∀ g₁ g₂ : Gate,
      compile (Gate.seq g₁ g₂) = seqProg (compile g₁) (compile g₂)

namespace PPMCompilerSpec

/-- **Gadget COMPOSABILITY (generic).**  The syntactic concatenation of two
    compiled gadget programs observes the CHAINED semantics — derived from
    the contract alone, so it holds for every compiler instance.  This is
    what lets per-gadget theorems be glued into pipelines (modexp = chained
    multiplier programs, etc.) while staying a single concrete PPM object. -/
theorem seq_observes (S : PPMCompilerSpec) (g₁ g₂ : Gate) (f : Nat → Bool) :
    S.Observes (S.seqProg (S.compile g₁) (S.compile g₂)) f
      (Gate.applyNat g₂ (Gate.applyNat g₁ f)) := by
  have h := S.compile_observes (Gate.seq g₁ g₂) f
  rwa [S.compile_seq] at h

/-- Magic demand is ADDITIVE under gadget composition (generic). -/
theorem seq_magicDemand (S : PPMCompilerSpec) (g₁ g₂ : Gate) :
    S.magicDemand (S.seqProg (S.compile g₁) (S.compile g₂))
      = S.magicDemand (S.compile g₁) + S.magicDemand (S.compile g₂) := by
  rw [← S.compile_seq, S.compile_magicDemand, S.compile_magicDemand,
      S.compile_magicDemand]
  rfl

end PPMCompilerSpec

/-- **Instance 1 (proven today): the magic-factory compiler.**  Programs are
    `MagicPPMProgram`s; observation is the provisioned total-correctness run:
    the program executes to completion (`MagicPPMProgramRel`) on a pool of
    exactly its own magic demand in certified-T tokens from `F`, and the
    final state observes the output bits. -/
def magicFactoryCompiler (F : TFactoryContract) : PPMCompilerSpec where
  Prog := MagicPPMProgram
  compile := compileArithmeticGateToMagicPPM
  Observes := fun p input out =>
    ∃ σ', MagicPPMProgramRel F p
        (encodeWithPool input (factoryProvision F (magicPPMRequestCount p))) σ'
      ∧ (magicBasisRefinesApplyNat F).observesBits σ' out
  compile_observes := fun g input =>
    compileToMagicPPM_provisioned_run_observe F g input
  magicDemand := magicPPMRequestCount
  compile_magicDemand := shorMagicDemand_eq_ccxCount
  seqProg := (· ++ ·)
  compile_seq := fun _ _ => rfl

end FormalRV.PPM.Gadgets
