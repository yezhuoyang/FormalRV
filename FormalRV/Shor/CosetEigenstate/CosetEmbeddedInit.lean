/-
  FormalRV.Shor.CosetEigenstate.CosetEmbeddedInit — the EMBEDDED-INIT coset Shor final
  state (resolution 1 of the `hinit` structural question).
  ════════════════════════════════════════════════════════════════════════════

  The Route-2 engine's `hinit : EmbedAgreeOff init_a init_i E_phys ∅` requires the coset
  side to START coset-embedded (`init_a = E_phys init_i`).  The ordinary `Shor_final_state`
  starts `|1⟩`-work (`Shor_initial_state = |0⟩_m ⊗ |1⟩_n ⊗ |0⟩_anc`), so `init = qpeInit`
  is NOT coset-embedded and `qpeInit = E_phys qpeInit` is false — the EmbedAgree-from-init
  framing cannot use it.

  RESOLUTION 1 (faithful to Gidney's runway construction): the actual coset Shor's work
  register begins as a COSET state (the runway is prepared at the start), i.e. as
  `E_phys` applied to the ideal `|1⟩` work init.  We define the coset Shor final state as
  the QPE stages run on the coset-EMBEDDED initial state `E_phys (qpeInit)`:

      Shor_final_state_cosetEmbedded f := orbitState (qpeStageMap f) (E_phys (qpeInit)) (m+1)

  With this, the two Route-2 obligations are DEFINITIONAL:
    * `hdecomp_a` — `Shor_final_state_cosetEmbedded f = orbitState (qpeStageMap f) init_a (m+1)`
      holds by `rfl` (it IS the definition);
    * `hinit` — `EmbedAgreeOff (E_phys qpeInit) qpeInit E_phys ∅` holds by `rfl`
      (`init_a = E_phys init_i` literally), since `EmbedAgreeOff … = (E_phys qpeInit)(…) =
      (E_phys qpeInit)(…)`.

  This is a NEW final-state object (the engine is untouched); the variant conditional
  success theorem over it is the downstream assembly (lemma 5).  `E_phys` is the embedding
  from `CosetEphys`; the stage map / init are the `hdecomp` from `QPEStageDecomp`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.QPEStageDecomp
import FormalRV.Shor.CosetEigenstate.CosetEphys

namespace FormalRV.Shor.CosetEigenstate.CosetEmbeddedInit

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.Shor.CosetEigenstate.EmbedOrbitCompose (orbitState EmbedAgreeOff)
open FormalRV.Shor.CosetEigenstate.QPEStageDecomp (qpeStageMap qpeInit)
open FormalRV.Shor.CosetEigenstate.CosetEphys (E_phys)

/-- The coset-EMBEDDED initial state: `E_phys` of the H-prepared ideal init `qpeInit`
    (the runway prepared at the start).  This is the `init_a` of the embedded-init route. -/
noncomputable def cosetEmbeddedInit (m n anc N cm : Nat) : QState (2 ^ m * 2 ^ n * 2 ^ anc) :=
  E_phys m n anc N cm (qpeInit m n anc)

/-- **The embedded-init coset Shor final state.**  The QPE stages run on the coset-embedded
    initial state.  (Distinct from `Shor_final_state f_coset`, which starts `|1⟩`-work;
    this starts coset-embedded, faithful to the runway construction.) -/
noncomputable def Shor_final_state_cosetEmbedded (m n anc N cm : Nat)
    (f : Nat → BaseUCom (n + anc)) : QState (2 ^ m * 2 ^ n * 2 ^ anc) :=
  orbitState (qpeStageMap m n anc f) (cosetEmbeddedInit m n anc N cm) (m + 1)

/-- **`hdecomp_a` (embedded-init), definitional.**  The embedded-init coset Shor final
    state is exactly the orbit of the stage map over the embedded init — by definition. -/
theorem hdecomp_a_cosetEmbedded (m n anc N cm : Nat) (f : Nat → BaseUCom (n + anc)) :
    Shor_final_state_cosetEmbedded m n anc N cm f
      = orbitState (qpeStageMap m n anc f) (cosetEmbeddedInit m n anc N cm) (m + 1) :=
  rfl

/-- **`hinit` (embedded-init), trivial by construction.**  The coset side starts as
    `E_phys` of the ideal init, so off the empty bad set the actual init `cosetEmbeddedInit`
    IS `E_phys (qpeInit)` — the EmbedAgree holds by `rfl`. -/
theorem hinit_cosetEmbedded (m n anc N cm : Nat) :
    EmbedAgreeOff (shorDvd m n anc) (cosetEmbeddedInit m n anc N cm) (qpeInit m n anc)
      (E_phys m n anc N cm) ∅ :=
  fun _ _ _ => rfl

end FormalRV.Shor.CosetEigenstate.CosetEmbeddedInit
