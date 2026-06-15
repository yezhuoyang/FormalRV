/-
  FormalRV.Shor.CosetEigenstate.RunwayIntertwine — the direct EmbedAgree route: the
  runway oracle INTERTWINES with the coset embedding, `Fa ∘ E_phys = E_phys ∘ Fi`.
  ════════════════════════════════════════════════════════════════════════════

  This is the per-oracle content `ApproxCosetOrbitShift`'s `hstep` actually needs (the
  EmbedAgree route), NOT the coset eigenstate (which is complementary).  It says: applying
  the runway-preserving coset oracle `Fa` to the coset-embedded ideal state equals embedding
  the ideal modular-multiply oracle `Fi`'s output:

      Fa (E_phys |z⟩) = E_phys (Fi |z⟩)        (for canonical residues `z < N`)

  where `E_phys |z⟩ = cosetState z` (the coset embedding) and `Fi |z⟩ = |(a·z) mod N⟩` (the
  ideal modular multiply).  The proof is a 4-step rewrite: `E_phys |z⟩ = cosetState z`, the
  runway oracle's EXACT coset shift `Fa(cosetState z) = cosetState((a·z) mod N)` (which
  `RunwayMul.runwayMul_cosetState_shift` supplies), then fold back `cosetState((a·z) mod N) =
  E_phys |(a·z) mod N⟩ = E_phys (Fi |z⟩)`.

  ROLE.  This is the abstract operator-level intertwining.  Feeding it to the engine's
  `EmbedOrbitCompose.embedAgreeOff_oracle_step` (which consumes the per-(x,y) `hintertwine`
  `O_c(D φ) = D(O_i φ)` off bad) gives the per-stage EmbedAgree preservation `hstep`, and
  `orbit_final_embedAgree` lifts it through the QPE orbit to the final-state EmbedAgree =
  `ApproxCosetOrbitShift`'s `agree`, discharging it for the runway oracle WITHOUT the
  eigenstate route.

  ⚠ WHAT REMAINS (circuit-coupled).  The hypotheses here (`hE`, `hFa`, `hFi`) are stated at
  the abstract state-operator level.  Lifting this to the engine's `jointIdx` `hintertwine`
  (with `E_phys = I_phase ⊗ E_data`, `Fa`/`Fi` the CONTROLLED oracles on the Shor register)
  and discharging the QPE stage-decomposition `hdecomp` are the circuit-coupled assembly,
  done together with the concrete reduced-lookup multiplier gate (see
  `COSET_MULTIPLIER_DESIGN.md`).  `hFa` is discharged per-residue by
  `runwayMul_cosetState_shift`; the single global `Fa` (one permutation over the disjoint
  orbit windows) is part of that assembly.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.RunwayMul

namespace FormalRV.Shor.CosetEigenstate.RunwayIntertwine

open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.ApproxOp (cosetState)

/-- **THE RUNWAY/EMBEDDING INTERTWINING (the direct EmbedAgree route).**  For the coset
    embedding `E_phys (ι z) = cosetState z` (residue `z` ↦ its coset state), the
    runway-preserving oracle `Fa` (with the EXACT coset shift `Fa(cosetState k) =
    cosetState((a·k) mod N)`, from `runwayMul_cosetState_shift`), and the ideal modular
    multiply `Fi (ι z) = ι ((a·z) mod N)`:

        Fa (E_phys (ι z)) = E_phys (Fi (ι z))      (canonical `z < N`).

    This is the per-oracle EmbedAgree intertwining `ApproxCosetOrbitShift`'s `hstep`
    consumes (via the orbit-composition engine) — the runway oracle and the ideal oracle
    are conjugate by `E_phys`, exactly, so `actual = E_phys·ideal` is preserved by the
    oracle stage. -/
theorem runwayMul_intertwines_Ephys {dim N m : Nat} (a : Nat)
    (ι : Nat → QState dim) (Fa Fi E_phys : QState dim → QState dim)
    (hE : ∀ k, k < N → E_phys (ι k) = cosetState dim N m k)
    (hFa : ∀ k, Fa (cosetState dim N m k) = cosetState dim N m ((a * k) % N))
    (hFi : ∀ k, k < N → Fi (ι k) = ι ((a * k) % N))
    (hmod : ∀ k, (a * k) % N < N)
    (k : Nat) (hk : k < N) :
    Fa (E_phys (ι k)) = E_phys (Fi (ι k)) := by
  calc Fa (E_phys (ι k))
      = Fa (cosetState dim N m k) := by rw [hE k hk]
    _ = cosetState dim N m ((a * k) % N) := hFa k
    _ = E_phys (ι ((a * k) % N)) := (hE _ (hmod k)).symm
    _ = E_phys (Fi (ι k)) := by rw [hFi k hk]

end FormalRV.Shor.CosetEigenstate.RunwayIntertwine
