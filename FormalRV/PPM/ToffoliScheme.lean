/-
  FormalRV.PPM.ToffoliScheme — a reusable interface for *multiple*
  provably-correct Toffoli realisations, and the bridge from the
  quantum gate down to the Boolean `Gate.applyNat (CCX)` semantics that
  the PPM/arithmetic layer uses.

  ## What this file delivers (Ask 2)

  * `ToffoliScheme` — an interface whose correctness field is a
    **theorem** (the gate permutes computational basis states by the
    Toffoli map), not an abstract contract.
  * Two concrete, sorry-free instances:
      - `cczTeleportScheme` — one `|CCZ⟩` magic state + Hadamards
        (the Litinski gate-teleportation route);
      - `eightTScheme` — the famous **8T→CCZ** seven-T phase polynomial
        + Hadamards.
    Both are proved to realise the *same* Toffoli unitary
    (`Had3 · CCZ · Had3 = Had3 · (8T) · Had3 = ccxPermMat`), differing
    only in their magic-resource cost.
  * `scheme_implements_gate_applyNat` — the bridge: on the 3-qubit
    computational basis the realised Toffoli computes exactly
    `Gate.applyNat (Gate.CCX 0 1 2)`, i.e. it flips the target iff both
    controls are set.  This is the (formerly assumed) Boolean Toffoli
    action, now *derived* from the quantum gate identity.

  ## Honesty boundary

  * The proofs are for the 3-qubit Toffoli core (`Fin 8`).  The
    `n`-qubit / arbitrary-control-index version `Gate.applyNat
    (Gate.CCX a b c)` is the standard identity-tensor embedding of this
    core on qubits `a,b,c`; that embedding (via `pad_u`/`f_to_vec`) is
    the remaining plumbing, not new physics.
  * The `|CCZ⟩` magic state's *distillation/cultivation* correctness,
    and the measurement-outcome Bell step of full gate teleportation,
    are separate concerns (the latter is the Litinski 64×64 step, left
    cited).  What is proved here is the **unitary gate identity** each
    scheme realises and its Boolean basis action.
-/
import FormalRV.PPM.ToffoliFromCCZ
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Framework.ToffoliScheme

open scoped Matrix
open FormalRV.Framework
open FormalRV.Framework.EightTToCCZ
open FormalRV.Framework.ToffoliFromCCZ
open FormalRV.BQAlgo

/-! ## §1. The scheme interface. -/

/-- A provably-correct realisation of the 3-qubit Toffoli gate.  The
    `basis_action` field is a theorem: the realised unitary `gate`
    permutes the computational basis states by the Toffoli map
    `ccxPerm` (flip the target iff both controls are set). -/
structure ToffoliScheme where
  /-- Human-readable name. -/
  name         : String
  /-- Magic-T states consumed. -/
  magicTCost   : Nat
  /-- Magic-CCZ states consumed. -/
  magicCCZCost : Nat
  /-- The 3-qubit unitary the scheme realises. -/
  gate         : Matrix (Fin 8) (Fin 8) ℂ
  /-- **Correctness (a theorem, not a contract):** the gate sends each
      basis vector `|k⟩` to `|ccxPerm k⟩`. -/
  basis_action : ∀ k : Fin 8,
    gate *ᵥ (fun j => if j = k then (1 : ℂ) else 0)
      = (fun i => if i = ccxPerm k then (1 : ℂ) else 0)

/-! ## §2. Two concrete schemes. -/

/-- **Scheme A — CCZ magic-state teleportation.**  Consumes one `|CCZ⟩`
    magic state; the realised gate is `H_c · CCZ · H_c`. -/
noncomputable def cczTeleportScheme : ToffoliScheme where
  name         := "CCZ-magic-state teleportation"
  magicTCost   := 0
  magicCCZCost := 1
  gate         := Had3 * cczMat * Had3
  basis_action := fun k => by
    rw [had_ccz_had_eq_ccxPermMat]; exact ccxPermMat_mulVec_basis k

/-- **Scheme B — 8T→CCZ.**  Consumes eight `|T⟩` states (the seven-T
    phase polynomial + catalyst); the realised gate is
    `H_c · (8T→CCZ) · H_c`. -/
noncomputable def eightTScheme : ToffoliScheme where
  name         := "8T-to-CCZ (seven-T phase polynomial)"
  magicTCost   := 8
  magicCCZCost := 0
  gate         := Had3 * tDecompMat * Had3
  basis_action := fun k => by
    rw [had_tDecomp_had_eq_ccxPermMat]; exact ccxPermMat_mulVec_basis k

/-- Both schemes realise the **same** Toffoli unitary — they differ only
    in magic-resource accounting. -/
theorem schemes_realise_same_gate :
    cczTeleportScheme.gate = eightTScheme.gate := by
  show Had3 * cczMat * Had3 = Had3 * tDecompMat * Had3
  rw [tDecompMat_eq_cczMat]

/-! ## §3. Bridge to the Boolean `Gate.applyNat (CCX)` semantics. -/

/-- The 3-bit register state encoded by basis index `k`: qubit `0 ↦ a`,
    `1 ↦ b`, `2 ↦ c` (and `false` elsewhere). -/
def bitfun (k : Fin 8) : Nat → Bool :=
  fun i => if i = 0 then aOf k else if i = 1 then bOf k else if i = 2 then cOf k else false

/-- **The bridge.**  Reading the Toffoli-permuted basis index `ccxPerm k`
    out in bits is exactly `Gate.applyNat (Gate.CCX 0 1 2)` applied to
    the bits of `k`.  So every `ToffoliScheme` (whose `basis_action`
    sends `|k⟩` to `|ccxPerm k⟩`) computes the Boolean Toffoli on the
    3-qubit register — the action that the PPM layer formerly *assumed*
    of `teleportCCXRel`. -/
theorem scheme_implements_gate_applyNat (k : Fin 8) :
    bitfun (ccxPerm k) = Gate.applyNat (Gate.CCX 0 1 2) (bitfun k) := by
  have hb := ccxPerm_is_boolean_toffoli k
  simp only [Prod.mk.injEq] at hb
  obtain ⟨ha, hbb, hcc⟩ := hb
  funext i
  simp only [Gate.applyNat_CCX]
  by_cases h2 : i = 2
  · subst h2
    rw [update_eq]
    simp only [bitfun]
    norm_num [hcc]
  · rw [update_neq _ _ _ _ h2]
    by_cases h0 : i = 0
    · subst h0; simp only [bitfun]; norm_num [ha]
    · by_cases h1 : i = 1
      · subst h1; simp only [bitfun]; norm_num [hbb]
      · simp only [bitfun, if_neg h0, if_neg h1, if_neg h2]

/-- Headline: the 8T→CCZ scheme computes the Boolean Toffoli. -/
theorem eightTScheme_implements_boolean_toffoli (k : Fin 8) :
    bitfun (ccxPerm k) = Gate.applyNat (Gate.CCX 0 1 2) (bitfun k) :=
  scheme_implements_gate_applyNat k

end FormalRV.Framework.ToffoliScheme
