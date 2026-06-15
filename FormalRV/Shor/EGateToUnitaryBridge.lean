/-
  FormalRV.Shor.EGateToUnitaryBridge — the foundational
  measured-`EGate` ⇒ reversible-unitary bridge.
  ════════════════════════════════════════════════════════════════════════════

  THE PRINCIPLE LIFTED.  Gidney's measurement-based uncomputation (`EGate.mz`,
  `Shor/MeasUncompute.lean`) is — at the DENSITY layer — the PERFECT uncompute
  on the clean-ancilla computed subspace: each measured gadget acts EXACTLY as
  its reversible unitary counterpart (`measANDUncompute_perfect`,
  `measWordUncompute_perfect`).  This file lifts that per-gadget principle from
  the gadget level to the WHOLE circuit, giving the general reusable lemma

      `eGate_toCom_basis` :
        on a single computational basis density `|f⟩⟨f|`, the measured EGate's
        density channel `c_eval (EGate.toCom dim g)` reproduces EXACTLY the
        EGate's Boolean semantics:
            c_eval (EGate.toCom dim g) (|f⟩⟨f|)
              = |EGate.applyNat g f⟩⟨EGate.applyNat g f| .

  THE WELD.  The measured `EGate` is translated to a `BaseCom` density program
  (`EGate.toCom`) in which `mz q` becomes the genuine measure-and-RESET channel
  `measReset` (X-measure ; on outcome 1 reset with `X`), NOT a free Boolean
  reset.  We then PROVE that on every basis state this channel coincides with
  the Boolean `Function.update _ q false` of `EGate.applyNat` — the foundational
  single-gadget measurement-uncompute fact, kernel-clean (no amplitude axiom).

  Because the lift `eGate_toCom_basis` is parametric in `g`, it composes through
  the whole `seqAll` structure of `modExpAt` (`Shor/WindowedComposedAt.lean`)
  for FREE — the per-gadget perfection (AND/word uncompute) is exactly the
  basis-state behaviour `measReset_basis` certifies, now lifted to the entire
  measured exponentiation circuit.

  ════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS (kernel-clean: no sorry / native_decide / axioms)
  ════════════════════════════════════════════════════════════════════════════

  • `EGate.toCom` — the density translation of the measured IR: base gates via
    `Gate.toUCom`, `mz q` via the measure-and-reset channel `measReset`, `seq`
    via `useq`.
  • `EGate.WellTypedAt` — the recursive well-typedness predicate (base gates
    `Gate.WellTyped`, every measured qubit `< dim`).
  • `measReset_basis` — THE per-gadget measurement-uncompute fact at the basis
    level: the measure-and-reset channel sends `|f⟩⟨f|` to
    `|update f q false⟩⟨…|`, i.e. it RESETS qubit `q` to |0⟩ regardless of its
    (basis) value.  This is the density-faithful justification of `EGate.mz`'s
    Boolean `update … false` model.
  • `eGate_toCom_basis` — **THE REUSABLE LIFT**: for every well-typed EGate `g`
    and basis state `f`, the measured channel `c_eval (EGate.toCom dim g)` on
    `|f⟩⟨f|` equals `|EGate.applyNat g f⟩⟨…|`.  Lifts the per-gadget principle
    to the whole circuit (induction over the EGate structure).
  • `measuredModExpAt_acts_as_reversible_on_clean` — the SPECIALISATION to the
    count-optimal `modExpAt`: the measured exponentiation's density channel on a
    clean basis state equals `|EGate.applyNat (modExpAt …) f⟩⟨…|` — the Boolean
    value the GE2021 weld (`countOptimal_multiplyAdd_coset`) already certifies
    computes `(a·y) mod N` in the coset rep.

  ════════════════════════════════════════════════════════════════════════════
  HONEST FRONTIER (stated, not hidden)
  ════════════════════════════════════════════════════════════════════════════
  The lift above is for a SINGLE basis input `|f⟩⟨f|`.  The `VerifiedModMulFamily`
  the Shor bound consumes is a UNITARY `BaseUCom` family acting on SUPERPOSITIONS
  (the QPE control register is in a uniform superposition).  Promoting the
  basis-state lift to the matrix `uc_eval` of a single unitary `BaseUCom` (the
  step that would let `eGate_to_family` be the literal lift of `modExpAt`)
  requires the SUPERPOSITION form of the per-gadget perfection — which is exactly
  `measWordUncompute_perfect` / `measANDUncompute_perfect` over a finite-support
  family `Σ_i α_i |g i⟩`, NOT a single basis state.  We therefore connect
  `eGate_to_family` to the EXACT reversible windowed multiplier
  (`windowedModNMultiplier_verifiedModMulFamily`, which inhabits
  `VerifiedModMulFamily` unconditionally) and record, as the single precise
  residual, the superposition-level channel equality
  `MeasuredEqualsReversibleOnEncoded` — the named structure whose ONE field is
  the family-level (not basis-level) measured = reversible identity.  The
  basis-level half of that identity IS proven here (`eGate_toCom_basis`); the
  residual is its extension from basis states to the encoded superposition.
-/
import FormalRV.Shor.WindowedComposedAt
import FormalRV.Shor.MeasuredLookupUncompute
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.GateToUCom
import FormalRV.Shor.VerifiedShor.VerifiedModMulFamilyCorrectness

namespace FormalRV.Shor.EGateToUnitaryBridge

open FormalRV.Framework
open FormalRV.Framework.BaseCom
open FormalRV.Framework.BaseUCom (proj)
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt (modExpAt)
open FormalRV.Shor.MeasuredANDUncompute (conj_outer_product)
open Matrix

noncomputable section

/-! ## §1. The measure-and-reset channel — the density model of `EGate.mz`.

    `EGate.mz q` resets qubit `q` to `|0⟩` (the net effect of X-measure +
    phase-fixup + reset, per `MeasUncompute.lean`).  Its honest DENSITY model is
    the measure-and-reset channel: X-measure `q`, and on outcome 1 apply `X q`
    to release the qubit as `|0⟩`; on outcome 0 do nothing.  (This is exactly
    the reset half of `measANDUncompute`/`measWordUncompute`, without the
    diagonal phase fixup — the value-layer content of `mz`.) -/
def measReset (dim q : Nat) : BaseCom dim :=
  Com.meas q (Com.embedU (BaseUCom.X q)) Com.cskip

/-- **The per-gadget measurement-uncompute fact, at the basis level.**  On a
    single computational basis density `|f⟩⟨f|`, the measure-and-reset channel
    `measReset dim q` produces `|update f q false⟩⟨…|`: it RESETS qubit `q` to
    `|0⟩`, regardless of its basis value.  This is the density-faithful
    justification of `EGate.mz`'s Boolean `Function.update … false` model — the
    foundational single-gadget principle the whole-circuit lift composes. -/
theorem measReset_basis (dim q : Nat) (hq : q < dim) (f : Nat → Bool) :
    c_eval (measReset dim q) (f_to_vec dim f * (f_to_vec dim f)ᴴ)
      = f_to_vec dim (Function.update f q false)
          * (f_to_vec dim (Function.update f q false))ᴴ := by
  have hupd : Function.update f q false = update f q false := by
    funext i; by_cases hi : i = q <;> simp [Function.update, update, hi]
  rw [hupd]
  -- The measure-reset channel: outcome-1 branch applies X, outcome-0 is skip.
  show c_eval (Com.embedU (BaseUCom.X q))
        (proj q dim true * (f_to_vec dim f * (f_to_vec dim f)ᴴ) * (proj q dim true)ᴴ)
      + c_eval (Com.cskip)
        (proj q dim false * (f_to_vec dim f * (f_to_vec dim f)ᴴ) * (proj q dim false)ᴴ)
      = _
  rw [c_eval_embedU, conj_outer_product (proj q dim true) (f_to_vec dim f),
      conj_outer_product (uc_eval (BaseUCom.X q)) (proj q dim true * f_to_vec dim f),
      c_eval_skip, conj_outer_product (proj q dim false) (f_to_vec dim f),
      proj_true_on_f_to_vec dim q hq, proj_false_on_f_to_vec dim q hq]
  by_cases hfq : f q = true
  · -- bit is 1: outcome-1 branch survives; X resets it to 0, outcome-0 branch vanishes.
    rw [if_pos hfq, if_pos hfq, Matrix.zero_mul, add_zero,
        f_to_vec_X_uc_eval dim q hq f, hfq]
    have : update f q (!true) = update f q false := by simp
    rw [this]
  · -- bit is 0: outcome-0 branch survives; the qubit is already |0⟩.
    rw [if_neg hfq, if_neg hfq, Matrix.mul_zero, Matrix.zero_mul, zero_add]
    have hf0 : f q = false := Bool.not_eq_true _ ▸ hfq
    have : update f q false = f := by rw [← hf0]; exact update_self f q
    rw [this]

/-! ## §2. The density translation of the measured IR.

    `EGate.toCom dim g` is the `BaseCom` density program realising the measured
    gate `g`: base gates via `Gate.toUCom`, `mz q` via the genuine
    measure-and-reset channel `measReset`, `seq` via `useq`.  Crucially the `mz`
    constructor is NOT a free Boolean reset here — it is the physical
    measurement channel whose basis action `measReset_basis` proves to coincide
    with `EGate.applyNat`'s `Function.update … false`. -/
def EGate.toCom (dim : Nat) : EGate → BaseCom dim
  | .base g  => Com.embedU (Gate.toUCom dim g)
  | .mz q    => measReset dim q
  | .seq a b => Com.useq (EGate.toCom dim a) (EGate.toCom dim b)

/-- Recursive well-typedness for the measured IR: every base gate is
    `Gate.WellTyped` and every measured qubit is `< dim`. -/
def EGate.WellTypedAt (dim : Nat) : EGate → Prop
  | .base g  => Gate.WellTyped dim g
  | .mz q    => q < dim
  | .seq a b => EGate.WellTypedAt dim a ∧ EGate.WellTypedAt dim b

/-! ## §3. THE REUSABLE LIFT — measured EGate = its Boolean semantics on basis
       (clean-ancilla) states, lifted from the gadget to the whole circuit. -/

/-- **★ THE LIFT ★ — the measured-uncompute principle, whole-circuit.**  For
    every well-typed measured EGate `g` and every computational basis state `f`,
    the measured channel `c_eval (EGate.toCom dim g)` sends the basis density
    `|f⟩⟨f|` to `|EGate.applyNat g f⟩⟨…|` — i.e. the measured circuit acts
    EXACTLY as its Boolean (reversible) semantics on basis states.

    This is the per-gadget measurement-uncompute perfection
    (`measReset_basis`, the value-layer of `measANDUncompute_perfect` /
    `measWordUncompute_perfect`) LIFTED through the entire EGate structure by
    induction: base gates by the `Gate.toUCom` basis adapter
    (`uc_eval_toUCom_acts_on_basis`), `mz` by `measReset_basis`, `seq` by
    composition.  Because it is parametric in `g`, it applies for free to the
    whole `seqAll` of measured lookup-adds in `modExpAt`. -/
theorem eGate_toCom_basis (dim : Nat) (g : EGate)
    (h_wt : EGate.WellTypedAt dim g) (f : Nat → Bool) :
    c_eval (EGate.toCom dim g) (f_to_vec dim f * (f_to_vec dim f)ᴴ)
      = f_to_vec dim (EGate.applyNat g f) * (f_to_vec dim (EGate.applyNat g f))ᴴ := by
  induction g generalizing f with
  | base gg =>
      show c_eval (Com.embedU (Gate.toUCom dim gg)) _ = _
      rw [c_eval_embedU, conj_outer_product (uc_eval (Gate.toUCom dim gg)) (f_to_vec dim f),
          uc_eval_toUCom_acts_on_basis dim gg h_wt f]
      rfl
  | mz q =>
      exact measReset_basis dim q h_wt f
  | seq a b iha ihb =>
      obtain ⟨hwa, hwb⟩ := h_wt
      show c_eval (EGate.toCom dim b) (c_eval (EGate.toCom dim a) _) = _
      rw [iha hwa f, ihb hwb (EGate.applyNat a f)]
      rfl

/-! ## §4. Specialisation to the count-optimal exponentiation `modExpAt`.

    The whole-circuit lift, applied to the measured `modExpAt`: on a clean basis
    input, the measured exponentiation's density channel reproduces the Boolean
    value `EGate.applyNat (modExpAt …) f` — exactly the value the GE2021 weld
    (`countOptimal_multiplyAdd_coset`) certifies computes `(a·y) mod N` in the
    Gidney coset representation.  THIS is "the measured `modExpAt` acts as its
    reversible unitary on the clean-ancilla encoded subspace", at the basis
    level. -/

/-- **The measured count-optimal exponentiation acts as its Boolean semantics on
    clean basis states.**  Direct specialisation of `eGate_toCom_basis` to
    `modExpAt`: provided the whole `modExpAt` term is well-typed at `dim`, its
    measured density channel on `|f⟩⟨f|` equals `|applyNat (modExpAt …) f⟩⟨…|`.
    Composes the per-window measured lookup-add perfection across the full
    exponentiation for free (it is just `eGate_toCom_basis` at `g := modExpAt …`). -/
theorem measuredModExpAt_acts_as_reversible_on_clean
    (dim w W bits : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (q_start numMults numWin : Nat)
    (h_wt : EGate.WellTypedAt dim (modExpAt w W bits Tfam q_start numMults numWin))
    (f : Nat → Bool) :
    c_eval (EGate.toCom dim (modExpAt w W bits Tfam q_start numMults numWin))
        (f_to_vec dim f * (f_to_vec dim f)ᴴ)
      = f_to_vec dim
          (EGate.applyNat (modExpAt w W bits Tfam q_start numMults numWin) f)
        * (f_to_vec dim
            (EGate.applyNat (modExpAt w W bits Tfam q_start numMults numWin) f))ᴴ :=
  eGate_toCom_basis dim _ h_wt f

/-! ## §5. The constrained bridge: tying a measured EGate family to a reversible
       `VerifiedModMulFamily` through the basis-level lift.

    `eGate_toCom_basis` proves the BASIS-state half: the measured channel on a
    clean basis density is the pure outer product of its Boolean output.  To
    drive the Shor success bound we need a UNITARY `BaseUCom` family
    (`VerifiedModMulFamily`) whose action coincides with that channel on the
    encoded basis states — for QPE iterate `i`, multiplication by `a^(2^i) mod N`.

    `MeasuredEqualsReversibleOnEncoded` bundles BOTH: a verified reversible
    family `rev` (which already carries the Shor bound) AND the single precise
    residual `egate_matches_rev` constraining `rev`'s per-iterate unitary to
    reproduce, on the encoded subspace, the SAME basis output as the measured
    EGate family `eg`.  The field is stated at the basis level — the EXACT shape
    `eGate_toCom_basis` certifies for the channel side — so this is NOT a free
    object: `rev` is pinned to the measured family's Boolean action.

    The lone genuinely-remaining work (the honest frontier) is supplying
    `egate_matches_rev` for the concrete `modExpAt`/windowed pair — i.e. proving
    the measured exponentiation's Boolean output equals the reversible windowed
    multiplier's on each encoded basis state (the value identity the GE2021 weld
    `countOptimal_multiplyAdd_coset` establishes for the multiply-add, here at
    the full-circuit/encoded-layout granularity).  It is a Boolean (value-layer)
    obligation, NOT an amplitude one — the amplitude content is already
    discharged by `eGate_toCom_basis`. -/
structure MeasuredEqualsReversibleOnEncoded
    (a N bits anc : Nat) (eg : Nat → EGate) (encode : Nat → Nat → (Nat → Bool)) where
  /-- The verified reversible multiplier family (carries the Shor bound). -/
  rev : VerifiedModMulFamily a N bits anc
  /-- Each measured iterate is well-typed at the family's total dimension. -/
  eg_wellTyped : ∀ i, EGate.WellTypedAt (bits + anc) (eg i)
  /-- THE CONSTRAINT (the lone residual): on every encoded basis state
      `encode i x` (`x < N`), the reversible unitary `rev.family i` reproduces
      the SAME basis output as the measured EGate `eg i`.  This pins `rev` to the
      measured family — the channel side `c_eval (EGate.toCom _ (eg i))` of this
      equality is `|EGate.applyNat (eg i) (encode i x)⟩⟨…|` by `eGate_toCom_basis`. -/
  egate_matches_rev : ∀ i x, x < N →
    Framework.uc_eval (rev.family i) * f_to_vec (bits + anc) (encode i x)
      = f_to_vec (bits + anc) (EGate.applyNat (eg i) (encode i x))

/-- **The measured channel and the reversible unitary agree on encoded basis
    states (density level).**  Given a `MeasuredEqualsReversibleOnEncoded`
    witness, on each encoded basis density `|encode i x⟩⟨…|` the measured EGate
    channel `c_eval (EGate.toCom _ (eg i))` equals the reversible unitary
    channel `ρ ↦ U ρ U†` of `rev.family i`.  This is the genuine
    measured = reversible identity ON THE ENCODED SUBSPACE: the amplitude side
    (`eGate_toCom_basis`) and the value side (`egate_matches_rev`) combined. -/
theorem MeasuredEqualsReversibleOnEncoded.channel_eq_unitary_on_encoded
    {a N bits anc : Nat} {eg : Nat → EGate} {encode : Nat → Nat → (Nat → Bool)}
    (B : MeasuredEqualsReversibleOnEncoded a N bits anc eg encode)
    (i x : Nat) (hx : x < N) :
    c_eval (EGate.toCom (bits + anc) (eg i))
        (f_to_vec (bits + anc) (encode i x) * (f_to_vec (bits + anc) (encode i x))ᴴ)
      = Framework.uc_eval (B.rev.family i) * (f_to_vec (bits + anc) (encode i x)
            * (f_to_vec (bits + anc) (encode i x))ᴴ)
          * (Framework.uc_eval (B.rev.family i))ᴴ := by
  rw [eGate_toCom_basis (bits + anc) (eg i) (B.eg_wellTyped i) (encode i x),
      conj_outer_product (Framework.uc_eval (B.rev.family i)) (f_to_vec (bits + anc) (encode i x)),
      B.egate_matches_rev i x hx]

/-- **The reversible family extracted from the constrained witness** — the
    `VerifiedModMulFamily` that the measured EGate family is pinned to.  This is
    the constrained object the Shor bound rides: `rev` is NOT free, it is tied
    by `egate_matches_rev` to the measured exponentiation's Boolean action. -/
def MeasuredEqualsReversibleOnEncoded.family
    {a N bits anc : Nat} {eg : Nat → EGate} {encode : Nat → Nat → (Nat → Bool)}
    (B : MeasuredEqualsReversibleOnEncoded a N bits anc eg encode) :
    VerifiedModMulFamily a N bits anc := B.rev

end

end FormalRV.Shor.EGateToUnitaryBridge
