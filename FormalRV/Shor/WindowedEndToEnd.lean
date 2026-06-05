/-
  FormalRV.Shor.WindowedEndToEnd — the windowed Shor pipeline, BOTH axes verified,
  bundled honestly in one place.

  ## What is CLOSED (kernel-clean, `[propext, Classical.choice, Quot.sound]`)

  • **SEMANTICS — the full Shor success theorem.**
    `WindowedShorConnection.windowed_shor_correct`: the windowed modular-multiplier QPE family
    achieves `probability_of_success ≥ κ / (log₂ N)⁴`.  This is the END-TO-END semantic
    composition — not merely "computes `a·x mod N`", but the actual Shor success-probability
    bound — assembled from the proven in-place round-trip
    (`windowedInplaceModMulGate_roundTrip`: `|x⟩|0⟩ ↦ |(c·x)%N⟩|0⟩`), the two SWAP cascades
    (`swapTargetWindows_h_tw`, `windowed_unload_concrete`), full well-typedness, and the
    modular-inverse arithmetic.  Nothing is `sorry`/axiom/`native_decide`.

  • **RESOURCES — the paper-matched Toffoli count.**
    `WindowedComposed.toffoli_modExp`: the full modular exponentiation composed from the
    babbush lookup-addition Gidney implements has Toffoli count
    `numMults · 2 · numWin · ((2^w − 1) + 2·bits)`, bridged to the paper's reported total by
    `WindowedComposedCost.total_gap` / `rsa2048_head_to_head` (RSA-2048: 2 578 993 152 vs the
    paper's 2 622 824 448, gap fully attributed to runway-folding + rounding).

  ## The HONEST unification nuance

  The two results are proven on two circuit *variants*:
    - SEMANTICS rides on `windowedInplaceModMulGate` (SQIR-Cuccaro + `windowed2SelectedAddGate`,
      a modular adder per window).
    - the paper-optimal COUNT rides on `modExp` (the babbush `unaryQROM` lookup-addition).
  Giving the *count-optimal* babbush circuit the *same* Shor-success guarantee requires one
  further fact, named precisely below (`BabbushLookupAddValueSpec`) and NOT faked: the general
  `applyNat` correctness of `babbushLookupAdd` (that on a basis state it nets the accumulator
  update `acc ↦ acc + T[address]`).  This is the EGate / measurement-uncompute analogue of the
  proven Gate-level `Lookup.unary_lookup_iteration_correct`, and is the single remaining bridge.
-/
import FormalRV.Shor.WindowedShorConnection
import FormalRV.Shor.WindowedComposed
import FormalRV.Shor.WindowedComposedCost

namespace FormalRV.Shor.WindowedEndToEnd

open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.Shor.WindowedComposed
open FormalRV.Shor.MeasUncompute

/-- **★ Windowed Shor — BOTH axes, one statement.**  For the standard Shor sizing/setting (plus
    the base modular inverse `a·ainv0 % N = 1`), the windowed pipeline delivers simultaneously:

    (A) **semantics** — the verified windowed modular-multiplier family hits the canonical Shor
        success-probability bound `≥ κ / (log₂ N)⁴` (`windowed_shor_correct`); and

    (B) **resources** — the babbush-composed modular exponentiation has the structural Toffoli
        count `numMults · 2 · numWin · ((2^w − 1) + 2·bits)` (`toffoli_modExp`), the count whose
        bridge to the paper's `0.3 n³` is proven in `WindowedComposedCost`.

    Each conjunct cites its own kernel-clean proof; this theorem simply records that the windowed
    construction is verified on *both* axes at once. -/
theorem windowed_shor_verified_both_axes
    (a r N m bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1) (h_setting : ShorSetting a r N m bits)
    (w numMults numWin W : Nat) (T : Nat → Nat) :
    probability_of_success a r N m bits anc
        (windowedModMulFamily a N bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4
    ∧ EGate.toffoli (modExp w W bits T numMults numWin)
        = numMults * 2 * numWin * ((2 ^ w - 1) + 2 * bits) :=
  ⟨windowed_shor_correct a r N m bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc h_inv0 h_setting,
   toffoli_modExp w W bits T numMults numWin⟩

/-! ## The single remaining unification fact (named, NOT faked).

`babbushLookupAdd` is `unaryQROM` (babbush read) · Cuccaro add · measure-clear.  The audit found
NO general `applyNat` correctness for it (only `native_decide` smoke-tests at `w = 2`).  The exact
fact needed to give the count-optimal babbush multiplier full Shor semantics is the per-primitive
value spec below — once it (plus a shared-accumulator layout rebuild of `modExp`) is in hand, the
babbush circuit inhabits `EncodeRoundTripModMul` and inherits `windowed_shor_correct`'s bound. -/

/-- **Named obligation.**  A decoder `dec`/encoder for the accumulator and address registers makes
    `babbushLookupAdd` realise one modular-lookup-add step of `windowedLookupFold`: on a basis
    state whose accumulator decodes to `acc` and whose address decodes to `addr`, the gate's
    `applyNat` leaves an accumulator decoding to `acc + T[addr]` (the Cuccaro non-modular add of the
    looked-up word), with the output/ancilla registers cleared.  This is the EGate /
    measurement-uncompute analogue of `Lookup.unary_lookup_iteration_correct` (proven, Gate-level).
    Stated as an explicit obligation, deliberately un-instantiated. -/
structure BabbushLookupAddValueSpec
    (w W : Nat) (T : Nat → Nat) (bits addrBase ancBase outBase q_start : Nat)
    (decAcc decAddr : (Nat → Bool) → Nat) where
  step : ∀ (f : Nat → Bool),
    decAcc (EGate.applyNat (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) f)
      = decAcc f + T (decAddr f)

/-- **Conditional unification.**  Granting the per-primitive value spec for `babbushLookupAdd`
    (`BabbushLookupAddValueSpec`), a single babbush lookup-add advances the accumulator by exactly
    the `windowedLookupFold` step `tableValue` when the address decodes to the relevant window.
    This is the elementary half of the unification; the global fold + coset-mod reduction then
    transfer via the already-proven `WindowedArith.windowedLookupFold_*` identities. -/
theorem babbush_step_matches_fold
    {w W : Nat} {T : Nat → Nat} {bits addrBase ancBase outBase q_start : Nat}
    {decAcc decAddr : (Nat → Bool) → Nat}
    (spec : BabbushLookupAddValueSpec w W T bits addrBase ancBase outBase q_start decAcc decAddr)
    (f : Nat → Bool) :
    decAcc (EGate.applyNat (babbushLookupAdd w W T bits addrBase ancBase outBase q_start) f)
      = decAcc f + T (decAddr f) :=
  spec.step f

end FormalRV.Shor.WindowedEndToEnd
