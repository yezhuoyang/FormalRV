/- WindowedShorConnection — Â§5-5c tightened residual + in-place composition glue.
   Part of the `WindowedShorConnection` re-export shim (same namespace). -/
import FormalRV.Shor.WindowedShorConnection.ForwardGate

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §5. The tightened residual: only the in-place completion.

    With the forward half proven, the residual obligation reduces to
    a single completion gate `complete c` that maps the windowed
    output `windowed2Input ((c*x)%N) … (b0_of_x x)(b1_of_x x) …`
    back to `encodeDataZeroAnc bits anc ((c*x)%N)` — i.e. uncompute
    the window registers (which still hold `x`) and move the result
    into the data register.  This is the windowed in-place wrapper
    (compute → swap → uncompute-via-inverse).  It is NOT instantiated
    here; per the project's hard rules it is a named, un-faked
    obligation, not a `sorry`. -/
structure WindowedCompletion (N bits anc : Nat) where
  /-- The in-place completion gate, per multiplier constant `c`. -/
  complete : Nat → Gate
  /-- The full composite (proven forward ; completion) is well-typed. -/
  wellTyped : ∀ c,
    Gate.WellTyped (bits + anc) (Gate.seq (windowedForwardGate c N bits) (complete c))
  /-- The completion maps the windowed output back to the canonical
      `encodeDataZeroAnc` layout, for every constant `c` invertible mod `N`
      (witnessed by some `d` with `(c*d) % N = 1`).  THIS is the one open
      circuit fact.  The invertibility guard is NOT a weakening of the
      intended contract but a soundness necessity (exactly as on
      `EncodeRoundTripModMul.roundTrip`): the composite
      `windowedForwardGate ; complete` is well-typed, hence acts injectively
      on basis states, yet via `windowedForwardGate_apply` an unguarded
      completion would force it to realize `x ↦ (c*x) % N`, which is
      non-injective on `[0,N)` for non-invertible `c` (e.g. `c = 0` collapses
      `0` and `1`) — so an unguarded round-trip would make the structure
      uninhabitable for every composite `N ≥ 2`.  Shor only ever instantiates
      `c := a^(2^i)` with `a` invertible mod `N`, so the guard is free at the
      use site (see `toEncodeRoundTripModMul`). -/
  roundTrip : ∀ c x, x < N → (∃ d, (c * d) % N = 1) →
    Gate.applyNat (complete c)
        (windowed2Input ((c * x) % N) (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) (wnumWin bits))
      = encodeDataZeroAnc bits anc ((c * x) % N)

/-- A `WindowedCompletion` yields an `EncodeRoundTripModMul`: the
    composite `forward ; complete` round-trips `encodeDataZeroAnc`,
    using the PROVEN `windowedForwardGate_apply` for the forward half
    and the completion's `roundTrip` for the rest. -/
noncomputable def WindowedCompletion.toEncodeRoundTripModMul
    {N bits anc : Nat} (W : WindowedCompletion N bits anc)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc) :
    EncodeRoundTripModMul N bits anc where
  gate := fun c => Gate.seq (windowedForwardGate c N bits) (W.complete c)
  wellTyped := W.wellTyped
  roundTrip := by
    intro c x hx hc
    rw [Gate.applyNat_seq,
        windowedForwardGate_apply c N bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx]
    exact W.roundTrip c x hx hc

/-- **HEADLINE bound from the windowed circuit, modulo the in-place
    completion.** Composing §3 with §5: once the windowed in-place
    completion gate is verified, the full Shor success-probability
    bound `≥ κ / (log₂ N)^4` holds for the windowed multiplier
    family.  The forward half is already proven
    (`windowedForwardGate_apply`); only `WindowedCompletion` remains. -/
theorem shor_correct_of_windowedCompletion
    {N bits anc : Nat} (W : WindowedCompletion N bits anc)
    (a r m : Nat) (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (ainv0 : Nat) (hN1 : 1 < N) (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        ((W.toEncodeRoundTripModMul hbits h_even hN_pos hN hN2 h_anc_pos).toVerifiedModMulFamily
          a hN ainv0 hN1 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  shor_correct_of_encodeRoundTrip
    (W.toEncodeRoundTripModMul hbits h_even hN_pos hN hN2 h_anc_pos) a r m hN
    ainv0 hN1 h_inv0 h_setting

/-! ## §5b. Gap 1 — the in-place multiplier composition (the hard glue).

    The in-place windowed multiplier realising `x ↦ (c*x)%N` in the
    `encodeDataZeroAnc` layout is the 5-stage gate

      windowedForwardGate(c)        -- encodeDataZeroAnc x ↦ windowed2Input ((c*x)%N) (windows=x)
      ; tw                          -- SWAP target↔windows: ↦ windowed2Input x (windows=(c*x)%N)
      ; selectedAdd((N-ainv)%N)     -- clears x: ↦ windowed2Input 0 (windows=(c*x)%N)
      ; windowedSwapLoadAdapter     -- UNLOAD: ↦ encodeDataZeroAnc ((c*x)%N)

    The theorem below proves the FULL round-trip of this gate,
    reusing:
      * `windowedForwardGate_apply` (§4, PROVEN) for stages 1-2,
      * `toyWindowed2SelectedAddGate_state_mul_correct` (PROVEN,
        window-preserving selected-add) for stage 3,
      * `windowed2Value_of_x_mod` (PROVEN) to decode the window value,
      * `modmult_inverse_clear_arith` (PROVEN, ModMult.lean
        §, q_start-independent) for the modular-inverse cancellation
        `(x + (N-ainv)·((c·x)%N)) % N = 0`.

    It is stated CONDITIONAL on exactly TWO swap-correctness lemmas,
    `h_tw` and `h_unload` — the genuinely-remaining windowed circuit
    facts (the SWAP-target↔windows gate and the SWAP unloader).  Both
    are clean disjoint-SWAP cascades; their correctness is the
    last-mile residual.  They are honest hypotheses, NOT `sorry`s. -/
theorem windowedInplaceModMul_roundTrip
    (tw : Gate) (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1)
    (h_tw : ∀ acc w, acc < 2 ^ bits → w < 2 ^ bits →
       Gate.applyNat tw
           (windowed2Input acc (wb0Idx bits) (wb1Idx bits)
             (windowed2_b0_of_x w) (windowed2_b1_of_x w) (wnumWin bits))
         = windowed2Input w (wb0Idx bits) (wb1Idx bits)
             (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) (wnumWin bits))
    (h_unload : ∀ y, y < 2 ^ bits →
       Gate.applyNat
           (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
           (windowed2Input 0 (wb0Idx bits) (wb1Idx bits)
             (windowed2_b0_of_x y) (windowed2_b1_of_x y) (wnumWin bits))
         = encodeDataZeroAnc bits anc y) :
    Gate.applyNat
        (Gate.seq (windowedForwardGate c N bits)
          (Gate.seq tw
            (Gate.seq
              (windowed2SelectedAddGate
                (toyWindow2SelectedAddStateSpecImpl ((N - ainv) % N) N).toSelectedAddSpec
                bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
              (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits)))))
        (encodeDataZeroAnc bits anc x)
      = encodeDataZeroAnc bits anc ((c * x) % N) := by
  have hx_pow : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have hcx : (c * x) % N < N := Nat.mod_lt _ hN_pos
  have hcx_pow : (c * x) % N < 2 ^ bits := Nat.lt_of_lt_of_le hcx hN
  have h_numWin : 2 * wnumWin bits = bits := by
    unfold wnumWin; exact Nat.mul_div_cancel' h_even
  simp only [Gate.applyNat_seq]
  -- Stages 1-2 (forward): encodeDataZeroAnc x ↦ windowed2Input ((c*x)%N) (windows = x).
  rw [windowedForwardGate_apply c N bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx]
  -- Stage 3 (tw): ↦ windowed2Input x (windows = (c*x)%N).
  rw [h_tw ((c * x) % N) x hcx_pow hx_pow]
  -- Stage 4 (selected-add by (N-ainv)%N): accumulate into the x target.
  rw [toyWindowed2SelectedAddGate_state_mul_correct bits N ((N - ainv) % N) 0
        (wnumWin bits) x (wb0Idx bits) (wb1Idx bits)
        (windowed2_b0_of_x ((c * x) % N)) (windowed2_b1_of_x ((c * x) % N))
        hbits hN_pos hN hN2 hx
        (by decide) (by decide) (by unfold sqir_modmult_rev_anc; omega)
        (by intro i _; unfold wb0Idx; omega)
        (by intro i _; unfold wb1Idx; omega)
        (by intro i _; unfold wb0Idx wb1Idx; omega)
        (by intro i _; unfold wb0Idx; omega)
        (by intro i _; unfold wb1Idx; omega)
        (by intro i j _ _ _; unfold wb0Idx; omega)
        (by intro i j _ _ _; unfold wb0Idx wb1Idx; omega)
        (by intro i j _ _ _; unfold wb1Idx wb0Idx; omega)
        (by intro i j _ _ _; unfold wb1Idx; omega)]
  -- Decode the window value: windowed2Value (bits of (c*x)%N) = (c*x)%N.
  rw [windowed2Value_of_x_mod, h_numWin, Nat.mod_eq_of_lt hcx_pow]
  -- Modular-inverse cancellation: (x + (N-ainv)·((c*x)%N)) % N = 0.
  rw [modmult_inverse_clear_arith N c ainv x hN_pos hx h_ainv_le h_inv]
  -- Stage 5 (unload): windowed2Input 0 (windows = (c*x)%N) ↦ encodeDataZeroAnc ((c*x)%N).
  rw [h_unload ((c * x) % N) hcx_pow]

/-! ## §5c. `h_unload` reduces to `windowedSwapLoadAdapter` being an
       involution.

    `windowedSwapLoadAdapter` is a product of disjoint transpositions,
    hence self-inverse.  Granting that involution, the unload step is
    just the loader run a second time on the loaded state — exactly
    the `forward + involution ⇒ reverse` pattern the codebase already
    uses for `encode_to_mult_adapter_reverse`
    (`reverse_register_swap_involution_general`).

    This lemma discharges `h_unload` from the single hypothesis
    `h_invol`, reducing the remaining gap-1 residual on the unload
    side to proving `windowedSwapLoadAdapter_involutive` (the direct
    analogue of `reverse_register_swap_involution_general`, which is
    an already-achieved proof pattern in this codebase). -/
theorem windowedUnload_of_involutive
    (bits anc numWin y : Nat) (b0Idx b1Idx : Nat → Nat)
    (hy : y < 2 ^ bits) (h_anc_pos : 0 < anc) (h_numWin_exact : 2 * numWin = bits)
    (h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_distinct_b0_b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_distinct_b0_b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_distinct_b1_b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_distinct_b1_b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j)
    (h_invol : ∀ f, Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) f) = f) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (windowed2Input 0 b0Idx b1Idx (windowed2_b0_of_x y) (windowed2_b1_of_x y) numWin)
      = encodeDataZeroAnc bits anc y := by
  have h_fwd := windowedSwapLoadAdapter_apply_encodeDataZeroAnc bits anc numWin y b0Idx b1Idx
    hy h_anc_pos h_numWin_exact h_b0_above h_b1_above h_b0_ne_b1
    h_distinct_b0_b0 h_distinct_b0_b1 h_distinct_b1_b0 h_distinct_b1_b1
  rw [← h_fwd]
  exact h_invol (encodeDataZeroAnc bits anc y)


end FormalRV.BQAlgo.WindowedShorConnection
