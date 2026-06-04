/-
  FormalRV.BQAlgo.WindowedShorConnection — wiring the
  windowed-arithmetic modular multiplier up to the HEADLINE
  Shor success-probability theorem.

  ## What this file proves (honest scope)

  The headline theorem `Shor_correct_verified_no_modmult_axioms`
  currently rides on the SQIR-faithful (Pipeline B) multiplier.
  The windowed-arithmetic (Pipeline C) chain culminating in
  `VerifiedShor.windowedSwapLoadAdapter_then_selectedAdd_apply_clean`
  is fully proven but ends in a `windowed2Input` output layout and
  is NOT yet connected to the headline.

  This file supplies the **connecting reduction**, proven and
  kernel-clean:

    * `EncodeRoundTripModMul N bits anc` — the precise residual
      obligation: a gate family that, per multiplier constant `c`,
      round-trips the canonical `encodeDataZeroAnc` layout
      (`x ↦ (c*x) % N`) and is well-typed.
    * `EncodeRoundTripModMul.toVerifiedModMulFamily` — turns any
      such obligation into the framework's reusable
      `VerifiedShor.VerifiedModMulFamily` contract, by reusing the
      existing matrix-level MCP bridge
      (`toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc`)
      and the well-typedness bridge
      (`uc_well_typed_toUCom_of_Gate_WellTyped`).
    * `shor_correct_of_encodeRoundTrip` — the HEADLINE
      success-probability bound `≥ κ / (log₂ N)^4` for the family,
      via `VerifiedModMulFamily.shorCorrect`.

  In other words: **every layer above the `encodeDataZeroAnc`
  round-trip is reusable**, so connecting the windowed multiplier
  to Shor reduces *exactly* to inhabiting `EncodeRoundTripModMul`
  with the windowed circuit.

  ## What remains (the genuinely-missing windowed circuit fact)

  `windowed_residual_target` and the docstring on
  `WindowedToEncodeRoundTrip` state the precise remaining work to
  inhabit `EncodeRoundTripModMul` from the proven windowed forward
  gate.  Per the project's hard rules we do NOT fake it with a
  `sorry` or a tautological closure; it is named as an explicit
  structure (analogous to `TFactoryToffoliObligation`) and left
  un-instantiated.  The three missing pieces are:

    1. An in-place wrapper (compute into a workspace accumulator,
       SWAP into the data register, then windowed-uncompute the
       original `x` using the inverse `c⁻¹ mod N`) — the windowed
       analogue of `sqir_modmult_inplace_candidate`.
    2. The output/uncompute adapter mapping the `windowed2Input`
       layout back to `encodeDataZeroAnc` (clearing the window
       registers, moving the result to the data register).
    3. Coverage of odd `bits` (the proven apex requires
       `2 * numWin = bits`, i.e. `bits` even; the headline uses
       `bits = Nat.log2 (2*N) + 1`).

  ## Honesty tier (per CLAUDE.md)

  - The reduction theorems below are **Verified** (semantic, not
    arithmetic-only): `mmi` invokes the matrix-vector MCP semantics
    via the existing bridge; `shorCorrect` is the real Shor
    success-probability theorem.
  - The windowed→`EncodeRoundTripModMul` step is **Scaffolded /
    open**: stated precisely, not proven, not faked.
-/
import FormalRV.Shor.VerifiedShor
import FormalRV.Arithmetic.MCPBridge
import FormalRV.Arithmetic.SQIRModMult

namespace FormalRV.BQAlgo.WindowedShorConnection

open FormalRV.SQIRPort
open FormalRV.Framework (Gate)
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed

/-! ## §1. The residual obligation: an `encodeDataZeroAnc`-layout
       modular multiplier family.

    This is the SINGLE interface the windowed (or any) circuit must
    meet to plug into the headline Shor theorem.  `gate c` is the
    compiled multiply-by-`c`-mod-`N` circuit in the canonical
    data+ancilla layout; `roundTrip` is its Boolean
    `Gate.applyNat` correctness in that layout. -/
structure EncodeRoundTripModMul (N bits anc : Nat) where
  /-- The multiply-by-`c` gate, indexed by the multiplier constant. -/
  gate : Nat → Gate
  /-- Each gate is well-typed at the total dimension `bits + anc`. -/
  wellTyped : ∀ c, Gate.WellTyped (bits + anc) (gate c)
  /-- Boolean correctness in the `encodeDataZeroAnc` layout:
      `|x⟩|0⟩ ↦ |(c*x) % N⟩|0⟩` for every `x < N`. -/
  roundTrip : ∀ c x, x < N →
    Gate.applyNat (gate c) (encodeDataZeroAnc bits anc x)
      = encodeDataZeroAnc bits anc ((c * x) % N)

/-! ## §2. Reduction: obligation ⟹ `VerifiedModMulFamily`.

    For QPE iterate `i` the family must multiply by `a^(2^i)`; we
    instantiate `gate` at the raw constant `a^(2^i)` so the
    round-trip target `((a^(2^i)) * x) % N` matches
    `MultiplyCircuitProperty (a^(2^i)) …` on the nose. -/
noncomputable def EncodeRoundTripModMul.toVerifiedModMulFamily
    {N bits anc : Nat} (W : EncodeRoundTripModMul N bits anc)
    (a : Nat) (hN : N ≤ 2 ^ bits) :
    VerifiedModMulFamily a N bits anc where
  family := fun i => Gate.toUCom (bits + anc) (W.gate (a ^ (2 ^ i)))
  mmi := by
    intro i
    exact toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc
      (W.wellTyped (a ^ (2 ^ i))) hN
      (fun x hx => W.roundTrip (a ^ (2 ^ i)) x hx)
  wellTyped := by
    intro i
    exact uc_well_typed_toUCom_of_Gate_WellTyped (bits + anc)
      (W.gate (a ^ (2 ^ i))) (W.wellTyped (a ^ (2 ^ i)))

/-! ## §3. The headline connection. -/

/-- **Connection theorem.** Any `encodeDataZeroAnc`-round-trip
    modular multiplier family yields the canonical Shor
    success-probability bound `≥ κ / (log₂ N)^4`.

    This is the wiring the windowed pipeline needs: it shows that
    *everything above the round-trip is already done*, so the
    windowed multiplier's only remaining job is to inhabit
    `EncodeRoundTripModMul`. -/
theorem shor_correct_of_encodeRoundTrip
    {N bits anc : Nat} (W : EncodeRoundTripModMul N bits anc)
    (a r m : Nat) (hN : N ≤ 2 ^ bits)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        (W.toVerifiedModMulFamily a hN).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (W.toVerifiedModMulFamily a hN).shorCorrect r m h_setting

/-! ## §4. Concrete windowed layout + the PROVEN forward gate.

    We pin the windowed circuit to a concrete ancilla layout so the
    proven apex
    `VerifiedShor.Windowed.windowedSwapLoadAdapter_then_selectedAdd_apply_clean`
    instantiates with all ~20 layout/distinctness hypotheses
    discharged.  This turns the windowed forward half into a
    standalone *proven* lemma `windowedForwardGate_apply`, narrowing
    the residual from "wire windowed arithmetic into Shor" to a
    single in-place completion gate. -/

/-- Number of windowSize-2 windows for a `bits`-wide register. -/
def wnumWin (bits : Nat) : Nat := bits / 2

/-- `b0` (even) window-register index for window `k`: placed just
    above the Cuccaro workspace `[0, 2*bits+3)`. -/
def wb0Idx (bits : Nat) : Nat → Nat := fun k => 2 * bits + 3 + 2 * k

/-- `b1` (odd) window-register index for window `k`. -/
def wb1Idx (bits : Nat) : Nat → Nat := fun k => 2 * bits + 4 + 2 * k

/-- The PROVEN windowed forward gate for multiplier constant `c`:
    SWAP-load `x` into the window registers, then run the
    multi-window selected-add.  Output is in `windowed2Input`
    layout. -/
noncomputable def windowedForwardGate (c N bits : Nat) : Gate :=
  Gate.seq
    (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
    (windowed2SelectedAddGate
      (toyWindow2SelectedAddStateSpecImpl c N).toSelectedAddSpec
      bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits))

/-- **Forward half — PROVEN.** At the concrete layout above, the
    windowed forward gate maps `encodeDataZeroAnc bits anc x` to the
    `windowed2Input` state with accumulator `(c*x) % N` and the
    window registers still holding `x`'s bits.  This is the apex
    `windowedSwapLoadAdapter_then_selectedAdd_apply_clean` with every
    layout/distinctness hypothesis discharged by `omega` (flag at 0,
    `b0Idx k = 2·bits+3+2k`, `b1Idx k = 2·bits+4+2k`,
    `numWin = bits/2`).

    Requires `bits` even (`2 ∣ bits`) for exact window coverage
    `2·numWin = bits`. -/
theorem windowedForwardGate_apply
    (c N bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits)
    (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_anc_pos : 0 < anc) (hx : x < N) :
    Gate.applyNat (windowedForwardGate c N bits) (encodeDataZeroAnc bits anc x)
      = windowed2Input ((c * x) % N) (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x x) (windowed2_b1_of_x x) (wnumWin bits) := by
  have hx_pow : x < 2 ^ bits := Nat.lt_of_lt_of_le hx hN
  have h_numWin : 2 * wnumWin bits = bits := by
    unfold wnumWin; exact Nat.mul_div_cancel' h_even
  unfold windowedForwardGate
  rw [windowedSwapLoadAdapter_then_selectedAdd_apply_clean
        bits anc (wnumWin bits) x N c 0 (wb0Idx bits) (wb1Idx bits)
        hx_pow h_anc_pos h_numWin hbits hN_pos hN hN2
        (by decide) (by decide)
        (by unfold sqir_modmult_rev_anc; omega)
        (by intro k _; unfold wb0Idx; omega)
        (by intro k _; unfold wb1Idx; omega)
        (by intro k _; unfold wb0Idx wb1Idx; omega)
        (by intro k _; unfold wb0Idx; omega)
        (by intro k _; unfold wb1Idx; omega)
        (by intro i j _ _ hij; unfold wb0Idx; omega)
        (by intro i j _ _ _; unfold wb0Idx wb1Idx; omega)
        (by intro i j _ _ _; unfold wb1Idx wb0Idx; omega)
        (by intro i j _ _ hij; unfold wb1Idx; omega)]
  rw [Nat.mod_eq_of_lt hx_pow]

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
      `encodeDataZeroAnc` layout.  THIS is the one open circuit fact. -/
  roundTrip : ∀ c x, x < N →
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
    intro c x hx
    rw [Gate.applyNat_seq,
        windowedForwardGate_apply c N bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx]
    exact W.roundTrip c x hx

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
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        ((W.toEncodeRoundTripModMul hbits h_even hN_pos hN hN2 h_anc_pos).toVerifiedModMulFamily
          a hN).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  shor_correct_of_encodeRoundTrip
    (W.toEncodeRoundTripModMul hbits h_even hN_pos hN hN2 h_anc_pos) a r m hN h_setting

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
      * `sqir_modmult_inverse_clear_arith` (PROVEN, SQIRModMult.lean
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
  rw [sqir_modmult_inverse_clear_arith N c ainv x hN_pos hx h_ainv_le h_inv]
  -- Stage 5 (unload): windowed2Input 0 (windows = (c*x)%N) ↦ encodeDataZeroAnc ((c*x)%N).
  rw [h_unload ((c * x) % N) hcx_pow]

/-! ## §5c. `h_unload` reduces to `windowedSwapLoadAdapter` being an
       involution.

    `windowedSwapLoadAdapter` is a product of disjoint transpositions,
    hence self-inverse.  Granting that involution, the unload step is
    just the loader run a second time on the loaded state — exactly
    the `forward + involution ⇒ reverse` pattern the codebase already
    uses for `sqir_encode_to_mult_adapter_reverse`
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

/-! ## §5d. Foundational atoms for `windowedSwapLoadAdapter_involutive`.

    `windowedSwapLoadAdapter` is a product of disjoint transpositions,
    so it is self-inverse — the involution `h_invol` that §5c needs.
    The two lemmas here are the verified building blocks of that proof
    (the remaining assembly — an update-frame induction, the
    swap/loader commutation, and the involution induction — follows
    the established `reverse_register_swap_involution_general`
    template and is the next dedicated step). -/

/-- A single `qubit_swap` is an involution (its own inverse). -/
theorem qubit_swap_involutive (a b : Nat) (f : Nat → Bool) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) (Gate.applyNat (qubit_swap a b) f) = f := by
  rw [qubit_swap_correct a b f hab, qubit_swap_correct a b _ hab]
  funext r
  by_cases hrb : r = b <;> by_cases hra : r = a <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- A `qubit_swap` commutes with an `update` at a position disjoint
    from both swapped qubits.  This is the frame property that lets
    the loader's swaps slide past updates on data/window registers —
    the inductive engine of the loader involution. -/
theorem qubit_swap_update_comm (a b p : Nat) (v : Bool) (h : Nat → Bool)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b) :
    Gate.applyNat (qubit_swap a b) (FormalRV.Framework.update h p v)
      = FormalRV.Framework.update (Gate.applyNat (qubit_swap a b) h) p v := by
  rw [qubit_swap_correct a b _ hab, qubit_swap_correct a b h hab]
  have hap := hpa.symm; have hbp := hpb.symm
  funext x
  by_cases hxp : x = p <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- **Update-frame for the SWAP loader.** `windowedSwapLoadAdapter`
    commutes with an `update` at a position `p` disjoint from all of
    its source/window positions.  This is the inductive engine of the
    loader involution: it lets a disjoint update slide through the
    whole swap cascade.  Proven by induction on `numWin` using
    `qubit_swap_update_comm`. -/
theorem windowedSwapLoadAdapter_update_frame
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin p : Nat) (v : Bool) (g : Nat → Bool)
    (h_src0_ne_b0 : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne_b1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (h_p_ne_src0 : ∀ k, k < numWin → p ≠ bits - 1 - 2 * k)
    (h_p_ne_src1 : ∀ k, k < numWin → p ≠ bits - 1 - (2 * k + 1))
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (FormalRV.Framework.update g p v)
      = FormalRV.Framework.update
          (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) p v := by
  revert h_src0_ne_b0 h_src1_ne_b1 h_p_ne_src0 h_p_ne_src1 h_p_ne_b0 h_p_ne_b1 g
  induction numWin with
  | zero => intro g _ _ _ _ _ _; rfl
  | succ n ih =>
    intro g h_src0_ne_b0 h_src1_ne_b1 h_p_ne_src0 h_p_ne_src1 h_p_ne_b0 h_p_ne_b1
    have hlt : n < n + 1 := Nat.lt_succ_self n
    simp only [windowedSwapLoadAdapter_succ, Gate.applyNat_seq]
    rw [ih g (fun k hk => h_src0_ne_b0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_src1_ne_b1 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_src0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_src1 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
          (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))]
    rw [qubit_swap_update_comm (bits - 1 - 2 * n) (b0Idx n) p v _
          (h_p_ne_src0 n hlt) (h_p_ne_b0 n hlt) (h_src0_ne_b0 n hlt)]
    rw [qubit_swap_update_comm (bits - 1 - (2 * n + 1)) (b1Idx n) p v _
          (h_p_ne_src1 n hlt) (h_p_ne_b1 n hlt) (h_src1_ne_b1 n hlt)]

/-- **Loader commutes with a disjoint swap.** `windowedSwapLoadAdapter`
    (over windows `0..numWin-1`) commutes with `qubit_swap a b` when
    `a, b` are disjoint from all of the loader's source/window
    positions.  Proven from the update-frame (both swapped values
    slide through the loader) plus `preserves_disjoint` (the loader
    leaves `a, b` fixed).  This is the step that lets each new
    window's swap block move past the recursive loader in the
    involution induction. -/
theorem windowedSwapLoadAdapter_comm_swap
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin a b : Nat) (g : Nat → Bool)
    (hab : a ≠ b)
    (h_src0_ne_b0 : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne_b1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k)
    (ha_src0 : ∀ k, k < numWin → a ≠ bits - 1 - 2 * k)
    (ha_src1 : ∀ k, k < numWin → a ≠ bits - 1 - (2 * k + 1))
    (ha_b0 : ∀ k, k < numWin → a ≠ b0Idx k)
    (ha_b1 : ∀ k, k < numWin → a ≠ b1Idx k)
    (hb_src0 : ∀ k, k < numWin → b ≠ bits - 1 - 2 * k)
    (hb_src1 : ∀ k, k < numWin → b ≠ bits - 1 - (2 * k + 1))
    (hb_b0 : ∀ k, k < numWin → b ≠ b0Idx k)
    (hb_b1 : ∀ k, k < numWin → b ≠ b1Idx k) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
        (Gate.applyNat (qubit_swap a b) g)
      = Gate.applyNat (qubit_swap a b)
          (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) := by
  rw [qubit_swap_correct a b g hab]
  rw [windowedSwapLoadAdapter_update_frame bits b0Idx b1Idx numWin b (g a) _
        h_src0_ne_b0 h_src1_ne_b1 hb_src0 hb_src1 hb_b0 hb_b1]
  rw [windowedSwapLoadAdapter_update_frame bits b0Idx b1Idx numWin a (g b) _
        h_src0_ne_b0 h_src1_ne_b1 ha_src0 ha_src1 ha_b0 ha_b1]
  rw [qubit_swap_correct a b
        (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) g) hab]
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx a numWin g
        h_src0_ne_b0 h_src1_ne_b1 ha_src0 ha_src1 ha_b0 ha_b1]
  rw [windowedSwapLoadAdapter_preserves_disjoint bits b0Idx b1Idx b numWin g
        h_src0_ne_b0 h_src1_ne_b1 hb_src0 hb_src1 hb_b0 hb_b1]

/-- Two `qubit_swap`s on four pairwise-distinct positions commute. -/
theorem qubit_swap_comm (a b c d : Nat) (g : Nat → Bool)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Gate.applyNat (qubit_swap a b) (Gate.applyNat (qubit_swap c d) g)
      = Gate.applyNat (qubit_swap c d) (Gate.applyNat (qubit_swap a b) g) := by
  rw [qubit_swap_correct c d g hcd, qubit_swap_correct a b g hab,
      qubit_swap_correct a b _ hab, qubit_swap_correct c d _ hcd]
  have hba := hab.symm; have hdc := hcd.symm; have hca := hac.symm
  have hda := had.symm; have hcb := hbc.symm; have hdb := hbd.symm
  funext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    by_cases hxd : x = d <;>
    simp_all [FormalRV.Framework.update_eq, FormalRV.Framework.update_neq]

/-- **The SWAP loader is an involution (self-inverse).** Applying
    `windowedSwapLoadAdapter` twice is the identity, because it is a
    product of pairwise-disjoint transpositions.  Proven by induction
    on `numWin`: the new window's swap block commutes past the
    recursive loader (`windowedSwapLoadAdapter_comm_swap`), the
    recursive call cancels by the induction hypothesis, and the two
    window swaps cancel via `qubit_swap_comm` + `qubit_swap_involutive`.

    This is the `h_invol` hypothesis required by
    `windowedUnload_of_involutive` (§5c), and hence — at the concrete
    layout — discharges the gap-1 `h_unload` obligation. -/
theorem windowedSwapLoadAdapter_involutive
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_2numWin : 2 * numWin ≤ bits)
    (h_b0_above : ∀ k, k < numWin → bits ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → bits ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j)
    (f : Nat → Bool) :
    Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin)
      (Gate.applyNat (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) f) = f := by
  revert h_2numWin h_b0_above h_b1_above h_b0_ne_b1
    h_dist_b0b0 h_dist_b0b1 h_dist_b1b0 h_dist_b1b1 f
  induction numWin with
  | zero => intro _ _ _ _ _ _ _ _ f; rfl
  | succ n ih =>
    intro h_2numWin h_b0_above h_b1_above h_b0_ne_b1
      h_dist_b0b0 h_dist_b0b1 h_dist_b1b0 h_dist_b1b1 f
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have ihn := ih (by omega)
      (fun k hk => h_b0_above k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b1_above k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_b0_ne_b1 k (Nat.lt_succ_of_lt hk))
      (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
      f
    simp only [windowedSwapLoadAdapter_succ, Gate.applyNat_seq]
    rw [windowedSwapLoadAdapter_comm_swap bits b0Idx b1Idx n (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b1_above n hlt; omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by omega)
          (fun k hk => by omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above n hlt; omega)
          (fun k hk => by have := h_b1_above n hlt; omega)
          (fun k hk => h_dist_b1b0 n k hlt (Nat.lt_succ_of_lt hk) (by omega))
          (fun k hk => h_dist_b1b1 n k hlt (Nat.lt_succ_of_lt hk) (by omega))]
    rw [windowedSwapLoadAdapter_comm_swap bits b0Idx b1Idx n (bits - 1 - 2 * n) (b0Idx n) _
          (by have := h_b0_above n hlt; omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by omega)
          (fun k hk => by omega)
          (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
          (fun k hk => by have := h_b0_above n hlt; omega)
          (fun k hk => by have := h_b0_above n hlt; omega)
          (fun k hk => h_dist_b0b0 n k hlt (Nat.lt_succ_of_lt hk) (by omega))
          (fun k hk => h_dist_b0b1 n k hlt (Nat.lt_succ_of_lt hk) (by omega))]
    rw [ihn]
    rw [qubit_swap_comm (bits - 1 - 2 * n) (b0Idx n) (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b0_above n hlt; omega)
          (by have := h_b1_above n hlt; omega)
          (by omega)
          (by have := h_b1_above n hlt; omega)
          (by have := h_b0_above n hlt; omega)
          (h_b0_ne_b1 n hlt)]
    rw [qubit_swap_involutive (bits - 1 - 2 * n) (b0Idx n) _ (by have := h_b0_above n hlt; omega)]
    rw [qubit_swap_involutive (bits - 1 - (2 * n + 1)) (b1Idx n) _
          (by have := h_b1_above n hlt; omega)]

/-- **gap-1 `h_unload` — CLOSED at the concrete layout.** Combining
    `windowedUnload_of_involutive` (§5c) with the now-proven loader
    involution, with every disjointness/bound hypothesis discharged by
    `omega` at the layout `wb0Idx k = 2·bits+3+2k`,
    `wb1Idx k = 2·bits+4+2k`, `wnumWin = bits/2`.  Requires `2 ∣ bits`. -/
theorem windowed_unload_concrete (bits anc y : Nat)
    (h_even : 2 ∣ bits) (h_anc_pos : 0 < anc) (hy : y < 2 ^ bits) :
    Gate.applyNat (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowed2Input 0 (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x y) (windowed2_b1_of_x y) (wnumWin bits))
      = encodeDataZeroAnc bits anc y := by
  have h_numWin : 2 * wnumWin bits = bits := by unfold wnumWin; exact Nat.mul_div_cancel' h_even
  exact windowedUnload_of_involutive bits anc (wnumWin bits) y (wb0Idx bits) (wb1Idx bits)
    hy h_anc_pos h_numWin
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ hij => by unfold wb0Idx; omega)
    (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
    (fun i j _ _ hij => by unfold wb1Idx; omega)
    (fun g => windowedSwapLoadAdapter_involutive bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
      (by unfold wnumWin; omega)
      (fun k _ => by unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
      (fun k _ => by unfold wb0Idx wb1Idx; omega)
      (fun i j _ _ hij => by unfold wb0Idx; omega)
      (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
      (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
      (fun i j _ _ hij => by unfold wb1Idx; omega)
      g)

/-! ## §5e. Gap-1 `h_tw` — the target↔windows SWAP cascade.

    `swapTargetWindows` swaps each accumulator b-position with the
    matching window register: acc-bit `2k` (Cuccaro b-position `4k+3`)
    ↔ window-b0 `k`, and acc-bit `2k+1` (b-position `4k+5`) ↔
    window-b1 `k`, for `k < numWin`.  All `2·numWin` transpositions are
    pairwise disjoint (b-positions `< 4·numWin+2 ≤` window positions),
    so the cascade is a clean product of disjoint swaps — the windowed
    analogue of Gidney's `fig:multiply` final SWAP.  Proven by the same
    funext + read-lemma pattern as
    `windowedSwapLoadAdapter_apply_encodeDataZeroAnc`. -/

/-- The target↔windows SWAP cascade over windows `0..numWin-1`.  Each
    step swaps the two Cuccaro b-positions `4n+3 = 2·(2n)+3` and
    `4n+5 = 2·(2n+1)+3` (holding accumulator bits `2n`, `2n+1`) with the
    window registers `b0Idx n`, `b1Idx n`. -/
noncomputable def swapTargetWindows
    (b0Idx b1Idx : Nat → Nat) : Nat → Gate
  | 0 => Gate.I
  | n + 1 =>
      Gate.seq
        (swapTargetWindows b0Idx b1Idx n)
        (Gate.seq
          (qubit_swap (4 * n + 3) (b0Idx n))
          (qubit_swap (4 * n + 5) (b1Idx n)))

@[simp] theorem swapTargetWindows_succ
    (b0Idx b1Idx : Nat → Nat) (n : Nat) :
    swapTargetWindows b0Idx b1Idx (n + 1)
      = Gate.seq
          (swapTargetWindows b0Idx b1Idx n)
          (Gate.seq
            (qubit_swap (4 * n + 3) (b0Idx n))
            (qubit_swap (4 * n + 5) (b1Idx n))) := rfl

/-- **Frame property for the SWAP cascade.**  A position `p` disjoint
    from every source (`4k+3`, `4k+5`) and every window (`b0Idx k`,
    `b1Idx k`) passes through the cascade unchanged.  The window-above
    bounds make each swap well-formed.  Mirrors
    `windowedSwapLoadAdapter_preserves_disjoint`. -/
theorem swapTargetWindows_preserves_disjoint
    (b0Idx b1Idx : Nat → Nat) (numWin p : Nat) (f : Nat → Bool)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_p_ne_t0 : ∀ k, k < numWin → p ≠ 4 * k + 3)
    (h_p_ne_t1 : ∀ k, k < numWin → p ≠ 4 * k + 5)
    (h_p_ne_b0 : ∀ k, k < numWin → p ≠ b0Idx k)
    (h_p_ne_b1 : ∀ k, k < numWin → p ≠ b1Idx k) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f p = f p := by
  induction numWin generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have h_t1_ne_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_t0_ne_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_t1_ne_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_b1 n hlt)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_t1 n hlt)]
    rw [qubit_swap_correct _ _ _ h_t0_ne_b0n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_b0 n hlt)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_p_ne_t0 n hlt)]
    exact ih f
      (fun k hk => by have := h_b0_above k (Nat.lt_succ_of_lt hk); omega)
      (fun k hk => by have := h_b1_above k (Nat.lt_succ_of_lt hk); omega)
      (fun k hk => h_p_ne_t0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_t1 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b0 k (Nat.lt_succ_of_lt hk))
      (fun k hk => h_p_ne_b1 k (Nat.lt_succ_of_lt hk))

/-- At a position `q` disjoint from all window registers, `windowed2Input`
    agrees with its Cuccaro base `cuccaro_input_F 2 false 0 acc`.  (The
    window updates all slide off via `update_neq`.) -/
theorem windowed2Input_at_window_disjoint
    (acc : Nat) (b0Idx b1Idx : Nat → Nat) (b0 b1 : Nat → Bool) (numWin q : Nat)
    (h_b0_disj : ∀ k, k < numWin → q ≠ b0Idx k)
    (h_b1_disj : ∀ k, k < numWin → q ≠ b1Idx k) :
    windowed2Input acc b0Idx b1Idx b0 b1 numWin q = cuccaro_input_F 2 false 0 acc q := by
  induction numWin with
  | zero => rfl
  | succ n ih =>
    rw [windowed2Input_succ]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_b1_disj n (Nat.lt_succ_self n))]
    rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_disj n (Nat.lt_succ_self n))]
    exact ih (fun k hk => h_b0_disj k (Nat.lt_succ_of_lt hk))
             (fun k hk => h_b1_disj k (Nat.lt_succ_of_lt hk))

/-- The Cuccaro base `cuccaro_input_F 2 false 0 v` is `false` at any `q`
    that is not a low b-position `2t+3` (`t < bits`): the only non-false
    branch is the b-register, and an `acc < 2^bits` has no set bit at
    index `≥ bits`. -/
theorem cuccaro_base_false (bits v q : Nat) (hv : v < 2 ^ bits)
    (h_not_b : ∀ t, t < bits → q ≠ 2 * t + 3) :
    cuccaro_input_F 2 false 0 v q = false := by
  simp only [cuccaro_input_F]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · -- odd offset: b-register, index `(q-2-1)/2`
    have ht : q = 2 * ((q - 2 - 1) / 2) + 3 := by omega
    have hge : bits ≤ (q - 2 - 1) / 2 := by
      by_contra hlt
      push_neg at hlt
      exact h_not_b _ hlt ht
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hge))
  · -- even offset: a-register is `0`
    exact Nat.zero_testBit _

/-- **Read at source `4k+3`.**  The cascade carries the value at the
    window register `b0Idx k` to the accumulator b-position `4k+3`. -/
theorem swapTargetWindows_read_t0
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (4 * k + 3) = f (b0Idx k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
    rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ 4 * n + 5 by omega)]
    rw [qubit_swap_correct _ _ _ h_b0n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 3 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_eq]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (b0Idx n) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b0_above n hlt; omega)
        (fun j hj => by have := h_b0_above n hlt; omega)
        (fun j hj => h_dist_b0b0 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
        (fun j hj => h_dist_b0b1 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 3 ≠ 4 * n + 3 by omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at source `4k+5`.**  The cascade carries the value at the
    window register `b1Idx k` to the accumulator b-position `4k+5`. -/
theorem swapTargetWindows_read_t1
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (4 * k + 5) = f (b1Idx k) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
      rw [FormalRV.Framework.update_eq]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ ((h_b0_ne_b1 n hlt).symm)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx n ≠ 4 * n + 3 by have := h_b1_above n hlt; omega)]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (b1Idx n) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above n hlt; omega)
        (fun j hj => by have := h_b1_above n hlt; omega)
        (fun j hj => h_dist_b1b0 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
        (fun j hj => h_dist_b1b1 n j hlt (Nat.lt_succ_of_lt hj) (by omega))
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ b1Idx n by have := h_b1_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ 4 * n + 5 by omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * k + 5 ≠ 4 * n + 3 by omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at window `b0Idx k`.**  The cascade carries the accumulator
    b-position `4k+3` to the window register `b0Idx k`. -/
theorem swapTargetWindows_read_b0
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (b0Idx k) = f (4 * k + 3) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_b0_ne_b1 n hlt)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx n ≠ 4 * n + 5 by have := h_b0_above n hlt; omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_eq]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (4 * n + 3) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by omega)
        (fun j hj => by omega)
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b0b1 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx k ≠ 4 * n + 5 by have := h_b0_above k (Nat.lt_succ_of_lt hkn'); omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b0b0 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b0Idx k ≠ 4 * n + 3 by have := h_b0_above k (Nat.lt_succ_of_lt hkn'); omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => h_b0_ne_b1 j (Nat.lt_succ_of_lt hj))
        (fun i j hi hj hij => h_dist_b0b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b0b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **Read at window `b1Idx k`.**  The cascade carries the accumulator
    b-position `4k+5` to the window register `b1Idx k`. -/
theorem swapTargetWindows_read_b1
    (b0Idx b1Idx : Nat → Nat) (numWin k : Nat) (f : Nat → Bool) (hk : k < numWin)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin) f (b1Idx k) = f (4 * k + 5) := by
  induction numWin with
  | zero => omega
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ, Gate.applyNat_seq, Gate.applyNat_seq]
    have h_b1n : 4 * n + 5 ≠ b1Idx n := by have := h_b1_above n hlt; omega
    have h_b0n : 4 * n + 3 ≠ b0Idx n := by have := h_b0_above n hlt; omega
    rw [qubit_swap_correct _ _ _ h_b1n]
    by_cases hkn : k = n
    · rw [hkn]
      rw [FormalRV.Framework.update_eq]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ b0Idx n by have := h_b0_above n hlt; omega)]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show 4 * n + 5 ≠ 4 * n + 3 by omega)]
      exact swapTargetWindows_preserves_disjoint b0Idx b1Idx n (4 * n + 5) f
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by omega)
        (fun j hj => by omega)
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
    · have hkn' : k < n := by omega
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b1b1 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx k ≠ 4 * n + 5 by have := h_b1_above k (Nat.lt_succ_of_lt hkn'); omega)]
      rw [qubit_swap_correct _ _ _ h_b0n]
      rw [FormalRV.Framework.update_neq _ _ _ _ (h_dist_b1b0 k n (Nat.lt_succ_of_lt hkn') hlt (by omega))]
      rw [FormalRV.Framework.update_neq _ _ _ _ (show b1Idx k ≠ 4 * n + 3 by have := h_b1_above k (Nat.lt_succ_of_lt hkn'); omega)]
      exact ih hkn'
        (fun j hj => by have := h_b0_above j (Nat.lt_succ_of_lt hj); omega)
        (fun j hj => by have := h_b1_above j (Nat.lt_succ_of_lt hj); omega)
        (fun i j hi hj hij => h_dist_b1b0 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)
        (fun i j hi hj hij => h_dist_b1b1 i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) hij)

/-- **The target↔windows SWAP — PROVEN.**  Applying `swapTargetWindows`
    to a `windowed2Input` whose accumulator is `acc` and whose windows
    carry `w`'s bits yields the `windowed2Input` whose accumulator is `w`
    and whose windows carry `acc`'s bits.  This is the open `h_tw`
    hypothesis of `windowedInplaceModMul_roundTrip`, discharged at the
    abstract layout (window indices above all `4·numWin+1` sources,
    pairwise distinct).  Proven by funext + the read/frame lemmas. -/
theorem swapTargetWindows_apply
    (bits acc w : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_numWin : 2 * numWin = bits)
    (hacc : acc < 2 ^ bits) (hw : w < 2 ^ bits)
    (h_b0_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b0Idx k)
    (h_b1_above : ∀ k, k < numWin → 4 * numWin + 2 ≤ b1Idx k)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_dist_b0b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b0Idx j)
    (h_dist_b0b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b0Idx i ≠ b1Idx j)
    (h_dist_b1b0 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b0Idx j)
    (h_dist_b1b1 : ∀ i j, i < numWin → j < numWin → i ≠ j → b1Idx i ≠ b1Idx j) :
    Gate.applyNat (swapTargetWindows b0Idx b1Idx numWin)
        (windowed2Input acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w) numWin)
      = windowed2Input w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) numWin := by
  have hbpos0 : ∀ (v i : Nat), cuccaro_input_F 2 false 0 v (4 * i + 3) = v.testBit (2 * i) := by
    intro v i
    rw [show 4 * i + 3 = 2 + 2 * (2 * i) + 1 by ring]
    exact cuccaro_input_F_at_b 2 (2 * i) false 0 v
  have hbpos1 : ∀ (v i : Nat), cuccaro_input_F 2 false 0 v (4 * i + 5) = v.testBit (2 * i + 1) := by
    intro v i
    rw [show 4 * i + 5 = 2 + 2 * (2 * i + 1) + 1 by ring]
    exact cuccaro_input_F_at_b 2 (2 * i + 1) false 0 v
  have h_not_b : ∀ q, (∀ k, k < numWin → q ≠ 4 * k + 3) → (∀ k, k < numWin → q ≠ 4 * k + 5) →
      ∀ j, j < bits → q ≠ 2 * j + 3 := by
    intro q ht0 ht1 j hj
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · have htw : t < numWin := by omega
      have := ht0 t htw; omega
    · have htw : t < numWin := by omega
      have := ht1 t htw; omega
  funext q
  by_cases hb0 : ∃ k, k < numWin ∧ q = b0Idx k
  · obtain ⟨k, hk, rfl⟩ := hb0
    rw [swapTargetWindows_read_b0 b0Idx b1Idx numWin k _ hk
          h_b0_above h_b1_above h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
    rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin (4 * k + 3)
          (fun j hj => by have := h_b0_above j hj; omega)
          (fun j hj => by have := h_b1_above j hj; omega)]
    rw [hbpos0 acc k]
    rw [windowed2Input_read_b0_bounded w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc)
          numWin k hk h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
    rfl
  · push_neg at hb0
    by_cases hb1 : ∃ k, k < numWin ∧ q = b1Idx k
    · obtain ⟨k, hk, rfl⟩ := hb1
      rw [swapTargetWindows_read_b1 b0Idx b1Idx numWin k _ hk
            h_b0_above h_b1_above h_dist_b1b0 h_dist_b1b1]
      rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin (4 * k + 5)
            (fun j hj => by have := h_b0_above j hj; omega)
            (fun j hj => by have := h_b1_above j hj; omega)]
      rw [hbpos1 acc k]
      rw [windowed2Input_read_b1_bounded w b0Idx b1Idx (windowed2_b0_of_x acc) (windowed2_b1_of_x acc)
            numWin k hk h_dist_b0b1 h_dist_b1b1]
      rfl
    · push_neg at hb1
      by_cases ht0 : ∃ k, k < numWin ∧ q = 4 * k + 3
      · obtain ⟨k, hk, rfl⟩ := ht0
        rw [swapTargetWindows_read_t0 b0Idx b1Idx numWin k _ hk
              h_b0_above h_b1_above h_dist_b0b0 h_dist_b0b1]
        rw [windowed2Input_read_b0_bounded acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w)
              numWin k hk h_b0_ne_b1 h_dist_b0b0 h_dist_b0b1]
        rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin (4 * k + 3)
              (fun j hj => by have := h_b0_above j hj; omega)
              (fun j hj => by have := h_b1_above j hj; omega)]
        rw [hbpos0 w k]
        rfl
      · push_neg at ht0
        by_cases ht1 : ∃ k, k < numWin ∧ q = 4 * k + 5
        · obtain ⟨k, hk, rfl⟩ := ht1
          rw [swapTargetWindows_read_t1 b0Idx b1Idx numWin k _ hk
                h_b0_above h_b1_above h_b0_ne_b1 h_dist_b1b0 h_dist_b1b1]
          rw [windowed2Input_read_b1_bounded acc b0Idx b1Idx (windowed2_b0_of_x w) (windowed2_b1_of_x w)
                numWin k hk h_dist_b0b1 h_dist_b1b1]
          rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin (4 * k + 5)
                (fun j hj => by have := h_b0_above j hj; omega)
                (fun j hj => by have := h_b1_above j hj; omega)]
          rw [hbpos1 w k]
          rfl
        · push_neg at ht1
          rw [swapTargetWindows_preserves_disjoint b0Idx b1Idx numWin q _
                h_b0_above h_b1_above ht0 ht1 hb0 hb1]
          rw [windowed2Input_at_window_disjoint acc b0Idx b1Idx _ _ numWin q hb0 hb1]
          rw [windowed2Input_at_window_disjoint w b0Idx b1Idx _ _ numWin q hb0 hb1]
          rw [cuccaro_base_false bits acc q hacc (h_not_b q ht0 ht1)]
          rw [cuccaro_base_false bits w q hw (h_not_b q ht0 ht1)]

/-- **`h_tw` at the concrete windowed layout — CLOSED.**  Instantiates
    `swapTargetWindows_apply` at `wb0Idx`/`wb1Idx`/`wnumWin`, discharging
    every layout hypothesis by `omega` (using `2 ∣ bits` for
    `2·wnumWin = bits`).  This is exactly the open `h_tw` hypothesis of
    `windowedInplaceModMul_roundTrip` with
    `tw := swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits)`. -/
theorem swapTargetWindows_h_tw (bits acc w : Nat)
    (h_even : 2 ∣ bits) (hacc : acc < 2 ^ bits) (hw : w < 2 ^ bits) :
    Gate.applyNat (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowed2Input acc (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x w) (windowed2_b1_of_x w) (wnumWin bits))
      = windowed2Input w (wb0Idx bits) (wb1Idx bits)
          (windowed2_b0_of_x acc) (windowed2_b1_of_x acc) (wnumWin bits) := by
  have h_numWin : 2 * wnumWin bits = bits := by unfold wnumWin; exact Nat.mul_div_cancel' h_even
  exact swapTargetWindows_apply bits acc w (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
    h_numWin hacc hw
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ hij => by unfold wb0Idx; omega)
    (fun i j _ _ _ => by unfold wb0Idx wb1Idx; omega)
    (fun i j _ _ _ => by unfold wb1Idx wb0Idx; omega)
    (fun i j _ _ hij => by unfold wb1Idx; omega)

/-! ## §6. Gap 2 — the even-`bits` (parity) restriction is WLOG.

    `windowedForwardGate_apply` needs `2 ∣ bits` (windowSize-2 exact
    coverage `2·numWin = bits`).  We close this as a genuine
    non-restriction: the Shor data-register width is a free parameter,
    and for any `N` one can always pick an EVEN width that still
    satisfies both the sizing predicate and the (relaxed) Shor
    setting.  Hence requiring even `bits` costs nothing.

    These are real, kernel-clean lemmas (monotonicity of the two
    predicates in the register width, plus an even-width existence
    witness at `log₂(2N)+1` rounded up to even). -/

/-- The relaxed Shor setting only constrains the data width through
    `N < 2^n`, which is monotone in `n`; so it transfers to any wider
    register. -/
theorem BasicSettingRelaxed_bits_mono
    {a r N m n n' : Nat} (h : BasicSettingRelaxed a r N m n) (hle : n ≤ n') :
    BasicSettingRelaxed a r N m n' :=
  ⟨h.1, h.2.1, h.2.2.1,
    Nat.lt_of_lt_of_le h.2.2.2 (Nat.pow_le_pow_right (by omega) hle)⟩

/-- Verified-circuit sizing is monotone in the register width. -/
theorem VerifiedCircuitSizing_bits_mono
    {N n n' : Nat} (h : VerifiedCircuitSizing N n) (hle : n ≤ n') :
    VerifiedCircuitSizing N n' :=
  ⟨le_trans h.1 hle,
   le_trans h.2.1 (Nat.pow_le_pow_right (by omega) hle),
   le_trans h.2.2 (Nat.pow_le_pow_right (by omega) hle)⟩

/-- **Even-width sizing always exists.** For any `N > 0` there is an
    even data width satisfying `VerifiedCircuitSizing`.  Witness:
    `log₂(2N)+1` rounded up to even.  This discharges the `2 ∣ bits`
    hypothesis as a free choice. -/
theorem exists_even_bits_sizing (N : Nat) (hN : 0 < N) :
    ∃ bits, 2 ∣ bits ∧ VerifiedCircuitSizing N bits := by
  have h0 : VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) :=
    VerifiedCircuitSizing_canonical_pow2_succ N hN
  exact ⟨(Nat.log2 (2 * N) + 1) + (Nat.log2 (2 * N) + 1) % 2,
    by omega, VerifiedCircuitSizing_bits_mono h0 (by omega)⟩

/-- **Even-width setting always exists.** Given a relaxed Shor setting
    at some width, there is an even width `≥` it that satisfies both
    the setting and the sizing — the canonical instantiation point for
    the windowed family once its in-place completion (gap 1) lands. -/
theorem exists_even_bits_setting_sizing
    {a r N m n : Nat} (hN : 0 < N) (h_setting : BasicSettingRelaxed a r N m n) :
    ∃ bits, n ≤ bits ∧ 2 ∣ bits
      ∧ BasicSettingRelaxed a r N m bits ∧ VerifiedCircuitSizing N bits := by
  have h0 : VerifiedCircuitSizing N (Nat.log2 (2 * N) + 1) :=
    VerifiedCircuitSizing_canonical_pow2_succ N hN
  -- Round (max n (log₂(2N)+1)) up to even.
  set base := max n (Nat.log2 (2 * N) + 1) with hbase
  refine ⟨base + base % 2, by omega, by omega,
    BasicSettingRelaxed_bits_mono h_setting (by omega),
    VerifiedCircuitSizing_bits_mono h0 (by omega)⟩

/-! ## §7. The windowed in-place modular multiplier — UNCONDITIONAL.

    With `h_tw` (`swapTargetWindows_h_tw`) and `h_unload`
    (`windowed_unload_concrete`) both now proven, the 5-stage in-place
    composition `windowedInplaceModMul_roundTrip` becomes an
    UNCONDITIONAL Boolean round-trip of the canonical `encodeDataZeroAnc`
    layout: `|x⟩|0⟩ ↦ |(c·x) % N⟩|0⟩`.  This is the windowed (Pipeline C)
    analogue of `sqir_modmult_inplace_candidate`, and the exact
    `EncodeRoundTripModMul.roundTrip` obligation for the windowed
    multiplier (for any constant `c` equipped with a modular inverse
    `ainv`). -/

/-- The windowed in-place multiply-by-`c`-mod-`N` gate at the concrete
    layout: forward (load+selected-add) ; SWAP target↔windows ; clear `x`
    via selected-add by `(N-ainv)%N` ; unload.  `ainv` is `c`'s modular
    inverse. -/
noncomputable def windowedInplaceModMulGate (c N ainv bits : Nat) : Gate :=
  Gate.seq (windowedForwardGate c N bits)
    (Gate.seq (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
      (Gate.seq
        (windowed2SelectedAddGate
          (toyWindow2SelectedAddStateSpecImpl ((N - ainv) % N) N).toSelectedAddSpec
          bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
        (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits))))

/-- **The windowed in-place modular multiplier is correct — UNCONDITIONAL.**
    Discharges the two swap obligations of `windowedInplaceModMul_roundTrip`
    with the now-proven `swapTargetWindows_h_tw` and
    `windowed_unload_concrete`. -/
theorem windowedInplaceModMulGate_roundTrip
    (c N ainv bits anc x : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc_pos : 0 < anc)
    (hx : x < N) (h_ainv_le : ainv ≤ N) (h_inv : (c * ainv) % N = 1) :
    Gate.applyNat (windowedInplaceModMulGate c N ainv bits) (encodeDataZeroAnc bits anc x)
      = encodeDataZeroAnc bits anc ((c * x) % N) := by
  unfold windowedInplaceModMulGate
  exact windowedInplaceModMul_roundTrip
    (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits))
    c N ainv bits anc x hbits h_even hN_pos hN hN2 h_anc_pos hx h_ainv_le h_inv
    (fun acc w hacc hw => swapTargetWindows_h_tw bits acc w h_even hacc hw)
    (fun y hy => windowed_unload_concrete bits anc y h_even h_anc_pos hy)

/-! ## §8. Structural well-typedness of the windowed gates.

    The headline `VerifiedModMulFamily` needs each iterate well-typed at
    the total dimension `bits + anc`.  The two SWAP cascades
    (`windowedSwapLoadAdapter`, `swapTargetWindows`) are products of
    `qubit_swap`s, so their well-typedness follows by induction from
    `qubit_swap_wellTyped`.  These reduce the well-typedness of the full
    in-place gate to the single remaining structural obligation
    `windowed2SelectedAddGate_wellTyped`. -/

/-- The target↔windows SWAP cascade is well-typed when every source
    `4k+3`/`4k+5` and window `b0Idx k`/`b1Idx k` is below `dim` and each
    swap pair is distinct. -/
theorem swapTargetWindows_wellTyped
    (dim : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (h_dim_pos : 0 < dim)
    (h_t0 : ∀ k, k < numWin → 4 * k + 3 < dim)
    (h_t1 : ∀ k, k < numWin → 4 * k + 5 < dim)
    (h_b0 : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1 : ∀ k, k < numWin → b1Idx k < dim)
    (h_t0_ne_b0 : ∀ k, k < numWin → 4 * k + 3 ≠ b0Idx k)
    (h_t1_ne_b1 : ∀ k, k < numWin → 4 * k + 5 ≠ b1Idx k) :
    Gate.WellTyped dim (swapTargetWindows b0Idx b1Idx numWin) := by
  induction numWin with
  | zero => exact h_dim_pos
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [swapTargetWindows_succ]
    exact ⟨ih (fun k hk => h_t0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t0_ne_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_t1_ne_b1 k (Nat.lt_succ_of_lt hk)),
           qubit_swap_wellTyped dim _ _ (h_t0 n hlt) (h_b0 n hlt) (h_t0_ne_b0 n hlt),
           qubit_swap_wellTyped dim _ _ (h_t1 n hlt) (h_b1 n hlt) (h_t1_ne_b1 n hlt)⟩

/-- The SWAP loader cascade is well-typed when every data source
    `bits-1-2k`/`bits-1-(2k+1)` and window `b0Idx k`/`b1Idx k` is below
    `dim` and each swap pair is distinct. -/
theorem windowedSwapLoadAdapter_wellTyped
    (bits : Nat) (b0Idx b1Idx : Nat → Nat) (numWin dim : Nat)
    (h_dim_pos : 0 < dim)
    (h_src0 : ∀ k, k < numWin → bits - 1 - 2 * k < dim)
    (h_src1 : ∀ k, k < numWin → bits - 1 - (2 * k + 1) < dim)
    (h_b0 : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1 : ∀ k, k < numWin → b1Idx k < dim)
    (h_src0_ne : ∀ k, k < numWin → bits - 1 - 2 * k ≠ b0Idx k)
    (h_src1_ne : ∀ k, k < numWin → bits - 1 - (2 * k + 1) ≠ b1Idx k) :
    Gate.WellTyped dim (windowedSwapLoadAdapter bits b0Idx b1Idx numWin) := by
  induction numWin with
  | zero => exact h_dim_pos
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [windowedSwapLoadAdapter_succ]
    exact ⟨ih (fun k hk => h_src0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src0_ne k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_src1_ne k (Nat.lt_succ_of_lt hk)),
           qubit_swap_wellTyped dim _ _ (h_src0 n hlt) (h_b0 n hlt) (h_src0_ne n hlt),
           qubit_swap_wellTyped dim _ _ (h_src1 n hlt) (h_b1 n hlt) (h_src1_ne n hlt)⟩

/-! ## §8b. Well-typedness of the window selected-add (discharges `h_sel_wt`).

    The window selected-add cascade is well-typed at `bits + anc` for
    `anc ≥ 2·bits+11`.  Each window step `toyWindow2SelectedAddGate` is
    `Case1 ; Case2 ; Case3`, each a `[X] ; CCX ; controlled-mod-add ; CCX ; [X]`.
    The CCX/X positions (`flagIdx=0`, `wb0Idx`, `wb1Idx`) are bounded by
    `omega`; the controlled-mod-add `sqirCuccaroImpl.gate` is well-typed at
    `sqir_modmult_rev_anc bits = 3·bits+11` by `clean_wellTyped` (control
    `0 < 2`, `0 ≠ flagPos=1`, `tableValue < N`) and lifted to `bits+anc`
    by `Gate.WellTyped.mono`. -/

/-- One window's selected-add gate is well-typed: `Case1 ; Case2 ; Case3`,
    each a CCX-sandwiched controlled-mod-add. -/
theorem toyWindow2SelectedAddGate_wellTyped
    (dim bits N a k flagIdx b0Idx b1Idx : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ctrl_lo : flagIdx < 2) (h_ctrl_ne1 : flagIdx ≠ 1)
    (h_anc_le : sqir_modmult_rev_anc bits ≤ dim)
    (h_flag_lt : flagIdx < dim) (h_b0_lt : b0Idx < dim) (h_b1_lt : b1Idx < dim)
    (h_b0_ne_b1 : b0Idx ≠ b1Idx) (h_b0_ne_flag : b0Idx ≠ flagIdx) (h_b1_ne_flag : b1Idx ≠ flagIdx) :
    Gate.WellTyped dim (toyWindow2SelectedAddGate bits N a k flagIdx b0Idx b1Idx) := by
  have h_ctrl_lt_anc : flagIdx < sqir_modmult_rev_anc bits := by
    unfold sqir_modmult_rev_anc; omega
  have hccx : Gate.WellTyped dim (Gate.CCX b0Idx b1Idx flagIdx) :=
    ⟨h_b0_lt, h_b1_lt, h_flag_lt, h_b0_ne_b1, h_b0_ne_flag, h_b1_ne_flag⟩
  have h_modadd : ∀ v, Gate.WellTyped dim
      (ControlledModAdd.sqirCuccaroImpl.gate bits N (tableValue a N 2 k v) flagIdx) := fun v =>
    Gate.WellTyped.mono
      (ControlledModAdd.clean_wellTyped ControlledModAdd.sqirCuccaroImpl bits N
        (tableValue a N 2 k v) 0 flagIdx false hbits hN_pos hN hN2
        (tableValue_lt_N a N 2 k v hN_pos) hN_pos (Or.inl h_ctrl_lo) h_ctrl_ne1 h_ctrl_lt_anc)
      h_anc_le
  unfold toyWindow2SelectedAddGate toyWindow2Case1Gate toyWindow2Case2Gate toyWindow2Case3Gate
  exact ⟨⟨h_b1_lt, hccx, h_modadd 1, hccx, h_b1_lt⟩,
         ⟨h_b0_lt, hccx, h_modadd 2, hccx, h_b0_lt⟩,
         hccx, h_modadd 3, hccx⟩

/-- The multi-window selected-add cascade is well-typed (induction over
    `numWin`, each step by `toyWindow2SelectedAddGate_wellTyped`). -/
theorem windowed2SelectedAddGate_wellTyped
    (dim bits N a flagIdx : Nat) (b0Idx b1Idx : Nat → Nat) (numWin : Nat)
    (hbits : 1 ≤ bits) (hN_pos : 0 < N) (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_ctrl_lo : flagIdx < 2) (h_ctrl_ne1 : flagIdx ≠ 1)
    (h_anc_le : sqir_modmult_rev_anc bits ≤ dim) (h_flag_lt : flagIdx < dim)
    (h_b0_lt : ∀ k, k < numWin → b0Idx k < dim)
    (h_b1_lt : ∀ k, k < numWin → b1Idx k < dim)
    (h_b0_ne_b1 : ∀ k, k < numWin → b0Idx k ≠ b1Idx k)
    (h_b0_ne_flag : ∀ k, k < numWin → b0Idx k ≠ flagIdx)
    (h_b1_ne_flag : ∀ k, k < numWin → b1Idx k ≠ flagIdx) :
    Gate.WellTyped dim
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl a N).toSelectedAddSpec
        bits flagIdx b0Idx b1Idx numWin) := by
  induction numWin with
  | zero =>
    rw [windowed2SelectedAddGate_zero]
    show 0 < dim
    exact lt_of_lt_of_le (show 0 < sqir_modmult_rev_anc bits by unfold sqir_modmult_rev_anc; omega) h_anc_le
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    rw [windowed2SelectedAddGate_succ]
    exact ⟨ih (fun k hk => h_b0_lt k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1_lt k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0_ne_b1 k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b0_ne_flag k (Nat.lt_succ_of_lt hk))
              (fun k hk => h_b1_ne_flag k (Nat.lt_succ_of_lt hk)),
           toyWindow2SelectedAddGate_wellTyped dim bits N a n flagIdx (b0Idx n) (b1Idx n)
             hbits hN_pos hN hN2 h_ctrl_lo h_ctrl_ne1 h_anc_le h_flag_lt
             (h_b0_lt n hlt) (h_b1_lt n hlt) (h_b0_ne_b1 n hlt)
             (h_b0_ne_flag n hlt) (h_b1_ne_flag n hlt)⟩

/-- **`h_sel_wt` — CLOSED at the concrete layout.**  The window
    selected-add gate is well-typed at `bits + anc` for `anc ≥ 2·bits+11`,
    discharging the obligation the headline previously carried. -/
theorem windowedSelectedAdd_wellTyped_concrete
    (bits N anc : Nat) (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc) (c' : Nat) :
    Gate.WellTyped (bits + anc)
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl c' N).toSelectedAddSpec
        bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
  windowed2SelectedAddGate_wellTyped (bits + anc) bits N c' 0 (wb0Idx bits) (wb1Idx bits)
    (wnumWin bits) hbits hN_pos hN hN2 (by omega) (by omega)
    (by show sqir_modmult_rev_anc bits ≤ bits + anc; unfold sqir_modmult_rev_anc; omega)
    (by omega)
    (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
    (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
    (fun k _ => by unfold wb0Idx wb1Idx; omega)
    (fun k _ => by unfold wb0Idx; omega)
    (fun k _ => by unfold wb1Idx; omega)

/-! ## §9. The windowed multiplier family and the HEADLINE Shor bound — UNCONDITIONAL.

    All gate-level facts now proven, we package the windowed multiplier as a
    `VerifiedModMulFamily` and derive the headline success-probability bound
    `≥ κ / (log₂ N)^4` with **no remaining obligations**: the in-place
    round-trip (§5b–§7) and full well-typedness (§8/§8b) are both proven, and
    the modular-inverse side is discharged — at QPE iterate `i` the inverse is
    `ainv0^(2^i) % N` with `(a^(2^i) · (ainv0^(2^i)%N)) % N = 1` via
    `mul_pow_mod_one`; `ainv0` is `Order`'s modular inverse
    (`Order_modinv_correct`).  Requires `anc ≥ 2·bits+11` so the SQIR-Cuccaro
    workspace (`3·bits+11`) fits the dimension. -/

/-- Well-typedness of the full windowed in-place gate at `bits + anc`.
    The two SWAP cascades are discharged by §8 and the window selected-add by
    §8b (`windowedSelectedAdd_wellTyped_concrete`); `anc ≥ 2·bits+11` keeps
    every position (window registers `≤ 3·bits+2`, mod-add workspace
    `3·bits+11`) inside the dimension. -/
theorem windowedInplaceModMulGate_wellTyped
    (c N ainv bits anc : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc) :
    Gate.WellTyped (bits + anc) (windowedInplaceModMulGate c N ainv bits) := by
  have h_sel : ∀ c', Gate.WellTyped (bits + anc)
      (windowed2SelectedAddGate (toyWindow2SelectedAddStateSpecImpl c' N).toSelectedAddSpec
        bits 0 (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    fun c' => windowedSelectedAdd_wellTyped_concrete bits N anc hbits h_even hN_pos hN hN2 h_anc c'
  have h_load : Gate.WellTyped (bits + anc)
      (windowedSwapLoadAdapter bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    windowedSwapLoadAdapter_wellTyped bits (wb0Idx bits) (wb1Idx bits) (wnumWin bits) (bits + anc)
      (by omega)
      (fun k _ => by omega)
      (fun k _ => by omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
      (fun k _ => by unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
  have h_swap : Gate.WellTyped (bits + anc)
      (swapTargetWindows (wb0Idx bits) (wb1Idx bits) (wnumWin bits)) :=
    swapTargetWindows_wellTyped (bits + anc) (wb0Idx bits) (wb1Idx bits) (wnumWin bits)
      (by omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb1Idx; omega)
      (fun k hk => by have hk2 : k < bits / 2 := hk; unfold wb0Idx; omega)
      (fun k _ => by unfold wb1Idx; omega)
  unfold windowedInplaceModMulGate windowedForwardGate
  exact ⟨⟨h_load, h_sel c⟩, h_swap, h_sel ((N - ainv) % N), h_load⟩

/-- **The windowed modular-multiplier QPE family.**  At iterate `i` it
    multiplies by `a^(2^i) mod N` using the in-place windowed gate with
    per-power inverse `ainv0^(2^i) % N`.  Both family contracts (`mmi`
    matrix semantics, `wellTyped`) are discharged via the universal
    bridges, the proven round-trip, and `mul_pow_mod_one`. -/
noncomputable def windowedModMulFamily
    (a N bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N bits anc where
  family := fun i => Gate.toUCom (bits + anc)
      (windowedInplaceModMulGate (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits)
  mmi := by
    intro i
    have h_wt := windowedInplaceModMulGate_wellTyped (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc
      hbits h_even hN_pos hN hN2 h_anc
    refine toUCom_satisfies_MultiplyCircuitProperty_of_applyNat_encodeDataZeroAnc h_wt hN ?_
    intro x hx
    have h_ainv_le : ainv0 ^ (2 ^ i) % N ≤ N := (Nat.mod_lt _ hN_pos).le
    have h_inv_i : (a ^ (2 ^ i) * (ainv0 ^ (2 ^ i) % N)) % N = 1 := by
      rw [Nat.mul_mod, Nat.mod_eq_of_lt (Nat.mod_lt _ hN_pos)]
      exact mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0
    exact windowedInplaceModMulGate_roundTrip (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc x
      hbits h_even hN_pos hN hN2 (by omega) hx h_ainv_le h_inv_i
  wellTyped := by
    intro i
    exact uc_well_typed_toUCom_of_Gate_WellTyped (bits + anc) _
      (windowedInplaceModMulGate_wellTyped (a ^ (2 ^ i)) N (ainv0 ^ (2 ^ i) % N) bits anc
        hbits h_even hN_pos hN hN2 h_anc)

/-- **HEADLINE — windowed multiplier ⟹ Shor success bound (UNCONDITIONAL).**
    The windowed (Pipeline C) modular multiplier achieves the canonical Shor
    success-probability bound `≥ κ / (log₂ N)^4`, with no remaining circuit
    obligations.  Every ingredient — the `h_tw` target↔windows SWAP, the
    in-place round-trip, the full gate well-typedness (SWAP cascades + window
    selected-add), and the modular-inverse arithmetic — is proven and
    kernel-clean.  The only hypotheses are the standard Shor sizing/setting
    facts plus the base modular inverse `a · ainv0 % N = 1` (obtainable from
    `Order_modinv_correct`) and `anc ≥ 2·bits+11`. -/
theorem windowed_shor_correct
    (a r N m bits anc ainv0 : Nat)
    (hbits : 1 ≤ bits) (h_even : 2 ∣ bits) (hN_pos : 0 < N) (hN1 : 1 < N)
    (hN : N ≤ 2 ^ bits) (hN2 : 2 * N ≤ 2 ^ bits) (h_anc : 2 * bits + 11 ≤ anc)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits anc
        (windowedModMulFamily a N bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc
          h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (windowedModMulFamily a N bits anc ainv0 hbits h_even hN_pos hN1 hN hN2 h_anc
    h_inv0).shorCorrect r m h_setting

end FormalRV.BQAlgo.WindowedShorConnection
