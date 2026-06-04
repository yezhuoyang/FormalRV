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

end FormalRV.BQAlgo.WindowedShorConnection
