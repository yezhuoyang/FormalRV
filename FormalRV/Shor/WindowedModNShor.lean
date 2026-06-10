/-
  FormalRV.Shor.WindowedModNShor — THE WELD: the in-place mod-N windowed
  (QROM-lookup) multiplier as an `EncodeRoundTripModMul` instance, and the
  Shor success bound derived for it.

  ## What this file delivers

  `windowedModNMultiplier` is, to our knowledge, the FIRST verified object
  carrying BOTH halves of the windowed-Shor story at once:

  * **The Shor success bound** — as an `EncodeRoundTripModMul N bits anc`
    instance it inherits, by one-line instantiation,
    `windowedModNMultiplier_verifiedModMulFamily : VerifiedModMulFamily` and
    `windowedModNMul_shor_correct : probability_of_success ≥ κ/(log₂ N)⁴`.
  * **Lookup-grade structure at arbitrary window size `w`** — the underlying
    gate is `windowedModNMulGate` (`Arithmetic/Windowed/WindowedModNInPlace`),
    the in-place `y ← (c·y) mod N` built from `numWin = bits/w` QROM unary
    table-lookups feeding Cuccaro adders with exact per-window mod-N
    reduction (the Gidney-windowing circuit shape), NOT a shift-and-add
    rewrite.  Its verified T-count is the windowed
    `2·numWin·(56·w·2^w + 56·bits)` (`tcount_windowedModNEncodeGate`):
    the `w·2^w` lookup-vs-adder trade the windowed literature optimizes.

  ## The layout adapter

  `windowedModNMulGate` speaks the windowed layout (ctrl wire 0 SET, lookup
  zone at wires `1..2w`, Cuccaro block at `1+2w`, y-register LSB-first at
  `yBase = 1+2w+(2·bits+1)`, comparison flag above), while
  `EncodeRoundTripModMul.roundTrip` is stated on `encodeDataZeroAnc bits anc x`
  (data BIG-endian in wires `0..bits-1`, zeros above).  The conjugation

      windowedEncodeIn  := swapCascade (data i ↔ y-wire (bits−1−i)) ; X 0
      gate c            := windowedEncodeIn ; windowedModNMulGate ; windowedEncodeOut
      windowedEncodeOut := X 0 ; swapCascade (same)

  moves the data into the y-register (reversing bit order: big-endian data
  position `i` ↔ LSB-first y-wire `bits−1−i`) and conjures/clears the
  windowed ctrl wire with a single X.  `swapCascade` is the register-level
  3-CX-cascade SWAP, with semantics from the proven cascade engine
  (`applyNat_cx_cascade_at/_frame`), mirroring `accYSwap`.

  ## Remaining delta to paper-optimal counts (named pointers)

  * **Gray-code reads** (`WindowedGrayLookup.lean`): halve the lookup factor
    `56·w·2^w → 14·2^w`-ish by Gray-ordered address updates — proven for the
    plain windowed multiplier, not yet replayed for the mod-N in-place chain.
  * **Measured uncompute** (`Shor/MeasUncompute*.lean`): the
    measurement-assisted lookup uncompute (cost `√`-ish of the read) — proven
    standalone, not yet welded into this `Gate`-level pipeline (the `Gate` IR
    is measurement-free by design).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Arithmetic.Windowed.WindowedModNInPlace
import FormalRV.Shor.MultiplierInstances

namespace FormalRV.BQAlgo.WindowedModNShor

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.SQIRPort
open FormalRV.BQAlgo
open VerifiedShor
open VerifiedShor.Windowed (nat_to_funbool_eq_testBit)
open FormalRV.BQAlgo.WindowedShorConnection
open FormalRV.BQAlgo.MultiplierInstances
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedLookupAdd (addrFlips)

/-! ## §1. Generic well-typedness engine (foldl-of-seq and CX cascades).

The mod-N windowed multiplier was proven CORRECT in
`WindowedModNInPlace.lean`, but `EncodeRoundTripModMul` additionally demands
`Gate.WellTyped (bits + anc)`.  No well-typedness lemmas existed for the
windowed/lookup circuit family; §1–§3 supply them, bottom-up. -/

private theorem wellTyped_foldl_seq_init (G : Nat → Gate) (dim : Nat) :
    ∀ (l : List Nat) (init : Gate), Gate.WellTyped dim init →
      (∀ k ∈ l, Gate.WellTyped dim (G k)) →
      Gate.WellTyped dim (l.foldl (fun g k => Gate.seq g (G k)) init) := by
  intro l
  induction l with
  | nil =>
    intro init hinit _
    exact hinit
  | cons a t ih =>
    intro init hinit h
    simp only [List.foldl_cons]
    exact ih (Gate.seq init (G a))
      ⟨hinit, h a (List.mem_cons.mpr (Or.inl rfl))⟩
      (fun k hk => h k (List.mem_cons.mpr (Or.inr hk)))

private theorem wellTyped_foldl_seq_range (G : Nat → Gate) (n dim : Nat)
    (h0 : 0 < dim) (h : ∀ k, k < n → Gate.WellTyped dim (G k)) :
    Gate.WellTyped dim
      ((List.range n).foldl (fun g k => Gate.seq g (G k)) Gate.I) :=
  wellTyped_foldl_seq_init G dim (List.range n) Gate.I h0
    (fun k hk => h k (List.mem_range.mp hk))

private theorem cxCascade_wellTyped (ctrl tgt : Nat → Nat) (n dim : Nat)
    (h0 : 0 < dim)
    (h : ∀ i, i < n → ctrl i < dim ∧ tgt i < dim ∧ ctrl i ≠ tgt i) :
    Gate.WellTyped dim (cxCascade ctrl tgt n) := by
  unfold cxCascade
  exact wellTyped_foldl_seq_range (fun i => Gate.CX (ctrl i) (tgt i)) n dim h0 h

/-! ## §2. Well-typedness of the QROM unary-lookup leg. -/

private theorem x_gates_from_indices_wellTyped (dim : Nat) (h0 : 0 < dim)
    (l : List Nat) (h : ∀ q ∈ l, q < dim) :
    Gate.WellTyped dim (x_gates_from_indices l) := by
  induction l with
  | nil => exact h0
  | cons i xs ih =>
    exact ⟨ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))),
           h i (List.mem_cons.mpr (Or.inl rfl))⟩

private theorem cx_gates_from_indices_wellTyped (ctrl dim : Nat) (h0 : 0 < dim)
    (hctrl : ctrl < dim) (l : List Nat)
    (h : ∀ t ∈ l, t < dim ∧ ctrl ≠ t) :
    Gate.WellTyped dim (cx_gates_from_indices ctrl l) := by
  induction l with
  | nil => exact h0
  | cons t xs ih =>
    exact ⟨ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))),
           hctrl, (h t (List.mem_cons.mpr (Or.inl rfl))).1,
           (h t (List.mem_cons.mpr (Or.inl rfl))).2⟩

private theorem prefix_and_step_wellTyped (i dim : Nat) (h : 2 * i + 2 < dim) :
    Gate.WellTyped dim (prefix_and_step i) := by
  unfold prefix_and_step ulookup_ctrl_idx ulookup_address_idx ulookup_and_idx
  by_cases hi : i = 0
  · rw [if_pos hi]
    subst hi
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rw [if_neg hi]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem prefix_and_cascade_wellTyped (n dim : Nat)
    (h : 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (prefix_and_cascade n) := by
  induction n with
  | zero => exact (by omega : 0 < dim)
  | succ k ih =>
    exact ⟨ih (by omega), prefix_and_step_wellTyped k dim (by omega)⟩

private theorem prefix_and_uncompute_wellTyped (n dim : Nat)
    (h : 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (prefix_and_uncompute n) := by
  induction n with
  | zero => exact (by omega : 0 < dim)
  | succ k ih =>
    exact ⟨prefix_and_step_wellTyped k dim (by omega), ih (by omega)⟩

private theorem unary_lookup_iteration_wellTyped (n_addr : Nat)
    (flips cnots : List Nat) (dim : Nat)
    (hn : 0 < n_addr) (hdim : 2 * n_addr + 1 ≤ dim)
    (hflips : ∀ q ∈ flips, q < dim)
    (hcnots : ∀ t ∈ cnots, t < dim ∧ ulookup_and_idx (n_addr - 1) ≠ t) :
    Gate.WellTyped dim (unary_lookup_iteration n_addr flips cnots) := by
  have hx := x_gates_from_indices_wellTyped dim (by omega) flips hflips
  have hctrl_lt : ulookup_and_idx (n_addr - 1) < dim := by
    unfold ulookup_and_idx
    omega
  show Gate.WellTyped dim
    (Gate.seq (Gate.seq (Gate.seq (Gate.seq (x_gates_from_indices flips)
      (prefix_and_cascade n_addr))
      (cx_gates_from_indices (ulookup_and_idx (n_addr - 1)) cnots))
      (prefix_and_uncompute n_addr)) (x_gates_from_indices flips))
  exact ⟨⟨⟨⟨hx, prefix_and_cascade_wellTyped n_addr dim hdim⟩,
    cx_gates_from_indices_wellTyped _ dim (by omega) hctrl_lt cnots hcnots⟩,
    prefix_and_uncompute_wellTyped n_addr dim hdim⟩, hx⟩

private theorem unary_lookup_multi_iteration_wellTyped (n_addr dim : Nat)
    (h0 : 0 < dim) (l : List (List Nat × List Nat))
    (h : ∀ pr ∈ l,
      Gate.WellTyped dim (unary_lookup_iteration n_addr pr.1 pr.2)) :
    Gate.WellTyped dim (unary_lookup_multi_iteration n_addr l) := by
  induction l with
  | nil => exact h0
  | cons pr rest ih =>
    obtain ⟨flips, cnots⟩ := pr
    exact ⟨ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq))),
           h (flips, cnots) (List.mem_cons.mpr (Or.inl rfl))⟩

private theorem mem_addrFlips_lt {w v q dim : Nat} (hq : q ∈ addrFlips w v)
    (hdim : 2 * w + 1 ≤ dim) : q < dim := by
  unfold addrFlips at hq
  obtain ⟨i, hi, heq⟩ := List.mem_filterMap.mp hq
  rw [List.mem_range] at hi
  by_cases hb : v.testBit i
  · rw [if_pos hb] at heq
    simp at heq
  · rw [if_neg hb] at heq
    have := Option.some.inj heq
    unfold ulookup_address_idx at this
    omega

private theorem mem_wordCnotsAt {pos : Nat → Nat} {W Tv t : Nat}
    (ht : t ∈ wordCnotsAt pos W Tv) : ∃ j, j < W ∧ t = pos j := by
  unfold wordCnotsAt at ht
  obtain ⟨j, hj, heq⟩ := List.mem_filterMap.mp ht
  rw [List.mem_range] at hj
  by_cases hb : Tv.testBit j
  · rw [if_pos hb] at heq
    exact ⟨j, hj, (Option.some.inj heq).symm⟩
  · rw [if_neg hb] at heq
    simp at heq

private theorem lookupReadAt_wellTyped (w W : Nat) (pos : Nat → Nat)
    (T : Nat → Nat) (dim : Nat) (hw : 0 < w) (hdim : 2 * w + 1 ≤ dim)
    (hpos : ∀ j, j < W → pos j < dim ∧ ulookup_and_idx (w - 1) ≠ pos j) :
    Gate.WellTyped dim (lookupReadAt w pos W T) := by
  unfold lookupReadAt
  apply unary_lookup_multi_iteration_wellTyped w dim (by omega)
  intro pr hpr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hpr
  apply unary_lookup_iteration_wellTyped w _ _ dim hw hdim
  · intro q hq
    exact mem_addrFlips_lt hq hdim
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := mem_wordCnotsAt ht
    exact hpos j hj

/-! ## §3. Well-typedness of the mod-N windowed multiplier itself. -/

private theorem targetComplement_wellTyped (n q_start dim : Nat)
    (h : q_start + 2 * n + 1 ≤ dim) :
    Gate.WellTyped dim (targetComplement n q_start) := by
  induction n with
  | zero => exact (by omega : 0 < dim)
  | succ k ih =>
    exact ⟨ih (by omega), (by omega : q_start + 2 * k + 1 < dim)⟩

private theorem regCompareXor_wellTyped (bits q_start flagPos dim : Nat)
    (h_ws : q_start + 2 * bits + 1 ≤ dim) (h_flag : flagPos < dim)
    (h_ne : flagPos ≠ q_start + 2 * bits) :
    Gate.WellTyped dim (regCompareXor bits q_start flagPos) :=
  ⟨targetComplement_wellTyped bits q_start dim h_ws,
   cuccaro_maj_chain_wellTyped bits q_start dim h_ws,
   ⟨by omega, h_flag, fun hh => h_ne hh.symm⟩,
   cuccaro_maj_chain_inv_wellTyped bits q_start dim h_ws,
   targetComplement_wellTyped bits q_start dim h_ws⟩

private theorem modNReduceFlag_wellTyped (bits q_start N flagPos dim : Nat)
    (h_ws : q_start + 2 * bits + 1 ≤ dim) (h_flag : flagPos < dim)
    (h_ne : flagPos ≠ q_start + 2 * bits)
    (h_add : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.WellTyped dim (modNReduceFlag bits q_start N flagPos) :=
  ⟨sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_ne,
   sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_add⟩

private theorem modNLookupAddStep_wellTyped (w bits N : Nat) (T : Nat → Nat)
    (q_start flagPos dim : Nat) (hw : 0 < w)
    (hq : 2 * w + 1 ≤ q_start) (h_ws : q_start + 2 * bits + 1 ≤ dim)
    (h_flag : flagPos < dim) (h_ne : flagPos ≠ q_start + 2 * bits)
    (h_add : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2) :
    Gate.WellTyped dim (modNLookupAddStep w bits N T q_start flagPos) := by
  have h_look : Gate.WellTyped dim (lookupReadAt w (addendIdx q_start) bits T) := by
    apply lookupReadAt_wellTyped w bits (addendIdx q_start) T dim hw (by omega)
    intro j hj
    unfold addendIdx ulookup_and_idx
    constructor <;> omega
  exact ⟨h_look, cuccaro_n_bit_adder_full_wellTyped bits q_start dim h_ws,
    h_look,
    modNReduceFlag_wellTyped bits q_start N flagPos dim h_ws h_flag h_ne h_add,
    h_look, regCompareXor_wellTyped bits q_start flagPos dim h_ws h_flag h_ne,
    h_look⟩

private theorem copyWindow_wellTyped (w yBase j dim : Nat) (h0 : 0 < dim)
    (hctrl : ∀ i, i < w → yBase + j * w + i < dim)
    (haddr : ∀ i, i < w → 1 + 2 * i < yBase) :
    Gate.WellTyped dim (copyWindow w yBase j) := by
  unfold copyWindow
  apply wellTyped_foldl_seq_range _ w dim h0
  intro i hi
  have h1 := hctrl i hi
  have h2 := haddr i hi
  unfold ulookup_address_idx
  exact ⟨h1, by omega, by omega⟩

private theorem windowedModNStep_wellTyped (w bits a N numWin j dim : Nat)
    (hw : 0 < w) (hj : j < numWin)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    Gate.WellTyped dim
      (windowedModNStep w bits a N (1 + 2 * w) (1 + 2 * w + (2 * bits + 1))
        (1 + 2 * w + (2 * bits + 1) + numWin * w) j) := by
  have hjw : (j + 1) * w ≤ numWin * w := Nat.mul_le_mul_right w hj
  have hjw' : j * w + w ≤ numWin * w := by
    calc j * w + w = (j + 1) * w := by ring
    _ ≤ numWin * w := hjw
  have hcw : Gate.WellTyped dim (copyWindow w (1 + 2 * w + (2 * bits + 1)) j) := by
    apply copyWindow_wellTyped w _ j dim (by omega)
    · intro i hi
      omega
    · intro i hi
      omega
  refine ⟨hcw, ?_, hcw⟩
  apply modNLookupAddStep_wellTyped w bits N _ (1 + 2 * w)
    (1 + 2 * w + (2 * bits + 1) + numWin * w) dim hw (by omega) (by omega)
    (by omega) (by omega)
  intro i hi
  omega

private theorem windowedModNMulCircuit_wellTyped (w bits a N numWin dim : Nat)
    (hw : 0 < w) (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    Gate.WellTyped dim (windowedModNMulCircuit w bits a N numWin) := by
  unfold windowedModNMulCircuit windowedModNMul
  apply wellTyped_foldl_seq_range _ numWin dim (by omega)
  intro j hj
  exact windowedModNStep_wellTyped w bits a N numWin j dim hw hj hdim

private theorem accYSwap_cuccaro_wellTyped (w bits dim : Nat)
    (hdim : 1 + 2 * w + (2 * bits + 1) + bits ≤ dim) :
    Gate.WellTyped dim (accYSwap cuccaroAdder w bits) := by
  have hc : ∀ i, i < bits →
      cuccaroAdder.augendIdx (1 + 2 * w) i < dim ∧
      1 + 2 * w + cuccaroAdder.span bits + i < dim ∧
      cuccaroAdder.augendIdx (1 + 2 * w) i
        ≠ 1 + 2 * w + cuccaroAdder.span bits + i := by
    intro i hi
    show 1 + 2 * w + 2 * i + 1 < dim ∧ 1 + 2 * w + (2 * bits + 1) + i < dim
      ∧ 1 + 2 * w + 2 * i + 1 ≠ 1 + 2 * w + (2 * bits + 1) + i
    omega
  unfold accYSwap
  exact ⟨⟨cxCascade_wellTyped _ _ bits dim (by omega) hc,
          cxCascade_wellTyped _ _ bits dim (by omega)
            (fun i hi => ⟨(hc i hi).2.1, (hc i hi).1,
              fun hh => (hc i hi).2.2 hh.symm⟩)⟩,
        cxCascade_wellTyped _ _ bits dim (by omega) hc⟩

/-- **Well-typedness of the in-place mod-N windowed multiplier** at any
    dimension covering the windowed layout (flag wire
    `1+2w+(2·bits+1)+numWin·w` inclusive). -/
theorem windowedModNMulGate_wellTyped (w bits N numWin c cinv dim : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits)
    (hdim : 1 + 2 * w + (2 * bits + 1) + numWin * w + 1 ≤ dim) :
    Gate.WellTyped dim (windowedModNMulGate w bits N numWin c cinv) :=
  ⟨⟨windowedModNMulCircuit_wellTyped w bits c N numWin dim hw hdim,
    accYSwap_cuccaro_wellTyped w bits dim (by omega)⟩,
   windowedModNMulCircuit_wellTyped w bits (N - cinv) N numWin dim hw hdim⟩

/-! ## §4. The register-level 3-cascade SWAP (the layout adapter's engine).

`swapCascade u v n` exchanges wires `u i ↔ v i` for `i < n` via three
interleaved CX cascades — the generic form of `accYSwap`, with semantics
inherited from the proven cascade engine `applyNat_cx_cascade_at/_frame`. -/

/-- Register-level SWAP between wires `u i` and `v i`, `i < n`:
    `CX(u→v) ; CX(v→u) ; CX(u→v)` per index. -/
def swapCascade (u v : Nat → Nat) (n : Nat) : Gate :=
  Gate.seq (Gate.seq (cxCascade u v n) (cxCascade v u n)) (cxCascade u v n)

private theorem swapCascade_wellTyped (u v : Nat → Nat) (n dim : Nat)
    (h0 : 0 < dim)
    (h : ∀ i, i < n → u i < dim ∧ v i < dim ∧ u i ≠ v i) :
    Gate.WellTyped dim (swapCascade u v n) :=
  ⟨⟨cxCascade_wellTyped u v n dim h0 h,
    cxCascade_wellTyped v u n dim h0
      (fun i hi => ⟨(h i hi).2.1, (h i hi).1, fun hh => (h i hi).2.2 hh.symm⟩)⟩,
   cxCascade_wellTyped u v n dim h0 h⟩

/-- **`swapCascade` post-state**: wires `u i` and `v i` are exchanged, every
    other wire untouched.  Needs `u`/`v` injective on `[0,n)` and the two
    zones disjoint. -/
theorem swapCascade_apply (u v : Nat → Nat) (n : Nat) (g : Nat → Bool)
    (hu_inj : ∀ i k, i < n → k < n → i ≠ k → u i ≠ u k)
    (hv_inj : ∀ i k, i < n → k < n → i ≠ k → v i ≠ v k)
    (huv : ∀ i k, i < n → k < n → u i ≠ v k) :
    (∀ i, i < n → Gate.applyNat (swapCascade u v n) g (u i) = g (v i))
    ∧ (∀ i, i < n → Gate.applyNat (swapCascade u v n) g (v i) = g (u i))
    ∧ (∀ p, (∀ i, i < n → p ≠ u i ∧ p ≠ v i) →
        Gate.applyNat (swapCascade u v n) g p = g p) := by
  have hvu : ∀ i k, i < n → k < n → v i ≠ u k :=
    fun i k hi hk => (huv k i hk hi).symm
  unfold swapCascade
  simp only [Gate.applyNat_seq]
  set g1 : Nat → Bool := Gate.applyNat (cxCascade u v n) g with hg1def
  set g2 : Nat → Bool := Gate.applyNat (cxCascade v u n) g1 with hg2def
  have hg1_at : ∀ k, k < n → g1 (v k) = xor (g (v k)) (g (u k)) := by
    intro k hk
    rw [hg1def]
    unfold cxCascade
    exact applyNat_cx_cascade_at u v g n hv_inj huv k hk
  have hg1_frame : ∀ p, (∀ k, k < n → p ≠ v k) → g1 p = g p := by
    intro p hp
    rw [hg1def]
    unfold cxCascade
    exact applyNat_cx_cascade_frame u v g n p hp
  have hg2_at : ∀ k, k < n → g2 (u k) = xor (g1 (u k)) (g1 (v k)) := by
    intro k hk
    rw [hg2def]
    unfold cxCascade
    exact applyNat_cx_cascade_at v u g1 n hu_inj hvu k hk
  have hg2_frame : ∀ p, (∀ k, k < n → p ≠ u k) → g2 p = g1 p := by
    intro p hp
    rw [hg2def]
    unfold cxCascade
    exact applyNat_cx_cascade_frame v u g1 n p hp
  have hg3_at : ∀ k, k < n →
      Gate.applyNat (cxCascade u v n) g2 (v k) = xor (g2 (v k)) (g2 (u k)) := by
    intro k hk
    unfold cxCascade
    exact applyNat_cx_cascade_at u v g2 n hv_inj huv k hk
  have hg3_frame : ∀ p, (∀ k, k < n → p ≠ v k) →
      Gate.applyNat (cxCascade u v n) g2 p = g2 p := by
    intro p hp
    unfold cxCascade
    exact applyNat_cx_cascade_frame u v g2 n p hp
  have hxor1 : ∀ a b : Bool, xor a (xor b a) = b := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hg3_frame _ (fun k hk => huv i k hi hk),
        hg2_at i hi,
        hg1_frame _ (fun k hk => huv i k hi hk),
        hg1_at i hi, hxor1]
  · intro i hi
    rw [hg3_at i hi,
        hg2_frame _ (fun k hk => hvu i k hi hk),
        hg2_at i hi,
        hg1_frame _ (fun k hk => huv i k hi hk),
        hg1_at i hi, hxor1]
  · intro p hp
    rw [hg3_frame p (fun k hk => (hp k hk).2),
        hg2_frame p (fun k hk => (hp k hk).1),
        hg1_frame p (fun k hk => (hp k hk).2)]

/-! ## §5. The layout adapters: `encodeDataZeroAnc` ↔ windowed layout.

`encodeDataZeroAnc bits anc x` holds `x` BIG-endian in wires `0..bits−1`
(zeros above); `mulInputOf` wants ctrl wire 0 SET and `x` LSB-first in the
y-register at `yBase = 1+2w+(2·bits+1)`.  The adapter swaps data wire `i`
with y-wire `bits−1−i` (handling both relocation AND bit-order reversal in
one cascade), then sets/clears the ctrl wire with an X. -/

/-- Literal-position form of `mulInputOf cuccaroAdder` off the ctrl wire. -/
private theorem mulInputOf_lit (w bits numWin y p : Nat) (hp : p ≠ 0) :
    mulInputOf cuccaroAdder w bits numWin y p
      = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y p :=
  mulInputOf_eq_encodeReg cuccaroAdder w bits numWin y p
    (by unfold ulookup_ctrl_idx; omega)

/-- A `ModNMulReady` state IS `mulInputOf` (function equality): the block
    and flag are clean, which is exactly what `mulInputOf` says there. -/
private theorem modNMulReady_eq (w bits numWin y : Nat) (f : Nat → Bool)
    (h : ModNMulReady w bits numWin y f) :
    f = mulInputOf cuccaroAdder w bits numWin y := by
  obtain ⟨hF, hD, hC, hG, hV⟩ := h
  funext p
  by_cases hpb : inBlock (1 + 2 * w) (2 * bits + 1) p
  · have hpb' : 1 + 2 * w ≤ p ∧ p < 1 + 2 * w + (2 * bits + 1) := hpb
    have hzero : mulInputOf cuccaroAdder w bits numWin y p = false := by
      rw [mulInputOf_lit w bits numWin y p (by omega)]
      unfold encodeReg
      rw [if_neg (by omega)]
    rw [hzero]
    rcases Nat.even_or_odd (p - (1 + 2 * w)) with ⟨m, hm⟩ | ⟨m, hm⟩
    · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [show p = 1 + 2 * w from by omega]
        exact hC
      · rw [show p = 1 + 2 * w + 2 * (m - 1) + 2 from by omega]
        exact hD (m - 1) (by omega)
    · rw [show p = 1 + 2 * w + 2 * m + 1 from by omega]
      exact hV m (by omega)
  · by_cases hpf : p = 1 + 2 * w + (2 * bits + 1) + numWin * w
    · rw [hpf, hG, mulInputOf_lit w bits numWin y _ (by omega)]
      symm
      exact encodeReg_high _ _ _ _ (by omega)
    · exact hF p hpb hpf

/-- IN-adapter: load `encodeDataZeroAnc` data into the windowed y-register
    (bit-reversing swap), then SET the lookup ctrl wire. -/
def windowedEncodeIn (w bits : Nat) : Gate :=
  Gate.seq
    (swapCascade (fun i => bits - 1 - i)
      (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits)
    (Gate.X ulookup_ctrl_idx)

/-- OUT-adapter: CLEAR the ctrl wire, then unload the y-register back into
    the data band (same bit-reversing swap — `swapCascade` is involutive on
    this input shape, so IN and OUT are mirror composites). -/
def windowedEncodeOut (w bits : Nat) : Gate :=
  Gate.seq (Gate.X ulookup_ctrl_idx)
    (swapCascade (fun i => bits - 1 - i)
      (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits)

/-- **IN-adapter semantics**: `encodeDataZeroAnc bits (2w+2·bits+3) x` is
    mapped to the clean windowed input `mulInputOf cuccaroAdder`. -/
private theorem windowedEncodeIn_apply (w bits numWin x : Nat)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits) (hx : x < 2 ^ bits) :
    Gate.applyNat (windowedEncodeIn w bits)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = mulInputOf cuccaroAdder w bits numWin x := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  set f0 : Nat → Bool := encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x
    with hf0
  have hf0_high : ∀ p, bits ≤ p → f0 p = false := by
    intro p hp
    by_cases hp2 : p < bits + (2 * w + 2 * bits + 3)
    · rw [hf0, show p = bits + (p - bits) from by omega]
      exact encodeDataZeroAnc_anc hx (by omega)
    · rw [hf0]
      exact encodeDataZeroAnc_oob (by omega) (by omega)
  have hf0_data : ∀ i, i < bits → f0 (bits - 1 - i) = x.testBit i := by
    intro i hi
    rw [hf0, encodeDataZeroAnc_data hx (by omega), nat_to_funbool_eq_testBit]
    congr 1
    omega
  unfold windowedEncodeIn
  simp only [Gate.applyNat_seq, Gate.applyNat_X, hctrl0]
  set s1 : Nat → Bool := Gate.applyNat
    (swapCascade (fun i => bits - 1 - i)
      (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits) f0 with hs1def
  obtain ⟨hs_u, hs_v, hs_fr⟩ := swapCascade_apply (fun i => bits - 1 - i)
      (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits f0
      (fun i k hi hk hne => by
        show bits - 1 - i ≠ bits - 1 - k
        omega)
      (fun i k hi hk hne => by
        show 1 + 2 * w + (2 * bits + 1) + i ≠ 1 + 2 * w + (2 * bits + 1) + k
        omega)
      (fun i k hi hk => by
        show bits - 1 - i ≠ 1 + 2 * w + (2 * bits + 1) + k
        omega)
  rw [← hs1def] at hs_u hs_v hs_fr
  have hs1_zero : s1 0 = false := by
    have h0 := hs_u (bits - 1) (by omega)
    rw [show bits - 1 - (bits - 1) = 0 from by omega] at h0
    rw [h0]
    exact hf0_high _ (by omega)
  funext p
  by_cases hp0 : p = 0
  · subst hp0
    rw [update_eq, hs1_zero]
    symm
    exact mulInputOf_ctrl cuccaroAdder w bits numWin x
  · rw [update_neq _ _ _ _ hp0, mulInputOf_lit w bits numWin x p hp0]
    rcases Nat.lt_or_ge p bits with hpb | hpb
    · -- data band: emptied by the swap; encodeReg is below its base
      have h0 := hs_u (bits - 1 - p) (by omega)
      rw [show bits - 1 - (bits - 1 - p) = p from by omega] at h0
      rw [h0, hf0_high _ (by omega)]
      symm
      unfold encodeReg
      rw [if_neg (by omega)]
    · rcases Nat.lt_or_ge p (1 + 2 * w + (2 * bits + 1)) with hpy | hpy
      · -- lookup zone + Cuccaro block: frame, clean on both sides
        rw [hs_fr p (fun i hi => ⟨by omega, by omega⟩), hf0_high p hpb]
        symm
        unfold encodeReg
        rw [if_neg (by omega)]
      · rcases Nat.lt_or_ge p (1 + 2 * w + (2 * bits + 1) + bits) with hpy2 | hpy2
        · -- y-register: receives the data bits LSB-first
          have h0 := hs_v (p - (1 + 2 * w + (2 * bits + 1))) (by omega)
          rw [show 1 + 2 * w + (2 * bits + 1)
                + (p - (1 + 2 * w + (2 * bits + 1))) = p from by omega] at h0
          rw [h0, hf0_data (p - (1 + 2 * w + (2 * bits + 1))) (by omega)]
          symm
          unfold encodeReg
          rw [if_pos ⟨by omega, by omega⟩]
        · -- flag and beyond: frame, clean on both sides
          rw [hs_fr p (fun i hi => ⟨by omega, by omega⟩), hf0_high p hpb]
          symm
          unfold encodeReg
          rw [if_neg (by omega)]

/-- **OUT-adapter semantics**: the clean windowed state `mulInputOf` with
    y-value `y` is mapped back to `encodeDataZeroAnc bits (2w+2·bits+3) y`. -/
private theorem windowedEncodeOut_apply (w bits numWin y : Nat)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits) (hy : y < 2 ^ bits) :
    Gate.applyNat (windowedEncodeOut w bits)
        (mulInputOf cuccaroAdder w bits numWin y)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) y := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  unfold windowedEncodeOut
  simp only [Gate.applyNat_seq, Gate.applyNat_X, hctrl0]
  set m1 : Nat → Bool := update (mulInputOf cuccaroAdder w bits numWin y) 0
      (!(mulInputOf cuccaroAdder w bits numWin y 0)) with hm1def
  have hm1 : ∀ p, m1 p
      = encodeReg (1 + 2 * w + (2 * bits + 1)) (numWin * w) y p := by
    intro p
    by_cases hp0 : p = 0
    · subst hp0
      rw [hm1def, update_eq,
          show mulInputOf cuccaroAdder w bits numWin y 0 = true from
            mulInputOf_ctrl cuccaroAdder w bits numWin y]
      symm
      unfold encodeReg
      rw [if_neg (by omega)]
      rfl
    · rw [hm1def, update_neq _ _ _ _ hp0]
      exact mulInputOf_lit w bits numWin y p hp0
  obtain ⟨hs_u, hs_v, hs_fr⟩ := swapCascade_apply (fun i => bits - 1 - i)
      (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits m1
      (fun i k hi hk hne => by
        show bits - 1 - i ≠ bits - 1 - k
        omega)
      (fun i k hi hk hne => by
        show 1 + 2 * w + (2 * bits + 1) + i ≠ 1 + 2 * w + (2 * bits + 1) + k
        omega)
      (fun i k hi hk => by
        show bits - 1 - i ≠ 1 + 2 * w + (2 * bits + 1) + k
        omega)
  apply eq_encodeDataZeroAnc_of_data_anc_oob (by omega) hy
  · -- data band holds nat_to_funbool bits y
    intro i hi
    have h0 := hs_u (bits - 1 - i) (by omega)
    rw [show bits - 1 - (bits - 1 - i) = i from by omega] at h0
    rw [h0, hm1 _,
        encodeReg_at (1 + 2 * w + (2 * bits + 1)) (numWin * w) y
          (bits - 1 - i) (by omega),
        nat_to_funbool_eq_testBit]
  · -- ancilla band is clean
    intro j hj
    rcases Nat.lt_or_ge (bits + j) (1 + 2 * w + (2 * bits + 1)) with hq | hq
    · rw [hs_fr (bits + j) (fun i hi => ⟨by omega, by omega⟩), hm1 _]
      unfold encodeReg
      rw [if_neg (by omega)]
    · rcases Nat.lt_or_ge (bits + j) (1 + 2 * w + (2 * bits + 1) + bits)
        with hq2 | hq2
      · have h0 := hs_v (bits + j - (1 + 2 * w + (2 * bits + 1))) (by omega)
        rw [show 1 + 2 * w + (2 * bits + 1)
              + (bits + j - (1 + 2 * w + (2 * bits + 1))) = bits + j
              from by omega] at h0
        rw [h0, hm1 _]
        unfold encodeReg
        rw [if_neg (by omega)]
      · rw [hs_fr (bits + j) (fun i hi => ⟨by omega, by omega⟩), hm1 _]
        unfold encodeReg
        rw [if_neg (by omega)]
  · -- out-of-band is clean
    intro p hp
    rw [hs_fr p (fun i hi => ⟨by omega, by omega⟩), hm1 _]
    unfold encodeReg
    rw [if_neg (by omega)]

/-! ## §6. THE WELD: the encode-layout windowed mod-N multiplier gate. -/

/-- **The encode-layout in-place mod-N windowed multiplier**:
    `windowedEncodeIn ; windowedModNMulGate c cinv ; windowedEncodeOut`. -/
def windowedModNEncodeGate (w bits N numWin c cinv : Nat) : Gate :=
  Gate.seq
    (Gate.seq (windowedEncodeIn w bits)
      (windowedModNMulGate w bits N numWin c cinv))
    (windowedEncodeOut w bits)

/-- **Round trip**: `|x⟩|0⟩ ↦ |(c·x) mod N⟩|0⟩` in the canonical
    `encodeDataZeroAnc` layout, at ancilla width `2w + 2·bits + 3`
    (lookup zone `2w` + Cuccaro block `2·bits+1` + ctrl + flag). -/
theorem windowedModNEncodeGate_apply (w bits numWin N c cinv x : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hx : x < N) (hcinv : cinv < N) (hinv : c * cinv % N = 1) :
    Gate.applyNat (windowedModNEncodeGate w bits N numWin c cinv)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (c * x % N) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  unfold windowedModNEncodeGate
  simp only [Gate.applyNat_seq]
  rw [windowedEncodeIn_apply w bits numWin x hbits hb1
        (Nat.lt_of_lt_of_le hx hN_le)]
  have hmid := windowedModNMulGate_correct w bits N numWin c cinv x hw hbits
    hN_pos hN2 hx hcinv hinv _ (modNMulReady_mulInputOf w bits numWin x)
  rw [modNMulReady_eq w bits numWin _ _ hmid]
  exact windowedEncodeOut_apply w bits numWin (c * x % N) hbits hb1
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hN_pos) hN_le)

/-- **Well-typedness** of the welded gate at the instance dimension
    `bits + (2w + 2·bits + 3)`. -/
theorem windowedModNEncodeGate_wellTyped (w bits N numWin c cinv : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) :
    Gate.WellTyped (bits + (2 * w + 2 * bits + 3))
      (windowedModNEncodeGate w bits N numWin c cinv) := by
  have hctrl0 : ulookup_ctrl_idx = 0 := rfl
  have hswap : Gate.WellTyped (bits + (2 * w + 2 * bits + 3))
      (swapCascade (fun i => bits - 1 - i)
        (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits) := by
    apply swapCascade_wellTyped _ _ bits _ (by omega)
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · show bits - 1 - i < bits + (2 * w + 2 * bits + 3)
      omega
    · show 1 + 2 * w + (2 * bits + 1) + i < bits + (2 * w + 2 * bits + 3)
      omega
    · show bits - 1 - i ≠ 1 + 2 * w + (2 * bits + 1) + i
      omega
  have hX : Gate.WellTyped (bits + (2 * w + 2 * bits + 3))
      (Gate.X ulookup_ctrl_idx) := by
    show ulookup_ctrl_idx < bits + (2 * w + 2 * bits + 3)
    rw [hctrl0]
    omega
  exact ⟨⟨⟨hswap, hX⟩,
    windowedModNMulGate_wellTyped w bits N numWin c cinv _ hw hbits (by omega)⟩,
    hX, hswap⟩

/-! ## §7. THE INSTANCE: `EncodeRoundTripModMul` for the windowed mod-N
       multiplier — the first QROM-lookup windowed multiplier carrying the
       full Shor success bound. -/

/-- **The arbitrary-window-size QROM-lookup mod-N multiplier as an
    `EncodeRoundTripModMul`.**

    Underlying verified gate: `windowedModNMulGate w bits N numWin c cinv`
    (`Arithmetic/Windowed/WindowedModNInPlace`), the in-place
    `y ← (c·y) mod N` built from per-window QROM unary lookups + Cuccaro
    adders + exact mod-N reduction, conjugated into the canonical
    `encodeDataZeroAnc` layout by the bit-reversing swap adapters.

    Per constant `c`, the instance reduces the constant (`c % N`) and
    computes its inverse internally (`modInv N c`); the interface's
    invertibility guard supplies exactly the witness `modInv_spec` needs —
    the same per-constant pattern as `cuccaroMultiplier`/`gidneyMultiplier`.

    Standing hypotheses: window size `0 < w`, exact tiling
    `numWin·w = bits` (the y-register matches the accumulator width),
    `1 ≤ bits`, `1 < N`, and headroom `2·N ≤ 2^bits` for the comparator. -/
noncomputable def windowedModNMultiplier (w bits numWin N : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits) :
    EncodeRoundTripModMul N bits (2 * w + 2 * bits + 3) where
  gate := fun c => windowedModNEncodeGate w bits N numWin (c % N) (modInv N c)
  wellTyped := fun c =>
    windowedModNEncodeGate_wellTyped w bits N numWin (c % N) (modInv N c)
      hw hbits
  roundTrip := by
    intro c x hx hc
    have hN_pos : 0 < N := by omega
    obtain ⟨h_lt, h_inv⟩ := modInv_spec N c hN_pos hc
    have h_inv' : (c % N) * modInv N c % N = 1 := by
      rw [Nat.mod_mul_mod]
      exact h_inv
    show Gate.applyNat
        (windowedModNEncodeGate w bits N numWin (c % N) (modInv N c))
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) ((c * x) % N)
    rw [windowedModNEncodeGate_apply w bits numWin N (c % N) (modInv N c) x
          hw hbits hb1 hN_pos hN2 hx h_lt h_inv',
        Nat.mod_mul_mod]

/-! ## §8. THE PAYOFF: one line to the framework family, one line to Shor. -/

/-- **One line to the framework family**: the windowed mod-N multiplier as a
    `VerifiedModMulFamily` (QPE iterate `i` multiplies by `a^(2^i) mod N`),
    given a base inverse `a · ainv0 ≡ 1 (mod N)`. -/
noncomputable def windowedModNMultiplier_verifiedModMulFamily
    (w bits numWin N a ainv0 : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) :
    VerifiedModMulFamily a N bits (2 * w + 2 * bits + 3) :=
  (windowedModNMultiplier w bits numWin N hw hbits hb1 hN1
      hN2).toVerifiedModMulFamily a (by omega) ainv0 hN1 h_inv0

/-- **One line to Shor — THE HEADLINE.**  The arbitrary-window-size
    QROM-lookup mod-N windowed multiplier achieves the canonical Shor
    success-probability bound `≥ κ / (log₂ N)⁴`: the first object in the
    development carrying BOTH the verified success bound AND
    lookup-grade (windowed, `w·2^w`-tradeoff) circuit structure. -/
theorem windowedModNMul_shor_correct
    (w bits numWin N a ainv0 r m : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_setting : ShorSetting a r N m bits) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
          hw hbits hb1 hN1 hN2 h_inv0).family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  (windowedModNMultiplier_verifiedModMulFamily w bits numWin N a ainv0
    hw hbits hb1 hN1 hN2 h_inv0).shorCorrect r m h_setting

/-! ## §9. Count rider: the welded gate keeps the windowed T-count.

The adapters are T-free (CX cascades + one X each), so the welded gate costs
exactly the two mod-N passes of the underlying in-place multiplier:
`2·numWin·(56·w·2^w + 56·bits)` T — the QROM-windowing `w·2^w`-vs-`bits`
trade, now attached to a Shor-success-bound-carrying object.  Remaining
delta to paper-optimal: Gray-code reads (`WindowedGrayLookup`) and
measured uncompute (`Shor/MeasUncompute*`), not yet welded in. -/

private theorem tcount_cxCascade_zero (ctrl tgt : Nat → Nat) (n : Nat) :
    tcount (cxCascade ctrl tgt n) = 0 := by
  rw [cxCascade, tcount_foldl_seq_const
        (fun i => Gate.CX (ctrl i) (tgt i)) 0 (fun _ => rfl)]
  simp [tcount]

/-- The 3-cascade SWAP is T-free. -/
theorem tcount_swapCascade (u v : Nat → Nat) (n : Nat) :
    tcount (swapCascade u v n) = 0 := by
  show tcount (cxCascade u v n) + tcount (cxCascade v u n)
      + tcount (cxCascade u v n) = 0
  rw [tcount_cxCascade_zero, tcount_cxCascade_zero]

/-- **Welded-gate T-count (exact, kernel-clean)**: T-free adapters + two
    mod-N windowed passes = `2·numWin·(56·w·2^w + 56·bits)`. -/
theorem tcount_windowedModNEncodeGate (w bits N numWin c cinv : Nat) :
    tcount (windowedModNEncodeGate w bits N numWin c cinv)
      = 2 * (numWin * (56 * w * 2 ^ w + 56 * bits)) := by
  show tcount (swapCascade (fun i => bits - 1 - i)
        (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits)
      + tcount (Gate.X ulookup_ctrl_idx)
      + tcount (windowedModNMulGate w bits N numWin c cinv)
      + (tcount (Gate.X ulookup_ctrl_idx)
        + tcount (swapCascade (fun i => bits - 1 - i)
            (fun i => 1 + 2 * w + (2 * bits + 1) + i) bits))
      = 2 * (numWin * (56 * w * 2 ^ w + 56 * bits))
  rw [tcount_swapCascade, tcount_windowedModNMulGate]
  simp [tcount]

end FormalRV.BQAlgo.WindowedModNShor
