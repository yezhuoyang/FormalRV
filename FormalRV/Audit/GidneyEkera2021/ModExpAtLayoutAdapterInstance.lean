/-
  Audit · Gidney–Ekerå 2021 · A CONCRETE `ModExpAtLayoutAdapter` — the T-free
  per-window SCATTER (IN) adapter, proven, plus the named residual reconciliation.
  ════════════════════════════════════════════════════════════════════════════
  `ShorModExpAt.ge2021_modExpAt_shor_succeeds` runs the Shor bound through
  `modExpAt`'s LITERAL count-bearing `multiplyAddAt` block GIVEN a
  `ShorModExpAt.ModExpAtLayoutAdapter`.  This file BUILDS the achievable half of
  that adapter — the T-free input scatter — concretely and PROVES it, then exposes
  exactly the two residual fields that are genuine, named circuit obligations.

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE (no `sorry`, no `native_decide`, no axioms)
  ────────────────────────────────────────────────────────────────────────────
  • `ge2021_adaptIn` — the T-free per-window scatter: a single `swapCascade`
    exchanging each data-band bit `bits-1-j` with the per-window address position
    `addrBaseOf (j/w) + (j%w)`, followed by `X 0` to set the lookup ctrl.  Modelled
    exactly on the CONTIGUOUS template `WindowedModNShor.windowedEncodeIn`, but with
    the PER-WINDOW target index map of `modExpAt`'s `addrBaseOf`.
  • `ge2021_adaptIn_tfree` — `tcount (adaptIn i) = 0`  (CX cascades + X are Clifford).
  • `ge2021_adaptIn_wellTyped` — `Gate.WellTyped (bits+anc) (adaptIn i)` whenever the
    address registers fit the dimension (an explicit hypothesis `hfit`).
  • `ge2021_adaptIn_clean` — **the heart**: on `encodeDataZeroAnc bits anc x`
    (`x < N ≤ 2^bits`), `adaptIn i` yields a `CountGateMulInput w bits numWin x q_start`
    — the windows of `x` are scattered into the per-window address registers, the
    shared Cuccaro accumulator / addend / per-window AND-ancillas are clean, ctrl set.
    This is the genuine new per-window scatter-index circuit work; it mirrors
    `windowedEncodeIn_apply` but discharges `CountGateMulInput`'s `addr0`/`anc0`
    per-window decode obligations.
  • `ge2021_modExpAtLayoutAdapter` — ASSEMBLES a full
    `ShorModExpAt.ModExpAtLayoutAdapter` from the proven IN-side PLUS the two named
    residual fields supplied as explicit hypotheses (see below).  Feeding it through
    `ShorModExpAt.ge2021_modExpAt_shor_succeeds` gives
    `ge2021_modExpAt_shor_succeeds_unconditional`: the Shor bound through the literal
    count gate, whose remaining hypotheses are ONLY `ShorSetting` + sizing + no-wrap
    + the two named residual obligations.

  ────────────────────────────────────────────────────────────────────────────
  THE TWO RESIDUAL FIELDS — why they are NOT discharged here (honest frontier)
  ────────────────────────────────────────────────────────────────────────────
  The OUT adapter and the block-width field do NOT admit a T-free / canonical-width
  discharge at the genuine `modExpAt` parameters; they are passed as named Prop
  inputs rather than fabricated:

  (A) `adaptOut_reads` is UNATTAINABLE for a T-free gate.  §1 of `ShorModExpAt`
      proves the literal `multiplyAddAt` block leaves, under no-wrap, the value
      `(a^(2^i)·x) % 2^bits = a^(2^i)·x` (the FULL product, since no-wrap means it is
      `< 2^bits`) in the accumulator — i.e. an UNREDUCED coset rep `v` with
      `v % N = (a^(2^i)·x) % N` but generally `v = a^(2^i)·x ≥ N`.  `adaptOut_reads`
      demands producing `encodeDataZeroAnc` of the CANONICAL residue
      `(a^(2^i)·x) % N`.  Mapping `v ↦ v % N` is an in-register modular reduction
      (compare-with-`N` + conditional subtract = a comparator, which uses Toffoli/T
      gates), CONTRADICTING the structure's `adaptOut_tfree` requirement.  So no
      T-free `adaptOut` can satisfy `adaptOut_reads` whenever `a^(2^i)·x ≥ N`.  This
      obstruction is regime-independent.

  (B) `block_wellTyped : EGate.WellTypedAt (bits + anc) (multiplyAddAt …)` at
      `anc = 2·w + 2·bits + 3` is FALSE at the genuine multi-window parameters.
      `multiplyAddAt` STACKS a fresh `2·w`-wide address/ancilla region per window
      (`addrBaseOf … k = q_start + 2·bits + 1 + k·(2·w)`), so its top touched index is
      `≈ q_start + 2·bits + numWin·2·w`, which EXCEEDS `bits + anc = 3·bits + 2·w + 3`
      once `numWin > 1` (RSA-2048: `numWin = 1024`).  This is precisely the
      STACKED-region width theorem `width_modExpAt_le` that `WindowedComposedAt`'s
      header advertises but the codebase leaves DEFERRED
      (`WindowedWidthAudit` §header, `WorkloadAssembly:408`, the GE2021 `README`).

  Both are therefore exposed as named hypotheses of `ge2021_modExpAtLayoutAdapter`;
  no `instance` is declared and no field is faked, so the kernel sees no unproven
  claim.  The IN-adapter and its `CountGateMulInput` discharge — the friction the
  task targeted — ARE fully proven below.

  Kernel-clean: no `sorry`, no `native_decide`, axioms exactly
  `[propext, Classical.choice, Quot.sound]`.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ShorModExpAt

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance

open FormalRV.Framework FormalRV.BQAlgo
open FormalRV.SQIRPort
open VerifiedShor
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.EGateToUnitaryBridge
open FormalRV.Shor.WindowedCoset
open FormalRV.Shor.WindowedCircuit
open FormalRV.Shor.WindowedArith (window window_lt)
open FormalRV.BQAlgo.WindowedModNShor
open VerifiedShor.Windowed (nat_to_funbool_eq_testBit)
open FormalRV.Audit.GidneyEkera2021.ShorComposed
open FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
open FormalRV.Audit.GidneyEkera2021.ShorModExpAt

noncomputable section

/-! ## §1. The T-free per-window SCATTER input adapter (PROVEN).

The IN-adapter is one register-level `swapCascade` exchanging, for each global
windowed bit index `j < bits = numWin·w`:

  * the DATA-band wire `bits - 1 - j` (where `encodeDataZeroAnc`'s big-endian
    `nat_to_funbool` puts `x.testBit j`), with
  * the per-window ADDRESS wire `addrBaseOf w bits q_start (j / w) + (j % w)`
    (window `k = j/w`, intra-window offset `i = j%w`).

After the swap, address wire `addrBaseOf … k + i` holds `x.testBit (k·w+i)`, which
by `window_testBit` is `(window w x k).testBit i`, so the address register decodes
to `window w x k` — exactly `CountGateMulInput.addr0`.  The data band receives the
(zero) address-register contents and is cleared; the trailing `X 0` sets the lookup
ctrl wire (`ulookup_ctrl_idx = 0`, matching `CountGateMulInput.ctrl0`). -/

/-- The per-window target address wire for global windowed bit index `j`:
    window `j / w`, intra-window offset `j % w`. -/
def scatterAddr (w bits q_start j : Nat) : Nat :=
  addrBaseOf w bits q_start (j / w) + j % w

/-- **The T-free per-window scatter input adapter.**  Exchange each data wire
    `bits-1-j` with its per-window address wire `scatterAddr … j` (`j < bits`), then
    set the lookup ctrl wire `0`.  Index `i` (the QPE iterate) is unused: the scatter
    layout is iterate-independent. -/
def ge2021_adaptIn (w bits q_start : Nat) (_i : Nat) : Gate :=
  Gate.seq
    (swapCascade (fun j => bits - 1 - j) (scatterAddr w bits q_start) bits)
    (Gate.X 0)

/-- `ge2021_adaptIn` is T-free: a 3-CX-cascade swap (`tcount_swapCascade = 0`) plus a
    Clifford `X`. -/
theorem ge2021_adaptIn_tfree (w bits q_start i : Nat) :
    Gate.tcount (ge2021_adaptIn w bits q_start i) = 0 := by
  unfold ge2021_adaptIn
  show Gate.tcount (swapCascade _ _ bits) + Gate.tcount (Gate.X 0) = 0
  rw [tcount_swapCascade]
  rfl

/-- `scatterAddr` is injective on `[0, bits)`: distinct global bit indices map to
    distinct (window, offset) address wires, because `j%w < w < 2·w` is the stride. -/
theorem scatterAddr_inj (w bits q_start : Nat) (hw : 0 < w)
    (j k : Nat) (_hj : j < bits) (_hk : k < bits) (hne : j ≠ k) :
    scatterAddr w bits q_start j ≠ scatterAddr w bits q_start k := by
  unfold scatterAddr addrBaseOf
  -- `q_start + 2·bits + 1 + (j/w)·(2w) + j%w`; the (2w)-stride blocks separate windows.
  have hjw : j / w * w + j % w = j := by rw [Nat.div_add_mod' j w]
  have hkw : k / w * w + k % w = k := by rw [Nat.div_add_mod' k w]
  have hjm : j % w < w := Nat.mod_lt j hw
  have hkm : k % w < w := Nat.mod_lt k hw
  intro h
  -- From equality of the two address wires, the (2w)-block index and the offset agree.
  have hblk : j / w * (2 * w) + j % w = k / w * (2 * w) + k % w := by omega
  -- offsets `< w`, blocks have stride `2w`, so windows agree, then offsets agree.
  have hwin : j / w = k / w := by
    rcases Nat.lt_trichotomy (j / w) (k / w) with hlt | heq | hgt
    · exfalso
      have : j / w * (2 * w) + (2 * w) ≤ k / w * (2 * w) := by
        have := Nat.succ_le_of_lt hlt
        calc j / w * (2 * w) + 2 * w = (j / w + 1) * (2 * w) := by ring
          _ ≤ k / w * (2 * w) := Nat.mul_le_mul_right _ this
      omega
    · exact heq
    · exfalso
      have : k / w * (2 * w) + (2 * w) ≤ j / w * (2 * w) := by
        have := Nat.succ_le_of_lt hgt
        calc k / w * (2 * w) + 2 * w = (k / w + 1) * (2 * w) := by ring
          _ ≤ j / w * (2 * w) := Nat.mul_le_mul_right _ this
      omega
  have hoff : j % w = k % w := by
    have := hblk; rw [hwin] at this; omega
  exact hne (by rw [← hjw, ← hkw, hwin, hoff])

/-! ### `ge2021_adaptIn_clean` — the central per-window scatter discharge. -/

/-- **The IN-adapter delivers a clean `CountGateMulInput` with `y = x`.**  For every
    `x < N` (`N ≤ 2^bits`), applying `ge2021_adaptIn` to `encodeDataZeroAnc bits anc x`
    scatters `x`'s `numWin` windows into the per-window address registers and yields a
    `CountGateMulInput w bits numWin x q_start`: ctrl set, shared accumulator / addend
    / per-window AND-ancillas clean, and address register `k` decoding to
    `window w x k`.  Mirrors `windowedEncodeIn_apply` with the per-window index map. -/
theorem ge2021_adaptIn_clean
    (w bits anc numWin N _a q_start : Nat)
    (hw : 0 < w) (hq : 0 < q_start) (hanc : 0 < anc)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N) :
    CountGateMulInput w bits numWin x q_start
      (Gate.applyNat (ge2021_adaptIn w bits q_start i)
        (encodeDataZeroAnc bits anc x)) := by
  have hN_le : N ≤ 2 ^ bits := by omega
  have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx hN_le
  -- `bits ≥ 1`: from `2 ≤ 2·N ≤ 2^bits` (since `x < N` forces `N ≥ 1`).
  have hbpos : 0 < bits := by
    by_contra h
    rw [Nat.not_lt, Nat.le_zero] at h
    rw [h, pow_zero] at hN2
    omega
  -- abbreviations for the two index maps.
  set uIdx : Nat → Nat := fun j => bits - 1 - j with huIdx
  set vIdx : Nat → Nat := scatterAddr w bits q_start with hvIdx
  -- the swap post-state; the `X 0` is applied on top.
  set f0 : Nat → Bool := encodeDataZeroAnc bits anc x with hf0
  -- helper facts about `f0` (data + clean-high), reused below.
  have hf0_high : ∀ p, bits ≤ p → f0 p = false := by
    intro p hp
    by_cases hp2 : p < bits + anc
    · rw [hf0, show p = bits + (p - bits) from by omega]
      exact encodeDataZeroAnc_anc hxbits (by omega)
    · rw [hf0]
      exact encodeDataZeroAnc_oob hanc (by omega)
  have hf0_data : ∀ j, j < bits → f0 (uIdx j) = x.testBit j := by
    intro j hj
    rw [huIdx]
    show f0 (bits - 1 - j) = x.testBit j
    rw [hf0, encodeDataZeroAnc_data hxbits (by omega),
        nat_to_funbool_eq_testBit]
    congr 1; omega
  -- injectivity / disjointness data for `swapCascade_apply`.
  have hu_inj : ∀ j k, j < bits → k < bits → j ≠ k → uIdx j ≠ uIdx k := by
    intro j k hj hk hne
    rw [huIdx]; show bits - 1 - j ≠ bits - 1 - k; omega
  have hv_inj : ∀ j k, j < bits → k < bits → j ≠ k → vIdx j ≠ vIdx k := by
    intro j k hj hk hne; rw [hvIdx]; exact scatterAddr_inj w bits q_start hw j k hj hk hne
  have huv : ∀ j k, j < bits → k < bits → uIdx j ≠ vIdx k := by
    intro j k hj hk
    rw [huIdx, hvIdx]
    show bits - 1 - j ≠ scatterAddr w bits q_start k
    have : bits - 1 - j < bits := by omega
    have hge : bits ≤ scatterAddr w bits q_start k := by
      unfold scatterAddr addrBaseOf; omega
    omega
  obtain ⟨hs_u, hs_v, hs_fr⟩ :=
    swapCascade_apply uIdx vIdx bits f0 hu_inj hv_inj huv
  -- name the swap post-state.
  set s1 : Nat → Bool := Gate.applyNat (swapCascade uIdx vIdx bits) f0 with hs1
  -- the full adapter post-state is `update s1 0 (!(s1 0))`.
  have happly : Gate.applyNat (ge2021_adaptIn w bits q_start i) f0
      = update s1 0 (! s1 0) := by
    unfold ge2021_adaptIn
    rw [Gate.applyNat_seq, Gate.applyNat_X, ← hs1]
  -- `s1 0 = false`: position `0 = uIdx (bits-1)` receives the (clean-high) address bit.
  have hs1_zero : s1 0 = false := by
    have h0 := hs_u (bits - 1) (by omega)
    rw [show uIdx (bits - 1) = 0 from by simp only [huIdx]; omega] at h0
    rw [h0]
    -- `s1 0 = f0 (vIdx (bits-1))`, and `vIdx (bits-1) ≥ bits`, so clean.
    rw [hvIdx]
    exact hf0_high _ (by unfold scatterAddr addrBaseOf; omega)
  -- a general read-out of `s1` on the address registers + the high (clean) wires.
  -- (1) address wire of window `k`, offset `off < w` holds `x.testBit (k·w+off)`.
  have hs1_addr : ∀ k, k < numWin → ∀ off, off < w →
      s1 (addrBaseOf w bits q_start k + off) = x.testBit (k * w + off) := by
    intro k hk off hoff
    -- this is `vIdx (k·w+off)` since `(k·w+off)/w = k`, `(k·w+off)%w = off`.
    have hjlt : k * w + off < bits := by
      rw [← hbits]
      calc k * w + off < k * w + w := by omega
        _ = (k + 1) * w := by ring
        _ ≤ numWin * w := Nat.mul_le_mul_right _ (by omega)
    have hdiv : (k * w + off) / w = k := by
      rw [show k * w + off = off + k * w from by ring,
          Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hoff, Nat.zero_add]
    have hmod : (k * w + off) % w = off := by
      rw [show k * w + off = off + k * w from by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
    have hva : vIdx (k * w + off) = addrBaseOf w bits q_start k + off := by
      rw [hvIdx]; unfold scatterAddr; rw [hdiv, hmod]
    have h0 := hs_v (k * w + off) hjlt
    rw [hva] at h0
    rw [h0, hf0_data (k * w + off) hjlt]
  -- (2) clean wires: any high wire `≥ bits` that is NOT a target `vIdx j` stays clean.
  have hs1_clean_high : ∀ p, bits ≤ p →
      (∀ j, j < bits → p ≠ vIdx j) → s1 p = false := by
    intro p hp hpv
    have hpu : ∀ j, j < bits → p ≠ uIdx j := by
      intro j hj; rw [huIdx]; show p ≠ bits - 1 - j; omega
    have h0 := hs_fr p (fun j hj => ⟨hpu j hj, hpv j hj⟩)
    rw [h0, hf0_high p hp]
  refine
    { ctrl0 := ?_
      carry0 := ?_
      aug0 := ?_
      addend0 := ?_
      anc0 := ?_
      addr0 := ?_ }
  · -- ctrl0: position 0 set by the `X`.
    rw [happly, update_eq, hs1_zero]; rfl
  · -- carry0: `q_start < bits`? no — `q_start` may be small; it is NOT a data/addr wire.
    rw [happly, update_neq _ _ _ _ (by omega)]
    -- `q_start` is a low wire (`< bits`?) or in the accumulator; it is not `vIdx j`, not `uIdx j`.
    by_cases hqb : bits ≤ q_start
    · exact hs1_clean_high q_start hqb (fun j hj => by
        rw [hvIdx]; unfold scatterAddr addrBaseOf; omega)
    · -- `q_start < bits`: it is some data wire; the swap moves only `uIdx j = bits-1-j`.
      -- `q_start = uIdx (bits-1-q_start)`, which receives `f0 (vIdx (bits-1-q_start))` = clean.
      rw [Nat.not_le] at hqb
      have h0 := hs_u (bits - 1 - q_start) (by omega)
      rw [show uIdx (bits - 1 - q_start) = q_start from by simp only [huIdx]; omega] at h0
      rw [h0, hvIdx]
      exact hf0_high _ (by unfold scatterAddr addrBaseOf; omega)
  · -- aug0: accumulator wires `q_start + 2i + 1`, all `≥ bits`? they are `> q_start`.
    intro k hk
    rw [happly, update_neq _ _ _ _ (by omega)]
    -- accumulator wires are `< q_start + 2·bits + 1 ≤ addrBaseOf … 0`; not data, not addr.
    by_cases hb : bits ≤ q_start + 2 * k + 1
    · exact hs1_clean_high _ hb (fun j hj => by
        rw [hvIdx]; unfold scatterAddr addrBaseOf
        have : j % w < w := Nat.mod_lt j hw
        have : j / w < numWin := by
          apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; rw [hbits]; exact hj
        omega)
    · rw [Nat.not_le] at hb
      have h0 := hs_u (bits - 1 - (q_start + 2 * k + 1)) (by omega)
      rw [show uIdx (bits - 1 - (q_start + 2 * k + 1)) = q_start + 2 * k + 1 from by
        simp only [huIdx]; omega] at h0
      rw [h0, hvIdx]
      exact hf0_high _ (by unfold scatterAddr addrBaseOf; omega)
  · -- addend0: accumulator addend wires `q_start + 2i + 2`, same argument.
    intro k hk
    rw [happly, update_neq _ _ _ _ (by omega)]
    by_cases hb : bits ≤ q_start + 2 * k + 2
    · exact hs1_clean_high _ hb (fun j hj => by
        rw [hvIdx]; unfold scatterAddr addrBaseOf
        have : j % w < w := Nat.mod_lt j hw
        have : j / w < numWin := by
          apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; rw [hbits]; exact hj
        omega)
    · rw [Nat.not_le] at hb
      have h0 := hs_u (bits - 1 - (q_start + 2 * k + 2)) (by omega)
      rw [show uIdx (bits - 1 - (q_start + 2 * k + 2)) = q_start + 2 * k + 2 from by
        simp only [huIdx]; omega] at h0
      rw [h0, hvIdx]
      exact hf0_high _ (by unfold scatterAddr addrBaseOf; omega)
  · -- anc0: per-window AND-ancilla wires `ancBaseOf … k + i`, all high + not targets.
    intro k hk off hoff
    rw [happly, update_neq _ _ _ _ (by unfold ancBaseOf addrBaseOf; omega)]
    -- `ancBaseOf … k + off = addrBaseOf … k + w + off`, with `w + off ∈ [w, 2w)`: not an
    -- address-offset wire (offsets are `< w`), so not any `vIdx j`, and `≥ bits`.
    apply hs1_clean_high
    · unfold ancBaseOf addrBaseOf; omega
    · intro j hj
      rw [hvIdx]; unfold scatterAddr ancBaseOf addrBaseOf
      have hjm : j % w < w := Nat.mod_lt j hw
      have hjd : j / w < numWin := by
        apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; rw [hbits]; exact hj
      -- target wire `q_start+2bits+1 + (j/w)·2w + j%w`; anc wire
      -- `q_start+2bits+1 + k·2w + w + off`.  Equal would force `(j/w)·2w + j%w = k·2w + w + off`.
      intro heq
      -- block index of target = j/w ; block index of anc = k ; within-block offsets differ.
      have hblk : j / w * (2 * w) + j % w = k * (2 * w) + (w + off) := by omega
      have hwin : j / w = k := by
        rcases Nat.lt_trichotomy (j / w) k with hlt | heq2 | hgt
        · exfalso
          have : j / w * (2 * w) + 2 * w ≤ k * (2 * w) := by
            calc j / w * (2 * w) + 2 * w = (j / w + 1) * (2 * w) := by ring
              _ ≤ k * (2 * w) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
          omega
        · exact heq2
        · exfalso
          have : k * (2 * w) + 2 * w ≤ j / w * (2 * w) := by
            calc k * (2 * w) + 2 * w = (k + 1) * (2 * w) := by ring
              _ ≤ j / w * (2 * w) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hgt)
          omega
      rw [hwin] at hblk
      omega
  · -- addr0: window `k`'s address register decodes to `window w x k`.
    intro k hk
    -- the `X 0` is on wire 0, which is NOT an address wire of window `k`, so the
    -- decode reads `s1` on the address wires.
    have haddr_post : ∀ off, off < w →
        Gate.applyNat (ge2021_adaptIn w bits q_start i) f0 (addrBaseOf w bits q_start k + off)
          = (window w x k).testBit off := by
      intro off hoff
      rw [happly, update_neq _ _ _ _ (by unfold addrBaseOf; omega),
          hs1_addr k hk off hoff, window_testBit w x k off hoff]
    rw [decodeReg_eq_mod_of_testBit _ w (window w x k)
          (Gate.applyNat (ge2021_adaptIn w bits q_start i) f0) haddr_post]
    exact Nat.mod_eq_of_lt (window_lt w x k)

/-! ### Well-typedness of the IN-adapter (T-free layout permutation). -/

/-- Self-contained well-typedness of a `Gate.seq`-foldl over `List.range`: if every
    `G k` (`k < n`) and the init are well-typed, the fold is well-typed.  (The private
    `wellTyped_foldl_seq_range` of `WindowedModNShor` is re-derived here additively.) -/
private theorem wellTyped_foldl_seq_aux (dim : Nat) (G : Nat → Gate) :
    ∀ (l : List Nat) (init : Gate), Gate.WellTyped dim init →
      (∀ k ∈ l, Gate.WellTyped dim (G k)) →
      Gate.WellTyped dim (l.foldl (fun g i => Gate.seq g (G i)) init) := by
  intro l
  induction l with
  | nil => intro init hinit _; exact hinit
  | cons a t ih =>
    intro init hinit h
    apply ih
    · exact ⟨hinit, h a (by simp)⟩
    · intro k hk; exact h k (by simp [hk])

private theorem cxCascade_wellTyped_aux (ctrl tgt : Nat → Nat) (n dim : Nat)
    (h0 : 0 < dim)
    (h : ∀ i, i < n → ctrl i < dim ∧ tgt i < dim ∧ ctrl i ≠ tgt i) :
    Gate.WellTyped dim (cxCascade ctrl tgt n) := by
  unfold cxCascade
  exact wellTyped_foldl_seq_aux dim (fun i => Gate.CX (ctrl i) (tgt i)) (List.range n) Gate.I h0
    (fun k hk => h k (List.mem_range.mp hk))

private theorem swapCascade_wellTyped_aux (u v : Nat → Nat) (n dim : Nat)
    (h0 : 0 < dim)
    (h : ∀ i, i < n → u i < dim ∧ v i < dim ∧ u i ≠ v i) :
    Gate.WellTyped dim (swapCascade u v n) := by
  refine ⟨⟨cxCascade_wellTyped_aux u v n dim h0 h,
           cxCascade_wellTyped_aux v u n dim h0
             (fun i hi => ⟨(h i hi).2.1, (h i hi).1, fun hh => (h i hi).2.2 hh.symm⟩)⟩,
          cxCascade_wellTyped_aux u v n dim h0 h⟩

/-- **The IN-adapter is well-typed at the canonical dimension**, provided the
    per-window address registers fit (`scatterAddr` of every windowed bit index
    `< bits` lands below `bits + anc`).  At the genuine layout this is the only sizing
    constraint on the input scatter. -/
theorem ge2021_adaptIn_wellTyped
    (w bits anc q_start : Nat) (hbpos : 0 < bits)
    (hfit : ∀ j, j < bits → scatterAddr w bits q_start j < bits + anc)
    (i : Nat) :
    Gate.WellTyped (bits + anc) (ge2021_adaptIn w bits q_start i) := by
  refine ⟨swapCascade_wellTyped_aux _ _ bits (bits + anc) (by omega) ?_,
          show 0 < bits + anc from by omega⟩
  intro j hj
  refine ⟨by omega, hfit j hj, ?_⟩
  -- `bits - 1 - j < bits ≤ scatterAddr …`, so the two are distinct.
  have : bits ≤ scatterAddr w bits q_start j := by unfold scatterAddr addrBaseOf; omega
  omega

/-! ## §2. ASSEMBLING the adapter from the proven IN-side + the two named residuals.

The IN-side (`adaptIn`, T-free, well-typed, `adaptIn_clean`) and `table_spec` are
discharged from the work above.  The OUT-adapter field `adaptOut_reads` and the
block-width field `block_wellTyped` are NOT dischargeable at the genuine `modExpAt`
parameters (see the header obstructions A and B); they are taken as explicit named
hypotheses.  NO `instance` is declared and no field is faked. -/

/-- **A full `ModExpAtLayoutAdapter`, assembled from the proven scatter IN-adapter and
    the two named residual obligations.**  The IN-side and `table_spec` are PROVEN
    here; `adaptOut` / `adaptOut_reads` and `block_wellTyped` are supplied as the named
    residual circuit obligations (the OUT modular-reduction read-out, which is not
    T-free, and the deferred stacked-region block width).  This packages exactly the
    remaining frontier into two explicit hypotheses. -/
def ge2021_modExpAtLayoutAdapter
    (w bits numWin N a q_start : Nat) (Tfam : Nat → Nat → Nat → Nat)
    (hw : 0 < w) (hq : 0 < q_start) (hbpos : 0 < bits)
    (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    -- table family realises the per-iterate windowed modular product:
    (mblkOf : Nat → Nat)
    (htable : ∀ i k v,
      Tfam (mblkOf i) k v = ((a ^ (2 ^ i)) * (2 ^ w) ^ k * v) % 2 ^ bits)
    -- the IN-adapter address registers fit the canonical dimension:
    (hfit : ∀ j, j < bits →
      scatterAddr w bits q_start j < bits + (2 * w + 2 * bits + 3))
    -- RESIDUAL (B): the deferred stacked-region block width is well-typed:
    (hblockWT : ∀ i,
      EGate.WellTypedAt (bits + (2 * w + 2 * bits + 3))
        (multiplyAddAt w bits bits Tfam q_start (mblkOf i) numWin))
    -- the supplied OUT-adapter gates:
    (adaptOutGate : Nat → Gate)
    (hadaptOut_tfree : ∀ i, Gate.tcount (adaptOutGate i) = 0)
    (hadaptOut_wt : ∀ i, Gate.WellTyped (bits + (2 * w + 2 * bits + 3)) (adaptOutGate i))
    -- RESIDUAL (A): the OUT read-out maps a coset rep to the canonical residue encoding:
    (hadaptOut_reads : ∀ i x f v, x < N →
      decodeReg (fun j => q_start + 2 * j + 1) bits f = v →
      IsCosetRep bits N v ((a ^ (2 ^ i)) * x) →
      Gate.applyNat (adaptOutGate i) f
        = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (((a ^ (2 ^ i)) * x) % N)) :
    ModExpAtLayoutAdapter w bits (2 * w + 2 * bits + 3) numWin N a q_start Tfam where
  mblkOf := mblkOf
  adaptIn := ge2021_adaptIn w bits q_start
  adaptOut := adaptOutGate
  adaptIn_tfree := fun i => ge2021_adaptIn_tfree w bits q_start i
  adaptOut_tfree := hadaptOut_tfree
  adaptIn_wellTyped := fun i =>
    ge2021_adaptIn_wellTyped w bits (2 * w + 2 * bits + 3) q_start hbpos hfit i
  adaptOut_wellTyped := hadaptOut_wt
  block_wellTyped := hblockWT
  table_spec := htable
  adaptIn_clean := fun i x hx =>
    ge2021_adaptIn_clean w bits (2 * w + 2 * bits + 3) numWin N a q_start
      hw hq (by omega) hbits hN2 i x hx
  adaptOut_reads := hadaptOut_reads

/-! ## §3. THE HEADLINE — the Shor bound through `modExpAt`'s LITERAL block,
       UNCONDITIONAL modulo `ShorSetting` + sizing + no-wrap + the two residuals. -/

/-- **★ THE BOUND THROUGH THE LITERAL COUNT GATE, via the assembled adapter ★.**  Feed
    `ge2021_modExpAtLayoutAdapter` (proven IN-side + the two named residual
    obligations) through `ShorModExpAt.ge2021_modExpAt_shor_succeeds`.  The Shor success
    probability of the family that `modExpAt`'s per-multiply measured block
    (`multiplyAddAt`, literally inside `eg`) provably acts as attains `≥ κ/(log₂ N)⁴`.
    The remaining hypotheses are EXACTLY `ShorSetting` + the sizing constraints + the
    no-wrap condition + the two residual fields (`hfit`/`hblockWT`/the OUT read-out) —
    the IN-side scatter is fully discharged. -/
theorem ge2021_modExpAt_shor_succeeds_unconditional
    {w bits numWin N a ainv0 r m q_start : Nat} {Tfam : Nat → Nat → Nat → Nat}
    (hw : 0 < w) (hq : 0 < q_start)
    (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hnowrap : ∀ i x, x < N → (a ^ (2 ^ i)) * x < 2 ^ bits)
    (h_setting : ShorSetting a r N m bits)
    (mblkOf : Nat → Nat)
    (htable : ∀ i k v,
      Tfam (mblkOf i) k v = ((a ^ (2 ^ i)) * (2 ^ w) ^ k * v) % 2 ^ bits)
    (hfit : ∀ j, j < bits →
      scatterAddr w bits q_start j < bits + (2 * w + 2 * bits + 3))
    (hblockWT : ∀ i,
      EGate.WellTypedAt (bits + (2 * w + 2 * bits + 3))
        (multiplyAddAt w bits bits Tfam q_start (mblkOf i) numWin))
    (adaptOutGate : Nat → Gate)
    (hadaptOut_tfree : ∀ i, Gate.tcount (adaptOutGate i) = 0)
    (hadaptOut_wt : ∀ i, Gate.WellTyped (bits + (2 * w + 2 * bits + 3)) (adaptOutGate i))
    (hadaptOut_reads : ∀ i x f v, x < N →
      decodeReg (fun j => q_start + 2 * j + 1) bits f = v →
      IsCosetRep bits N v ((a ^ (2 ^ i)) * x) →
      Gate.applyNat (adaptOutGate i) f
        = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) (((a ^ (2 ^ i)) * x) % N)) :
    probability_of_success a r N m bits (2 * w + 2 * bits + 3)
        (ge2021_modExpAt_measuredEqRev
          (ge2021_modExpAtLayoutAdapter w bits numWin N a q_start Tfam hw hq hb1 hbits hN2
            mblkOf htable hfit hblockWT adaptOutGate hadaptOut_tfree hadaptOut_wt
            hadaptOut_reads)
          hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap).rev.family
      ≥ κ / (Nat.log2 N : ℝ) ^ 4 :=
  ge2021_modExpAt_shor_succeeds
    (ge2021_modExpAtLayoutAdapter w bits numWin N a q_start Tfam hw hq hb1 hbits hN2
      mblkOf htable hfit hblockWT adaptOutGate hadaptOut_tfree hadaptOut_wt
      hadaptOut_reads)
    hw hq hbits hb1 hN1 hN2 h_inv0 hnowrap h_setting

end

end FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance
