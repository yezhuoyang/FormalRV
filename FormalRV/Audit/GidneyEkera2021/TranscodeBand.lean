/-
  Audit · Gidney–Ekerå 2021 · `TranscodeBand` — a GENERIC T-free wire-permutation
  band-mover, plus the SPECIFIC accumulator→data-band instance.
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  A T-free (`tcount = 0`) reversible gate that MOVES a `bits`-wide register
  from one set of qubit positions to a DISJOINT set of positions — a pure wire
  permutation realised by a SWAP cascade.  This is the layout-reconciliation
  engine needed to take the reduced residue out of `multiplyAddAt`'s INTERLEAVED
  accumulator band (positions `q_start + 2·j + 1`, LSB-first per `decodeReg`) and
  drop it into `encodeDataZeroAnc`'s BIG-endian data band `[0, bits)` (data wire
  `i` carrying `v.testBit (bits-1-i)`, i.e. `nat_to_funbool bits v i`).

  ────────────────────────────────────────────────────────────────────────────
  WHAT IS PROVEN HERE (no `sorry`, no `native_decide`, kernel-clean)
  ────────────────────────────────────────────────────────────────────────────
  GENERIC BAND-MOVER (`transcodeBand src dst len := swapCascade src dst len`):
  • `transcodeBand_tcount`     — `tcount = 0` (3 CX cascades, Clifford).
  • `transcodeBand_wellTyped`  — `WellTyped D` given both ranges fit in `[0,D)`
                                  and `src k ≠ dst k`.
  • `transcodeBand_apply`      — for `f` with the `dst`-range all-false, and
      `src`/`dst` injective + fully disjoint:
        (a) READOUT  : `applyNat … (dst k) = f (src k)`     (value moved to dst),
        (b) CLEAR    : `applyNat … (src k) = false`         (source emptied),
        (c) FRAME    : positions off `src ∪ dst` are untouched.

  SPECIFIC INSTANCE
  (`transcodeAccToData w bits q_start :=
        transcodeBand (fun j => q_start + 2·j + 1) (fun j => bits-1-j) bits`):
  • `transcodeAccToData_tcount`     — T-free.
  • `transcodeAccToData_wellTyped`  — well-typed at any `D` covering both bands.
  • `transcodeAccToData_apply`      — THE RECONCILIATION.  Given the accumulator
      band decodes to `v` (`decodeReg (fun j => q_start+2·j+1) bits f = v`), the
      data band `[0,bits)` is all-false, and the accumulator band sits above the
      data band (`bits ≤ q_start`):
        · data band reproduces `encodeDataZeroAnc bits anc v` on `[0,bits)`,
        · accumulator band `q_start+2·j+1` is cleared,
        · everything off the two bands is framed.

  ────────────────────────────────────────────────────────────────────────────
  THE ENDIANNESS CRUX (verified against `encodeDataZeroAnc_data`)
  ────────────────────────────────────────────────────────────────────────────
  `decodeReg (fun j => q_start+2·j+1) bits f` is LSB-first: accumulator wire
  `q_start+2·j+1` carries `v.testBit j`  (`decodeReg_testBit`).
  `encodeDataZeroAnc bits anc v i = nat_to_funbool bits v i = v.testBit (bits-1-i)`
  for `i < bits`  (`encodeDataZeroAnc_data` ∘ `nat_to_funbool_eq_testBit`) — i.e.
  BIG-endian: data wire `i` carries `v.testBit (bits-1-i)`.  The swap therefore
  sends accumulator index `j` to data wire `bits-1-j` (and equivalently data wire
  `i` receives accumulator index `bits-1-i`), reversing the bit order in the same
  cascade.  Hence `dst j := bits-1-j`.

  Where this fits:  `ShorModExpAt.ModExpAtLayoutAdapter.adaptOut_reads` demands the
  big-endian read-out of the accumulator residue.  This file discharges the T-free
  layout/endianness half of that read-out (the value `v` itself, NOT `v % N`; the
  modular `% N` reduction is the genuine Toffoli cost noted in
  `ModExpAtLayoutAdapterInstance`, and is out of scope for a T-free gate).

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.WindowedModNShor

namespace FormalRV.Audit.GidneyEkera2021.TranscodeBand

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.BQAlgo.WindowedModNShor (swapCascade swapCascade_apply
  swapCascade_wellTyped tcount_swapCascade)
open FormalRV.Shor.WindowedCircuit (decodeReg_testBit)
open VerifiedShor.Windowed (nat_to_funbool_eq_testBit)

/-! ## §1. The generic T-free band-mover.

`transcodeBand src dst len` is exactly `swapCascade src dst len`: it exchanges,
for each `k < len`, the wire at `src k` with the wire at `dst k`, via the proven
3-CX-cascade SWAP engine.  All semantics are inherited from `swapCascade`. -/

/-- **Generic band-mover.**  A T-free wire permutation that, for each `k < len`,
    swaps position `src k` with position `dst k`.  (Three interleaved CX cascades
    — `swapCascade`.) -/
def transcodeBand (src dst : Nat → Nat) (len : Nat) : Gate :=
  swapCascade src dst len

/-- The band-mover is T-free (it is a Clifford SWAP cascade). -/
theorem transcodeBand_tcount (src dst : Nat → Nat) (len : Nat) :
    (transcodeBand src dst len).tcount = 0 := by
  unfold transcodeBand
  exact tcount_swapCascade src dst len

/-- The band-mover is well-typed at dimension `D` whenever both ranges fit in
    `[0, D)` and corresponding positions differ (`src k ≠ dst k`). -/
theorem transcodeBand_wellTyped (src dst : Nat → Nat) (len D : Nat)
    (hD : 0 < D)
    (hfit : ∀ k, k < len → src k < D ∧ dst k < D)
    (hne : ∀ k, k < len → src k ≠ dst k) :
    Gate.WellTyped D (transcodeBand src dst len) := by
  unfold transcodeBand
  exact swapCascade_wellTyped src dst len D hD
    (fun k hk => ⟨(hfit k hk).1, (hfit k hk).2, hne k hk⟩)

/-- **Generic band-mover semantics.**  With the `dst`-range all-false in `f`, and
    `src`/`dst` injective on `[0,len)` and the two ranges fully disjoint:
    (a) READOUT — `dst k` now holds `f (src k)` (the value moved to `dst`);
    (b) CLEAR   — `src k` now holds `false` (source emptied);
    (c) FRAME   — every position off `src ∪ dst` is unchanged. -/
theorem transcodeBand_apply (src dst : Nat → Nat) (len : Nat) (f : Nat → Bool)
    (hsrc_inj : ∀ i k, i < len → k < len → i ≠ k → src i ≠ src k)
    (hdst_inj : ∀ i k, i < len → k < len → i ≠ k → dst i ≠ dst k)
    (hdisj : ∀ i k, i < len → k < len → src i ≠ dst k)
    (hdst_false : ∀ k, k < len → f (dst k) = false) :
    (∀ k, k < len → Gate.applyNat (transcodeBand src dst len) f (dst k) = f (src k))
    ∧ (∀ k, k < len → Gate.applyNat (transcodeBand src dst len) f (src k) = false)
    ∧ (∀ p, (∀ k, k < len → p ≠ src k ∧ p ≠ dst k) →
        Gate.applyNat (transcodeBand src dst len) f p = f p) := by
  unfold transcodeBand
  obtain ⟨h_u, h_v, h_fr⟩ :=
    swapCascade_apply src dst len f hsrc_inj hdst_inj hdisj
  refine ⟨?_, ?_, ?_⟩
  · -- readout: `applyNat (dst k) = f (src k)` (second conjunct of swapCascade_apply)
    intro k hk
    exact h_v k hk
  · -- clear: `applyNat (src k) = f (dst k) = false` (first conjunct + dst all-false)
    intro k hk
    rw [h_u k hk]
    exact hdst_false k hk
  · -- frame (third conjunct)
    intro p hp
    exact h_fr p hp

/-! ## §2. The specific instance: accumulator band → big-endian data band.

`transcodeAccToData w bits q_start` moves the in-place multiplier's interleaved
accumulator (`src j = q_start + 2·j + 1`, LSB-first) into `encodeDataZeroAnc`'s
big-endian data band (`dst j = bits - 1 - j`).  The map `j ↦ bits-1-j` is the
exact bit-reversal that takes LSB-first weight-`2^j` to big-endian data wire
`bits-1-j` (where `encodeDataZeroAnc bits anc v` carries `v.testBit j`). -/

/-- **Accumulator→data band-mover.**  `src j = q_start + 2·j + 1` (the interleaved
    accumulator wire of weight `2^j`), `dst j = bits - 1 - j` (the big-endian data
    wire that `encodeDataZeroAnc` puts `v.testBit j` at). -/
def transcodeAccToData (w bits q_start : Nat) : Gate :=
  transcodeBand (fun j => q_start + 2 * j + 1) (fun j => bits - 1 - j) bits

/-- The accumulator→data mover is T-free. -/
theorem transcodeAccToData_tcount (w bits q_start : Nat) :
    (transcodeAccToData w bits q_start).tcount = 0 := by
  unfold transcodeAccToData
  exact transcodeBand_tcount _ _ _

/-- The accumulator→data mover is well-typed at any `D` covering both bands:
    the top accumulator wire `q_start + 2·(bits-1) + 1 < D`, and the accumulator
    sits above the data band (`bits ≤ q_start`, so the two bands never collide). -/
theorem transcodeAccToData_wellTyped (w bits q_start D : Nat)
    (hbits : 0 < bits) (hq : bits ≤ q_start)
    (hD : q_start + 2 * bits < D) :
    Gate.WellTyped D (transcodeAccToData w bits q_start) := by
  unfold transcodeAccToData
  refine transcodeBand_wellTyped _ _ bits D (by omega) ?_ ?_
  · intro k hk
    refine ⟨by omega, by omega⟩
  · intro k hk
    -- `src k = q_start+2k+1 ≥ q_start+1 > q_start ≥ bits > bits-1-k = dst k`
    omega

/-- **THE RECONCILIATION (specific instance).**  Suppose:
    · the accumulator band decodes to `v`
      (`decodeReg (fun j => q_start+2·j+1) bits f = v`);
    · the big-endian data band `[0,bits)` is all-false in `f`;
    · the accumulator band lies strictly above the data band (`bits ≤ q_start`).
    Then, after `transcodeAccToData`:
    (a) DATA  — the data band `[0,bits)` reproduces `encodeDataZeroAnc bits anc v`
        (the EXACT big-endian convention; `anc` is a free spectator parameter);
    (b) CLEAR — every accumulator wire `q_start + 2·j + 1` (`j < bits`) is `false`;
    (c) FRAME — every position off the two bands is unchanged. -/
theorem transcodeAccToData_apply (w bits q_start anc : Nat) (f : Nat → Bool)
    (v : Nat) (_hbits : 0 < bits) (hq : bits ≤ q_start)
    (hv : decodeReg (fun j => q_start + 2 * j + 1) bits f = v)
    (hvlt : v < 2 ^ bits)
    (hdata0 : ∀ i, i < bits → f i = false) :
    (∀ i, i < bits →
        Gate.applyNat (transcodeAccToData w bits q_start) f i
          = encodeDataZeroAnc bits anc v i)
    ∧ (∀ j, j < bits →
        Gate.applyNat (transcodeAccToData w bits q_start) f (q_start + 2 * j + 1)
          = false)
    ∧ (∀ p, (∀ j, j < bits → p ≠ q_start + 2 * j + 1 ∧ p ≠ bits - 1 - j) →
        Gate.applyNat (transcodeAccToData w bits q_start) f p = f p) := by
  unfold transcodeAccToData
  set src : Nat → Nat := fun j => q_start + 2 * j + 1 with hsrc
  set dst : Nat → Nat := fun j => bits - 1 - j with hdst
  -- injectivity / disjointness facts for the two index maps.
  have hsrc_inj : ∀ i k, i < bits → k < bits → i ≠ k → src i ≠ src k := by
    intro i k _ _ hik; simp only [hsrc]; omega
  have hdst_inj : ∀ i k, i < bits → k < bits → i ≠ k → dst i ≠ dst k := by
    intro i k hi hk hik; simp only [hdst]; omega
  have hdisj : ∀ i k, i < bits → k < bits → src i ≠ dst k := by
    intro i k _ hk; simp only [hsrc, hdst]; omega
  -- the data band is exactly the `dst`-range; it is all-false by hypothesis.
  have hdst_false : ∀ k, k < bits → f (dst k) = false := by
    intro k hk; simp only [hdst]; exact hdata0 _ (by omega)
  obtain ⟨h_read, h_clear, h_frame⟩ :=
    transcodeBand_apply src dst bits f hsrc_inj hdst_inj hdisj hdst_false
  refine ⟨?_, ?_, ?_⟩
  · -- (a) DATA: data wire `i` = `dst (bits-1-i)`; readout gives `f (src (bits-1-i))`
    --     = `v.testBit (bits-1-i)` = `encodeDataZeroAnc bits anc v i`.
    intro i hi
    -- rewrite `i` as `dst (bits-1-i)` with `bits-1-i < bits`.
    have hidx : dst (bits - 1 - i) = i := by simp only [hdst]; omega
    have hlt : bits - 1 - i < bits := by omega
    have hr := h_read (bits - 1 - i) hlt
    rw [hidx] at hr
    rw [hr]
    -- `f (src (bits-1-i)) = (decodeReg src bits f).testBit (bits-1-i)`.
    have hbit : f (src (bits - 1 - i))
        = (decodeReg src bits f).testBit (bits - 1 - i) :=
      (decodeReg_testBit src bits f (bits - 1 - i) hlt).symm
    rw [hbit, hv]
    -- big-endian target: `encodeDataZeroAnc bits anc v i = v.testBit (bits-1-i)`.
    rw [encodeDataZeroAnc_data hvlt hi, nat_to_funbool_eq_testBit]
  · -- (b) CLEAR: each accumulator wire `src j` is emptied.
    intro j hj
    exact h_clear j hj
  · -- (c) FRAME.
    intro p hp
    exact h_frame p hp

end FormalRV.Audit.GidneyEkera2021.TranscodeBand
