/-
  FormalRV.Shor.GidneyInPlace.ProductAddLayout
  ───────────────────────────────────────────────
  LAYOUT AUDIT (layout only — NO arithmetic correctness here, by directive).

  Goal: pin the EXACT local register layout for the faithful Gidney two-register
  in-place product-add, and DETERMINE whether the packed two-base adder instance
  `contiguousPackedAdder` (valid := addBase = accBase + bits) is sufficient, or
  whether a RELOCATED contiguous instance (independent addend base) is needed
  BEFORE any arithmetic-correctness proof.

  ── The faithful construction (GIDNEY_INPLACE_DESIGN §2) ────────────────────────
      pass 1:  b += a·k        accumulator = b,  multiplicand = a  (read for lookup)
      pass 2:  a -= b·kInv      accumulator = a,  multiplicand = b
      then:    (a,b) := (b,a)   logical relabel
  So BOTH registers must, in turn, serve as the adder's ACCUMULATOR; each pass also
  needs an addend-temp (the per-window lookup output, `A.addendIdx`) and carry.

  ── Existing single-pass layout (ReducedLookupCosetGate, `cosetDim`) ────────────
  `cosetModMulCircuitOf` runs `windowedMulTOf` at `q_start = 1+2w`,
  `yBase = 1+2w + span`, on `cosetDim w bits = 2 + 2w + 3·bits` qubits:
      [0, 1+2w)              lookup zone   (ctrl=0; address 1,3,…,2w-1; AND-anc 2,4,…,2w)
      [1+2w, 1+2w+span)      ONE adder region (accumulator + addend-temp + carry)
      [1+2w+span, …)         the multiplicand y-register (a BARE `bits` block)
  Key: `windowedMulTOf` takes `q_start` (accumulator base) and `yBase` (multiplicand
  base) as INDEPENDENT free parameters; only `…CircuitTOf` hard-wires
  `yBase = q_start + span`.  The multiplicand is read by `copyWindow` from `yBase`,
  so it can sit at ANY base.

  ── The design-doc cosetDim two-register layout (§4.1) — audited below ──────────
  Pack `a`, `b` ADJACENT after the lookup zone, with ONE SHARED addend-temp + carry:
      [0, 1+2w)                       lookup zone
      [1+2w,        1+2w+bits)        register a            (`aReg`)
      [1+2w+bits,   1+2w+2·bits)      register b            (`bReg`)
      [1+2w+2·bits, 1+2w+3·bits)      shared addend-temp    (`temp`)
      {1+2w+3·bits}                   carry                 (`carry`)
  total = 2 + 2w + 3·bits = `cosetDim w bits`  (resource-faithful: matches the
  retired single-region accYSwap variant's footprint).
-/
import FormalRV.Arithmetic.Adder.ContiguousTransport

namespace FormalRV.Shor.GidneyInPlace.ProductAddLayout

open FormalRV.BQAlgo

/-! ## §1. The design-doc `cosetDim` two-register layout (bases). -/

/-- Shared lookup zone occupies `[0, 1+2w)`. -/
def lookupZone (w : Nat) : Nat := 1 + 2 * w
/-- Register `a` base (just after the lookup zone). -/
def aReg (w : Nat) : Nat := 1 + 2 * w
/-- Register `b` base (adjacent, after `a`). -/
def bReg (w bits : Nat) : Nat := 1 + 2 * w + bits
/-- Shared addend-temp (per-window lookup output) base. -/
def temp (w bits : Nat) : Nat := 1 + 2 * w + 2 * bits
/-- Carry / adder ancilla position. -/
def carry (w bits : Nat) : Nat := 1 + 2 * w + 3 * bits
/-- Total local dimension `= cosetDim w bits = 2 + 2w + 3·bits`. -/
def productAddDim (w bits : Nat) : Nat := 2 + 2 * w + 3 * bits

/-- The local dimension is exactly `cosetDim w bits` (resource-faithful). -/
theorem productAddDim_eq_cosetDim (w bits : Nat) :
    productAddDim w bits = 2 + 2 * w + 3 * bits := rfl

/-! ## §2. Well-formedness: the five blocks are pairwise disjoint and fit `[0, dim)`.

These omega facts ARE the layout audit's safety check — they rule out the silent
collision John flagged as the next bug risk. (Pure index arithmetic; no semantics.) -/

/-- The lookup zone, `a`, `b`, the temp and the carry are pairwise disjoint, and the
    whole footprint is `[0, productAddDim)`. -/
theorem blocks_disjoint (w bits : Nat) :
    -- lookup zone strictly below a
    lookupZone w ≤ aReg w
    -- a-block [aReg, aReg+bits) below b
    ∧ aReg w + bits ≤ bReg w bits
    -- b-block [bReg, bReg+bits) below temp
    ∧ bReg w bits + bits ≤ temp w bits
    -- temp-block [temp, temp+bits) below carry
    ∧ temp w bits + bits ≤ carry w bits
    -- carry is the last position
    ∧ carry w bits < productAddDim w bits := by
  unfold lookupZone aReg bReg temp carry productAddDim; omega

/-! ## §3. The valid-sufficiency DETERMINATION.

Pass 1 (b += a·k): accumulator = `bReg`, addend-temp = `temp`.  The packed adder
wants `addBase = accBase + bits`; here `temp = bReg + bits` holds, so
`contiguousPackedAdder.valid` IS satisfied. -/
theorem pass1_packed_valid (w bits : Nat) :
    contiguousPackedAdder.valid bits (bReg w bits) (temp w bits) := by
  show temp w bits = bReg w bits + bits
  unfold temp bReg; omega

/-- Pass 2 (a -= b·kInv): accumulator = `aReg`.  The packed adder would put its
    addend-temp at `aReg + bits` — but that position **is** `bReg`, i.e. register
    `b`'s low bit.  So the packed layout's addend-temp COLLIDES with register `b`
    (which pass 2 needs intact as the multiplicand). -/
theorem pass2_packed_temp_hits_b (w bits : Nat) :
    aReg w + bits = bReg w bits := by
  unfold aReg bReg; omega

/-- Consequently, with the SHARED temp at `temp` (the only spot that avoids `b`),
    pass 2's adder has `addBase = temp = aReg + 2·bits ≠ aReg + bits`, so
    `contiguousPackedAdder.valid` FAILS for pass 2 whenever `bits > 0`.

    ⇒ DETERMINATION: on the resource-faithful `cosetDim` layout, `contiguousPackedAdder`
    is sufficient for pass 1 but NOT pass 2.  Pass 2 needs a RELOCATED two-base
    instance whose `valid` accepts `addBase = accBase + 2·bits` (an independent
    addend base), built on the same `relabelGate`/`applyNat_relabelGate` transport. -/
theorem pass2_packed_invalid (w bits : Nat) (hbits : 0 < bits) :
    ¬ contiguousPackedAdder.valid bits (aReg w) (temp w bits) := by
  show ¬ (temp w bits = aReg w + bits)
  unfold temp aReg; omega

/-! ## §4. The alternative (dedicated-temp) layout — packed valid, but +bits qubits.

If instead each register gets its OWN packed adder region
`[base, base + (2·bits+1))` (register + addend-temp + carry), laid out disjointly:
    a-region = [1+2w,            1+2w + (2bits+1))
    b-region = [1+2w + (2bits+1), 1+2w + 2·(2bits+1))
then BOTH passes satisfy `contiguousPackedAdder.valid` (addend always at
accBase+bits), and the multiplicand is the OTHER region's register part (read by
`copyWindow` at an independent `yBase`).  Cost: total `3 + 2w + 4·bits` qubits —
`bits` MORE than `cosetDim` (two temp slots reserved though only one is ever live). -/

/-- `a`-region base for the dedicated-temp layout. -/
def aRegionDed (w : Nat) : Nat := 1 + 2 * w
/-- `b`-region base for the dedicated-temp layout (after a full `2bits+1` a-region). -/
def bRegionDed (w bits : Nat) : Nat := 1 + 2 * w + (2 * bits + 1)
/-- Total dimension of the dedicated-temp layout (`bits` more than `cosetDim`). -/
def productAddDimDed (w bits : Nat) : Nat := 3 + 2 * w + 4 * bits

theorem productAddDimDed_eq (w bits : Nat) :
    productAddDimDed w bits = lookupZone w + 2 * (2 * bits + 1) := by
  unfold productAddDimDed lookupZone; omega

/-- Dedicated layout, pass 1: accumulator `bRegionDed`, addend at `bRegionDed+bits`
    (packed) — `valid` holds. -/
theorem dedicated_pass1_valid (w bits : Nat) :
    contiguousPackedAdder.valid bits (bRegionDed w bits) (bRegionDed w bits + bits) := rfl

/-- Dedicated layout, pass 2: accumulator `aRegionDed`, addend at `aRegionDed+bits`
    (packed) — `valid` holds; and that addend slot is below `b`'s region, so no
    collision (the a-region's own temp slot). -/
theorem dedicated_pass2_valid (w bits : Nat) :
    contiguousPackedAdder.valid bits (aRegionDed w) (aRegionDed w + bits) := rfl

/-- In the dedicated layout the a-region (registers + temp + carry, width `2bits+1`)
    sits entirely below the b-region, so pass 2's packed addend-temp never hits `b`. -/
theorem dedicated_regions_disjoint (w bits : Nat) :
    aRegionDed w + (2 * bits + 1) ≤ bRegionDed w bits := by
  unfold aRegionDed bRegionDed; omega

end FormalRV.Shor.GidneyInPlace.ProductAddLayout
