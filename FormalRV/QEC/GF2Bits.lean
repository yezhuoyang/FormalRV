/-
  FormalRV.QEC.GF2Bits — KERNEL-FAST GF(2) verification over Nat bitsets.

  ## The design fix (John, 2026-06-10)

  "Verification is much easier than finding — if we cannot verify
  efficiently in Lean, there is a problem with our design."  The problem:
  `dotBit` walks `List Bool` cell-by-cell, so one 2610-wide dot product is
  ~2610 kernel reductions and a k = 744 basis certificate is ~10⁹ — hours.
  The kernel, however, has GMP-accelerated `Nat` arithmetic: with vectors as
  bitsets (bit j = entry j, the `BasisCodec` encoding the import pipeline
  already uses), a dot product is ONE `land` plus a LOG-depth shift-XOR
  parity fold — ~13 big-integer ops.  The full lp16 certificate drops from
  ~10⁹ list reductions to ~10⁷ GMP ops.

  `validBitsCert` below is the bitset-level basis certificate (in-kernel
  membership + symplectic δ-pairing), kernel-`decide`-able at paper scale.

  ## Honest trust status

  Until the parametric BRIDGE lemma
      `dotBitN (vecToBits a) (vecToBits b) = dotBit a b`
  is proven (the tracked one-time obligation — `parityFold` correctness via
  `Nat.testBit_xor`/`testBit_shiftRight`, GF2Linearity-style), a green
  `validBitsCert` is a KERNEL-CHECKED NUMERICAL certificate against the real
  constructed matrices — independent of the Python solver — but not yet a
  proof of `LogicalBasis.valid`.  The instance cross-checks below pin the
  two representations against each other on the corpus where both run.

  No Mathlib.  No `sorry`, no `axiom`.
-/

import FormalRV.QEC.BasisCodec
import FormalRV.QEC.GF2Linear

set_option maxRecDepth 16384

namespace FormalRV.QEC

open FormalRV.Framework.LDPC

/-- Parity (XOR of all bits) of a Nat of width ≤ 8192, by a log-depth
    shift-XOR fold — every step a single kernel-accelerated GMP op. -/
def parityFold (x : Nat) : Bool :=
  let x := x ^^^ (x >>> 4096)
  let x := x ^^^ (x >>> 2048)
  let x := x ^^^ (x >>> 1024)
  let x := x ^^^ (x >>> 512)
  let x := x ^^^ (x >>> 256)
  let x := x ^^^ (x >>> 128)
  let x := x ^^^ (x >>> 64)
  let x := x ^^^ (x >>> 32)
  let x := x ^^^ (x >>> 16)
  let x := x ^^^ (x >>> 8)
  let x := x ^^^ (x >>> 4)
  let x := x ^^^ (x >>> 2)
  let x := x ^^^ (x >>> 1)
  x &&& 1 == 1

/-- GF(2) dot product of two bitset vectors: `land` + parity. -/
def dotBitN (a b : Nat) : Bool := parityFold (a &&& b)

/-- Every row of `rows` is GF(2)-orthogonal to `v` (all bitsets). -/
def allOrthoBits (rows : List Nat) (v : Nat) : Bool :=
  rows.all (fun r => ! dotBitN r v)

/-- The symplectic δ-pairing over bitset bases. -/
def pairsDeltaBits (lxs lzs : List Nat) : Bool :=
  lxs.zipIdx.all (fun xi =>
    lzs.zipIdx.all (fun zj => dotBitN xi.1 zj.1 == decide (xi.2 = zj.2)))

/-- A check matrix as bitset rows (one-time in-kernel encoding). -/
def matBits (m : BoolMat) : List Nat := m.map vecToBits

/-- **The bitset basis certificate**: every lx in ker(H_Z), every lz in
    ker(H_X), δ-pairing — the content of `LogicalBasis.valid`, in the
    representation the kernel is fast at. -/
def validBitsCert (hxB hzB : List Nat) (lxs lzs : List Nat) : Bool :=
  lxs.all (allOrthoBits hzB) && lzs.all (allOrthoBits hxB)
    && pairsDeltaBits lxs lzs

/-! ## Representation cross-checks (small corpus, both paths kernel-run) -/

example : dotBitN 0b1011 0b1110 = false := by decide  -- and = 0b1010, 2 bits
example : dotBitN 0b1011 0b0110 = true := by decide   -- and = 0b0010, 1 bit
example : parityFold 0 = false := by decide
example : parityFold (2 ^ 4095) = true := by decide

/-- The bitset dot agrees with the legacy `dotBit` on sampled vectors. -/
example :
    dotBitN (vecToBits [true, false, true]) (vecToBits [true, true, true])
      = dotBit [true, false, true] [true, true, true] := by decide

end FormalRV.QEC
