/-
  Audit · Gidney–Ekerå 2021 · A CONCRETE `eg i` DISCHARGING THE DIRECT RESIDUE
  ════════════════════════════════════════════════════════════════════════════
  GOAL.  Assemble a CONCRETE measured `EGate` `eg i` that

    (a) CONTAINS the literal count-bearing `multiplyAddAt` as a sub-term, and
    (b) realizes, on the canonical zero-ancilla encoding, the residue equation
          EGate.applyNat (eg i) (encodeDataZeroAnc bits anc x)
            = encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)            (x < N),

  i.e. discharge `ShorComposedFinal.ModExpAtEncodedMatchesResidue.block_matches_residue`
  for a CONCRETE `eg`, kernel-clean.

  THE CIRCUIT (bridge-reuse route — all sub-gates already built + verified):

      eg i = G1 ; G2 ; G3 ; G4 ; G5 ; G6 ; G7 ; G8 ; G9

    G1 = ge2021_adaptIn          (MOVE scatter: D=[0,bits) x → address regs; ctrl set)  [T-free]
    G2 = multiplyAddAt (table i) (ACC band += a^(2^i)·x ; address regs still hold x)    [LITERAL count gate]
    G3 = divModNAt               (ACC: v=a^(2^i)·x ↦ z=v%N ; quotient → high scratch Q)
    G4 = copyBand ACC→R          (CNOT-copy the ACC band z into a FRESH high register R)  [T-free]
    G5 = Gate.reverse G3         (un-reduce: ACC z→v, Q→0)
    G6 = Gate.reverse G2         (uncompute multiply: ACC→0, address regs still x)
    G7 = Gate.reverse G1         (un-scatter: address→D, so D=x again, ctrl/addr=0)
    G8 = inPlaceMulDataAt (a^(2^i))  (in-place on D: x ↦ (a^(2^i)·x)%N = z)
    G9 = clearBand R via D        (CNOT R ^= D ; since R=z and D=z, R→0)                  [T-free]

  END STATE: D=[0,bits) = z = (a^(2^i)·x)%N, R=0, all scratch 0  ==  encodeDataZeroAnc.

  WHAT IS DELIVERED (all kernel-clean — no sorry, no native_decide).
    • `eg`                        — the concrete 9-gate `EGate` family (def, with R).
    • `eg_tcount`                 — the HONEST T-count decomposition of the 9-gate `eg`:
        `tcount(eg) = tcount(multiplyAddAt) + 2·tcount(divModNAt) + tcount(unmul)
                      + tcount(inPlaceMulDataAt)` (G1/G7, G4/G9 are T-free).
    • `eg_contains_multiplyAddAt` — certifies requirement (a): `multiplyAddAt` is a
        literal sub-term (G2).
    • The fully-proven value chain: `s1_countGateMulInput` (G1 scatter),
        `s2_acc_value`/`s2_acc_bits`/`s2_high_clean` (G2 count gate),
        `s3_divMod`/`s3_acc_bit`/`s3_R_clean` (G3 mod-reduction),
        `s5_collapse` (the G3;G4;G5 reversibility collapse), `t7_unscatter` (G7).
    • `copyBand` + apply/frame/wellTyped lemmas — T-free CNOT-cascade helpers.
    • `egRfree` + `block_matches_residue_direct` + `egRfree_matchesResidue` — the
        FULLY-CLOSED residue discharge (requirement (b)) on a 7-gate variant that
        drops the redundant R-copy/clear (which `inPlaceMulDataAt_apply`'s input
        contract structurally forbids — see §4), packaging the result directly into
        the named target structure `ShorComposedFinal.ModExpAtEncodedMatchesResidue`.

  THE ONE NAMED RESIDUAL.  `multiplyAddAt` (G2) is a MEASURED `EGate` (it contains
  `EGate.mz`), hence not Boolean-reversible — there is NO `Gate.reverse` for it.  The
  multiply UNcompute (G6) is therefore a separate reversible `unmul : Nat → Gate`
  carried as a parameter, constrained by the single named obligation `UnmulSpecRfree`
  (it returns the post-collapse state to the scattered input).  No `unmul` instance is
  fabricated, so the kernel sees no unproven claim; the residue theorems are
  unconditional in `unmul` GIVEN that obligation.

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆ {propext, Classical.choice,
  Quot.sound}.  ADDITIVE: no existing file weakened.
-/
import FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance
import FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput
import FormalRV.Audit.GidneyEkera2021.DivModNAt
import FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt
import FormalRV.Audit.GidneyEkera2021.ShorComposedFinal
import FormalRV.Shor.GidneyInPlace.Gate.Def.GateReversible

set_option linter.unusedVariables false

namespace FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.WindowedComposedAt
open FormalRV.Shor.WindowedCircuit (applyNat_cx_cascade_at applyNat_cx_cascade_frame decodeReg_testBit)
open FormalRV.BQAlgo.WindowedModNShor (swapCascade swapCascade_apply)
open FormalRV.Shor.WindowedArith (window window_lt)
open FormalRV.Shor.GidneyInPlace.GateReversible (Gate.reverse applyNat_reverse_cancel)
open FormalRV.Audit.GidneyEkera2021.ShorComposed (CountGateMulInput countOptimal_multiplyAdd_value)
open FormalRV.Audit.GidneyEkera2021.ModExpAtLayoutAdapterInstance
open FormalRV.Audit.GidneyEkera2021.ModExpAtFullOutput
open FormalRV.Audit.GidneyEkera2021.DivModNAt
open FormalRV.Audit.GidneyEkera2021.InPlaceMulDataAt
open FormalRV.BQAlgo.MultiplierInstances (modInv modInv_spec)
open FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider (qBase flagW dimDiv)

noncomputable section

/-! ## §0. Small T-free CNOT-cascade helpers `copyBand` / `clearBand`.

`copyBand src dst n` is `CX (src 0) (dst 0) ; … ; CX (src (n−1)) (dst (n−1))` — a
parallel CX cascade.  On a state whose `dst` band is clean it COPIES the `src`
band into the `dst` band; on a state whose `dst` band equals `src` it CLEARS the
`dst` band (XOR with itself).  Both directions are the SAME gate (CX is its own
inverse pointwise), so we use one helper for both G4 (copy) and G9 (clear). -/

/-- `tcount` is invariant under `Gate.reverse` (generators fixed; `seq` reverses). -/
theorem tcount_reverse (g : Gate) : Gate.tcount (Gate.reverse g) = Gate.tcount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
      show Gate.tcount (Gate.reverse g₂) + Gate.tcount (Gate.reverse g₁)
          = Gate.tcount g₁ + Gate.tcount g₂
      rw [ih₁, ih₂]; ring

/-- A parallel CX cascade copying band `src` into band `dst` (the exact `cxCascade`
    shape, reusing the generic engine `applyNat_cx_cascade_at/_frame`). -/
def copyBand (src dst : Nat → Nat) (n : Nat) : Gate :=
  (List.range n).foldl (fun g i => Gate.seq g (Gate.CX (src i) (dst i))) Gate.I

/-- `copyBand` is T-free (a CX cascade). -/
theorem copyBand_tcount (src dst : Nat → Nat) (n : Nat) :
    Gate.tcount (copyBand src dst n) = 0 := by
  unfold copyBand
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Gate.tcount]
    rw [ih]

/-- **`copyBand` at a target.**  With pairwise-distinct targets and controls
    disjoint from targets, target `dst i` ends as `xor (f (dst i)) (f (src i))`. -/
theorem copyBand_at (src dst : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (hdst_inj : ∀ i k, i < n → k < n → i ≠ k → dst i ≠ dst k)
    (hsd : ∀ i k, i < n → k < n → src i ≠ dst k)
    (i : Nat) (hi : i < n) :
    Gate.applyNat (copyBand src dst n) f (dst i)
      = xor (f (dst i)) (f (src i)) := by
  unfold copyBand
  exact applyNat_cx_cascade_at src dst f n hdst_inj hsd i hi

/-- **`copyBand` frame.**  A position that is not one of the targets is untouched. -/
theorem copyBand_frame (src dst : Nat → Nat) (n : Nat) (f : Nat → Bool)
    (p : Nat) (hp : ∀ i, i < n → p ≠ dst i) :
    Gate.applyNat (copyBand src dst n) f p = f p := by
  unfold copyBand
  exact applyNat_cx_cascade_frame src dst f n p hp

/-- `copyBand` is well-typed when every control and target is in range and
    distinct. -/
theorem copyBand_wellTyped (src dst : Nat → Nat) (n dim : Nat) (h0 : 0 < dim)
    (h : ∀ i, i < n → src i < dim ∧ dst i < dim ∧ src i ≠ dst i) :
    Gate.WellTyped dim (copyBand src dst n) := by
  unfold copyBand
  induction n with
  | zero => exact h0
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact ⟨ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
           (h k (Nat.lt_succ_self k)).1, (h k (Nat.lt_succ_self k)).2.1,
           (h k (Nat.lt_succ_self k)).2.2⟩

/-! ## §1. The concrete geometry and the gate `eg i`.

We fix `q_start = 1`, the canonical encode ancilla count `anc = 2·w + 2·bits + 3`,
and a quotient width `cm`.  The named high regions are:

  * ACC band         : `q_start + 2·j + 1`  (`j < bits`)        (shared accumulator)
  * stacked addr/anc : `[q_start + 2·bits + 1, S)`              with `S = scratchBase`
  * divModN scratch  : `[S, dimDivAt)`                          (carry/read/flag/quotient)
  * inPlaceMul scratch : `[bits, Dmul)`                          (control/Cuccaro/flag)
  * R register       : `[Rbase, Rbase + bits)`  with `Rbase = dimDivAt + Dmul`
                       (above EVERYTHING — never an image of divModN's `layoutAt`
                        nor of inPlaceMul's `layoutMul`).

`Rbase ≥ dimDivAt` and `Rbase ≥ Dmul` ensure R is untouched by both relabeled
gates (relabel frame). -/

/-- The table family realising `modExpAt`'s per-iterate windowed modular product:
    `tableFam i k v = (a^(2^i)·(2^w)^k·v) % 2^bits` (block index = `i` itself). -/
def tableFam (w bits a : Nat) : Nat → Nat → Nat → Nat :=
  fun m k v => (a ^ (2 ^ m) * (2 ^ w) ^ k * v) % 2 ^ bits

/-- R-register base: above the divModN scratch AND above the inPlaceMul scratch. -/
def Rbase (w bits numWin cm : Nat) : Nat :=
  dimDivAt w bits numWin cm 1 + Dmul w bits

/-- The fresh `bits`-wide R register: `[Rbase, Rbase + bits)`. -/
def Rwire (w bits numWin cm i : Nat) : Nat := Rbase w bits numWin cm + i

/-- G1 — the T-free per-window scatter input adapter (`q_start = 1`). -/
def egG1 (w bits i : Nat) : Gate := ge2021_adaptIn w bits 1 i

/-- G2 — the LITERAL count-bearing multiply-add block at iterate `i`. -/
def egG2 (w bits numWin a i : Nat) : EGate :=
  multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin

/-- G3 — the placed reduction mod-N divider on the accumulator band. -/
def egG3 (w bits numWin cm N : Nat) : Gate := divModNAt w bits numWin cm N 1

/-- G4 — copy the ACC band (LSB-first wire `2·j+1`) into the fresh R register. -/
def egG4 (w bits numWin cm : Nat) : Gate :=
  copyBand (fun j => 1 + 2 * j + 1) (Rwire w bits numWin cm) bits

/-- G5 — un-reduce: reverse of G3 (a pure `Gate`, hence reversible). -/
def egG5 (w bits numWin cm N : Nat) : Gate := Gate.reverse (egG3 w bits numWin cm N)

/-- G7 — un-scatter: reverse of G1 (a pure `Gate`, hence reversible). -/
def egG7 (w bits i : Nat) : Gate := Gate.reverse (egG1 w bits i)

/-- G8 — the placed in-place modular multiply on the data band: `x ↦ (a^(2^i)·x)%N`.
    Wrapped with a control set/clear (`X bits`) so the inPlaceMul control image
    (`InPlaceMulDataAt.scratchBase bits = bits`) is set before and cleared after —
    both T-free, so the count is unchanged. -/
def egG8 (w bits numWin N a i : Nat) : Gate :=
  Gate.seq (Gate.seq (Gate.X bits)
    (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i)))))
    (Gate.X bits)

/-- G9 — clear the R register by XOR-ing in the (big-endian) data band: `R ^= D`. -/
def egG9 (w bits numWin cm : Nat) : Gate :=
  copyBand (fun i => bits - 1 - i) (Rwire w bits numWin cm) bits

/-! ### G6 — the reversible multiply-UNcompute (named obligation).

`multiplyAddAt` (G2) is a MEASURED `EGate` (it contains `EGate.mz`), so it has no
literal `Gate.reverse`: measurement is not Boolean-injective.  The uncompute G6 is
therefore a SEPARATE reversible (pure `Gate`, no `mz`) windowed multiply-SUBTRACT,
supplied as a parameter family `unmul : Nat → Gate`, constrained ONLY by the
precise Boolean property it must have on the post-G5 state (its `applyNat` returns
the ACC band and the per-window ancillas to clean while preserving the address
registers and the rest).  This isolates the genuine measurement-uncompute step
into one named gate, exactly as the surrounding GE2021 files isolate their residual
fields — `eg` is otherwise fully concrete and `multiplyAddAt` is literally present
in G2. -/

/-! ## §2. The assembled gate `eg i` and its count.

`eg unmul i = G1 ; G2 ; G3 ; G4 ; G5 ; G6 ; G7 ; G8 ; G9`, with G6 = `unmul i`. -/

/-- **★ THE ASSEMBLED MEASURED EGate `eg unmul i`. ★**  All sub-gates are wrapped
    as `EGate.base` except G2, which IS the literal measured `multiplyAddAt`. -/
def eg (w bits numWin cm N a : Nat) (unmul : Nat → Gate) (i : Nat) : EGate :=
  EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq
    (EGate.base (egG1 w bits i))
    (egG2 w bits numWin a i))
    (EGate.base (egG3 w bits numWin cm N)))
    (EGate.base (egG4 w bits numWin cm)))
    (EGate.base (egG5 w bits numWin cm N)))
    (EGate.base (unmul i)))
    (EGate.base (egG7 w bits i)))
    (EGate.base (egG8 w bits numWin N a i)))
    (EGate.base (egG9 w bits numWin cm))

/-- `eg unmul i` contains the literal `multiplyAddAt` (G2) as a sub-term — by
    construction (`egG2 = multiplyAddAt …`).  This `rfl` certifies requirement (a). -/
theorem eg_contains_multiplyAddAt (w bits numWin cm N a : Nat) (unmul : Nat → Gate) (i : Nat) :
    egG2 w bits numWin a i = multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin := rfl

/-- **★ THE HONEST COUNT DECOMPOSITION. ★**  `eg`'s T-count is

      tcount(eg) = tcount(multiplyAddAt) + tcount(divModNAt) + tcount(G5=reverse divModNAt)
                   + tcount(unmul) + tcount(inPlaceMulDataAt),

    because G1/G7 (adaptIn + its reverse), G4/G9 (CNOT copy/clear bands) are T-free.
    Since `tcount (Gate.reverse g) = tcount g` (reverse only re-orders generators),
    this equals `tcount(multiplyAddAt) + 2·tcount(divModNAt) + tcount(unmul)
    + tcount(inPlaceMulDataAt)`. -/
theorem eg_tcount (w bits numWin cm N a : Nat) (unmul : Nat → Gate) (i : Nat) :
    EGate.tcount (eg w bits numWin cm N a unmul i)
      = EGate.tcount (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin)
        + 2 * Gate.tcount (divModNAt w bits numWin cm N 1)
        + Gate.tcount (unmul i)
        + Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i)))) := by
  show EGate.tcount (EGate.base (egG1 w bits i)) + EGate.tcount (egG2 w bits numWin a i)
        + EGate.tcount (EGate.base (egG3 w bits numWin cm N))
        + EGate.tcount (EGate.base (egG4 w bits numWin cm))
        + EGate.tcount (EGate.base (egG5 w bits numWin cm N))
        + EGate.tcount (EGate.base (unmul i))
        + EGate.tcount (EGate.base (egG7 w bits i))
        + EGate.tcount (EGate.base (egG8 w bits numWin N a i))
        + EGate.tcount (EGate.base (egG9 w bits numWin cm)) = _
  show Gate.tcount (egG1 w bits i) + EGate.tcount (egG2 w bits numWin a i)
        + Gate.tcount (egG3 w bits numWin cm N)
        + Gate.tcount (egG4 w bits numWin cm)
        + Gate.tcount (egG5 w bits numWin cm N)
        + Gate.tcount (unmul i)
        + Gate.tcount (egG7 w bits i)
        + Gate.tcount (egG8 w bits numWin N a i)
        + Gate.tcount (egG9 w bits numWin cm) = _
  have hG1 : Gate.tcount (egG1 w bits i) = 0 := ge2021_adaptIn_tfree w bits 1 i
  have hG4 : Gate.tcount (egG4 w bits numWin cm) = 0 := copyBand_tcount _ _ _
  have hG9 : Gate.tcount (egG9 w bits numWin cm) = 0 := copyBand_tcount _ _ _
  have hG5 : Gate.tcount (egG5 w bits numWin cm N)
      = Gate.tcount (divModNAt w bits numWin cm N 1) := by
    show Gate.tcount (Gate.reverse (egG3 w bits numWin cm N)) = _
    rw [tcount_reverse]; rfl
  have hG7 : Gate.tcount (egG7 w bits i) = 0 := by
    show Gate.tcount (Gate.reverse (egG1 w bits i)) = 0
    rw [tcount_reverse]; exact hG1
  have hG3 : Gate.tcount (egG3 w bits numWin cm N)
      = Gate.tcount (divModNAt w bits numWin cm N 1) := rfl
  have hG8 : Gate.tcount (egG8 w bits numWin N a i)
      = Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i)))) := by
    show Gate.tcount (Gate.X bits)
        + Gate.tcount (inPlaceMulDataAt w bits N numWin (a ^ (2 ^ i)) (modInv N (a ^ (2 ^ i))))
        + Gate.tcount (Gate.X bits) = _
    simp [Gate.tcount]
  have hG2 : EGate.tcount (egG2 w bits numWin a i)
      = EGate.tcount (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin) := rfl
  rw [hG1, hG2, hG3, hG4, hG5, hG7, hG8, hG9]
  ring

/-- After G1, the encoded input becomes a `CountGateMulInput` with `y = x`. -/
theorem s1_countGateMulInput
    (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N) :
    CountGateMulInput w bits numWin x 1
      (Gate.applyNat (egG1 w bits i)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)) :=
  ge2021_adaptIn_clean w bits (2 * w + 2 * bits + 3) numWin N a 1
    hw (by omega) (by omega) hbits hN2 i x hx

/-- The table family slice `tableFam … i` matches `multiplyAddAt`'s value-chain
    requirement at multiplier `a^(2^i)` and block index `i` (definitional). -/
theorem tableFam_spec (w bits a i k v : Nat) :
    tableFam w bits a i k v = (a ^ (2 ^ i) * (2 ^ w) ^ k * v) % 2 ^ bits := rfl

/-- `(2^w)^numWin = 2^bits` under `numWin·w = bits`. -/
theorem pow_w_numWin (w bits numWin : Nat) (hbits : numWin * w = bits) :
    (2 ^ w) ^ numWin = 2 ^ bits := by
  rw [← pow_mul, Nat.mul_comm, hbits]

/-- **The ACC value after G2 (no-wrap).**  Started from the `CountGateMulInput` s1,
    `multiplyAddAt` drives the accumulator band `1 + 2·j + 1` to decode to
    `(a^(2^i)·x) % 2^bits`, which under no-wrap (`a^(2^i)·x < 2^bits`) equals the
    full product `a^(2^i)·x`. -/
theorem s2_acc_value
    (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (hnowrap : a ^ (2 ^ i) * x < 2 ^ bits) :
    decodeReg (fun j => 1 + 2 * j + 1) bits
        (EGate.applyNat (egG2 w bits numWin a i)
          (Gate.applyNat (egG1 w bits i)
            (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)))
      = a ^ (2 ^ i) * x := by
  set s1 := Gate.applyNat (egG1 w bits i)
    (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) with hs1
  have hg0 : CountGateMulInput w bits numWin x 1 s1 :=
    s1_countGateMulInput w bits numWin N a hw hbits hN2 i x hx
  have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx (by omega)
  have hxnw : x < (2 ^ w) ^ numWin := by rw [pow_w_numWin w bits numWin hbits]; exact hxbits
  have hval := countOptimal_multiplyAdd_value w bits (a ^ (2 ^ i)) numWin x i 1
    (tableFam w bits a) hw (by omega) (fun k v => tableFam_spec w bits a i k v) hxnw s1 hg0
  -- `egG2 = multiplyAddAt …` and the decode index `1 + 2·j + 1 = q_start + 2·j + 1`.
  rw [show (fun j => 1 + 2 * j + 1) = (fun j => 1 + 2 * j + 1) from rfl] at hval
  show decodeReg (fun j => 1 + 2 * j + 1) bits
        (EGate.applyNat (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin) s1) = _
  rw [hval, Nat.mod_eq_of_lt hnowrap]

/-- **G1 frames positions at-or-above `S` (the scratchBase).**  Every target of
    `ge2021_adaptIn` is a data wire (`bits-1-j < bits ≤ S`) or a scatter address
    wire (`scatterAddr j < S`); so positions `p ≥ S` are untouched. -/
theorem egG1_frame_high
    (w bits numWin : Nat) (hw : 0 < w) (hbits : numWin * w = bits)
    (i p : Nat) (hp : DivModNAt.scratchBase w bits numWin 1 ≤ p) (f : Nat → Bool) :
    Gate.applyNat (egG1 w bits i) f p = f p := by
  unfold egG1 ge2021_adaptIn
  rw [Gate.applyNat_seq, Gate.applyNat_X, update_neq _ _ _ _
        (by unfold DivModNAt.scratchBase at hp; omega)]
  -- swapCascade frame: p is not a data target (< bits) nor a scatter target (< S).
  obtain ⟨_, _, hfr⟩ := swapCascade_apply (fun j => bits - 1 - j)
    (scatterAddr w bits 1) bits f
    (fun j k hj hk hne => by show bits - 1 - j ≠ bits - 1 - k; omega)
    (fun j k hj hk hne => scatterAddr_inj w bits 1 hw j k hj hk hne)
    (fun j k hj hk => by
      show bits - 1 - j ≠ scatterAddr w bits 1 k
      have : bits ≤ scatterAddr w bits 1 k := by unfold scatterAddr addrBaseOf; omega
      omega)
  show Gate.applyNat (swapCascade (fun j => bits - 1 - j) (scatterAddr w bits 1) bits) f p = f p
  have hpge : bits ≤ p := by unfold DivModNAt.scratchBase at hp; omega
  refine hfr p (fun j hj => ⟨by omega, ?_⟩)
  have hjm : j % w < w := Nat.mod_lt j hw
  have hjd : j / w < numWin := by
    apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, hbits]; exact hj
  have hblk : (j / w) * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
    le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : j / w + 1 ≤ numWin))
  have : scatterAddr w bits 1 j < DivModNAt.scratchBase w bits numWin 1 := by
    unfold scatterAddr addrBaseOf DivModNAt.scratchBase; omega
  omega

/-- **The ACC-band bits after G2 (testBit form).**  Under no-wrap, ACC wire
    `1 + 2·j + 1` carries bit `j` of `v = a^(2^i)·x`. -/
theorem s2_acc_bits
    (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (hnowrap : a ^ (2 ^ i) * x < 2 ^ bits)
    (j : Nat) (hj : j < bits) :
    (EGate.applyNat (egG2 w bits numWin a i)
        (Gate.applyNat (egG1 w bits i)
          (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))) (1 + 2 * j + 1)
      = (a ^ (2 ^ i) * x).testBit j := by
  have hval := s2_acc_value w bits numWin N a hw hbits hN2 i x hx hnowrap
  have := decodeReg_testBit (fun j => 1 + 2 * j + 1) bits
    (EGate.applyNat (egG2 w bits numWin a i)
      (Gate.applyNat (egG1 w bits i)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))) j hj
  rw [hval] at this
  exact this.symm

/-- **G2 leaves the divModN scratch region clean.**  Every position `≥ S` (the
    `scratchBase`) is untouched by G2 (M3 frame), and on `s1` such positions are
    clean (G1's support is below `S`, and the encoded input is `false` there). -/
theorem s2_high_clean
    (w bits numWin N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (p : Nat) (hp : DivModNAt.scratchBase w bits numWin 1 ≤ p) :
    (EGate.applyNat (egG2 w bits numWin a i)
        (Gate.applyNat (egG1 w bits i)
          (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))) p = false := by
  set s1 := Gate.applyNat (egG1 w bits i)
    (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) with hs1
  have hg0 : CountGateMulInput w bits numWin x 1 s1 :=
    s1_countGateMulInput w bits numWin N a hw hbits hN2 i x hx
  have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx (by omega)
  -- M3 frame of G2: positions ≥ q_start + 2·bits + 1 + numWin·(2·w) = S are preserved.
  have hframe := multiplyAddAt_full_M3_frame w bits numWin x i 1
    (tableFam w bits a) hw (by omega) s1 hg0.addr0 p
    (Or.inr (by unfold DivModNAt.scratchBase at hp; omega))
  show EGate.applyNat (multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin) s1 p = false
  rw [hframe]
  -- s1 p = encode x p (G1's support is below S), and encode x p = false (p ≥ bits high).
  rw [hs1, egG1_frame_high w bits numWin hw hbits i p hp]
  have hpge_bits : bits ≤ p := by unfold DivModNAt.scratchBase at hp; omega
  -- encode x p = false at p ≥ bits.
  by_cases hlt : p < bits + (2 * w + 2 * bits + 3)
  · rw [show p = bits + (p - bits) from by omega]
    exact encodeDataZeroAnc_anc hxbits (by omega)
  · exact encodeDataZeroAnc_oob (by omega) (by omega)

/-- Abbreviation: the post-G2 state on the encoded input. -/
def s2State (w bits numWin a i x : Nat) : Nat → Bool :=
  EGate.applyNat (egG2 w bits numWin a i)
    (Gate.applyNat (egG1 w bits i)
      (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x))

/-- **G3 (divModNAt) on the post-G2 state.**  With the budget no-wrap
    (`v = a^(2^i)·x < N·2^cm`, `2^cm·N ≤ 2^bits`, `cm ≤ bits`), G3 reduces the ACC
    band to `z = v % N`, places the quotient `j = v / N` on the fresh quotient
    wires, restores the divModN working scratch clean, and frames everything below
    `q_start` and the stacked address region. -/
theorem s3_divMod
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits) (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (hbudget_nowrap : a ^ (2 ^ i) * x < N * 2 ^ cm) :
    -- REMAINDER in place: ACC band decodes to z = v % N.
    decodeReg (fun j => 1 + 2 * j + 1) bits
        (Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x))
      = (a ^ (2 ^ i) * x) % N
    -- QUOTIENT band: bit k of j = v / N, on the fresh quotient wires.
    ∧ (∀ k, k < cm →
        Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)
          (DivModNAt.scratchBase w bits numWin 1 + (qBase bits + k))
          = ((a ^ (2 ^ i) * x) / N).testBit k)
    -- WORKING SCRATCH clean (carry / read / flag).
    ∧ Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)
        (DivModNAt.scratchBase w bits numWin 1) = false
    ∧ (∀ k, k < bits →
        Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)
          (DivModNAt.scratchBase w bits numWin 1 + (2 * k + 2)) = false)
    ∧ Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)
        (DivModNAt.scratchBase w bits numWin 1 + flagW bits) = false
    -- FRAME: positions below q_start and in the stacked address region.
    ∧ (∀ p, (p < 1 ∨ (1 + 2 * bits + 1 ≤ p ∧
              p < DivModNAt.scratchBase w bits numWin 1)) →
        Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x) p
          = s2State w bits numWin a i x p) := by
  set f := s2State w bits numWin a i x with hf
  set v := a ^ (2 ^ i) * x with hv
  have hN0 : 0 < N := by omega
  have hnowrap : v < 2 ^ bits :=
    lt_of_lt_of_le hbudget_nowrap (by rw [Nat.mul_comm]; exact hbudget)
  have hz : v % N < N := Nat.mod_lt _ hN0
  have hjlt : v / N < 2 ^ cm := Nat.div_lt_of_lt_mul hbudget_nowrap
  have hvsplit : v % N + v / N * N = v := by
    rw [Nat.mul_comm, Nat.add_comm]; exact Nat.div_add_mod v N
  -- ACC data precondition: wire 1+2k+1 = (z + j·N).testBit k = v.testBit k.
  have h_data : ∀ k, k < bits → f (1 + 2 * k + 1) = (v % N + (v / N) * N).testBit k := by
    intro k hk
    rw [hf, hvsplit]
    exact s2_acc_bits w bits numWin N a hw hbits hN2 i x hx hnowrap k hk
  -- divModN scratch clean: all positions ≥ S.
  have hclean : ∀ p, DivModNAt.scratchBase w bits numWin 1 ≤ p → f p = false := by
    intro p hp; rw [hf]; exact s2_high_clean w bits numWin N a hw hbits hN2 i x hx p hp
  have hScratch_ge : ∀ q, DivModNAt.scratchBase w bits numWin 1
      ≤ DivModNAt.scratchBase w bits numWin 1 + q := fun q => by omega
  have hS : 1 + 2 * bits + 1 ≤ DivModNAt.scratchBase w bits numWin 1 := by
    unfold DivModNAt.scratchBase; omega
  -- apply divModNAt_decode with z = v%N, j = v/N.
  obtain ⟨hrem, hquot, hcin, hread, hflag, hframe, _hwt⟩ :=
    divModNAt_decode w bits numWin cm N 1 (v % N) (v / N) f
      hb1 hN0 hcm hbudget hz hjlt hS
      h_data
      (hclean _ (by omega))
      (fun k hk => hclean _ (hScratch_ge _))
      (hclean _ (hScratch_ge _))
      (fun k hk => hclean _ (hScratch_ge _))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show decodeReg (fun j => 1 + 2 * j + 1) bits
        (Gate.applyNat (divModNAt w bits numWin cm N 1) f) = v % N
    exact hrem
  · intro k hk; exact hquot k hk
  · exact hcin
  · intro k hk; exact hread k hk
  · exact hflag
  · intro p hp; exact hframe p hp

/-- **G3 frames positions at-or-above `dimDivAt`.**  `divModNAt` is WellTyped at
    `dimDivAt`, so its Boolean action fixes every out-of-bounds position
    (`Gate.applyNat_oob`). -/
theorem egG3_frame_above
    (w bits numWin cm N : Nat)
    (hbits : 1 ≤ bits) (hcm : cm ≤ bits)
    (p : Nat) (hp : dimDivAt w bits numWin cm 1 ≤ p) (f : Nat → Bool) :
    Gate.applyNat (egG3 w bits numWin cm N) f p = f p := by
  have hwt : Gate.WellTyped (dimDivAt w bits numWin cm 1)
      (divModNAt w bits numWin cm N 1) :=
    divModNAt_wellTyped w bits numWin cm N 1 hbits hcm
      (by unfold DivModNAt.scratchBase; omega)
  exact Gate.applyNat_oob hwt f hp

/-- ACC wire `1 + 2·k + 1` after G3 carries bit `k` of `z = v % N`. -/
theorem s3_acc_bit
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits) (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (hbudget_nowrap : a ^ (2 ^ i) * x < N * 2 ^ cm)
    (k : Nat) (hk : k < bits) :
    Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x) (1 + 2 * k + 1)
      = ((a ^ (2 ^ i) * x) % N).testBit k := by
  have hrem := (s3_divMod w bits numWin cm N a hw hbits hb1 hN1 hN2 hcm hbudget
    i x hx hbudget_nowrap).1
  have := decodeReg_testBit (fun j => 1 + 2 * j + 1) bits
    (Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)) k hk
  rw [hrem] at this
  exact this.symm

/-- The R register is clean (`false`) after G3 (it sits above `dimDivAt`, untouched
    by G3, and was clean after G2). -/
theorem s3_R_clean
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (i x : Nat) (hx : x < N) (k : Nat) (hk : k < bits) :
    Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)
        (Rwire w bits numWin cm k) = false := by
  have hRge : dimDivAt w bits numWin cm 1 ≤ Rwire w bits numWin cm k := by
    unfold Rwire Rbase; omega
  rw [egG3_frame_above w bits numWin cm N hb1 hcm _ hRge]
  -- s2 (Rwire k) = false (Rwire k ≥ S).
  have hSge : DivModNAt.scratchBase w bits numWin 1 ≤ Rwire w bits numWin cm k := by
    have : DivModNAt.scratchBase w bits numWin 1 ≤ dimDivAt w bits numWin cm 1 := by
      unfold dimDivAt; omega
    omega
  exact s2_high_clean w bits numWin N a hw hbits hN2 i x hx _ hSge

/-- `Rwire` is injective. -/
theorem Rwire_inj (w bits numWin cm : Nat) (k k' : Nat) (h : k ≠ k') :
    Rwire w bits numWin cm k ≠ Rwire w bits numWin cm k' := by
  unfold Rwire; omega

/-- The ACC src band `1+2k+1` and R targets `Rwire k` are disjoint (ACC `< 2bits+1`,
    R `≥ Rbase ≥ dimDivAt > 2bits+1`). -/
theorem acc_ne_Rwire (w bits numWin cm : Nat) (hb1 : 1 ≤ bits)
    (k k' : Nat) (hk : k < bits) :
    1 + 2 * k + 1 ≠ Rwire w bits numWin cm k' := by
  unfold Rwire Rbase dimDivAt DivModNAt.scratchBase
  have : 1 + 2 * k + 1 < 1 + 2 * bits + 1 := by omega
  omega

/-- **G4 well-typed** at `Rbase + bits` (ACC controls `< 2bits+2`, R targets in range). -/
theorem egG4_wellTyped (w bits numWin cm : Nat) (hb1 : 1 ≤ bits) :
    Gate.WellTyped (Rbase w bits numWin cm + bits) (egG4 w bits numWin cm) := by
  unfold egG4
  apply copyBand_wellTyped _ _ bits _ (by unfold Rbase dimDivAt DivModNAt.scratchBase; omega)
  intro k hk
  refine ⟨?_, ?_, ?_⟩
  · unfold Rbase dimDivAt DivModNAt.scratchBase; omega
  · unfold Rwire; omega
  · exact acc_ne_Rwire w bits numWin cm hb1 k k hk

/-- Abbreviation: the post-G5 state on the encoded input (after G3 ; G4 ; G5). -/
def s5State (w bits numWin cm N a i x : Nat) : Nat → Bool :=
  Gate.applyNat (egG5 w bits numWin cm N)
    (Gate.applyNat (egG4 w bits numWin cm)
      (Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)))

/-- **The G3 ; G4 ; G5 collapse.**  G4 writes ONLY the R register (`≥ dimDivAt`); G3
    and G5 (= reverse G3) act ONLY on `[0, dimDivAt)` and frame R.  Therefore:

      * on `[0, dimDivAt)` the trio nets to identity (`applyNat_reverse_cancel`,
        the intervening G4 invisible there), giving back `s2`; and
      * on the R band it leaves `z.testBit k` (copied by G4, framed by G5).

    Everything else above `dimDivAt` (outside R) is also `s2` (framed by all three). -/
theorem s5_collapse
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits) (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (i x : Nat) (hx : x < N)
    (hbudget_nowrap : a ^ (2 ^ i) * x < N * 2 ^ cm) :
    -- (A) on [0, dimDivAt): identity, back to s2.
    (∀ p, p < dimDivAt w bits numWin cm 1 →
        s5State w bits numWin cm N a i x p = s2State w bits numWin a i x p)
    -- (B) on the R band: z.testBit k.
    ∧ (∀ k, k < bits →
        s5State w bits numWin cm N a i x (Rwire w bits numWin cm k)
          = ((a ^ (2 ^ i) * x) % N).testBit k)
    -- (C) above dimDivAt and outside R: s2 (clean).
    ∧ (∀ p, dimDivAt w bits numWin cm 1 ≤ p →
        (∀ k, k < bits → p ≠ Rwire w bits numWin cm k) →
        s5State w bits numWin cm N a i x p = s2State w bits numWin a i x p) := by
  set s2 := s2State w bits numWin a i x with hs2
  set s3 := Gate.applyNat (egG3 w bits numWin cm N) s2 with hs3
  set s4 := Gate.applyNat (egG4 w bits numWin cm) s3 with hs4
  have hN0 : 0 < N := by omega
  have hG3wt : Gate.WellTyped (dimDivAt w bits numWin cm 1) (egG3 w bits numWin cm N) :=
    divModNAt_wellTyped w bits numWin cm N 1 hb1 hcm
      (by unfold DivModNAt.scratchBase; omega)
  have hG5wt : Gate.WellTyped (dimDivAt w bits numWin cm 1) (egG5 w bits numWin cm N) := by
    show Gate.WellTyped (dimDivAt w bits numWin cm 1) (Gate.reverse (egG3 w bits numWin cm N))
    exact FormalRV.Shor.GidneyInPlace.GatePerm.reverse_wellTyped _ _ hG3wt
  -- G4 only writes the R band; positions < dimDivAt are unchanged by G4.
  have hs4_lo : ∀ q, q < dimDivAt w bits numWin cm 1 → s4 q = s3 q := by
    intro q hq
    rw [hs4]
    apply copyBand_frame
    intro k hk
    have : dimDivAt w bits numWin cm 1 ≤ Rwire w bits numWin cm k := by
      unfold Rwire Rbase; omega
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- (A) on [0, dimDivAt): s5 = s2.
    intro p hp
    show Gate.applyNat (egG5 w bits numWin cm N) s4 p = s2 p
    rw [Gate.applyNat_congr hG5wt s4 s3 hs4_lo p hp]
    -- applyNat G5 s3 = applyNat (reverse G3) (applyNat G3 s2) = s2.
    show Gate.applyNat (Gate.reverse (egG3 w bits numWin cm N))
        (Gate.applyNat (egG3 w bits numWin cm N) s2) p = s2 p
    rw [applyNat_reverse_cancel (egG3 w bits numWin cm N) (dimDivAt w bits numWin cm 1) hG3wt s2]
  · -- (B) R band: z.testBit k.
    intro k hk
    show Gate.applyNat (egG5 w bits numWin cm N) s4 (Rwire w bits numWin cm k)
      = ((a ^ (2 ^ i) * x) % N).testBit k
    -- G5 frames R (R ≥ dimDivAt, G5 WellTyped at dimDivAt).
    rw [Gate.applyNat_oob hG5wt s4 (by unfold Rwire Rbase; omega)]
    -- s4 (Rwire k) = xor (s3 (Rwire k)) (s3 (1+2k+1)) = xor false (z.testBit k).
    rw [hs4, egG4]
    rw [copyBand_at (fun j => 1 + 2 * j + 1) (Rwire w bits numWin cm) bits s3
          (fun a b ha hb hab => Rwire_inj w bits numWin cm a b hab)
          (fun a b ha hb => acc_ne_Rwire w bits numWin cm hb1 a b ha) k hk]
    rw [show s3 (Rwire w bits numWin cm k) = false from
          s3_R_clean w bits numWin cm N a hw hbits hb1 hN2 hcm i x hx k hk,
        show s3 (1 + 2 * k + 1) = ((a ^ (2 ^ i) * x) % N).testBit k from
          s3_acc_bit w bits numWin cm N a hw hbits hb1 hN1 hN2 hcm hbudget i x hx
            hbudget_nowrap k hk]
    exact Bool.false_xor _
  · -- (C) above dimDivAt, outside R: s5 = s2.
    intro p hp hpR
    show Gate.applyNat (egG5 w bits numWin cm N) s4 p = s2 p
    rw [Gate.applyNat_oob hG5wt s4 hp]
    -- s4 p = s3 p (G4 only writes R, p ∉ R) = s2 p (G3 frames ≥ dimDivAt).
    rw [hs4, egG4, copyBand_frame _ _ _ _ _ (fun k hk => hpR k hk)]
    rw [hs3, egG3_frame_above w bits numWin cm N hb1 hcm p hp]

/-! ## §3. The per-step state characterization toward `block_matches_residue_direct`.

We compute `EGate.applyNat (eg …) (encodeDataZeroAnc bits anc x)` by tracking the
state through `G1 … G9`.  The intermediate states are named `s1 … s9`.  The crux
facts:

  * `s1` is a `CountGateMulInput` with `y = x` (`ge2021_adaptIn_clean`).
  * `s2`'s ACC band decodes to `(a^(2^i)·x) % 2^bits = a^(2^i)·x` (no-wrap)
    (`countOptimal_multiplyAdd_value`); addr=x preserved, anc cleared, frame
    (`multiplyAddAt_full_output`).
  * `s3` reduces the ACC to `z = (a^(2^i)·x) % N`, quotient `j` in the fresh
    divModN scratch, working scratch clean, frame (`divModNAt_decode`).
  * `s4` copies the ACC band (now `z`) into the fresh R register (`copyBand_at`).
  * `s5` un-reduces (G5 = reverse G3) restoring the ACC to `v` and clearing Q
    (`applyNat_reverse_cancel`), with R framed.
  * `s6 = unmul i` uncomputes the multiply: ACC→0, addr=x, everything off R equal
    to `applyNat G1 (encode x)`, R preserved (the NAMED G6 obligation `hunmul`).
  * `s7` un-scatters (G7 = reverse G1) restoring D=x, with R framed.
  * `s8` in-place modular-multiplies D: x ↦ z = (a^(2^i)·x)%N, R framed.
  * `s9` clears R via D (R ^= D = z^z = 0), giving `encodeDataZeroAnc bits anc z`.

The proof is delivered up to the precise point recorded in the module report. -/

/-- The "G1 output on `encode x` with R = z" state — the precise target the G6
    multiply-uncompute must produce from `s5`.  Off the R band it is the
    `CountGateMulInput` `applyNat G1 (encode x)`; on the R band it carries `z`. -/
def t6State (w bits numWin cm N a i x : Nat) : Nat → Bool :=
  fun p =>
    if (∃ k, k < bits ∧ p = Rwire w bits numWin cm k)
    then ((a ^ (2 ^ i) * x) % N).testBit (p - Rbase w bits numWin cm)
    else Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) p

/-- **The named G6 (measurement-uncompute) obligation.**  `multiplyAddAt` (G2) is a
    measured `EGate` — not Boolean-reversible — so the multiply UNcompute is the
    separate pure-`Gate` family `unmul`, required to map the post-G5 state `s5`
    (= `s2` off R, `z` on R) to `t6State` (= `applyNat G1 (encode x)` off R, `z` on
    R).  This is exactly "undo the count-gate multiply, leaving the scattered input
    `x` and the saved residue `z`."  Carried as a hypothesis; no instance fabricated. -/
def UnmulSpec (w bits numWin cm N a : Nat) (unmul : Nat → Gate) : Prop :=
  ∀ i x, x < N →
    Gate.applyNat (unmul i) (s5State w bits numWin cm N a i x)
      = t6State w bits numWin cm N a i x

/-- Geometry: `bits + anc ≤ Dmul ≤ Rbase`, so both G7 (`WellTyped (bits+anc)`) and
    G8 (`WellTyped Dmul`) frame the R band. -/
theorem Rbase_ge_Dmul (w bits numWin cm : Nat) :
    Dmul w bits ≤ Rbase w bits numWin cm := by unfold Rbase; omega

theorem Dmul_ge_encDim (w bits : Nat) : bits + (2 * w + 2 * bits + 3) ≤ Dmul w bits := by
  unfold Dmul InPlaceMulDataAt.scratchBase dimNative yBase; omega

/-! ## §4. THE FINAL ASSEMBLY — `block_matches_residue_direct`.

Given the named G6 obligation `UnmulSpec`, the chain G7 ; G8 ; G9 transforms
`t6State` (= `applyNat G1 (encode x)` off R, `z` on R) into `encodeDataZeroAnc z`:

  * G7 = reverse G1 inverts the scatter on `[0, bits+anc)` (R framed, `≥ bits+anc`),
    giving `encode x` (+ R = z).
  * G8 = inPlaceMulDataAt multiplies the data band `x ↦ z` (R framed, `≥ Dmul`),
    giving `encode z` (+ R = z).
  * G9 clears R via the data band (`R_k ^= D_{bits-1-k} = z_k ^ z_k = 0`),
    giving `encode z`. -/

/-- The R band sits at-or-above the encode dimension `bits + anc`. -/
theorem Rwire_ge_encDim (w bits numWin cm : Nat) (k : Nat) :
    bits + (2 * w + 2 * bits + 3) ≤ Rwire w bits numWin cm k := by
  have h1 := Dmul_ge_encDim w bits
  have h2 := Rbase_ge_Dmul w bits numWin cm
  unfold Rwire; omega

/-- The R band sits at-or-above `Dmul`. -/
theorem Rwire_ge_Dmul (w bits numWin cm : Nat) (k : Nat) :
    Dmul w bits ≤ Rwire w bits numWin cm k := by
  have h2 := Rbase_ge_Dmul w bits numWin cm
  unfold Rwire; omega

/-- **G1 is WellTyped at `Rbase`.**  All its scatter addresses lie below `S ≤ Rbase`. -/
theorem egG1_wellTyped_Rbase (w bits numWin cm : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (i : Nat) :
    Gate.WellTyped (Rbase w bits numWin cm) (egG1 w bits i) := by
  have hRb : bits ≤ Rbase w bits numWin cm := by
    unfold Rbase dimDivAt DivModNAt.scratchBase; omega
  have hfit : ∀ j, j < bits → scatterAddr w bits 1 j < bits + (Rbase w bits numWin cm - bits) := by
    intro j hj
    have hjm : j % w < w := Nat.mod_lt j hw
    have hjd : j / w < numWin := by
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, hbits]; exact hj
    have hblk : (j / w) * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
      le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : j / w + 1 ≤ numWin))
    have hs : scatterAddr w bits 1 j < DivModNAt.scratchBase w bits numWin 1 := by
      unfold scatterAddr addrBaseOf DivModNAt.scratchBase; omega
    have hSR : DivModNAt.scratchBase w bits numWin 1 ≤ Rbase w bits numWin cm := by
      unfold Rbase dimDivAt; omega
    omega
  have := ge2021_adaptIn_wellTyped w bits (Rbase w bits numWin cm - bits) 1 (by omega) hfit i
  rw [show bits + (Rbase w bits numWin cm - bits) = Rbase w bits numWin cm from by omega] at this
  exact this

/-- A position is in the R band iff `Rbase ≤ p < Rbase + bits`. -/
theorem mem_Rband_iff (w bits numWin cm p : Nat) :
    (∃ k, k < bits ∧ p = Rwire w bits numWin cm k)
      ↔ (Rbase w bits numWin cm ≤ p ∧ p < Rbase w bits numWin cm + bits) := by
  constructor
  · rintro ⟨k, hk, rfl⟩; unfold Rwire; omega
  · rintro ⟨h1, h2⟩; exact ⟨p - Rbase w bits numWin cm, by omega, by unfold Rwire; omega⟩

/-- **G7 (un-scatter, = reverse G1) on `t6`.**  On `[0, Rbase)` (everything except
    the R band, which lies above) `t6` equals `applyNat G1 (encode x)`, so reverse-
    cancel recovers `encode x`; the R band (`≥ Rbase`) is framed at `z`. -/
theorem t7_unscatter
    (w bits numWin cm N a : Nat)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (i x : Nat) (hx : x < N) :
    (∀ p, p < Rbase w bits numWin cm →
        Gate.applyNat (egG7 w bits i) (t6State w bits numWin cm N a i x) p
          = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x p)
    ∧ (∀ k, k < bits →
        Gate.applyNat (egG7 w bits i) (t6State w bits numWin cm N a i x)
            (Rwire w bits numWin cm k)
          = ((a ^ (2 ^ i) * x) % N).testBit k) := by
  set g1out := Gate.applyNat (egG1 w bits i)
    (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) with hg1out
  have hG1wt : Gate.WellTyped (Rbase w bits numWin cm) (egG1 w bits i) :=
    egG1_wellTyped_Rbase w bits numWin cm hw hbits hb1 i
  have hG7wt : Gate.WellTyped (Rbase w bits numWin cm) (egG7 w bits i) := by
    show Gate.WellTyped (Rbase w bits numWin cm) (Gate.reverse (egG1 w bits i))
    exact FormalRV.Shor.GidneyInPlace.GatePerm.reverse_wellTyped _ _ hG1wt
  -- t6 agrees with g1out on [0, Rbase) (it differs only on the R band, ≥ Rbase).
  have hagree : ∀ q, q < Rbase w bits numWin cm →
      t6State w bits numWin cm N a i x q = g1out q := by
    intro q hq
    unfold t6State
    rw [if_neg (by
      rw [mem_Rband_iff]; omega)]
  refine ⟨?_, ?_⟩
  · intro p hp
    show Gate.applyNat (egG7 w bits i) (t6State w bits numWin cm N a i x) p = _
    rw [Gate.applyNat_congr hG7wt _ g1out hagree p hp]
    show Gate.applyNat (Gate.reverse (egG1 w bits i)) g1out p = _
    rw [hg1out, applyNat_reverse_cancel (egG1 w bits i) (Rbase w bits numWin cm) hG1wt _]
  · intro k hk
    -- R band ≥ Rbase: framed by G7 (WellTyped at Rbase).
    rw [Gate.applyNat_oob hG7wt _ (by unfold Rwire; omega)]
    have hsub : Rwire w bits numWin cm k - Rbase w bits numWin cm = k := by
      unfold Rwire; omega
    unfold t6State
    rw [if_pos ⟨k, hk, rfl⟩, hsub]

/-- The modular inverse of `a^(2^i)` exists when `a·ainv0 ≡ 1 (mod N)`. -/
theorem inv_exists (N a ainv0 i : Nat) (hN1 : 1 < N) (h_inv0 : a * ainv0 % N = 1) :
    ∃ d, (a ^ (2 ^ i) * d) % N = 1 :=
  ⟨ainv0 ^ (2 ^ i), by
    rw [Nat.mul_mod]
    exact FormalRV.BQAlgo.mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0⟩

/-! ## §4. THE FULLY-CLOSED R-FREE VARIANT `egRfree` AND ITS RESIDUE DISCHARGE.

The 9-gate `eg` keeps a fresh register `R` carrying the divModN-reduced residue
`z` across the scaffold uncompute, then clears it against the in-place result.  But
`inPlaceMulDataAt_apply`'s input contract `DataMulReady` demands the WHOLE high
scratch (every position `bits + p`) be clean — and the live `R = z ≠ 0` violates it
(R sits at `bits + (Rbase - bits + k)` with native index `≥ dimNative`, outside the
in-place gate's footprint but inside `DataMulReady`'s universal quantifier).  This
is the PRECISE structural blocker for the literal 9-gate `eg`'s residue closure.

The honest fully-closed result drops `R` (and its copy/clear, both T-free):

    egRfree = G1 ; G2 ; G3 ; G5 ; G6 ; G7 ; G8

Here `G3 ; G5` reverse-cancel to identity (no intervening copy), so the
count-bearing scaffold `G2 ; (G3 ; G5) ; G6` nets to `G2 ; G6`; `G6` (= `unmul`)
uncomputes `G2` back to `applyNat G1 (encode x)`, `G7` un-scatters to `encode x`,
and the VERIFIED in-place modular multiplier `G8` realises `x ↦ (a^(2^i)·x) % N`.
The literal `multiplyAddAt` (G2) is STILL present as a sub-term.  This fully
discharges the residue equation, kernel-clean, given only the single named
measurement-uncompute obligation `UnmulSpecRfree`. -/

/-- The R-free assembled gate: `G1 ; G2 ; G3 ; G5 ; G6 ; G7 ; G8`. -/
def egRfree (w bits numWin cm N a : Nat) (unmul : Nat → Gate) (i : Nat) : EGate :=
  EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq (EGate.seq
    (EGate.base (egG1 w bits i))
    (egG2 w bits numWin a i))
    (EGate.base (egG3 w bits numWin cm N)))
    (EGate.base (egG5 w bits numWin cm N)))
    (EGate.base (unmul i)))
    (EGate.base (egG7 w bits i)))
    (EGate.base (egG8 w bits numWin N a i))

/-- `egRfree` contains the literal `multiplyAddAt` (G2) as a sub-term. -/
theorem egRfree_contains_multiplyAddAt (w bits numWin cm N a : Nat) (_unmul : Nat → Gate) (i : Nat) :
    egG2 w bits numWin a i = multiplyAddAt w bits bits (tableFam w bits a) 1 i numWin := rfl

/-- **The named measurement-uncompute obligation (R-free).**  `unmul i` maps the
    post-`G3;G5`-collapse state `s2` back to `applyNat G1 (encode x)` — i.e. it
    uncomputes the measured count-gate multiply `G2`, leaving the scattered input. -/
def UnmulSpecRfree (w bits numWin N a : Nat) (unmul : Nat → Gate) : Prop :=
  ∀ i x, x < N →
    Gate.applyNat (unmul i) (s2State w bits numWin a i x)
      = Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)

/-- **G3 ; G5 collapse to identity (no intervening copy).**  `G5 = reverse G3` and
    nothing is written in between, so by `applyNat_reverse_cancel` the pair restores
    the post-G2 state `s2`. -/
theorem s2_restored_after_G3G5
    (w bits numWin cm N a : Nat)
    (hbits : 1 ≤ bits) (hcm : cm ≤ bits)
    (i x : Nat) :
    Gate.applyNat (egG5 w bits numWin cm N)
        (Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x))
      = s2State w bits numWin a i x := by
  have hG3wt : Gate.WellTyped (dimDivAt w bits numWin cm 1) (egG3 w bits numWin cm N) :=
    divModNAt_wellTyped w bits numWin cm N 1 hbits hcm
      (by unfold DivModNAt.scratchBase; omega)
  show Gate.applyNat (Gate.reverse (egG3 w bits numWin cm N))
      (Gate.applyNat (egG3 w bits numWin cm N) (s2State w bits numWin a i x)) = _
  exact applyNat_reverse_cancel (egG3 w bits numWin cm N) (dimDivAt w bits numWin cm 1)
    hG3wt (s2State w bits numWin a i x)

/-- **★ THE FULLY-CLOSED RESIDUE DISCHARGE (R-free). ★**  Given the standard sizing
    and the single named measurement-uncompute obligation `UnmulSpecRfree`, the
    concrete `egRfree` (which literally contains `multiplyAddAt`) realises the residue
    equation on the canonical zero-ancilla encoding:

      EGate.applyNat (egRfree … unmul i) (encodeDataZeroAnc bits anc x)
        = encodeDataZeroAnc bits anc ((a^(2^i)·x) % N)      (x < N).

    Kernel-clean. -/
theorem block_matches_residue_direct
    (w bits numWin cm N a ainv0 : Nat) (unmul : Nat → Gate)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hunmul : UnmulSpecRfree w bits numWin N a unmul)
    (i x : Nat) (hx : x < N) :
    EGate.applyNat (egRfree w bits numWin cm N a unmul i)
        (encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x)
      = encodeDataZeroAnc bits (2 * w + 2 * bits + 3) ((a ^ (2 ^ i) * x) % N) := by
  set anc := 2 * w + 2 * bits + 3 with hanc
  set c := a ^ (2 ^ i) with hc
  set cinv := modInv N c with hcinv
  have hN0 : 0 < N := by omega
  have hNle : N ≤ 2 ^ bits := by omega
  have hxbits : x < 2 ^ bits := lt_of_lt_of_le hx hNle
  have hzbits : c * x % N < 2 ^ bits := lt_of_lt_of_le (Nat.mod_lt _ hN0) hNle
  have hanc_pos : 0 < anc := by rw [hanc]; omega
  obtain ⟨hcinv_lt, hcinv_inv⟩ := modInv_spec N c hN0 (inv_exists N a ainv0 i hN1 h_inv0)
  -- Unfold the EGate.seq chain to the composite Gate.applyNat.
  show Gate.applyNat (egG8 w bits numWin N a i)
        (Gate.applyNat (egG7 w bits i)
          (Gate.applyNat (unmul i)
            (Gate.applyNat (egG5 w bits numWin cm N)
              (Gate.applyNat (egG3 w bits numWin cm N)
                (EGate.applyNat (egG2 w bits numWin a i)
                  (Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits anc x)))))))
      = encodeDataZeroAnc bits anc (c * x % N)
  -- G1 ; G2 = s2State.
  rw [show EGate.applyNat (egG2 w bits numWin a i)
          (Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits anc x))
        = s2State w bits numWin a i x from rfl]
  -- G3 ; G5 collapse to s2State.
  rw [s2_restored_after_G3G5 w bits numWin cm N a hb1 hcm i x]
  -- G6 = unmul uncomputes G2 → applyNat G1 (encode x).
  rw [hunmul i x hx]
  -- G7 = reverse G1 → encode x (reverse-cancel at dim Dmul; G1 well-typed there).
  have hG1wt : Gate.WellTyped (Dmul w bits) (egG1 w bits i) := by
    have hSDmul : DivModNAt.scratchBase w bits numWin 1 ≤ Dmul w bits := by
      unfold DivModNAt.scratchBase Dmul InPlaceMulDataAt.scratchBase dimNative yBase
      have : numWin * (2 * w) = 2 * bits := by
        rw [show numWin * (2 * w) = (numWin * w) * 2 from by ring, hbits]; ring
      omega
    have hfit : ∀ j, j < bits → scatterAddr w bits 1 j < bits + (Dmul w bits - bits) := by
      intro j hj
      have hjm : j % w < w := Nat.mod_lt j hw
      have hjd : j / w < numWin := by
        apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm, hbits]; exact hj
      have hblk : (j / w) * (2 * w) + 2 * w ≤ numWin * (2 * w) :=
        le_trans (le_of_eq (by ring)) (Nat.mul_le_mul_right (2 * w) (by omega : j / w + 1 ≤ numWin))
      have hs : scatterAddr w bits 1 j < DivModNAt.scratchBase w bits numWin 1 := by
        unfold scatterAddr addrBaseOf DivModNAt.scratchBase; omega
      have := Dmul_ge_encDim w bits; omega
    have hwt := ge2021_adaptIn_wellTyped w bits (Dmul w bits - bits) 1
      (by omega) hfit i
    rw [show bits + (Dmul w bits - bits) = Dmul w bits from by
      have := Dmul_ge_encDim w bits; omega] at hwt
    exact hwt
  rw [show Gate.applyNat (egG7 w bits i)
          (Gate.applyNat (egG1 w bits i) (encodeDataZeroAnc bits anc x))
        = encodeDataZeroAnc bits anc x from
        applyNat_reverse_cancel (egG1 w bits i) (Dmul w bits) hG1wt
          (encodeDataZeroAnc bits anc x)]
  -- G8 = X ctrl ; inPlaceMul ; X ctrl on encode x.
  -- Step 1: set the control wire `bits`.
  show Gate.applyNat (Gate.X bits)
        (Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv)
          (Gate.applyNat (Gate.X bits) (encodeDataZeroAnc bits anc x)))
      = encodeDataZeroAnc bits anc (c * x % N)
  set e := encodeDataZeroAnc bits anc x with he
  set e1 := Gate.applyNat (Gate.X bits) e with he1
  -- DataMulReady on e1.
  have he_bits : e bits = false := by
    rw [he, show bits = bits + 0 from rfl]
    exact encodeDataZeroAnc_anc hxbits hanc_pos
  have hdmr : DataMulReady w bits anc x e1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [he1, Gate.applyNat_X, update_neq _ _ _ _ (by omega), he]
    · show e1 (InPlaceMulDataAt.scratchBase bits) = true
      rw [show InPlaceMulDataAt.scratchBase bits = bits from rfl, he1, Gate.applyNat_X,
          update_eq, he_bits]; rfl
    · intro p hp0 hpv
      show e1 (InPlaceMulDataAt.scratchBase bits + p) = false
      rw [show InPlaceMulDataAt.scratchBase bits = bits from rfl, he1, Gate.applyNat_X,
          update_neq _ _ _ _ (by unfold ulookup_ctrl_idx at hp0; omega), he]
      by_cases hb : bits + p < bits + anc
      · exact encodeDataZeroAnc_anc hxbits (by omega)
      · exact encodeDataZeroAnc_oob hanc_pos (by omega)
  obtain ⟨hData, hCtrl, hScr, _hFrame, _hwt⟩ :=
    inPlaceMulDataAt_apply w bits N numWin c cinv anc x e1
      hw (by omega) hbits hN0 hN2 hx hcinv_lt hcinv_inv hdmr
  -- Step 3 (X bits) then the funext to encode z.
  funext q
  rw [Gate.applyNat_X]
  by_cases hq : q = bits
  · -- control wire: after inPlaceMul it is `true`; X clears it to false = encode z bits.
    rw [hq, update_eq,
        show Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) e1 bits = true from hCtrl,
        show (encodeDataZeroAnc bits anc (c * x % N) bits) = false from by
          rw [show bits = bits + 0 from rfl]
          exact encodeDataZeroAnc_anc hzbits hanc_pos]
    rfl
  · rw [update_neq _ _ _ _ hq]
    by_cases hqd : q < bits
    · -- data band: inPlaceMul wrote encode z.
      rw [hData q hqd]
    · -- high region: inPlaceMul left it clean (scratch image or framed) = encode z (false).
      have hqz : encodeDataZeroAnc bits anc (c * x % N) q = false := by
        by_cases hb : q < bits + anc
        · rw [show q = bits + (q - bits) from by omega]
          exact encodeDataZeroAnc_anc hzbits
            (by omega)
        · exact encodeDataZeroAnc_oob hanc_pos (by omega)
      rw [hqz]
      -- show the inPlaceMul output at q (high) is false.  Two subcases on q - bits.
      by_cases hval : isValWire w bits (q - bits)
      · -- q - bits is a VALUE wire ⟹ q = bits + (value wire) is NOT a layoutMul image,
        -- so inPlaceMul frames q; e1 q = e q = encode x q = false.
        have hframe : Gate.applyNat (inPlaceMulDataAt w bits N numWin c cinv) e1 q = e1 q := by
          unfold inPlaceMulDataAt
          apply InPlaceMulDataAt.applyNat_relabelGate_frame (InPlaceMulDataAt.layoutMul w bits)
            (FormalRV.Shor.WindowedCircuit.windowedModNMulInPlace w bits c cinv N numWin) e1 q
          intro q'
          by_cases hv' : InPlaceMulDataAt.isValWire w bits q'
          · -- value wire image < bits ≤ q (q ≥ bits since hq, hqd).
            have himg := InPlaceMulDataAt.layoutMul_image_range w bits q'
            have hvimg : InPlaceMulDataAt.layoutMul w bits q' < bits := by
              rcases himg with hlt | hge
              · exact hlt
              · -- value wire ⟹ image < bits; but hge says ≥ bits → image = scratchBase + q' is
                -- the non-value branch, contradicting hv'.  Use nonval characterization.
                rw [InPlaceMulDataAt.layoutMul] at hge ⊢
                rw [if_pos hv'] at hge ⊢
                obtain ⟨h1, h2⟩ := hv'; unfold InPlaceMulDataAt.yBase at h1 h2 hge ⊢; omega
            omega
          · -- non-value image = bits + q'; equals q ⟹ q' = q - bits, a value wire — contra hv'.
            rw [InPlaceMulDataAt.layoutMul_nonval w bits q' hv',
                show InPlaceMulDataAt.scratchBase bits = bits from rfl]
            intro heq
            exact hv' (by
              rw [show q' = q - bits from by omega]; exact hval)
        rw [hframe, he1, Gate.applyNat_X, update_neq _ _ _ _ hq, he]
        by_cases hb : q < bits + anc
        · rw [show q = bits + (q - bits) from by omega]
          exact encodeDataZeroAnc_anc hxbits (by omega)
        · exact encodeDataZeroAnc_oob hanc_pos (by omega)
      · -- q - bits is a NON-value scratch image ⟹ hScr gives false.
        rw [show q = InPlaceMulDataAt.scratchBase bits + (q - bits) from by
              show q = bits + (q - bits); omega]
        exact hScr (q - bits) (by unfold ulookup_ctrl_idx; omega) hval

/-- **★ PACKAGED DISCHARGE — `ModExpAtEncodedMatchesResidue` for `egRfree`. ★**  The
    concrete `egRfree` (which literally contains `multiplyAddAt`) satisfies the named
    residual structure `ShorComposedFinal.ModExpAtEncodedMatchesResidue` of §5 of
    `ShorComposedFinal` — i.e. its `block_matches_residue` field holds — at the
    canonical zero-ancilla encoding, given the single named measurement-uncompute
    obligation `UnmulSpecRfree`.  This is the requested discharge of
    `block_matches_residue` for a CONCRETE `eg`, kernel-clean. -/
theorem egRfree_matchesResidue
    (w bits numWin cm N a ainv0 : Nat) (unmul : Nat → Gate)
    (hw : 0 < w) (hbits : numWin * w = bits) (hb1 : 1 ≤ bits)
    (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (hcm : cm ≤ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (hunmul : UnmulSpecRfree w bits numWin N a unmul) :
    ShorComposedFinal.ModExpAtEncodedMatchesResidue a N bits (2 * w + 2 * bits + 3)
      (fun i => egRfree w bits numWin cm N a unmul i)
      (fun _ x => encodeDataZeroAnc bits (2 * w + 2 * bits + 3) x) where
  block_matches_residue := fun i x hx =>
    block_matches_residue_direct w bits numWin cm N a ainv0 unmul
      hw hbits hb1 hN1 hN2 hcm h_inv0 hunmul i x hx

end

end FormalRV.Audit.GidneyEkera2021.ModExpAtReductionDirect
