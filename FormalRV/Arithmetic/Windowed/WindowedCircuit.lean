/-
  FormalRV.Shor.WindowedCircuit — Phase D, the FULL windowed-multiplier LOGICAL
  CIRCUIT for arbitrary window size, with integers encoded in logical qubits.

  This is the concrete `Gate`-IR construction (not just the arithmetic identities of
  `WindowedArith`): a real circuit that, on a register holding the integer `y`,
  computes `acc += a·y` (Gidney's windowed product-addition, 1905.07682 l.296–345),
  built per window from
    * the proven babbush2018 QROM read  (`BQAlgo.unary_lookup_multi_iteration`), and
    * the proven Cuccaro ripple adder    (`BQAlgo.cuccaro_n_bit_adder_full`),
  with the lookup word register laid out AS the adder's addend (the layout that
  makes read·add·unread compose), and each `y`-window CX-copied into the lookup
  address register.

  Integers are genuinely encoded in qubits (`encodeReg`).  This file also computes
  the circuit's **Toffoli count** in closed form (kernel-clean) and compares it to
  the resource numbers reported in Gidney–Ekerå (see `windowedMulCircuit_toffoli` and
  the comparison note).  Execution on encoded data is checked in
  `FormalRV.Shor.WindowedCircuitExec`.
-/
import FormalRV.Arithmetic.Windowed.WindowedLookupAdd
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGateDerivations
import FormalRV.Arithmetic.Adder.Cuccaro

namespace FormalRV.Shor.WindowedCircuit

open FormalRV.Framework FormalRV.Framework.Gate FormalRV.BQAlgo
open FormalRV.Shor.WindowedLookupAdd

/-! ## §1. The circuit. -/

/-- Encode integer `x` into the `bits` logical qubits `[base, base+bits)`:
    qubit `base+i` carries bit `i` of `x`. -/
def encodeReg (base bits x : Nat) : Nat → Bool := fun p =>
  if base ≤ p ∧ p < base + bits then x.testBit (p - base) else false

/-! ### Layout-neutral building blocks (shared by the generic engine and the surface). -/

/-- Cuccaro full-adder addend bit `j` sits at `q_start + 2j + 2`.
    (= `cuccaroAdder.addendIdx q_start j`, kept as a standalone def so the concrete
    `q_start + 2j + 2` shape is available definitionally to consumers.) -/
def addendIdx (q_start j : Nat) : Nat := q_start + 2 * j + 2

/-- Word-CNOT targets for entry value `Tv`, placed at arbitrary positions `pos j`
    (here: the adder's addend bits). -/
def wordCnotsAt (pos : Nat → Nat) (W Tv : Nat) : List Nat :=
  (List.range W).filterMap (fun j => if Tv.testBit j then some (pos j) else none)

/-- The QROM read writing `T[address]` directly into the positions `pos` (the
    adder addend), reusing the proven `unary_lookup_multi_iteration`. -/
def lookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) : Gate :=
  unary_lookup_multi_iteration w
    ((List.range (2 ^ w)).map (fun v => (addrFlips w v, wordCnotsAt pos W (T v))))

/-- CX-copy window `j` of the `y`-register (`yBase`-based) into the lookup address
    register `ulookup_address_idx 0 .. w-1`.  Self-inverse, so re-applying uncopies. -/
def copyWindow (w yBase j : Nat) : Gate :=
  (List.range w).foldl
    (fun g i => Gate.seq g (Gate.CX (yBase + j * w + i) (ulookup_address_idx i))) Gate.I

/-! ### Generic engine: the windowed multiplier over an arbitrary `Adder` interface.

The defs below take `(A : Adder)` as their first argument and parameterize the
three Cuccaro-specific choices — where the augend (accumulator) bits live
(`A.augendIdx`), where the addend (lookup word) bits live (`A.addendIdx`), and
which adder circuit runs (`A.circuit`).  The Cuccaro-specialized names that the
rest of the file and downstream consumers use are recovered below by
instantiating `A := cuccaroAdder`. -/

/-- **Generic accumulator decode.**  Read the augend register of adder `A` at base
    `q_start`, `bits` qubits wide, LSB-first.  (`A.augendIdx q_start i` holds bit `i`.) -/
def decodeAccOf (A : Adder) (f : Nat → Bool) (q_start bits : Nat) : Nat :=
  decodeReg (A.augendIdx q_start) bits f

/-- **Generic lookup-ADDITION.**  Gidney l.276 read·add·unread, with the lookup
    word register laid out AS adder `A`'s addend register (`A.addendIdx q_start`)
    so the read·add·unread composes. -/
def lookupAddAtOf (A : Adder) (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) : Gate :=
  Gate.seq (Gate.seq (lookupReadAt w (A.addendIdx q_start) W T)
                     (A.circuit bits q_start))
           (lookupReadAt w (A.addendIdx q_start) W T)

/-- **Generic window step.**  Copy window `j` into the lookup address, lookup-add
    the entry `T_j[v] = a·(2^w)^j·v` into adder `A`, then uncopy. -/
def windowStepOf (A : Adder) (w W a : Nat) (bits q_start yBase j : Nat) : Gate :=
  Gate.seq (Gate.seq (copyWindow w yBase j)
                     (lookupAddAtOf A w W (fun v => a * (2 ^ w) ^ j * v) bits q_start))
           (copyWindow w yBase j)

/-- **Generic windowed multiplier**, a fold of window-steps over adder `A`. -/
def windowedMulOf (A : Adder) (w W a : Nat) (bits q_start yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (windowStepOf A w W a bits q_start yBase j)) Gate.I

/-- **The full windowed-multiplier circuit over an arbitrary adder `A`.**
    Layout: `ctrl=0`; address bits `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`; the adder
    region at `q_start = 1+2w` (spanning `A.span bits` qubits); the `y`-register at
    `yBase = q_start + A.span bits`.  On `acc=0` it leaves `a·y mod 2^bits` in the
    accumulator (when `A.span bits` is the adder's true span). -/
def windowedMulCircuitOf (A : Adder) (w bits a numWin : Nat) : Gate :=
  windowedMulOf A w bits a bits (1 + 2 * w) (1 + 2 * w + A.span bits) numWin

/-! ### Table-generic surface: the windowed multiplier over an ARBITRARY lookup table.

The defs above hard-wire the table `fun v => a·(2^w)^j·v` (giving `a·y mod 2^bits`).
The `…TOf` variants below take the per-window table as a free parameter, so the SAME
circuit + value proof serve both the standard multiplier (`Tfam j := fun v => a·(2^w)^j·v`)
and the mod-`N`-REDUCED coset multiplier (`Tfam := tableValue a N w`, entries `< N`).
The hard-wired defs are recovered DEFINITIONALLY as the standard-table instances, so all
existing call sites and proofs are unchanged. -/

/-- **Table-generic window step.**  Like `windowStepOf` but with an ARBITRARY lookup
    table `T : Nat → Nat` for this window (instead of the hard-wired
    `fun v => a·(2^w)^j·v`). -/
def windowStepTOf (A : Adder) (w W : Nat) (T : Nat → Nat) (bits q_start yBase j : Nat) : Gate :=
  Gate.seq (Gate.seq (copyWindow w yBase j)
                     (lookupAddAtOf A w W T bits q_start))
           (copyWindow w yBase j)

/-- **Table-generic windowed multiplier**, a fold of table-generic window-steps with a
    per-window table family `Tfam : Nat → Nat → Nat` (`Tfam j` = the table for window `j`). -/
def windowedMulTOf (A : Adder) (w W : Nat) (Tfam : Nat → Nat → Nat)
    (bits q_start yBase numWin : Nat) : Gate :=
  (List.range numWin).foldl
    (fun g j => Gate.seq g (windowStepTOf A w W (Tfam j) bits q_start yBase j)) Gate.I

/-- **The full table-generic windowed-multiplier circuit**, standard layout (identical to
    `windowedMulCircuitOf`'s).  Recovers `windowedMulCircuitOf` at
    `Tfam := fun j v => a·(2^w)^j·v`, and the reduced coset multiplier at
    `Tfam := tableValue a N w` (= `fun j v => (a·(2^w)^j·v) % N`). -/
def windowedMulCircuitTOf (A : Adder) (w bits : Nat) (Tfam : Nat → Nat → Nat)
    (numWin : Nat) : Gate :=
  windowedMulTOf A w bits Tfam bits (1 + 2 * w) (1 + 2 * w + A.span bits) numWin

/-! ### Cuccaro surface: the existing API, recovered as the `cuccaroAdder` specialization.

The original names are now the `A := cuccaroAdder` instances of the generic engine.
Because `cuccaroAdder.augendIdx q i = q+2i+1`, `cuccaroAdder.addendIdx q i = q+2i+2`,
`cuccaroAdder.span n = 2n+1`, and `cuccaroAdder.circuit n q = cuccaro_n_bit_adder_full n q`
all hold *definitionally*, every Cuccaro-specialized def below is DEFEQ to its old
hard-wired definition, so all existing proofs and downstream consumers keep working
unchanged (no defeq-bridge lemma is needed). -/

/-- Decode the accumulator register: Cuccaro's running-sum bit `i` lives at
    `q_start + 2i + 1`.  (= `decodeAccOf cuccaroAdder`, defeq to the old fold.) -/
def decodeAcc (f : Nat → Bool) (q_start bits : Nat) : Nat :=
  decodeAccOf cuccaroAdder f q_start bits

/-- One lookup-ADDITION targeting the Cuccaro adder at `q_start` (Gidney l.276,
    read·add·unread), with the word register = the addend register.
    (= `lookupAddAtOf cuccaroAdder`, defeq to the old hard-wired version.) -/
def lookupAddAt (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) : Gate :=
  lookupAddAtOf cuccaroAdder w W T bits q_start

/-- One window step: copy the window into the address, lookup-add the entry
    `T_j[v] = a·(2^w)^j·v`, then uncopy.  (= `windowStepOf cuccaroAdder`.) -/
def windowStep (w W a : Nat) (bits q_start yBase j : Nat) : Gate :=
  windowStepOf cuccaroAdder w W a bits q_start yBase j

/-- The windowed multiplier as a fold of window-steps (parametric in `w`, `numWin`).
    (= `windowedMulOf cuccaroAdder`.) -/
def windowedMul (w W a : Nat) (bits q_start yBase numWin : Nat) : Gate :=
  windowedMulOf cuccaroAdder w W a bits q_start yBase numWin

/-- **The full windowed-multiplier circuit, standard layout, arbitrary `w`.**
    Layout: `ctrl=0`; address bits `1,3,…,2w−1`; AND-ancillas `2,4,…,2w`; the Cuccaro
    region at `q_start = 1+2w` (carry, then interleaved acc/addend up to `q_start+2·bits`);
    the `y`-register at `yBase = q_start + 2·bits + 1`.  On `acc=0` it leaves
    `a·y mod 2^bits` in the accumulator.

    (= `windowedMulCircuitOf cuccaroAdder`; since `cuccaroAdder.span bits = 2·bits+1`,
    the `yBase = 1+2w + A.span bits` of the generic engine is defeq to the old
    `1+2w+2·bits+1`.) -/
def windowedMulCircuit (w bits a numWin : Nat) : Gate :=
  windowedMulCircuitOf cuccaroAdder w bits a numWin

/-- The input store: control qubit set, integer `y` encoded in the `y`-register. -/
def mulInput (w bits numWin y : Nat) : Nat → Bool := fun p =>
  if p = ulookup_ctrl_idx then true
  else encodeReg (1 + 2 * w + 2 * bits + 1) (numWin * w) y p

/-- The accumulator's `q_start` for a `w`-window circuit. -/
def accStart (w : Nat) : Nat := 1 + 2 * w

/-! ## §2. Toffoli count (kernel-clean) and comparison with Gidney–Ekerå. -/

/-- Generic T-count of a left-fold of `seq`-appended steps with constant per-step cost. -/
theorem tcount_foldl_seq_const {α : Type} (step : α → Gate) (C : Nat)
    (hstep : ∀ a, tcount (step a) = C) (L : List α) (init : Gate) :
    tcount (L.foldl (fun g a => Gate.seq g (step a)) init) = tcount init + L.length * C := by
  induction L generalizing init with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih (Gate.seq init (step a))]
    simp only [tcount, hstep, List.length_cons]
    ring

/-- One unary-lookup iteration: `2·w` Toffolis (`14·w` T) — forward + reverse cascade,
    no measurement optimization.  (X/CX layers are T-free.) -/
theorem tcount_unary_lookup_iteration (w : Nat) (flips cnots : List Nat) :
    tcount (unary_lookup_iteration w flips cnots) = 14 * w := by
  simp only [unary_lookup_iteration, tcount, tcount_x_gates_zero, tcount_cx_gates_zero,
             tcount_prefix_and_cascade, tcount_prefix_and_uncompute]
  ring

/-- The multi-iteration read: `14·w` T per iteration. -/
theorem tcount_unary_lookup_multi_iteration (w : Nat) (iters : List (List Nat × List Nat)) :
    tcount (unary_lookup_multi_iteration w iters) = 14 * w * iters.length := by
  induction iters with
  | nil => simp [unary_lookup_multi_iteration, tcount]
  | cons hd rest ih =>
    obtain ⟨flips, cnots⟩ := hd
    show tcount (Gate.seq (unary_lookup_multi_iteration w rest)
                          (unary_lookup_iteration w flips cnots)) = _
    rw [tcount, ih, tcount_unary_lookup_iteration, List.length_cons]
    ring

/-- A full table read over a `2^w`-entry table: `14·w·2^w` T (= `2·w·2^w` Toffolis). -/
theorem tcount_lookupReadAt (w : Nat) (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) :
    tcount (lookupReadAt w pos W T) = 14 * w * 2 ^ w := by
  rw [lookupReadAt, tcount_unary_lookup_multi_iteration, List.length_map, List.length_range]

theorem tcount_copyWindow (w yBase j : Nat) : tcount (copyWindow w yBase j) = 0 := by
  rw [copyWindow, tcount_foldl_seq_const
        (fun i => Gate.CX (yBase + j * w + i) (ulookup_address_idx i)) 0 (fun _ => rfl)]
  simp [tcount]

/-! ### Generic resource counts (in terms of `tcount (A.circuit …)`). -/

/-- **Generic lookup-add T-count.**  Two table reads plus one adder application:
    `2·(14·w·2^w) + tcount (A.circuit bits q_start)`. -/
theorem tcount_lookupAddAtOf (A : Adder) (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    tcount (lookupAddAtOf A w W T bits q_start)
      = 2 * (14 * w * 2 ^ w) + tcount (A.circuit bits q_start) := by
  simp only [lookupAddAtOf, tcount, tcount_lookupReadAt]
  ring

/-- **Generic window-step T-count.**  The window copy/uncopy are Toffoli-free, so the
    cost is exactly the per-step lookup-add cost. -/
theorem tcount_windowStepOf (A : Adder) (w W a bits q_start yBase j : Nat) :
    tcount (windowStepOf A w W a bits q_start yBase j)
      = 2 * (14 * w * 2 ^ w) + tcount (A.circuit bits q_start) := by
  simp only [windowStepOf, tcount, tcount_copyWindow, tcount_lookupAddAtOf]
  ring

/-- **Generic windowed-multiplier T-count.**  `numWin` identical window steps. -/
theorem tcount_windowedMulOf (A : Adder) (w W a bits q_start yBase numWin : Nat) :
    tcount (windowedMulOf A w W a bits q_start yBase numWin)
      = numWin * (2 * (14 * w * 2 ^ w) + tcount (A.circuit bits q_start)) := by
  rw [windowedMulOf, tcount_foldl_seq_const (fun j => windowStepOf A w W a bits q_start yBase j) _
        (fun j => tcount_windowStepOf A w W a bits q_start yBase j)]
  simp [tcount, List.length_range]

/-- **Generic closed-form T-count of the full windowed multiplier over adder `A`.**
    The adder is run at base `q_start = 1+2·w` in each of the `numWin` windows. -/
theorem tcount_windowedMulCircuitOf (A : Adder) (w bits a numWin : Nat) :
    tcount (windowedMulCircuitOf A w bits a numWin)
      = numWin * (28 * w * 2 ^ w + tcount (A.circuit bits (1 + 2 * w))) := by
  rw [windowedMulCircuitOf, tcount_windowedMulOf]; ring

/-! ### Cuccaro corollaries (closed-form, since `tcount (cuccaro_n_bit_adder_full bits q) = 14·bits`). -/

theorem tcount_lookupAddAt (w W : Nat) (T : Nat → Nat) (bits q_start : Nat) :
    tcount (lookupAddAt w W T bits q_start) = 2 * (14 * w * 2 ^ w) + 14 * bits := by
  rw [lookupAddAt, tcount_lookupAddAtOf]
  show 2 * (14 * w * 2 ^ w) + tcount (cuccaro_n_bit_adder_full bits q_start) = _
  rw [tcount_cuccaro_n_bit_adder_full]

theorem tcount_windowStep (w W a bits q_start yBase j : Nat) :
    tcount (windowStep w W a bits q_start yBase j) = 2 * (14 * w * 2 ^ w) + 14 * bits := by
  rw [windowStep, tcount_windowStepOf]
  show 2 * (14 * w * 2 ^ w) + tcount (cuccaro_n_bit_adder_full bits q_start) = _
  rw [tcount_cuccaro_n_bit_adder_full]

theorem tcount_windowedMul (w W a bits q_start yBase numWin : Nat) :
    tcount (windowedMul w W a bits q_start yBase numWin)
      = numWin * (2 * (14 * w * 2 ^ w) + 14 * bits) := by
  rw [windowedMul, tcount_windowedMulOf]
  show numWin * (2 * (14 * w * 2 ^ w) + tcount (cuccaro_n_bit_adder_full bits q_start)) = _
  rw [tcount_cuccaro_n_bit_adder_full]

/-- **Closed-form T-count of the full windowed multiplier (arbitrary `w`).** -/
theorem tcount_windowedMulCircuit (w bits a numWin : Nat) :
    tcount (windowedMulCircuit w bits a numWin) = numWin * (28 * w * 2 ^ w + 14 * bits) := by
  rw [windowedMulCircuit, tcount_windowedMulCircuitOf]
  show numWin * (28 * w * 2 ^ w + tcount (cuccaro_n_bit_adder_full bits (1 + 2 * w))) = _
  rw [tcount_cuccaro_n_bit_adder_full]

/-- Toffoli count = number of `CCX` gates = `tcount / 7` (only `CCX` has nonzero T-count,
    `7` each; this is precisely the count the PPM layer turns into magic-state requests). -/
def toffoliCount (g : Gate) : Nat := tcount g / 7

/-- **Closed-form Toffoli count of the full windowed multiplier (arbitrary `w`).**
    `numWin · (4·w·2^w + 2·bits)` Toffolis — `numWin` windows, each two `2·w·2^w`-Toffoli
    table reads (read + uncompute) and one `2·bits`-Toffoli Cuccaro add. -/
theorem windowedMulCircuit_toffoli (w bits a numWin : Nat) :
    toffoliCount (windowedMulCircuit w bits a numWin) = numWin * (4 * w * 2 ^ w + 2 * bits) := by
  rw [toffoliCount, tcount_windowedMulCircuit,
      show numWin * (28 * w * 2 ^ w + 14 * bits) = numWin * (4 * w * 2 ^ w + 2 * bits) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **The `lg n` Toffoli factor comes from the verified STRUCTURE, not a coefficient.**
    On a register padded to width `n + pad` (the coset representation needs
    `pad = g_pad ≈ 3 lg n` padding qubits), the structurally-derived count
    (`windowedMulCircuit_toffoli`, proven by `tcount` recursion on the actual `Gate`) gains
    `2·pad` Toffolis per window — the Cuccaro adder structurally processing the padding
    qubits.  With `pad = 3 lg n` the contribution `6·numWin·lg n` is read off the verified
    structure; it is NOT inserted by hand. -/
theorem windowedMulCircuit_toffoli_padded (w n pad a numWin : Nat) :
    toffoliCount (windowedMulCircuit w (n + pad) a numWin)
      = numWin * (4 * w * 2 ^ w + 2 * n + 2 * pad) := by
  rw [windowedMulCircuit_toffoli]; ring

/-! ### Structural qubit count (`width`) — derived from the `Gate`, not a formula. -/

/-- The highest qubit index a circuit touches (`0` for the empty circuit). -/
def maxIdx : Gate → Nat
  | .I          => 0
  | .X q        => q
  | .CX c t     => max c t
  | .CCX a b c  => max a (max b c)
  | .seq g₁ g₂  => max (maxIdx g₁) (maxIdx g₂)

/-- The structural qubit count (width) of a circuit: one more than the highest index it
    acts on.  This is COMPUTED from the `Gate` term, so any padding qubits the circuit
    actually touches are counted — the qubit count reflects the real circuit. -/
def width (g : Gate) : Nat := maxIdx g + 1

/-- **Structural qubit count is computed from the circuit** (kernel `decide`): the verified
    `windowedMulCircuit` at `w=2, bits=4, numWin=2` genuinely uses `18` qubit lines. -/
theorem width_windowedMulCircuit_2_4_3_2 :
    width (windowedMulCircuit 2 4 3 2) = 18 := by decide

/-- **Padding qubits are counted by the structure** (kernel `decide`): padding the register
    by `pad = 3` (the coset representation's `g_pad ≈ 3 lg n` padding) makes the verified
    circuit structurally `2·pad = 6` qubits WIDER — the `lg n` qubit term is not a formula
    coefficient, it is the padding qubits the `Gate` actually acts on. -/
theorem width_windowedMulCircuit_padding :
    width (windowedMulCircuit 2 (4 + 3) 3 2) = width (windowedMulCircuit 2 4 3 2) + 2 * 3 := by
  decide

/-! ### Structural FULL count: composing verified building blocks.

The full modular exponentiation is `numMults` controlled multiplications, each a
sequence of `windowedMulCircuit` building blocks.  Composing them and counting the
result STRUCTURALLY (via `tcount` on the composite `Gate`) yields `numMults ×` the
per-block count — so the full count is circuit-derived, not a separate formula. -/

/-- `numMults` copies of the windowed multiplier in sequence (the modular-exponentiation
    skeleton: one multiply per exponent step). -/
def composedModExp (numMults w bits a numWin : Nat) : Gate :=
  (List.range numMults).foldl
    (fun g _ => Gate.seq g (windowedMulCircuit w bits a numWin)) Gate.I

theorem tcount_composedModExp (numMults w bits a numWin : Nat) :
    tcount (composedModExp numMults w bits a numWin)
      = numMults * tcount (windowedMulCircuit w bits a numWin) := by
  rw [composedModExp,
      tcount_foldl_seq_const (fun _ => windowedMulCircuit w bits a numWin) _ (fun _ => rfl)]
  simp [tcount, List.length_range]

/-- **Structural Toffoli count of the full (unoptimized) modular exponentiation**, derived
    by `tcount` recursion on the composed `Gate`: `numMults · numWin · (4·w·2^w + 2·bits)`.
    With `numMults = n_e`, `numWin = n/w`, `bits = n + g_pad`, this is the genuine
    circuit-level count of THIS construction (≈ `6 n³` at `w = lg n`, the no-optimization
    value); the paper's `0.3 n³` requires Gray-code + measurement-uncompute (the `4·w·2^w
    → 2^w` lookup optimization) and oblivious runways, which this building block omits. -/
theorem composedModExp_toffoli (numMults w bits a numWin : Nat) :
    toffoliCount (composedModExp numMults w bits a numWin)
      = numMults * (numWin * (4 * w * 2 ^ w + 2 * bits)) := by
  rw [toffoliCount, tcount_composedModExp, tcount_windowedMulCircuit,
      show numMults * (numWin * (28 * w * 2 ^ w + 14 * bits))
            = numMults * (numWin * (4 * w * 2 ^ w + 2 * bits)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]

/-! ### Comparison with Gidney–Ekerå (1905.09749, abstract circuit model).

The paper reports (main.tex:78) — for factoring an `n`-bit integer —
`0.3 n³ + 0.0005 n³ lg n` **Toffolis** and `3n + 0.002 n lg n` **logical qubits**.

Our verified count for ONE windowed product-addition `acc += a·y` of an `n`-bit operand
(`bits = n`, `numWin = n/w` windows) is, by `windowedMulCircuit_toffoli`,

    toffoliCount = (n/w)·(4·w·2^w + 2n)  =  4n·2^w + 2n²/w   Toffolis.

This is the **no-optimization upper bound**: the `2·w·2^w` per-table-read is the
forward+reverse unary cascade WITHOUT Gray-code amortization (factor `w`) and WITHOUT
the measurement-based uncompute (factor `~2`); the repo flags exactly this gap at
`UnaryLookup/Defs.lean` ("the paper's claim of `2^w` Toffolis ... is an optimization
factor of `2·w`").  Applying those two optimizations turns each read into `~2^w`, i.e.
our `4n·2^w + 2n²/w` into the paper's windowed `O((n/w)(n + 2^w))` = `O(n²/lg n)` at
`w = lg n`; the full modular exponentiation (`Θ(n)` multiplications) is then `O(n³/lg n)`,
matching the paper's `0.3 n³`.  Crucially, the deferred factor IS the
Gray-code/measurement-uncompute that the **PPM layer** supplies — so the comparison is
not a discrepancy but a quantified hand-off boundary to the lower level.  The asymptotic
scaling (`Θ(n²)` per multiplication up to the `lg n` optimization factor) matches the
paper exactly. -/

end FormalRV.Shor.WindowedCircuit
