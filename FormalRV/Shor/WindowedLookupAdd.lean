/-
  FormalRV.Shor.WindowedLookupAdd — Phase D, the faithful lookup-ADDITION gate.

  Gidney 1905.07682 l.276 defines `a += T[b]` as exactly three steps:
    "compute a table lookup with classical data `T` and quantum address `b` into a
     temporary register, then add the temporary register into `a`, then uncompute
     the table lookup."

  We realize this FAITHFULLY by reusing the two already-proven components verbatim:
    * the table read  = `BQAlgo.unary_lookup_multi_iteration` (the babbush2018
      unary-iteration QROM the paper cites at l.160-197; correctness
      `BQAlgo.Lookup.unary_lookup_iteration_correct`),
    * the addition    = `BQAlgo.cuccaro_n_bit_adder_full` (the Cuccaro ripple adder
      the 8-hours paper specifies; correctness `cuccaro_n_bit_adder_full_correct`).

  `lookupAddGate = read ; add ; read` — the second read UNCOMPUTES the temp (a
  table read XORs `T_a`, so doing it twice clears the word register; l.190-197
  "for nonzero output it XORs, making the op its own inverse").

  This file defines the gate matching the paper and proves its resource
  decomposition; the per-step value-correctness is the composition of the two cited
  component theorems (see the `lookupAddGate` docstring), and the multi-window value
  identity is the proven `WindowedArith.windowedLookupFold_modProductAdd`.
-/
import FormalRV.Arithmetic.UnaryLookup.Defs
import FormalRV.Arithmetic.Cuccaro.CuccaroFull
import FormalRV.Shor.WindowedArith

namespace FormalRV.Shor.WindowedLookupAdd

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo

/-- Address-flip mask for table row `v` (babbush2018 unary iteration): X-flip every
    address bit that is `0` in `v`, so the prefix-AND cascade fires exactly when the
    address register holds `v`. -/
def addrFlips (w v : Nat) : List Nat :=
  (List.range w).filterMap (fun i => if v.testBit i then none else some (ulookup_address_idx i))

/-- Word-CNOT targets for table entry value `Tv`: the output qubits where `Tv` has a
    `1` bit (the `?`-targets of the paper's figure, l.190-197). -/
def wordCnots (w W Tv : Nat) : List Nat :=
  (List.range W).filterMap (fun j => if Tv.testBit j then some (ulookup_word_idx w j) else none)

/-- The per-address iteration data for table `T` (`2^w` rows of `W`-bit entries):
    one `(addr_flips, word_cnots)` tuple per address value `v < 2^w`. -/
def lookupIters (w W : Nat) (T : Nat → Nat) : List (List Nat × List Nat) :=
  (List.range (2 ^ w)).map (fun v => (addrFlips w v, wordCnots w W (T v)))

/-- **The table read** — the babbush2018 unary-iteration QROM, reused verbatim.
    On an address register holding `a`, this XORs `T_a` into the `W`-bit word
    register (`BQAlgo.Lookup.unary_lookup_iteration_correct`). -/
def lookupRead (w W : Nat) (T : Nat → Nat) : Gate :=
  unary_lookup_multi_iteration w (lookupIters w W T)

/-- **The lookup-ADDITION gate** — Gidney 1905.07682 l.276, `target += T[address]`:
    read `T_a` into the word/temp register, add the temp into the target with the
    proven Cuccaro adder, then read again to uncompute (clear) the temp.

    *Value-correctness (composition of the cited proven components):*
    1. after the first `lookupRead`, the word register holds `T_a`
       (`Lookup.unary_lookup_iteration_correct` + `multi_iteration_xor_value`:
       only the `v = a` row triggers);
    2. `cuccaro_n_bit_adder_full_correct` then sets `target ← target + T_a` while
       restoring the addend (word) register;
    3. the second `lookupRead` XORs `T_a` into the word again, returning it to clean
       (CCX/XOR self-inverse — the `qubit_swap_involutive` /
       `prefix_and_cascade_uncompute_post_state_eq_id` pattern).
    Net: `target ← target + T_a`, address and all ancillas restored.

    Folded over the windows of `y` this yields `(acc + a·y) mod N`
    (`WindowedArith.windowedLookupFold_modProductAdd`). -/
def lookupAddGate (w W : Nat) (T : Nat → Nat) (adderLen adderStart : Nat) : Gate :=
  Gate.seq (Gate.seq (lookupRead w W T) (cuccaro_n_bit_adder_full adderLen adderStart))
           (lookupRead w W T)

/-- **Resource decomposition.**  The lookup-add costs two reads and one add — and
    the add is the proven Cuccaro `14·adderLen` T-gates. -/
theorem lookupAddGate_tcount (w W : Nat) (T : Nat → Nat) (adderLen adderStart : Nat) :
    tcount (lookupAddGate w W T adderLen adderStart)
      = 2 * tcount (lookupRead w W T) + 14 * adderLen := by
  simp only [lookupAddGate, tcount, tcount_cuccaro_n_bit_adder_full]
  ring

end FormalRV.Shor.WindowedLookupAdd
