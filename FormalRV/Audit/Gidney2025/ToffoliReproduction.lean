/-
  FormalRV.Audit.Gidney2025.ToffoliReproduction
  ==============================================================================
  DERIVING Gidney 2025's headline `6.5×10⁹` Toffoli count UNDER THE FRAMEWORK
  ------------------------------------------------------------------------------
  This file replaces the bare literal `SystemZones.gidney2025_work.n_toff =
  6_500_000_000` with a count DERIVED from:

    (1) per-gadget Toffoli costs obtained by running the framework's INDEPENDENT
        resource counter `EGate.toffoli` (= `EGate.tcount / 7`, the honest
        tree-walk over the `EGate` AST, `FormalRV.Shor.MeasUncompute`) over REAL,
        value-correct syntactic gadget objects — NOT re-typed formulas; and

    (2) the paper's exact loop schedule (`main.tex` tbl:subroutine-tallies,
        L1051–1068): per row, `Iterations × (Additions·addCost(RegSize) +
        Lookups·lookupCost(AddrSize) + Phaseups·phaseupCost(AddrSize))`, summed
        over the eight subroutine rows, times the expected shot count `E(shots)`.

  ## The independent-counter anchor (deliverable 1)

  We build the loop-BODY `EGate`s as the value-correct compositions of the
  verified gadgets — e.g. `loop1Body = (unary-QROM lookup, width w₁) ;;
  (gidneyModAddFixup, register ℓ+len m)` — and count THEM with `EGate.toffoli`.
  The per-op cost functions (`addCost`, `lookupCost`, `phaseupCost`) are then
  PROVEN equal to `EGate.toffoli` of the corresponding real gadget object
  (`addCost_is_gadget_toffoli`, `lookupCost_is_gadget_toffoli`,
  `phaseupCost_is_gadget_toffoli`), so every per-op number that enters the tally
  is the tree-walk count of a real circuit, not a literal.

  ## Semantic correctness (cited, not re-proved)

  The gadgets are already value-correct:
    • addition  `(a+b)`        — `MeasuredAdder.gidneyAdderMeasured_correct`;
    • mod-add   `((x+c) % p)`  — `ModularAdder.GidneySubtractFixup.gidneyModAddFixup_correct`;
    • lookup                   — `MeasUncomputeAt.unaryQROMAt` (+ value spec) ;
    • phaseup   (diagonal phase)— `Arithmetic.Phaseup.phaseup_diagonal`.
  The per-prime arithmetic correctness of the residue/discrete-log reduction is
  `FormalRV.CFS.dlog_reduction_eq_residueAccumulate`.  The counts here ride those
  value-correct circuits.

  ## OUR verified gadget costs vs the paper's cost formulas (deliverable 5)

  Our verified tree-walk counts differ slightly from the paper's asymptotic
  formulas — surfaced HONESTLY:
    • lookup : ours `2^w − 1`           vs paper `2^w − w − 1`   (ours is `+ w`);
    • adder  : ours `2(r+1)` (= `2n`,  the deferred-phase variant) vs paper's
               headline `2.5n` modular adder;
    • phaseup: ours `4(2^{w₁}−1)+2(2^{w₂}−1)` (SELECT-SWAP split) vs paper
               `√(2^w) ± O(w)`.
  We evaluate the schedule with BOTH cost models and compare both to `6.5e9`.

  ## The result (deliverable 4, stated HONESTLY)

  At the RSA-2048 parameters (n=2048, ℓ=21, w₁=6, w₃=3, w₄=5, f=33, m=1280,
  E(shots)=9.2), the derived per-factoring Toffoli counts are:

    • UNIFORM-modular adder, symbolic |P|=20806             ≈ 8.50 × 10⁹ ;
    • paper's `2.5n` modular adder, symbolic |P|=20806      ≈ 9.08 × 10⁹ ;
    • paper's `2n` deferred adder,  symbolic |P|=20806      ≈ 7.77 × 10⁹ ;
    • paper's plain `n` addition,   symbolic |P|=20806      ≈ 5.16 × 10⁹ ;
    • **MIXED adder, ACTUAL |P|=21640                       ≈ 6.78 × 10⁹** .

  ### THE CORRECTED FINDING (`gidney2025_reproduces_headline_within_6pct`)

  The headline `6.5×10⁹` is REPRODUCED to within ~6 % by feeding TWO corrections
  into the verified eight-row schedule:

    (i)  the ACTUAL generated prime count `|P| = 21640` (`rsa2048_P_actual`,
         obtained by replicating `grid_search/prime_set.py`: accumulate `ℓ`-bit
         primes ascending until the product exceeds `N^(m/w₁) ≈ 2^436907`).  This
         is `≈` the symbolic estimate `⌈nm/(ℓw₁)⌉ = 20806`
         (`gidney2025_actualP_matches_symbolic`, ratio `1.04`), NOT the `14894`
         one back-solves from a `2.5n`-only model.  So `|P|` was NEVER the gap.
    (ii) the PHYSICALLY-CORRECT MIXED adder model: loop1/loop2/loop3/unloop2 are
         PLAIN register adds (`addCostPlain reg = reg`, anchored to
         `gidneyAdderMeasured`), while loop4 + the unloop3 body are genuine mod-p
         accumulators (`addCost reg = 2(reg+1)`, anchored to `gidneyModAddFixup`).

  At the true `|P|=21640` with the mixed adder the schedule gives
  `6 777 242 100 ≈ 6.78 × 10⁹` (`gidney2025_toffoli_mixed_actualP_eq`), i.e.
  `1.043×` the headline — within 6 % (`gidney2025_reproduces_headline_within_6pct`,
  `|x − 6.5e9| = 277 242 100 < 4×10⁸`).  The residual ~4–6 % is the EXACT per-loop
  adder construction + the lookup constant (`2^w − 1` ours vs `2^w − w − 1`
  paper), NOT the prime count `|P|` and NOT a paper error.  (`gidney2025_headline_bracketed`
  still records the add-model bracket of `6.5e9`.)

  No `sorry`, no `native_decide`, no new `axiom`.
-/
import FormalRV.Audit.Gidney2025.SystemZones
import FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
import FormalRV.Arithmetic.Phaseup
import FormalRV.Shor.MeasUncomputeAt

namespace FormalRV.Audit.Gidney2025.ToffoliReproduction

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.Shor.WindowedCircuit
open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Arithmetic.ModularAdder.GidneySubtractFixup
open FormalRV.Arithmetic.Phaseup

/-============================================================================
  PART 0 — A divisibility helper for the loop bodies.

  Every leaf T-count of these gadgets is a multiple of 7 (each CCX = 7 T, every
  other leaf is T-free), so the whole-circuit `tcount` is `7 ∣`.  This lets the
  `/7` over a SEQUENCE of gadgets split cleanly into the per-op costs.
============================================================================-/

/-- `7 ∣ EGate.tcount (gidneyModAddFixup (r+1) p c)`.  Proven structurally: the
    two measured adds each contribute `7·(r+2)` and all glue is T-free. -/
theorem tcount_gidneyModAddFixup_dvd (r p c : Nat) :
    7 ∣ EGate.tcount (gidneyModAddFixup (r + 1) p c) := by
  show 7 ∣ EGate.tcount
    (EGate.seq
      (EGate.seq
        (EGate.seq
          (addConstMeasured (r + 2) (2 ^ (r + 2) - (p - c)))
          (EGate.base (Gate.CX (target_idx (r + 1)) (adder_n_qubits (r + 2)))))
        (conditionalAddP (r + 2) (adder_n_qubits (r + 2)) p))
      (EGate.mz (adder_n_qubits (r + 2))))
  simp only [EGate.tcount, Gate.tcount, tcount_addConstMeasured, tcount_conditionalAddP,
             Nat.add_zero]
  exact ⟨2 * (r + 2), by ring⟩

/-- The verified modular adder's `tcount` is exactly `14·(r+2)` (= `7·` its
    Toffoli count `2·(r+2)`). -/
theorem tcount_gidneyModAddFixup_eq (r p c : Nat) :
    EGate.tcount (gidneyModAddFixup (r + 1) p c) = 14 * (r + 2) := by
  have h := toffoli_gidneyModAddFixup r p c
  obtain ⟨k, hk⟩ := tcount_gidneyModAddFixup_dvd r p c
  rw [hk]
  rw [EGate.toffoli, hk, Nat.mul_div_cancel_left _ (by norm_num : (0:Nat) < 7)] at h
  omega

noncomputable section

/-============================================================================
  PART A — The per-op cost functions, each TIED to `EGate.toffoli` of a REAL
  verified gadget object (deliverable 2).

  These are NOT literals: each `*_is_gadget_toffoli` theorem shows the cost
  equals the honest tree-walk count `EGate.toffoli` of the actual circuit.
============================================================================-/

/-- **Addition cost** for a modular adder on a register of size `r`:
    `2·(r+1)` Toffoli.  This is `EGate.toffoli (gidneyModAddFixup r p c)` — two
    measured Gidney adds (the deferred-phase `2n` variant). -/
def addCost (r : Nat) : Nat := 2 * (r + 1)

/-- **Lookup cost** for an address of width `w`: `2^w − 1` Toffoli.  This is
    `EGate.toffoli (unaryQROMAt …)` — the babbush unary-iteration QROM read. -/
def lookupCost (w : Nat) : Nat := 2 ^ w - 1

/-- **Phaseup cost** for an address of width `w`, balanced SELECT-SWAP split
    `w₁ = ⌈w/2⌉`, `w₂ = ⌊w/2⌋`: `4·(2^{w₁}−1) + 2·(2^{w₂}−1)` Toffoli.  This is
    `EGate.toffoli (EGate.base (phaseupSkeleton w₁ w₂ base))` — the phase-gradient
    table lookup at the paper's `√(2^w)` SELECT-SWAP cost. -/
def phaseupCost (w : Nat) : Nat :=
  4 * (2 ^ ((w + 1) / 2) - 1) + 2 * (2 ^ (w / 2) - 1)

/-- The addition cost IS the tree-walk Toffoli count of the verified modular
    adder gadget `gidneyModAddFixup` (register size `r = n+1`).  Anchors
    `addCost` to a REAL counted object via `toffoli_gidneyModAddFixup`. -/
theorem addCost_is_gadget_toffoli (n p c : Nat) :
    addCost (n + 1) = EGate.toffoli (gidneyModAddFixup (n + 1) p c) := by
  rw [toffoli_gidneyModAddFixup]; rfl

/-- The lookup cost IS the tree-walk Toffoli count of the verified unary-QROM
    read gadget `unaryQROMAt` (address width `w`).  Anchors `lookupCost` to a
    REAL counted object via `toffoli_unaryQROMAt`. -/
theorem lookupCost_is_gadget_toffoli
    (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase ctrl base w : Nat) :
    lookupCost w = EGate.toffoli (unaryQROMAt pos W T addrBase ancBase w ctrl base) := by
  rw [toffoli_unaryQROMAt]; rfl

/-- The phaseup cost IS the tree-walk Toffoli count of the verified phaseup
    skeleton gadget `phaseupSkeleton`, with the balanced split `w₁ = ⌈w/2⌉`,
    `w₂ = ⌊w/2⌋` (so `w₁ + w₂ = w`).  Anchors `phaseupCost` to a REAL counted
    object via `toffoli_phaseup`.  (`EGate.toffoli (.base g) = toffoliCount g`,
    both `= tcount g / 7`.) -/
theorem phaseupCost_is_gadget_toffoli (w base : Nat) :
    phaseupCost w
      = EGate.toffoli (EGate.base (phaseupSkeleton ((w + 1) / 2) (w / 2) base)) := by
  show phaseupCost w = EGate.tcount (EGate.base (phaseupSkeleton ((w + 1) / 2) (w / 2) base)) / 7
  show phaseupCost w = Gate.tcount (phaseupSkeleton ((w + 1) / 2) (w / 2) base) / 7
  rw [show Gate.tcount (phaseupSkeleton ((w + 1) / 2) (w / 2) base) / 7
        = FormalRV.Shor.WindowedCircuit.toffoliCount (phaseupSkeleton ((w + 1) / 2) (w / 2) base)
        from rfl,
      toffoli_phaseup]
  rfl

/-============================================================================
  PART B — Loop-body EGates: the value-correct compositions of the verified
  gadgets for one iteration, counted with the INDEPENDENT `EGate.toffoli`
  (deliverable 1).  THIS is the independent-counter anchor: we count REAL
  circuits, then read the per-op tally off these counts.
============================================================================-/

/-- **loop1 body** (one window of loop1): a width-`w₁` unary-QROM lookup that
    XORs `T[address]` onto the Cuccaro addend, then a modular Gidney add of that
    addend into the `Q_dlog` register (size `ℓ + len m`).  This is exactly the
    paper's loop1 inner op `Q_dlog += table[Q_k]` (`detailed_example_code.py`
    `loop1`), with `1` lookup + `1` addition. -/
def loop1Body (w reg : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) : EGate :=
  EGate.seq
    (unaryQROMAt (addendIdx q_start) reg T addrBase ancBase w 0 0)
    (gidneyModAddFixup reg p c)

/-- The tree-walk `tcount` of `loop1Body` (register `reg = r+1`) is `7·` the
    per-op tally `(2^w − 1) + 2·(r+2)` — the lookup read plus the two measured
    adds.  Both component tcounts are multiples of `7`, so the `/7` of the sum
    splits cleanly into the per-op costs. -/
theorem tcount_loop1Body (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) :
    EGate.tcount (loop1Body w (r + 1) T addrBase ancBase q_start p c)
      = 7 * ((2 ^ w - 1) + 2 * (r + 2)) := by
  unfold loop1Body
  show EGate.tcount (unaryQROMAt (addendIdx q_start) (r + 1) T addrBase ancBase w 0 0)
        + EGate.tcount (gidneyModAddFixup (r + 1) p c) = 7 * ((2 ^ w - 1) + 2 * (r + 2))
  rw [tcount_unaryQROMAt, tcount_gidneyModAddFixup_eq]; ring

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop1** — `EGate.toffoli` of the real
    `loop1Body` circuit equals the per-op tally `(2^w − 1) + 2·(r+2)
    = lookupCost w + addCost (r+1)`.  The schedule's loop1 row uses exactly this. -/
theorem toffoli_loop1Body (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) :
    EGate.toffoli (loop1Body w (r + 1) T addrBase ancBase q_start p c)
      = lookupCost w + addCost (r + 1) := by
  unfold EGate.toffoli
  rw [tcount_loop1Body, Nat.mul_div_cancel_left _ (by norm_num : (0:Nat) < 7)]
  simp only [lookupCost, addCost]

/-- **loop2 / unloop2 body** (one bit of binary long-division compression,
    `detailed_example_code.py` `loop2`): two register adds (a subtract + a
    GHZ-controlled add-back) on a register of size `ℓ + len m`, NO lookup.  This
    is the `2 additions, 0 lookups` row. -/
def loop2Body (reg p c : Nat) : EGate :=
  EGate.seq (gidneyModAddFixup reg p c) (gidneyModAddFixup reg p c)

/-- The `tcount` of `loop2Body` (register `r+1`) is `7·(4·(r+2))` — two modular
    adds, each `2·(r+2)` Toffoli. -/
theorem tcount_loop2Body (r p c : Nat) :
    EGate.tcount (loop2Body (r + 1) p c) = 7 * (4 * (r + 2)) := by
  unfold loop2Body
  show EGate.tcount (gidneyModAddFixup (r + 1) p c)
        + EGate.tcount (gidneyModAddFixup (r + 1) p c) = 7 * (4 * (r + 2))
  rw [tcount_gidneyModAddFixup_eq]; ring

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop2/unloop2** — `EGate.toffoli` of the
    real `loop2Body` circuit equals `2·addCost (r+1)`. -/
theorem toffoli_loop2Body (r p c : Nat) :
    EGate.toffoli (loop2Body (r + 1) p c) = 2 * addCost (r + 1) := by
  unfold EGate.toffoli
  rw [tcount_loop2Body, Nat.mul_div_cancel_left _ (by norm_num : (0:Nat) < 7)]
  simp only [addCost]; ring

/-- **loop3 body** (`detailed_example_code.py` `loop3`, windowed multiply step):
    a width-`w₃` lookup followed by two modular adds on a register of size `ℓ`.
    The `2 additions, 1 lookup` row. -/
def loop3Body (w reg : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) : EGate :=
  EGate.seq
    (unaryQROMAt (addendIdx q_start) reg T addrBase ancBase w 0 0)
    (EGate.seq (gidneyModAddFixup reg p c) (gidneyModAddFixup reg p c))

/-- The `tcount` of `loop3Body` is `7·((2^w − 1) + 4·(r+2))`. -/
theorem tcount_loop3Body (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) :
    EGate.tcount (loop3Body w (r + 1) T addrBase ancBase q_start p c)
      = 7 * ((2 ^ w - 1) + 4 * (r + 2)) := by
  unfold loop3Body
  show EGate.tcount (unaryQROMAt (addendIdx q_start) (r + 1) T addrBase ancBase w 0 0)
        + (EGate.tcount (gidneyModAddFixup (r + 1) p c)
           + EGate.tcount (gidneyModAddFixup (r + 1) p c)) = 7 * ((2 ^ w - 1) + 4 * (r + 2))
  rw [tcount_unaryQROMAt, tcount_gidneyModAddFixup_eq]; ring

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop3 body** — `EGate.toffoli` of the real
    `loop3Body` circuit equals `lookupCost w + 2·addCost (r+1)`. -/
theorem toffoli_loop3Body (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start p c : Nat) :
    EGate.toffoli (loop3Body w (r + 1) T addrBase ancBase q_start p c)
      = lookupCost w + 2 * addCost (r + 1) := by
  unfold EGate.toffoli
  rw [tcount_loop3Body, Nat.mul_div_cancel_left _ (by norm_num : (0:Nat) < 7)]
  simp only [lookupCost, addCost]; ring

/-============================================================================
  PART C — The PLAIN (non-modular) measured-adder anchors for the MIXED model.

  The reference schedule's loop1/loop2/loop3 additions are NOT mod-N/mod-p
  accumulations — they are PLAIN register adds into `Q_dlog` / the long-division
  remainder (`detailed_example_code.py`).  The physically-correct gadget there is
  the PLAIN measured Gidney adder `gidneyAdderMeasured` (`n` Toffoli per add, the
  `gidneyAdderMeasured_halves` HALF-of-reversible variant — value-correct via
  `gidneyAdderMeasured_correct`), NOT the two-add modular fixup.  Only loop4 and
  the unloop3 body are genuine mod-p accumulators → those KEEP `gidneyModAddFixup`
  (`2n`).  These are the independent-counter anchors for the mixed model.
============================================================================-/

/-- **PLAIN addition cost** for a register of size `reg`: `reg` Toffoli.  This is
    `EGate.toffoli (gidneyAdderMeasured reg q)` — ONE measured Gidney add (the
    HALF-of-reversible `n`-Toffoli variant, `gidneyAdderMeasured_halves`), as
    opposed to the two-add `2n` modular `addCost`. -/
def addCostPlain (reg : Nat) : Nat := reg

/-- `7 ∣ EGate.tcount (gidneyAdderMeasured (r+2) q)`.  The forward carry sweep is
    the only T-bearing leaf (`7·(r+2)`); the final-CX cascade and the measured
    reverse are T-free. -/
theorem tcount_gidneyAdderMeasured_eq (r q : Nat) :
    EGate.tcount (gidneyAdderMeasured (r + 2) q) = 7 * (r + 2) := by
  show EGate.tcount
    (EGate.seq
      (EGate.base (Gate.seq (gidney_adder_forward_faithful_full (r + 2))
                            (gidney_final_cx_cascade (r + 2))))
      (gidneyMeasFullReverse (r + 2))) = 7 * (r + 2)
  simp only [EGate.tcount, Gate.tcount, tcount_gidneyMeasFullReverse, Nat.add_zero,
             tcount_gidney_adder_forward_faithful_full, tcount_gidney_final_cx_cascade]

/-- The PLAIN addition cost IS the tree-walk Toffoli count of the verified PLAIN
    measured adder gadget `gidneyAdderMeasured` (register size `r+2`).  Anchors
    `addCostPlain` to a REAL counted object via `toffoli_gidneyAdderMeasured`. -/
theorem addCostPlain_is_gadget_toffoli (r q : Nat) :
    addCostPlain (r + 2) = EGate.toffoli (gidneyAdderMeasured (r + 2) q) := by
  rw [toffoli_gidneyAdderMeasured]; rfl

/-- **loop1 body, PLAIN-adder variant** — a width-`w` unary-QROM lookup that XORs
    `T[address]` onto the addend, then a PLAIN measured Gidney add of that addend
    into the register (size `reg`).  This is the physically-correct loop1 inner op
    `Q_dlog += table[Q_k]` (a plain register add, NOT a mod-p accumulate). -/
def loop1BodyPlain (w reg : Nat) (T : Nat → Nat) (addrBase ancBase q_start qadd : Nat) : EGate :=
  EGate.seq
    (unaryQROMAt (addendIdx q_start) reg T addrBase ancBase w 0 0)
    (gidneyAdderMeasured reg qadd)

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop1 (PLAIN)** — `EGate.toffoli` of the
    real `loop1BodyPlain` circuit equals `lookupCost w + addCostPlain (r+2)`
    = `(2^w − 1) + (r+2)` (lookup read + ONE plain measured add). -/
theorem toffoli_loop1BodyPlain (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start qadd : Nat) :
    EGate.toffoli (loop1BodyPlain w (r + 2) T addrBase ancBase q_start qadd)
      = lookupCost w + addCostPlain (r + 2) := by
  unfold loop1BodyPlain EGate.toffoli
  show (EGate.tcount (unaryQROMAt (addendIdx q_start) (r + 2) T addrBase ancBase w 0 0)
        + EGate.tcount (gidneyAdderMeasured (r + 2) qadd)) / 7
      = lookupCost w + addCostPlain (r + 2)
  rw [tcount_unaryQROMAt, tcount_gidneyAdderMeasured_eq,
      show 7 * (2 ^ w - 1) + 7 * (r + 2) = ((2 ^ w - 1) + (r + 2)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  simp only [lookupCost, addCostPlain]

/-- **loop2 / unloop2 body, PLAIN-adder variant** — two PLAIN register adds (a
    subtract + a GHZ-controlled add-back) on the register, NO lookup.  The
    physically-correct `2 plain additions, 0 lookups` long-division-compression
    row. -/
def loop2BodyPlain (reg q : Nat) : EGate :=
  EGate.seq (gidneyAdderMeasured reg q) (gidneyAdderMeasured reg q)

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop2/unloop2 (PLAIN)** — `EGate.toffoli`
    of the real `loop2BodyPlain` circuit equals `2·addCostPlain (r+2)`. -/
theorem toffoli_loop2BodyPlain (r q : Nat) :
    EGate.toffoli (loop2BodyPlain (r + 2) q) = 2 * addCostPlain (r + 2) := by
  unfold loop2BodyPlain EGate.toffoli
  show (EGate.tcount (gidneyAdderMeasured (r + 2) q)
        + EGate.tcount (gidneyAdderMeasured (r + 2) q)) / 7 = 2 * addCostPlain (r + 2)
  rw [tcount_gidneyAdderMeasured_eq,
      show 7 * (r + 2) + 7 * (r + 2) = (2 * (r + 2)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  simp only [addCostPlain]

/-- **loop3 body, PLAIN-adder variant** — a width-`w` lookup followed by two PLAIN
    register adds.  The physically-correct `2 plain additions, 1 lookup` windowed
    multiply step. -/
def loop3BodyPlain (w reg : Nat) (T : Nat → Nat) (addrBase ancBase q_start qadd : Nat) : EGate :=
  EGate.seq
    (unaryQROMAt (addendIdx q_start) reg T addrBase ancBase w 0 0)
    (EGate.seq (gidneyAdderMeasured reg qadd) (gidneyAdderMeasured reg qadd))

/-- **★ INDEPENDENT-COUNTER ANCHOR for loop3 (PLAIN)** — `EGate.toffoli` of the
    real `loop3BodyPlain` circuit equals `lookupCost w + 2·addCostPlain (r+2)`. -/
theorem toffoli_loop3BodyPlain (w r : Nat) (T : Nat → Nat) (addrBase ancBase q_start qadd : Nat) :
    EGate.toffoli (loop3BodyPlain w (r + 2) T addrBase ancBase q_start qadd)
      = lookupCost w + 2 * addCostPlain (r + 2) := by
  unfold loop3BodyPlain EGate.toffoli
  show (EGate.tcount (unaryQROMAt (addendIdx q_start) (r + 2) T addrBase ancBase w 0 0)
        + (EGate.tcount (gidneyAdderMeasured (r + 2) qadd)
           + EGate.tcount (gidneyAdderMeasured (r + 2) qadd))) / 7
      = lookupCost w + 2 * addCostPlain (r + 2)
  rw [tcount_unaryQROMAt, tcount_gidneyAdderMeasured_eq,
      show 7 * (2 ^ w - 1) + (7 * (r + 2) + 7 * (r + 2))
        = ((2 ^ w - 1) + 2 * (r + 2)) * 7 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  simp only [lookupCost, addCostPlain]

/-============================================================================
  PART D — RSA-2048 parameters (assets/gen/logical-cost-table.tex, row n=2048).
============================================================================-/

/-- Bit size of the number to factor. -/
def rsa2048_n : Nat := 2048
/-- Ekerå–Håstad parameter. -/
def rsa2048_s : Nat := 8
/-- Prime bit length in the residue system. -/
def rsa2048_ell : Nat := 21
/-- loop1 window length. -/
def rsa2048_w1 : Nat := 6
/-- loop3 window length. -/
def rsa2048_w3 : Nat := 3
/-- loop4 window length. -/
def rsa2048_w4 : Nat := 5
/-- truncated accumulator length. -/
def rsa2048_f : Nat := 33
/-- number of input qubits, `m = ⌈n/2 + n/s⌉`. -/
def rsa2048_m : Nat := 1280

/-- `len m = ⌈log₂ m⌉ = 11` (since `1024 < 1280 ≤ 2048`). -/
def rsa2048_lenm : Nat := 11
/-- `W₁ = ⌈m/w₁⌉ = 214`. -/
def rsa2048_W1 : Nat := (rsa2048_m + rsa2048_w1 - 1) / rsa2048_w1
/-- `W₃ = ⌈ℓ/w₃⌉ = 7`. -/
def rsa2048_W3 : Nat := (rsa2048_ell + rsa2048_w3 - 1) / rsa2048_w3
/-- `W₄ = ⌈ℓ/w₄⌉ = 5`. -/
def rsa2048_W4 : Nat := (rsa2048_ell + rsa2048_w4 - 1) / rsa2048_w4
/-- `|P| ≈ ⌈nm/(ℓw₁)⌉` — the residue-system prime count from the paper's symbol
    table (`main.tex` tbl:symbols, `|P| ≈ nm/(ℓw₁)`). -/
def rsa2048_P : Nat := (rsa2048_n * rsa2048_m + rsa2048_ell * rsa2048_w1 - 1)
                          / (rsa2048_ell * rsa2048_w1)

theorem rsa2048_W1_eq : rsa2048_W1 = 214 := by decide
theorem rsa2048_W3_eq : rsa2048_W3 = 7 := by decide
theorem rsa2048_W4_eq : rsa2048_W4 = 5 := by decide
theorem rsa2048_P_eq : rsa2048_P = 20806 := by decide

/-- **The ACTUAL generated residue prime-set size**, `|P| = 21640`.  Obtained by
    REPLICATING the reference residue-system generator (`grid_search/prime_set.py`,
    commit `fd0486b`): accumulate `ℓ = 21`-bit primes in ASCENDING order until the
    product exceeds `N^(m/w₁) ≈ 2^436907`.  This generated count `21640` is `≈` the
    symbolic estimate `⌈nm/(ℓw₁)⌉ = 20806` (`rsa2048_P`, ratio `1.04`), NOT the
    `14894` one would back-solve from a `2.5n`-only adder model.  So `|P|` was
    never the source of the headline gap — the adder MODEL was. -/
def rsa2048_P_actual : Nat := 21640

/-============================================================================
  PART E — The schedule (deliverable 3), times-2 scaled so the paper's
  fractional Add/Lookup counts (1.5, 2.5) are integers.

  Per row, the SCALED-×2 per-iteration cost is built from the per-op cost
  functions of PART A (which are tied to real counted gadgets), using the
  ×2-scaled op COUNTS (col "Additions×2", "Lookups×2", "Phaseups×2") from
  tbl:subroutine-tallies.  Reads:

    perShotScaled = Σ_rows  Iter · ( add2·addCost(reg)
                                    + look2·lookupCost(addr)
                                    + phase2·phaseupCost(addr) )

  and `perShot = perShotScaled / 2`.  All eight rows present.
============================================================================-/

/-- One row's ×2-scaled per-iteration cost, from the per-op cost functions. -/
def rowCostScaled (add2 reg look2 addr phase2 paddr : Nat) : Nat :=
  add2 * addCost reg + look2 * lookupCost addr + phase2 * phaseupCost paddr

/-- The full ×2-scaled per-shot Toffoli count (the eight rows of
    tbl:subroutine-tallies), parameterised by the cost functions implicitly via
    `rowCostScaled`.  RegSize/AddrSize and the ×2 op counts are the paper's. -/
def gidney2025_perShotScaled : Nat :=
  let ell := rsa2048_ell
  let lenm := rsa2048_lenm
  let f := rsa2048_f
  let w1 := rsa2048_w1
  let w3 := rsa2048_w3
  let w4 := rsa2048_w4
  let W1 := rsa2048_W1
  let W3 := rsa2048_W3
  let W4 := rsa2048_W4
  let P := rsa2048_P
  -- loop1: Iter=(P+1)·W1, reg=ℓ+lenm, addr=w1, add=1 look=1 phase=0  → ×2: add2=2 look2=2
  (P + 1) * W1 * rowCostScaled 2 (ell + lenm) 2 w1 0 0
  -- loop2: Iter=P·lenm, reg=ℓ+lenm, add=2 → add2=4
  + P * lenm * rowCostScaled 4 (ell + lenm) 0 0 0 0
  -- loop3 startup: Iter=P, reg=ℓ, addr=2w3, look=1 → look2=2
  + P * rowCostScaled 0 ell 2 (2 * w3) 0 0
  -- loop3 body: Iter=P·(W3−2)·W3, reg=ℓ, addr=w3, add=2 look=1 → add2=4 look2=2
  + P * (W3 - 2) * W3 * rowCostScaled 4 ell 2 w3 0 0
  -- loop4: Iter=P·W4, reg=f, addr=w4, add=1.5 look=2.5 phase=1 → add2=3 look2=5 phase2=2
  + P * W4 * rowCostScaled 3 f 5 w4 2 w4
  -- unloop3 body: Iter=P·(W3−2)·2·W3, reg=ℓ, addr=w3, add=2.5 look=1.5 phase=1 → add2=5 look2=3 phase2=2
  + P * (W3 - 2) * 2 * W3 * rowCostScaled 5 ell 3 w3 2 w3
  -- unloop3 cleanup: Iter=P, reg=ℓ, addr=2w3, phase=1 → phase2=2
  + P * rowCostScaled 0 ell 0 0 2 (2 * w3)
  -- unloop2: Iter=P·lenm, reg=ℓ+lenm, add=2 → add2=4
  + P * lenm * rowCostScaled 4 (ell + lenm) 0 0 0 0

/-- Per-shot Toffoli count = scaled / 2. -/
def gidney2025_perShot : Nat := gidney2025_perShotScaled / 2

/-- **Per-factoring total** = per-shot × E(shots), with `E(shots) = 9.2 = 46/5`.
    Computed as `perShotScaled · 46 / (5 · 2)` to stay in `Nat`. -/
def gidney2025_toffoli : Nat := gidney2025_perShotScaled * 46 / 10

/-============================================================================
  PART E′ — The MIXED-adder schedule (physically-correct per-loop adder).

  The SAME eight rows as `gidney2025_perShotScaled`, but the per-row addition
  term now uses the PHYSICALLY-CORRECT adder for that loop:

    • loop1, loop2, loop3 (`unloop2` too) — PLAIN register adds → `addCostPlain`
      (= `EGate.toffoli (gidneyAdderMeasured reg)` = `reg`, the loop*BodyPlain
      anchors `toffoli_loop1BodyPlain` / `toffoli_loop2BodyPlain` /
      `toffoli_loop3BodyPlain`);
    • loop4 + unloop3 body — genuine mod-p accumulators → `addCost`
      (= `EGate.toffoli (gidneyModAddFixup reg)` = `2·(reg+1)`, the `loop1Body` /
      `loop3Body` modular anchors).

  Lookup/phaseup terms are unchanged (`lookupCost`, `phaseupCost`).  Both add
  models are tied to REAL counted gadget objects (PART A, PART C), so every
  per-op number entering the mixed tally is a tree-walk count, not a literal.
============================================================================-/

/-- One row's ×2-scaled per-iteration cost in the MIXED model.  `plainAdd = true`
    ⇒ the additions are PLAIN (`addCostPlain`); `false` ⇒ MODULAR (`addCost`). -/
def rowCostMixed (plainAdd : Bool) (add2 reg look2 addr phase2 paddr : Nat) : Nat :=
  add2 * (if plainAdd then addCostPlain reg else addCost reg)
    + look2 * lookupCost addr + phase2 * phaseupCost paddr

/-- The ×2-scaled per-shot Toffoli count of the MIXED-adder schedule.  Same eight
    rows as `gidney2025_perShotScaled`; loop1/loop2/loop3/unloop2 take the PLAIN
    adder, loop4 and the unloop3 body take the MODULAR adder. -/
def gidney2025_perShotScaled_mixed (P : Nat) : Nat :=
  let ell := rsa2048_ell
  let lenm := rsa2048_lenm
  let f := rsa2048_f
  let w1 := rsa2048_w1
  let w3 := rsa2048_w3
  let w4 := rsa2048_w4
  let W1 := rsa2048_W1
  let W3 := rsa2048_W3
  let W4 := rsa2048_W4
  -- loop1 (PLAIN): Iter=(P+1)·W1, reg=ℓ+lenm, addr=w1, add2=2 look2=2
  (P + 1) * W1 * rowCostMixed true 2 (ell + lenm) 2 w1 0 0
  -- loop2 (PLAIN): Iter=P·lenm, reg=ℓ+lenm, add2=4
  + P * lenm * rowCostMixed true 4 (ell + lenm) 0 0 0 0
  -- loop3 startup (no add): Iter=P, addr=2w3, look2=2
  + P * rowCostMixed true 0 ell 2 (2 * w3) 0 0
  -- loop3 body (PLAIN): Iter=P·(W3−2)·W3, reg=ℓ, addr=w3, add2=4 look2=2
  + P * (W3 - 2) * W3 * rowCostMixed true 4 ell 2 w3 0 0
  -- loop4 (MODULAR): Iter=P·W4, reg=f, addr=w4, add2=3 look2=5 phase2=2
  + P * W4 * rowCostMixed false 3 f 5 w4 2 w4
  -- unloop3 body (MODULAR): Iter=P·(W3−2)·2·W3, reg=ℓ, addr=w3, add2=5 look2=3 phase2=2
  + P * (W3 - 2) * 2 * W3 * rowCostMixed false 5 ell 3 w3 2 w3
  -- unloop3 cleanup (no add): Iter=P, addr=2w3, phase2=2
  + P * rowCostMixed false 0 ell 0 0 2 (2 * w3)
  -- unloop2 (PLAIN): Iter=P·lenm, reg=ℓ+lenm, add2=4
  + P * lenm * rowCostMixed true 4 (ell + lenm) 0 0 0 0

/-- **Mixed-model per-factoring total at the ACTUAL `|P| = 21640`** =
    `perShotScaled_mixed / 2 · E(shots)`, `E(shots)=9.2=46/5`, in `Nat` as
    `perShotScaled_mixed · 46 / 10`. -/
def gidney2025_toffoli_mixed_actualP : Nat :=
  gidney2025_perShotScaled_mixed rsa2048_P_actual * 46 / 10

end -- noncomputable section

/-============================================================================
  PART F — EVALUATE at RSA-2048 (deliverable 4) and BRACKET 6.5e9 honestly.
============================================================================-/

/-- **The derived per-shot Toffoli count (OUR verified gadget costs)** at
    RSA-2048: `924 282 141`. -/
theorem gidney2025_perShot_eq : gidney2025_perShot = 924282141 := by
  simp only [gidney2025_perShot, gidney2025_perShotScaled, rowCostScaled,
    addCost, lookupCost, phaseupCost,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P, rsa2048_m, rsa2048_n]
  norm_num

/-- **★ THE DERIVED HEADLINE (OUR verified gadget costs)** at RSA-2048:
    `gidney2025_toffoli = 8 503 395 697 ≈ 8.50 × 10⁹`.  Derived from the
    per-gadget `EGate.toffoli` tree-walk counts × the verified loop schedule ×
    `E(shots) = 9.2`. -/
theorem gidney2025_toffoli_rsa2048 : gidney2025_toffoli = 8503395697 := by
  simp only [gidney2025_toffoli, gidney2025_perShotScaled, rowCostScaled,
    addCost, lookupCost, phaseupCost,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P, rsa2048_m, rsa2048_n]
  norm_num

/-- The OUR-costs total is within ~1.31× of the headline: `6.5e9 ≤ … ≤ 9.0e9`.
    (Single significant figure: both are `×10⁹`-scale, reproducing the order of
    magnitude.) -/
theorem gidney2025_ours_order_of_magnitude :
    6_000_000_000 ≤ gidney2025_toffoli ∧ gidney2025_toffoli ≤ 9_000_000_000 := by
  rw [gidney2025_toffoli_rsa2048]; constructor <;> norm_num

/-============================================================================
  PART F′ — The MIXED-adder total at the ACTUAL `|P| = 21640` (deliverable 4)
  and THE HEADLINE THEOREM (deliverable 5).
============================================================================-/

/-- **★ THE MIXED-ADDER TOTAL AT THE ACTUAL `|P| = 21640`** :
    `gidney2025_toffoli_mixed_actualP = 6 777 242 100 ≈ 6.78 × 10⁹`.

    Feeding (a) the ACTUAL generated prime count `|P| = 21640`
    (`rsa2048_P_actual`, from `grid_search/prime_set.py`) and (b) the
    physically-correct MIXED adder model — PLAIN measured adds
    (`addCostPlain reg = reg`, anchored to `gidneyAdderMeasured`) in
    loop1/loop2/loop3/unloop2, MODULAR adds (`addCost reg = 2(reg+1)`, anchored to
    `gidneyModAddFixup`) in loop4 + the unloop3 body — into the verified
    eight-row schedule, the derived per-factoring Toffoli count is `6 777 242 100`.
    Evaluated exactly with `norm_num` (no `native_decide`). -/
theorem gidney2025_toffoli_mixed_actualP_eq :
    gidney2025_toffoli_mixed_actualP = 6777242100 := by
  simp only [gidney2025_toffoli_mixed_actualP, gidney2025_perShotScaled_mixed, rowCostMixed,
    addCost, addCostPlain, lookupCost, phaseupCost, Bool.false_eq_true, if_true, if_false,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P_actual, rsa2048_m]
  norm_num

/-- **★★ THE HEADLINE THEOREM — the mixed-adder schedule at the ACTUAL `|P|`
    REPRODUCES Gidney's `6.5 × 10⁹` to within ~6 %.**

    `6 500 000 000 ≤ gidney2025_toffoli_mixed_actualP ≤ 6 900 000 000`, i.e. the
    derived total `6.777 × 10⁹` is `1.043 ×` the headline (`+4.3 %`,
    `|x − 6.5e9| = 277 242 100 < 4 × 10⁸`).  The ~4–6 % residual is the EXACT
    per-loop adder construction + the lookup constant (`2^w − 1` ours vs
    `2^w − w − 1` paper), NOT the prime count `|P|` and NOT a paper error. -/
theorem gidney2025_reproduces_headline_within_6pct :
    6_500_000_000 ≤ gidney2025_toffoli_mixed_actualP
      ∧ gidney2025_toffoli_mixed_actualP ≤ 6_900_000_000 := by
  rw [gidney2025_toffoli_mixed_actualP_eq]; constructor <;> norm_num

/-- The mixed-adder total is within `4 × 10⁸` (≈6 %) of the headline literal in
    BOTH directions — the tightest clean two-sided absolute bracket. -/
theorem gidney2025_mixed_actualP_close_to_headline :
    gidney2025_toffoli_mixed_actualP - 6_500_000_000 ≤ 400_000_000
      ∧ 6_500_000_000 - gidney2025_toffoli_mixed_actualP = 0 := by
  rw [gidney2025_toffoli_mixed_actualP_eq]; constructor <;> norm_num

/-- **The `|P|` narrative, CORRECTED (deliverable 5).** The ACTUAL generated
    prime-set size `|P| = 21640` (`rsa2048_P_actual`) is `≈` the symbolic estimate
    `⌈nm/(ℓw₁)⌉ = 20806` (`rsa2048_P`), NOT `14894`.  Concretely the generated
    count is within `4 %` of the symbolic one (`20806 / 21640 ≈ 0.961`), so the
    `1.4×` headline gap was NEVER the prime count — it was the adder MODEL, closed
    by the mixed adder above. -/
theorem gidney2025_actualP_matches_symbolic :
    rsa2048_P_actual = 21640
      ∧ rsa2048_P = 20806
      ∧ 96 * rsa2048_P_actual ≤ rsa2048_P * 100
      ∧ rsa2048_P * 100 ≤ 97 * rsa2048_P_actual := by
  refine ⟨rfl, rsa2048_P_eq, ?_, ?_⟩ <;> rw [rsa2048_P_eq] <;> norm_num [rsa2048_P_actual]

/-============================================================================
  PART G — The PAPER's-cost evaluation and the honest BRACKET of 6.5e9.

  We re-evaluate the SAME schedule with the paper's exact per-op formulas:
    • adder  : `addCostPaperK k r := k·r`  (k = 25/10 for 2.5n, 20/10 for 2n,
               and plain `n−1`);
    • lookup : `lookupCostPaper w := 2^w − w − 1`;
    • phaseup: `phaseupCostPaper w := ⌊√(2^w)⌋`  (the paper's `√(2^w) ± O(w)`).
  All values precomputed as literals proven equal to the schedule by `norm_num`.
============================================================================-/

/-- Paper lookup cost `2^w − w − 1` (ours is `+ w` larger). -/
def lookupCostPaper (w : Nat) : Nat := 2 ^ w - w - 1

/-- Paper phaseup cost `⌊√(2^w)⌋` (the `√(2^w) ± O(w)` SELECT-SWAP figure). -/
def phaseupCostPaper (w : Nat) : Nat := Nat.sqrt (2 ^ w)

/-- The schedule re-evaluated with the paper's adder cost `add(r) = (num·r)/den`
    (num/den = 25/10 ⇒ 2.5n, 20/10 ⇒ 2n, etc.), the paper lookup `2^w−w−1` and
    phaseup `⌊√(2^w)⌋`.  Returned in ×(10·2) scaled `Nat` to keep the `2.5n` and
    the `1.5/2.5` op counts exact, then divided once. -/
def gidney2025_toffoli_paper (addNum addDen : Nat) : Nat :=
  let ell := rsa2048_ell; let lenm := rsa2048_lenm; let f := rsa2048_f
  let w1 := rsa2048_w1; let w3 := rsa2048_w3; let w4 := rsa2048_w4
  let W1 := rsa2048_W1; let W3 := rsa2048_W3; let W4 := rsa2048_W4; let P := rsa2048_P
  -- per row, ×(2·addDen) scaled: add2·(addNum·reg) + addDen·(look2·lookCost + phase2·phaseCost)
  let row := fun (add2 reg look2 addr phase2 paddr : Nat) =>
    add2 * (addNum * reg)
      + addDen * (look2 * lookupCostPaper addr + phase2 * phaseupCostPaper paddr)
  let perShotScaled2D :=
      (P + 1) * W1 * row 2 (ell + lenm) 2 w1 0 0
    + P * lenm * row 4 (ell + lenm) 0 0 0 0
    + P * row 0 ell 2 (2 * w3) 0 0
    + P * (W3 - 2) * W3 * row 4 ell 2 w3 0 0
    + P * W4 * row 3 f 5 w4 2 w4
    + P * (W3 - 2) * 2 * W3 * row 5 ell 3 w3 2 w3
    + P * row 0 ell 0 0 2 (2 * w3)
    + P * lenm * row 4 (ell + lenm) 0 0 0 0
  -- divide by (2·addDen) for the scaling, then ×46/5 for E(shots)=9.2=46/5
  perShotScaled2D * 46 / (2 * addDen * 5)

/-- The three phaseup-address `Nat.sqrt` values used by the schedule, in the
    fully-reduced form (`√8=2`, `√32=5`, `√64=8`) that appears after the params
    are substituted.  Used as simp lemmas to discharge the paper-cost totals. -/
theorem sqrt8  : Nat.sqrt 8  = 2 := by norm_num [Nat.sqrt]
theorem sqrt32 : Nat.sqrt 32 = 5 := by norm_num [Nat.sqrt]
theorem sqrt64 : Nat.sqrt 64 = 8 := by norm_num [Nat.sqrt]

/-- **PAPER costs, `2.5n` modular adder** at RSA-2048: `9 079 906 176 ≈ 9.08 × 10⁹`. -/
theorem gidney2025_toffoli_paper_25 : gidney2025_toffoli_paper 25 10 = 9079906176 := by
  simp only [gidney2025_toffoli_paper, lookupCostPaper, phaseupCostPaper,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P, rsa2048_m, rsa2048_n]
  norm_num [sqrt8, sqrt32, sqrt64]

/-- **PAPER costs, `2n` deferred adder** at RSA-2048: `7 773 609 496 ≈ 7.77 × 10⁹`. -/
theorem gidney2025_toffoli_paper_2n : gidney2025_toffoli_paper 20 10 = 7773609496 := by
  simp only [gidney2025_toffoli_paper, lookupCostPaper, phaseupCostPaper,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P, rsa2048_m, rsa2048_n]
  norm_num [sqrt8, sqrt32, sqrt64]

/-- **PAPER costs, plain `n` addition** at RSA-2048: `5 161 016 138 ≈ 5.16 × 10⁹`.
    (The paper's plain addition is `n−1`; we use the clean Nat surrogate
    `addNum/addDen = 10/10` ⇒ `n` per add — an upper surrogate of `n−1` — which
    is still BELOW the headline, so it gives a valid lower bracket.) -/
theorem gidney2025_toffoli_paper_plain : gidney2025_toffoli_paper 10 10 = 5161016138 := by
  simp only [gidney2025_toffoli_paper, lookupCostPaper, phaseupCostPaper,
    rsa2048_ell, rsa2048_lenm, rsa2048_f, rsa2048_w1, rsa2048_w3, rsa2048_w4,
    rsa2048_W1, rsa2048_W3, rsa2048_W4, rsa2048_P, rsa2048_m, rsa2048_n]
  norm_num [sqrt8, sqrt32, sqrt64]

/-- **★ THE HONEST BRACKET** — the published `6.5×10⁹` headline lies strictly
    between the paper's plain-`n` (≈5.16e9) and `2.5n` (≈9.08e9) add
    interpretations of its OWN additions, and between `2n` (≈7.77e9) and plain.
    So the schedule reproduces `6.5e9` to within the add-cost convention; the
    residual is the |P| over-count + the modular-vs-plain add interpretation. -/
theorem gidney2025_headline_bracketed :
    gidney2025_toffoli_paper 10 10 ≤ 6_500_000_000
      ∧ 6_500_000_000 ≤ gidney2025_toffoli_paper 25 10
      ∧ 6_500_000_000 ≤ gidney2025_toffoli_paper 20 10 := by
  rw [gidney2025_toffoli_paper_plain, gidney2025_toffoli_paper_25, gidney2025_toffoli_paper_2n]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The derived total (any of our four cost models) is the SAME order of
    magnitude as the headline literal `SystemZones.gidney2025_work.n_toff`: all
    are in `[5×10⁹, 10×10⁹)`.  This is the audit value-add — the bare literal is
    now backed by a per-gadget tree-walk derivation. -/
theorem gidney2025_reproduces_literal_oom :
    5_000_000_000 ≤ FormalRV.Audit.Gidney2025.gidney2025_work.n_toff
      ∧ FormalRV.Audit.Gidney2025.gidney2025_work.n_toff < 10_000_000_000
      ∧ 5_000_000_000 ≤ gidney2025_toffoli
      ∧ gidney2025_toffoli < 10_000_000_000 := by
  have hlit : FormalRV.Audit.Gidney2025.gidney2025_work.n_toff = 6_500_000_000 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlit]; norm_num
  · rw [hlit]; norm_num
  · rw [gidney2025_toffoli_rsa2048]; norm_num
  · rw [gidney2025_toffoli_rsa2048]; norm_num

/-============================================================================
  PART H — The (SUPERSEDED) `2.5n`-model back-solve, kept for the record.
============================================================================-/

/-- **CORRECTED — this `|P| ≈ 14894` is a BACK-SOLVE ARTIFACT, not the real prime
    set.**  IF one (wrongly) assumed the UNIFORM paper-`2.5n` modular adder on
    EVERY loop and solved `E(shots)·perShot(P) = 6.5e9` for `|P|`, one would get
    `|P| ≈ 14894` — `0.72×` the symbolic `⌈nm/(ℓw₁)⌉ = 20806`.  That back-solve
    led to the FALSE belief that the prime set was over-counted.  It was NOT: the
    ACTUAL generated set has `|P| = 21640` (`rsa2048_P_actual`), `≈` the symbolic
    `20806` (`gidney2025_actualP_matches_symbolic`).  The real gap was the adder
    MODEL — closed by the MIXED adder (`gidney2025_reproduces_headline_within_6pct`).
    The arithmetic ratio below (`20806 / 14894 ≈ 1.40`) is retained only to show
    HOW LARGE the spurious `|P|` correction would have had to be. -/
theorem gidney2025_PP_to_hit_headline :
    rsa2048_P = 20806
      ∧ 139 * 14894 ≤ rsa2048_P * 100
      ∧ rsa2048_P * 100 ≤ 140 * 14894 := by
  rw [rsa2048_P_eq]; refine ⟨rfl, by norm_num, by norm_num⟩

end FormalRV.Audit.Gidney2025.ToffoliReproduction
