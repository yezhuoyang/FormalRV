/-
  Audit · cain-xu-2026 (arXiv:2603.28627) · LAYER 2 — ARITHMETIC, FAITHFUL re-audit
  ════════════════════════════════════════════════════════════════════════════
  Cain-Xu's logical arithmetic reuses the Gidney-2018 ripple-carry adder and the
  Babbush QROM lookup.  An earlier audit pass compared the paper's counts against
  our REVERSIBLE gadgets and found a systematic factor-2 (adder 2n vs paper n;
  lookup 2·(2^w−1) vs paper 2^w).  THAT GAP WAS OURS, NOT THE PAPER'S: the paper
  costs the MEASUREMENT-uncomputed gadgets (free reverse pass), and we had only
  built the reversible versions.

  We have now built the faithful MEASURED gadgets (FormalRV/Arithmetic/MeasuredAdder/,
  all kernel-clean, all computing the RIGHT VALUE) and the measured QROM read
  already existed.  This file re-anchors the paper's per-gadget Toffoli equations
  on those verified objects.  RESULT: the adder/lookup Toffoli counts MATCH the
  paper exactly (n, 2n) or up to a +1 root-AND (lookup), gadget-for-gadget — so
  there is NO arithmetic gap from the gadget side.  The only Cain-Xu findings that
  SURVIVE are the paper's own internal arithmetic inconsistencies (recorded at the
  bottom), which are independent of any implementation.

  PAPER EQUATION  →  VERIFIED FAITHFUL OBJECT (measured uncompute, computes a+b):
   • E3 adder        n   Toffoli  →  `toffoli_gidneyAdderMeasured = n`            (value: `gidneyAdderMeasured_correct`, target = a+b)
   • E4 ctrl-adder   2n  Toffoli  →  `toffoli_gidneyAdderMeasuredControlled = 2n` (value: `gidneyAdderMeasuredControlled_correct`, target = ctrl?a+b:b)
   • E3→E4 factor 2            →  `gidneyAdderMeasuredControlled_doubles`         (the Toffoli count exactly doubles; the paper's 25→30 τ_s TIME ratio differs only because τ includes surgery I/O, not the gadget Toffoli count)
   • E9 lookup read  2^q_a Toff →  `toffoli_unaryQROMAt = 2^q_a − 1`              (merged-AND measured QROM; paper rounds the root AND up by 1)
-/
import FormalRV.Arithmetic.MeasuredAdder
import FormalRV.Shor.MeasUncomputeAt

namespace FormalRV.Audit.CainXu2026.Faithful

open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt

/-! ## E3 — the adder.  Paper: `n` Toffoli/add (Gidney-2018, measured reverse).
    Now on a VERIFIED circuit that computes `(a+b) % 2^bits` on the target. -/

/-- **E3 faithful**: the measured Gidney adder has Toffoli count `n` (= the paper's
    `q_A`), and it genuinely computes the sum (`gidneyAdderMeasured_correct`). -/
theorem cainxu_E3_adder_toffoli (n q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) = n + 2 :=
  toffoli_gidneyAdderMeasured n q_start

/-! ## E4 — the controlled adder.  Paper: `2n` Toffoli (= `2·q_A`).
    Now on a VERIFIED circuit computing `ctrl ? (a+b) : b`. -/

/-- **E4 faithful**: the controlled measured adder has Toffoli count `2n`
    (= the paper's `2·q_A`), and it computes the controlled sum
    (`gidneyAdderMeasuredControlled_correct`). -/
theorem cainxu_E4_ctrl_adder_toffoli (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl) = 2 * (n + 2) :=
  toffoli_gidneyAdderMeasuredControlled n q_start ctrl

/-- **E3 → E4, the verified factor-2**: the controlled adder's Toffoli count is
    EXACTLY twice the uncontrolled adder's — the paper's `q_A → 2·q_A` jump, on
    verified circuits.  (The paper's `25 → 30 τ_s` time ratio is smaller than 2×
    only because `τ` bundles the surgery I/O term, not the gadget Toffoli count.) -/
theorem cainxu_E3_to_E4_factor_two (n q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (n + 2) q_start ctrl)
      = 2 * EGate.toffoli (gidneyAdderMeasured (n + 2) q_start) :=
  gidneyAdderMeasuredControlled_doubles n q_start ctrl

/-! ## E9 — the QROM lookup.  Paper: `2^q_a` Toffoli (Babbush merged-AND, measured).
    Our measured QROM read is `2^q_a − 1` — the paper rounds the single root AND up. -/

/-- **E9 faithful — count bundled with a value property.**  The measured unary QROM read
    simultaneously (i) has Toffoli count `2^d − 1` (= the paper's `2^q_a` minus the one merged-AND
    root) AND (ii) leaves its `d` ancilla qubits CLEARED after the read — the no-garbage hallmark of a
    correct measured-uncompute QROM (no leftover ancilla to corrupt later windows).  This makes the E9
    count a property of a circuit with a genuine (if partial) value behaviour, on par with E3/E4
    (which are likewise count theorems whose value lemmas are `#check`'d).  Note (ii) is ancilla
    restoration, NOT the full word-selection — that is `unaryQROMAt_selects_word` (it needs the
    address-disjointness + `pos`-injectivity contract), witnessed below. -/
theorem cainxu_E9_lookup_read_toffoli
    (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase d ctrl base : Nat) :
    EGate.toffoli (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 2 ^ d - 1
    ∧ (∀ (f : Nat → Bool) (i : Nat), i < d →
        EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f (ancBase + i) = false) :=
  ⟨toffoli_unaryQROMAt pos W T addrBase ancBase d ctrl base,
   fun f i hi => unaryQROMAt_anc_cleared pos W T addrBase ancBase d ctrl base f i hi⟩

/-! ## The faithful-gadget WITNESSES — the counts above ride circuits that compute
    the correct arithmetic value (not bare `Nat` defs). -/

-- E3 adder value: target register = (a+b) % 2^bits.
#check @gidneyAdderMeasured_correct
#check @gidneyAdderMeasured_target_val
-- E4 controlled adder value: target = (if ctrl then a+b else b) % 2^bits.
#check @gidneyAdderMeasuredControlled_correct
#check @gidneyAdderMeasuredControlled_target_val
-- E9 lookup value: selects word `T (l)` under the address-disjointness contract, ancilla cleared.
#check @unaryQROMAt_selects_word
#check @unaryQROMAt_anc_cleared

/-
  ════════════════════════════════════════════════════════════════════════════
  FAITHFUL AUDIT VERDICT (Cain-Xu logical arithmetic)
  ════════════════════════════════════════════════════════════════════════════
  GADGET SIDE — NO GAP.  With the faithful measured gadgets, every per-gadget
  Toffoli equation the paper uses is reproduced on a verified, value-correct
  circuit: adder = n, controlled adder = 2n (exactly 2×), lookup read = 2^q_a − 1.
  The previously-reported factor-2 was an artifact of our reversible gadgets and
  is now CLOSED.  The only residual is the lookup's +1 (the paper rounds the
  single merged-AND root up), which is a conservative over-count in the paper's
  favour, not an error.

  SURVIVING PAPER FINDINGS (internal inconsistencies, implementation-independent;
  see FormalRV.PaperClaims for the decide-checked refutations):
   • E10:  0.5·25 + 0.5·71 = 48 τ_s, but the paper states ≈43 τ_s (11.6% low; 43
           is unreachable from the paper's own 25 and 71 inputs).
   • E7/E9: the lookup is split into ⌈q_w/(k_p−3)⌉ sub-lookups in the prose but
           ⌈q_w/(k_p−1)⌉ in Eq E9 — 5 vs 4 for RSA, a self-contradiction.
  These are the genuine, announceable Cain-Xu arithmetic gaps.
-/

end FormalRV.Audit.CainXu2026.Faithful
