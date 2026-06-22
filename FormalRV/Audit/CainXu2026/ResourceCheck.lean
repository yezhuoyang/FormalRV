/-
  Audit · cain-xu-2026 (arXiv:2603.28627) · ABOVE-PPM ARITHMETIC RESOURCE CHECK
  ════════════════════════════════════════════════════════════════════════════
  Checking the paper's STATED above-PPM arithmetic resource counts against an INDEPENDENT verified
  Toffoli count (the tree-walk counter `EGate.toffoli` run on the actual measured gadgets cain-xu
  uses — Gidney measured ripple adder + Babbush unary lookup).  cain-xu states only TWO bare
  arithmetic Toffoli counts (both quoted from refs, not derived): adder = q_A (App.5.3 line 635),
  unary lookup = 2^{q_a} (App.5.4 line 676).  Everything else it states is a PPM-compilation
  TIME cost (τ_s cycles), or the RSA 50/50 / ECC 40/50/10 Toffoli SPLIT (App.5.5, STATED assumptions).

  RESULT (each row a verified-count check, not a quoted number):
   • adder Toffoli = q_A                         ✅ MATCHES verified `toffoli_gidneyAdderMeasured`.
   • controlled-adder Toffoli = 2·q_A            ✅ MATCHES verified `toffoli_gidneyAdderMeasuredControlled`.
   • unary lookup Toffoli = 2^{q_a}              ⚠ verified count is 2^{q_a} − 1; the paper OVERCOUNTS
                                                  by exactly 1 (the single merged-AND root) — conservative,
                                                  in the paper's favour, NOT an error.
   • RSA 50/50 lookup/adder split                CHECKED below from the verified gadget counts: it is
                                                  accurate to ~1–2% at the stated params (q_a=6,q_A=33)
                                                  IFF each window does a MODULAR add (~2 raw adds); a
                                                  single plain add would give ~66/34.
-/
import FormalRV.Arithmetic.MeasuredAdder
import FormalRV.Shor.MeasUncomputeAt

namespace FormalRV.Audit.CainXu2026.ResourceCheck

open FormalRV.Arithmetic.MeasuredAdder
open FormalRV.Shor.MeasUncompute
open FormalRV.Shor.MeasUncomputeAt
open FormalRV.BQAlgo (decodeReg)

/-! ## The two arithmetic primitives, with their INDEPENDENTLY-COUNTED verified Toffoli costs. -/

/-- **Verified Babbush unary lookup Toffoli** over `q_a` address bits = `2^{q_a} − 1`
    (tree-walk counter on the real measured QROM). -/
theorem verified_lookup_toffoli (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase q_a ctrl base : Nat) :
    EGate.toffoli (unaryQROMAt pos W T addrBase ancBase q_a ctrl base) = 2 ^ q_a - 1 :=
  toffoli_unaryQROMAt pos W T addrBase ancBase q_a ctrl base

/-- **Verified Gidney measured adder Toffoli** over `q_A` bits = `q_A`
    (the `(q_A+2)`-bit measured adder; tree-walk counter on the real gadget). -/
theorem verified_adder_toffoli (q_A q_start : Nat) :
    EGate.toffoli (gidneyAdderMeasured (q_A + 2) q_start) = q_A + 2 :=
  toffoli_gidneyAdderMeasured q_A q_start

/-- **Verified controlled Gidney measured adder Toffoli** over `q_A` bits = `2·q_A`. -/
theorem verified_ctrl_adder_toffoli (q_A q_start ctrl : Nat) :
    EGate.toffoli (gidneyAdderMeasuredControlled (q_A + 2) q_start ctrl) = 2 * (q_A + 2) :=
  toffoli_gidneyAdderMeasuredControlled q_A q_start ctrl

/-! ## Paper check (lookup): the paper's `2^{q_a}` exceeds the verified count by EXACTLY 1. -/

/-- The paper states the unary lookup costs `2^{q_a}` Toffoli; the verified count is `2^{q_a} − 1`,
    so the paper's figure is the verified count PLUS ONE (the merged-AND root the paper rounds up).
    Conservative (over-count in the paper's favour), NOT an arithmetic error. -/
theorem lookup_paper_overcounts_by_one (pos : Nat → Nat) (W : Nat) (T : Nat → Nat)
    (addrBase ancBase q_a ctrl base : Nat) :
    EGate.toffoli (unaryQROMAt pos W T addrBase ancBase q_a ctrl base) + 1 = 2 ^ q_a := by
  rw [toffoli_unaryQROMAt]
  have : 1 ≤ 2 ^ q_a := Nat.one_le_two_pow
  omega

/-! ## THE 50/50 SPLIT CHECK — verified from the gadget counts, NOT taken on faith.

    cain-xu (App.5.5, STATED assumption sourced to Gidney2025) claims the RSA-2048 modexp Toffoli
    count is ≈ 50% lookups + 50% adders.  In a windowed modular multiplier, each window performs ONE
    Babbush lookup plus `addsPerWindow` Gidney additions.  Both per-gadget costs below ARE the verified
    counts above (`lookupTotPerWindow q_a = verified_lookup_toffoli`,
    `adderTotPerWindow k q_A = k · verified_adder_toffoli`). -/

/-- Lookup Toffoli contributed by one window (= the verified Babbush lookup count `2^{q_a} − 1`). -/
def lookupTotPerWindow (q_a : Nat) : Nat := 2 ^ q_a - 1
/-- Adder Toffoli contributed by one window: `addsPerWindow` Gidney `q_A`-bit adds (each = verified `q_A`). -/
def adderTotPerWindow (addsPerWindow q_A : Nat) : Nat := addsPerWindow * q_A

/-- **One PLAIN add per window ⇒ the split is LOOKUP-HEAVY (~66/34), NOT 50/50.**  At the paper's
    stated RSA params (q_a = 6 address bits ⇒ lookup 63; q_A = 33 word bits ⇒ add 33), a single
    non-modular addition per window gives lookup fraction `100·63/(63+33) = 65%`. -/
theorem split_plain_add_is_lookup_heavy :
    lookupTotPerWindow 6 = 63
    ∧ adderTotPerWindow 1 33 = 33
    ∧ 100 * lookupTotPerWindow 6 / (lookupTotPerWindow 6 + adderTotPerWindow 1 33) = 65 := by
  decide

/-- **One MODULAR add (≈ 2 raw adds) per window ⇒ the split IS ≈ 50/50.**  A modular addition =
    addition + conditional subtraction ≈ 2 Gidney adds (66 Toffoli), so lookup fraction
    `100·63/(63+66) = 48%` — i.e. the paper's 50/50 holds to within ~2 points. -/
theorem split_modular_add_is_balanced :
    lookupTotPerWindow 6 = 63
    ∧ adderTotPerWindow 2 33 = 66
    ∧ 100 * lookupTotPerWindow 6 / (lookupTotPerWindow 6 + adderTotPerWindow 2 33) = 48 := by
  decide

/-- **VERDICT (50/50 split, verified).**  The lookup leg (63) and the MODULAR-add leg (66) are within
    `3` of each other — so the split is 50/50 to within `3/129 ≈ 2.3%`; whereas the single-plain-add
    leg (33) is `30` below the lookup leg (≈ 66/34).  Hence cain-xu's STATED 50/50 RSA Toffoli split
    is ACCURATE at the stated parameters PRECISELY because the windowed multiplier accumulates with a
    MODULAR addition (~2 raw adds per window); it is a justified approximation, checked here against
    the independent verified gadget counts (`verified_lookup_toffoli`, `verified_adder_toffoli`), not
    asserted. -/
theorem fifty_fifty_split_holds_for_modular_add :
    -- balanced under a modular (2-raw-add) window, to within 3 Toffoli:
    (lookupTotPerWindow 6 ≤ adderTotPerWindow 2 33 ∧ adderTotPerWindow 2 33 ≤ lookupTotPerWindow 6 + 3)
    -- but a single plain add is far from balanced (lookup exceeds adder by 30):
    ∧ adderTotPerWindow 1 33 + 30 = lookupTotPerWindow 6 := by
  decide

/-! ## Reported-value sweep: amortized τ_Toff (App.5.5 E10–E13), code rates, and qubit totals.

    Each reported number checked against its OWN formula at the paper's inputs (integer-scaled to clear
    the `0.x` fractions; `decide`).  Verdict: the cost model is internally consistent EXCEPT E10. -/

/-- **E11 (RSA balanced τ_Toff) — MATCH (exact).**  `0.5·13 + 0.5·7 = 10`, the reported value. -/
theorem cainxu_E11_tau_toff_consistent : (13 + 7) / 2 = 10 := by decide

/-- **E12 (ECC space-eff τ_Toff) — ROUNDING-OK.**  `0.4·25 + 0.5·15 + 0.1·550 = 72.5` (×10 = 725),
    reported `72` (clean rounding). -/
theorem cainxu_E12_tau_toff_within_rounding : 4 * 25 + 5 * 15 + 1 * 550 = 725 := by decide

/-- **E13 (ECC balanced τ_Toff) — ROUNDING-OK.**  `0.4·25 + 0.5·15 + 0.1·11 = 18.6` (×10 = 186),
    reported `19` (rounds to nearest). -/
theorem cainxu_E13_tau_toff_within_rounding : 4 * 25 + 5 * 15 + 1 * 11 = 186 := by decide

/-- **E10 (RSA space-eff τ_Toff) — PAPER-INTERNAL-INCONSISTENCY (the one load-bearing arithmetic error).**
    The paper's own split `0.5·25 + 0.5·71 = 48`, but it reports `43` (off by 5, ~12%; the inputs 25 and
    71 are each individually correct).  So of the four amortized-τ_Toff cells (E10–E13), E11 is exact,
    E12/E13 round cleanly, and ONLY E10 is wrong — an isolated slip, not a redefinition. -/
theorem cainxu_E10_tau_toff_inconsistent : (25 + 71) / 2 = 48 ∧ (25 + 71) / 2 ≠ 43 := by decide

/-- **Code-rate cells (tab:all_codes) — lp_20 rate ROUNDING-INCONSISTENCY.**  `1224/4350 = 0.2814` and
    `1480/5278 = 0.2804` (×10⁴ floors below) — BOTH ≈ 0.28; yet the table reports lp_20 as `0.29` while
    lp_24 (the same ≈0.28) as `0.28`.  So the lp_20 `0.29` cell is `formula(inputs) ≠ reported` under any
    consistent rounding rule. -/
theorem cainxu_rate_lp20_rounds_to_28 :
    1224 * 10000 / 4350 = 2813 ∧ 1480 * 10000 / 5278 = 2804 := by decide

/-- **Qubit zone breakdowns (tab:space_breakdown) — MATCH (exact).**  Memory `N = n + ⌊(n−k)/2⌋`;
    resource `= 5·factory(367) + 10·cultivator(73)`; operation `N_𝒜 = qubits + X-checks` summed over the
    three ancilla systems.  All exact — the qubit arithmetic carries NO error. -/
theorem cainxu_zone_breakdowns_match :
    4350 + (4350 - 1224) / 2 = 5913              -- memory (lp_20 memory code)
    ∧ 7177 = 5278 + (5278 - 1480) / 2            -- memory (lp_24)
    ∧ 5 * 367 + 10 * 73 = 2565                    -- resource (magic) zone
    ∧ 342 + 200 + 189 + 104 + 39 + 20 = 894 := by decide  -- operation zone N_𝒜 (SE, lp_20)

/-- **Total physical-qubit counts (the headline numbers) — MATCH (exact).**  All four architectures'
    totals reproduce from `memory + processor + resource + operation`; the "as few as 10,000" headline
    is `9739` rounded.  The qubit budget is arithmetically clean — E10 (a τ_Toff cell) is the only error. -/
theorem cainxu_qubit_totals_match :
    5913 + 367 + 2565 + 894 = 9739        -- space-efficient, lp_20 memory
    ∧ 7177 + 367 + 2565 + 924 = 11033     -- space-efficient, lp_24 memory
    ∧ 5913 + 1609 + 2565 + 1874 = 11961   -- balanced, lp_20
    ∧ 7177 + 1609 + 2565 + 1904 = 13255 := by decide  -- balanced, lp_24

/-! ## The lookup equation GROUNDED in the faithful value-correct circuit (answering "is the paper
    over-optimistic about how lookups compile?"). -/

/-- **★ THE UNARY-LOOKUP EQUATION IS ACHIEVABLE BY A FAITHFUL CIRCUIT — QianXu is NOT over-optimistic. ★**
    The SAME syntactic circuit `unaryQROMAt` SIMULTANEOUSLY (under its address-disjointness contract):
    (value) SELECTS exactly the addressed table word `T[addr]` into each word position `pos j` (it is a
    genuinely-correct lookup, not a stripped-down object — `unaryQROMAt_selects_word`); AND
    (count) has Toffoli count `2^d − 1` on that very circuit (`toffoli_unaryQROMAt`); AND
    (comparison) `count + 1 = 2^d` = the paper's claimed lookup Toffoli.
    So the paper's lookup equation `2^q_a` is REALISED by a faithful value-correct circuit costing
    `2^q_a − 1` — the paper is CONSERVATIVE (over-counts by exactly the one merged-AND root), NOT
    over-optimistic.  (This is the rigorous version of the check: the count rides a circuit PROVEN to
    compute the right lookup, so it cannot be hiding compilation cost.) -/
theorem cainxu_lookup_faithful_not_overoptimistic
    (pos : Nat → Nat) (W : Nat) (T : Nat → Nat) (addrBase ancBase d ctrl base : Nat)
    (hpos_inj : ∀ j k, j < W → k < W → pos j = pos k → j = k) (f : Nat → Bool)
    (h1 : ∀ i j, i < d → j < W → ancBase + i ≠ pos j)
    (h2 : ∀ i i', i < d → i' < d → ancBase + i ≠ addrBase + i')
    (h3 : ∀ i j, i < d → j < W → addrBase + i ≠ pos j)
    (h4 : ∀ j, j < W → ctrl ≠ pos j)
    (h5 : ∀ i, i < d → ctrl ≠ ancBase + i)
    (h6 : ∀ i, i < d → f (ancBase + i) = false) :
    (∀ j, j < W →
        EGate.applyNat (unaryQROMAt pos W T addrBase ancBase d ctrl base) f (pos j)
          = xor (f (pos j))
              (f ctrl && (T (base + decodeReg (fun i => addrBase + i) d f)).testBit j))
    ∧ EGate.toffoli (unaryQROMAt pos W T addrBase ancBase d ctrl base) = 2 ^ d - 1
    ∧ EGate.toffoli (unaryQROMAt pos W T addrBase ancBase d ctrl base) + 1 = 2 ^ d := by
  refine ⟨unaryQROMAt_selects_word pos W T addrBase ancBase hpos_inj d ctrl base f h1 h2 h3 h4 h5 h6,
          toffoli_unaryQROMAt pos W T addrBase ancBase d ctrl base, ?_⟩
  rw [toffoli_unaryQROMAt]
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

end FormalRV.Audit.CainXu2026.ResourceCheck
