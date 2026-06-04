/-
  FormalRV.Shor.WindowedComposedCost — the BRIDGE between the structurally-composed Toffoli
  count of `WindowedComposed.modExp` (built from `babbushLookupAdd`) and the paper's reported
  total `WindowedCostModel.toffoliCount`.  This is what closes the user's concern: the counts
  are no longer verified in isolation — the full-mod-exp structural count and the paper number
  are related by ONE proven identity, with the gap NAMED, not hand-waved.

  Per lookup-addition, the paper charges (main.tex l.712, `g_mul`-corrected)
      perLookupToffoli = 2n + n·g_pad/g_sep + 2^{g_exp+g_mul}
  whereas the circuit we actually build (`babbushLookupAdd`) costs
      structPerLookup  = (2^{g_exp+g_mul} − 1) + 2n.
  The difference is EXACTLY `1 + n·g_pad/g_sep`:
      • `+1`           : the paper rounds the babbush lookup `2^w − 1` up to `2^w`;
      • `+n·g_pad/g_sep`: the runway-folding additions (main.tex l.695 — "several small additions
                          to temporarily reduce the runway registers") that a single
                          lookup-addition does not contain.
  Both terms are real modelling choices in the paper; our composed circuit is HONEST about
  omitting them (it is the bare lookup-add-uncompute loop), and the total gap is therefore
  exactly `LookupAdditionCount · (1 + n·g_pad/g_sep)`.
-/
import FormalRV.Shor.WindowedCostModel
import FormalRV.Shor.WindowedComposed

namespace FormalRV.Shor.WindowedComposedCost

open FormalRV.Shor.WindowedCostModel
open FormalRV.Framework FormalRV.Shor.MeasUncompute
open scoped Classical

/-- The per-lookup-addition Toffoli cost actually realised by `babbushLookupAdd`, as `ℚ`,
    with the paper's window `w = g_exp+g_mul = 10` (so `2^w = 2^10`) and adder width `n`. -/
def structPerLookup (n : ℚ) : ℚ := (2 ^ 10 - 1) + 2 * n

/-- The structurally-composed Toffoli total: the SAME lookup-addition count as the paper,
    times the cost of the lookup-addition we actually build. -/
def structToffoliCount (n n_e : ℚ) : ℚ := lookupAdditionCount n n_e * structPerLookup n

/-- **★ The exact per-lookup-addition gap ★.**  The paper's charge exceeds the
    structurally-realised `babbushLookupAdd` cost by exactly `1 + n·g_pad/g_sep`
    (`g_pad = 3L+10`, `g_sep = 1024`): `+1` rounding of `2^w−1 → 2^w`, plus the
    runway-folding additions. -/
theorem perLookup_gap (n L : ℚ) :
    perLookupToffoli n L - structPerLookup n = 1 + n * (3 * L + 10) / 1024 := by
  unfold perLookupToffoli structPerLookup; ring

/-- **★ The exact TOTAL gap ★** between the paper's reported `ToffoliCount` and the
    structurally-composed count (at the same `LookupAdditionCount`): it is precisely
    `LookupAdditionCount · (1 + n·g_pad/g_sep)` — no unexplained slack. -/
theorem total_gap (n n_e L : ℚ) :
    toffoliCount n n_e L - structToffoliCount n n_e
      = lookupAdditionCount n n_e * (1 + n * (3 * L + 10) / 1024) := by
  unfold toffoliCount structToffoliCount
  rw [← perLookup_gap n L]; ring

/-- The structural count is a genuine LOWER bound on the paper's reported count
    (the omitted runway-folding + rounding only add cost), for `n, L ≥ 0`. -/
theorem structToffoliCount_le_paper (n n_e L : ℚ)
    (hn : 0 ≤ n) (hne : 0 ≤ n_e) (hL : 0 ≤ L) :
    structToffoliCount n n_e ≤ toffoliCount n n_e L := by
  have hgap : toffoliCount n n_e L - structToffoliCount n n_e
      = lookupAdditionCount n n_e * (1 + n * (3 * L + 10) / 1024) := total_gap n n_e L
  have hlac : 0 ≤ lookupAdditionCount n n_e := by
    rw [lookupAdditionCount_eq]; positivity
  have hfac : 0 ≤ 1 + n * (3 * L + 10) / 1024 := by positivity
  nlinarith [mul_nonneg hlac hfac, hgap]

/-! ## RSA-2048 head-to-head (n = 2048, n_e = 3072, lg n = 11). -/

/-- Structural per-lookup-addition cost at RSA-2048 = `5119` (`= 2^10 − 1 + 2·2048`). -/
theorem structPerLookup_rsa : structPerLookup 2048 = 5119 := by
  unfold structPerLookup; norm_num

/-- Paper per-lookup-addition cost at RSA-2048 = `5206`; the per-op gap is exactly `87`
    (`= 1` rounding `+ 86` runway-folding, `86 = 2048·43/1024`). -/
theorem perLookup_rsa :
    perLookupToffoli 2048 11 = 5206
    ∧ perLookupToffoli 2048 11 - structPerLookup 2048 = 87 := by
  refine ⟨by unfold perLookupToffoli; norm_num, ?_⟩
  rw [perLookup_gap]; norm_num

/-- **The end-to-end head-to-head at RSA-2048.**  The lookup-addition count is `503808`
    on both sides; the structurally-composed circuit costs `503808 · 5119 = 2 578 993 152`
    Toffolis, versus the paper's reported `503808 · 5206 = 2 622 824 448`.  The total gap is
    exactly `43 831 296` (1.67%), decomposing as `503808` (lookup rounding) `+ 43 327 488`
    (runway folding). -/
theorem rsa2048_head_to_head :
    structToffoliCount 2048 3072 = 2578993152
    ∧ toffoliCount 2048 3072 11 = 2622824448
    ∧ toffoliCount 2048 3072 11 - structToffoliCount 2048 3072 = 43831296
    ∧ (43831296 : ℚ) = 503808 * 1 + 503808 * 86 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · unfold structToffoliCount structPerLookup lookupAdditionCount; norm_num
  · unfold toffoliCount lookupAdditionCount perLookupToffoli; norm_num
  · unfold toffoliCount structToffoliCount structPerLookup lookupAdditionCount perLookupToffoli
    norm_num

/-! ## The structural `ℚ` total IS the actual `EGate.toffoli` (cast), at RSA-2048.

The composed `EGate` `WindowedComposed.modExp` with `numMults·2·numWin = 503808` lookup-additions,
window `w = 10`, adder width `bits = 2048`, has Toffoli count exactly `2 578 993 152` — i.e. the
structural model `structToffoliCount 2048 3072` is realised by a concrete emittable circuit, not
just an arithmetic expression.  (`503808 = 246·2·1024` is a factorisation of the paper's
leading-term lookup-addition count into multiplications × 2 multiply-adds × windows.) -/

open FormalRV.Shor.WindowedComposed

theorem rsa2048_structural_circuit_toffoli (W : Nat) (T : Nat → Nat) :
    EGate.toffoli (modExp 10 W 2048 T 246 1024) = 2578993152 := by
  rw [toffoli_modExp]; norm_num

/-- And that concrete circuit Toffoli count, cast to `ℚ`, equals the structural cost model
    `structToffoliCount 2048 3072` — closing the loop between circuit and number. -/
theorem rsa2048_circuit_matches_model (W : Nat) (T : Nat → Nat) :
    (EGate.toffoli (modExp 10 W 2048 T 246 1024) : ℚ) = structToffoliCount 2048 3072 := by
  rw [rsa2048_structural_circuit_toffoli]
  unfold structToffoliCount structPerLookup lookupAdditionCount; norm_num

end FormalRV.Shor.WindowedComposedCost
