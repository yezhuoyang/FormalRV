/-
  FormalRV.BQAlgo.Cuccaro — the Cuccaro–Draper–Kutin–Moulton ripple-carry
  adder, encoded as concrete `Gate` data over the Framework IR.

  Per CLAUDE.md "Paper-claim-first workflow", every claim has the form
  `paper_claim_X` (paper's stated number) + `X_meets_paper_claim` (theorem
  that our derivation matches). Either the proof closes (paper verified
  for this component) or it doesn't (gap found).

  This file covers cost claims (T-count). Semantic correctness — does the
  MAJ gadget actually compute the majority function on bits? — lives in
  `BQAlgo/CuccaroCorrectness.lean`.

  Refs:
    - Cuccaro, Draper, Kutin, Moulton, "A new quantum ripple-carry addition
      circuit" (arXiv:quant-ph/0410184).
    - SQIR/examples/shor/ModMult.v (Coq encoding we're mirroring).
    - SQIR/examples/shor/ResourceShor.v `bcgcount_MAJ` ≤ 3 (gate count,
      not T-count). Each MAJ has 1 CCX + 2 CX, so under the textbook 7-T
      Toffoli decomposition, T-count is 7 per MAJ.
-/
import FormalRV.Core.Gate

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate

/-! ## Paper claims (state first; verify below) -/

/-- Per-MAJ T-count claim.
    Source chain: SQIR `bcgcount_MAJ` ≤ 3 (gate count) ⟹ 1 Toffoli + 2 CX
    per MAJ ⟹ 7 T-gates per Toffoli (textbook) ⟹ 7 T-gates per MAJ. -/
def paper_claim_MAJ_tcount : Nat := 7

/-- Per-UMA T-count claim. Same derivation as MAJ. -/
def paper_claim_UMA_tcount : Nat := 7

/-! ## Cuccaro MAJ and UMA — concrete encoding

    MAJ a b c  =  CX c b ; CX c a ; CCX a b c
    UMA a b c  =  CCX a b c ; CX c a ; CX a b
-/

/-- Cuccaro MAJ gadget. -/
def cuccaro_MAJ (a b c : Nat) : Gate :=
  seq (CX c b) (seq (CX c a) (CCX a b c))

/-- Cuccaro UMA gadget. -/
def cuccaro_UMA (a b c : Nat) : Gate :=
  seq (CCX a b c) (seq (CX c a) (CX a b))

/-! ## Verification: does our encoding meet the cost claim? -/

/-- ✅ MAJ meets the paper claim (T-count = 7). -/
theorem MAJ_meets_paper_claim (a b c : Nat) :
    tcount (cuccaro_MAJ a b c) = paper_claim_MAJ_tcount := by
  simp [cuccaro_MAJ, tcount, paper_claim_MAJ_tcount]

/-- ✅ UMA meets the paper claim (T-count = 7). -/
theorem UMA_meets_paper_claim (a b c : Nat) :
    tcount (cuccaro_UMA a b c) = paper_claim_UMA_tcount := by
  simp [cuccaro_UMA, tcount, paper_claim_UMA_tcount]

/-! ## Smoke tests -/

example : tcount (cuccaro_MAJ 0 1 2) = 7 := by decide
example : tcount (cuccaro_UMA 0 1 2) = 7 := by decide
example : tcount (seq (cuccaro_MAJ 0 1 2) (cuccaro_UMA 0 1 2)) = 14 := by decide

/-! ## Parametric cost lemmas (gate-label invariance)

    The concrete `decide` examples above check the T-count at specific
    qubit labels (0, 1, 2). The lemmas below establish that the cost
    is independent of *which* qubits the MAJ/UMA gadget targets — a
    property the paper implicitly assumes when summing per-block costs
    over a register width. -/

/-- The MAJ T-count is 7 for *every* qubit assignment, not just (0,1,2). -/
theorem MAJ_tcount_label_invariant (a b c a' b' c' : Nat) :
    tcount (cuccaro_MAJ a b c) = tcount (cuccaro_MAJ a' b' c') := by
  rw [MAJ_meets_paper_claim a b c, MAJ_meets_paper_claim a' b' c']

/-- The UMA T-count is 7 for *every* qubit assignment. -/
theorem UMA_tcount_label_invariant (a b c a' b' c' : Nat) :
    tcount (cuccaro_UMA a b c) = tcount (cuccaro_UMA a' b' c') := by
  rw [UMA_meets_paper_claim a b c, UMA_meets_paper_claim a' b' c']

/-- Parametric MAJ+UMA pair cost: 14 T for any qubit assignment. -/
theorem MAJ_UMA_pair_tcount (a b c a' b' c' : Nat) :
    tcount (seq (cuccaro_MAJ a b c) (cuccaro_UMA a' b' c')) = 14 := by
  simp [tcount, MAJ_meets_paper_claim a b c, UMA_meets_paper_claim a' b' c',
        paper_claim_MAJ_tcount, paper_claim_UMA_tcount]

/-! ## Phase A: n-block Cuccaro chains (scope expansion 2026-05-12)

    The single-gadget verification above (`MAJ_meets_paper_claim`) is
    sufficient at the per-Toffoli layer. Phase A deepens this by
    chaining gadgets into an n-block adder skeleton, deriving the
    multi-block T-count from first principles. -/

/-- A chain of `n` MAJ gadgets, each operating on a triple of
    consecutive qubits starting at `q_start`, then `q_start + 2`,
    then `q_start + 4`, ... (the Cuccaro ripple structure). -/
def cuccaro_maj_chain : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
          (cuccaro_maj_chain n (q_start + 2))

/-- A chain of `n` UMA gadgets in the same ripple structure. -/
def cuccaro_uma_chain : Nat → Nat → Gate
  | 0,     _       => I
  | n + 1, q_start =>
      seq (cuccaro_UMA q_start (q_start + 1) (q_start + 2))
          (cuccaro_uma_chain n (q_start + 2))

/-- T-count of an n-block MAJ chain is exactly `7 * n` (no
    cross-block savings from gate-level optimization alone). -/
theorem tcount_cuccaro_maj_chain (n q_start : Nat) :
    tcount (cuccaro_maj_chain n q_start) = 7 * n := by
  induction n generalizing q_start with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (cuccaro_MAJ q_start (q_start + 1) (q_start + 2))
                      (cuccaro_maj_chain k (q_start + 2))) = 7 * (k + 1)
    simp [tcount, MAJ_meets_paper_claim, paper_claim_MAJ_tcount,
          ih (q_start + 2)]
    omega

/-- T-count of an n-block UMA chain is exactly `7 * n`. -/
theorem tcount_cuccaro_uma_chain (n q_start : Nat) :
    tcount (cuccaro_uma_chain n q_start) = 7 * n := by
  induction n generalizing q_start with
  | zero => rfl
  | succ k ih =>
    show tcount (seq (cuccaro_UMA q_start (q_start + 1) (q_start + 2))
                      (cuccaro_uma_chain k (q_start + 2))) = 7 * (k + 1)
    simp [tcount, UMA_meets_paper_claim, paper_claim_UMA_tcount,
          ih (q_start + 2)]
    omega

/-- A simplified n-bit Cuccaro adder skeleton: `n` MAJs forward,
    then `n` UMAs back. Real Cuccaro has additional CX corrections
    at the boundaries (paper p. 22-24); for the T-count this
    skeleton is exact since CX is T-free. -/
def cuccaro_n_bit_adder_skeleton (n q_start : Nat) : Gate :=
  seq (cuccaro_maj_chain n q_start) (cuccaro_uma_chain n q_start)

/-- **n-bit adder T-count is `14 * n`** — verified from gate-level
    construction (not taken as a paper input). This re-derives the
    "per-block" claim qianxu uses in Eq. E3 from the actual Cuccaro
    gate sequence. -/
theorem tcount_cuccaro_n_bit_adder_skeleton (n q_start : Nat) :
    tcount (cuccaro_n_bit_adder_skeleton n q_start) = 14 * n := by
  show tcount (seq (cuccaro_maj_chain n q_start)
                    (cuccaro_uma_chain n q_start)) = 14 * n
  simp [tcount, tcount_cuccaro_maj_chain, tcount_cuccaro_uma_chain]
  omega

/-- Smoke: 4-bit adder skeleton has 14 × 4 = 56 T-gates. -/
example : tcount (cuccaro_n_bit_adder_skeleton 4 0) = 56 := by decide

/-! ## CCX-pair-removal optimization

    First real circuit-rewrite step: detect an adjacent `CCX a b c ; CCX
    a b c` pair and replace it with the identity. Semantically valid
    because CCX is its own inverse (see `CCX_CCX_id` in
    `Framework.PadAction`). This is a *single-shot top-level* pass —
    deeper rewriting requires multi-pass or normalization. -/

/-- Top-level CCX-pair-removal: if the outermost `seq` contains the same
    `CCX a b c` on both sides, replace with `I` (zero T-count). All
    other shapes are returned unchanged. -/
def optimize_ccx_pair_top : Gate → Gate
  | seq (CCX a b c) (CCX a' b' c') =>
      if a = a' ∧ b = b' ∧ c = c' then I
      else seq (CCX a b c) (CCX a' b' c')
  | seq g₁ g₂ => seq g₁ g₂
  | I => I
  | X q => X q
  | CX a b => CX a b
  | CCX a b c => CCX a b c

/-- Smoke test: the optimization detects an identical adjacent CCX pair
    and reduces T-count from 14 to 0. -/
example : tcount (optimize_ccx_pair_top (seq (CCX 0 1 2) (CCX 0 1 2))) = 0 := by
  decide

/-- Smoke test: when the two CCX's differ (different target), the
    optimizer leaves the circuit unchanged. -/
example : tcount (optimize_ccx_pair_top (seq (CCX 0 1 2) (CCX 0 1 3))) = 14 := by
  decide

/-- Smoke test: non-CCX shapes are passed through. -/
example : optimize_ccx_pair_top (seq (X 0) (CX 0 1)) = seq (X 0) (CX 0 1) := by
  decide

/-- The optimization never increases T-count: it either rewrites a
    matching CCX pair to `I` (drops 14 T's) or leaves the circuit
    unchanged. Combined with the semantic justification in
    `Framework.PadAction.CCX_CCX_id`, this is a real T-count
    monotonicity proof for a top-level circuit rewrite. -/
theorem tcount_optimize_ccx_pair_top_le (g : Gate) :
    tcount (optimize_ccx_pair_top g) ≤ tcount g := by
  cases g with
  | I => exact Nat.le.refl
  | X _ => exact Nat.le.refl
  | CX _ _ => exact Nat.le.refl
  | CCX _ _ _ => exact Nat.le.refl
  | seq g₁ g₂ =>
    cases g₁ with
    | CCX a b c =>
      cases g₂ with
      | CCX a' b' c' =>
        simp [optimize_ccx_pair_top]
        split
        · simp [tcount]
        · exact Nat.le.refl
      | _ => exact Nat.le.refl
    | _ => exact Nat.le.refl

/-- Gate-count monotonicity for the top-level CCX-pair rewrite. Same
    case structure as the T-count version: pair-match drops gcount
    from 2 to 0, all other shapes are unchanged. -/
theorem gcount_optimize_ccx_pair_top_le (g : Gate) :
    gcount (optimize_ccx_pair_top g) ≤ gcount g := by
  cases g with
  | I => exact Nat.le.refl
  | X _ => exact Nat.le.refl
  | CX _ _ => exact Nat.le.refl
  | CCX _ _ _ => exact Nat.le.refl
  | seq g₁ g₂ =>
    cases g₁ with
    | CCX a b c =>
      cases g₂ with
      | CCX a' b' c' =>
        simp [optimize_ccx_pair_top]
        split
        · simp [gcount]
        · exact Nat.le.refl
      | _ => exact Nat.le.refl
    | _ => exact Nat.le.refl

/-- Recursive deep CCX-pair-removal: bottom-up, optimize children first,
    then apply the top-level rewrite. Catches nested patterns that
    `optimize_ccx_pair_top` alone misses. -/
def optimize_ccx_pairs_deep : Gate → Gate
  | seq g₁ g₂ =>
      optimize_ccx_pair_top
        (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂))
  | g => g

/-- Smoke test: nested CCX pair inside a seq is detected. Without
    the deep optimizer, `optimize_ccx_pair_top` alone wouldn't touch
    a CCX pair hidden behind a `seq (X 0) (...)`. -/
example :
    tcount (optimize_ccx_pairs_deep
      (seq (X 0) (seq (CCX 0 1 2) (CCX 0 1 2)))) = 0 := by
  decide

/-- Smoke test: deep optimizer also catches the trivial top-level case. -/
example :
    tcount (optimize_ccx_pairs_deep (seq (CCX 0 1 2) (CCX 0 1 2))) = 0 := by
  decide

/-- Deep optimization is also T-count-monotone-non-increasing. Inductive
    proof: assume both children's T-counts are bounded above by their
    pre-optimization values (IH), then chain through `seq` additivity
    and the top-level monotonicity result. -/
theorem tcount_optimize_ccx_pairs_deep_le (g : Gate) :
    tcount (optimize_ccx_pairs_deep g) ≤ tcount g := by
  induction g with
  | I => exact Nat.le.refl
  | X _ => exact Nat.le.refl
  | CX _ _ => exact Nat.le.refl
  | CCX _ _ _ => exact Nat.le.refl
  | seq g₁ g₂ ih₁ ih₂ =>
    show tcount (optimize_ccx_pair_top
            (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
         ≤ tcount g₁ + tcount g₂
    calc tcount (optimize_ccx_pair_top
            (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
        ≤ tcount (seq (optimize_ccx_pairs_deep g₁)
                       (optimize_ccx_pairs_deep g₂)) :=
            tcount_optimize_ccx_pair_top_le _
      _ = tcount (optimize_ccx_pairs_deep g₁)
          + tcount (optimize_ccx_pairs_deep g₂) := rfl
      _ ≤ tcount g₁ + tcount g₂ := Nat.add_le_add ih₁ ih₂

/-- Nat-fueled iteration of `optimize_ccx_pairs_deep`. Useful as a
    fixpoint driver: pick an upper bound on the number of passes
    (e.g., bounded by gate count) and the result is guaranteed to be
    no worse than the input. -/
def optimize_ccx_iter : Nat → Gate → Gate
  | 0, g => g
  | n + 1, g => optimize_ccx_iter n (optimize_ccx_pairs_deep g)

/-- Iterated optimization preserves T-count monotonicity. Inductive
    on the fuel: each step composes the deep optimizer's bound with
    the previous iterates'. -/
theorem tcount_optimize_ccx_iter_le (n : Nat) (g : Gate) :
    tcount (optimize_ccx_iter n g) ≤ tcount g := by
  induction n generalizing g with
  | zero => exact Nat.le.refl
  | succ k ih =>
    show tcount (optimize_ccx_iter k (optimize_ccx_pairs_deep g)) ≤ tcount g
    exact Nat.le_trans (ih _) (tcount_optimize_ccx_pairs_deep_le g)

/-- Smoke: a top-level CCX pair optimizes to T-count 0 even with one
    iteration of fuel. -/
example : tcount (optimize_ccx_iter 5 (seq (CCX 0 1 2) (CCX 0 1 2))) = 0 := by
  decide

/-- Smoke: a single (un-pairable) CCX is not affected by any number of
    iterations — T-count stays at 7. -/
example : tcount (optimize_ccx_iter 10 (CCX 0 1 2)) = 7 := by decide

/-! ## Identity-elimination rewrite

    Companion to the CCX-pair rewrite: when an `I` (no-op identity)
    appears on the left or right of a `seq`, drop it. This is the
    "second pass" that lets cascading CCX patterns separated by an
    `I` (produced by a prior CCX-pair-removal) collapse further. -/

/-- Top-level identity-elimination: drops `I` from either side of an
    outermost `seq`. -/
def optimize_I_top : Gate → Gate
  | seq I g => g
  | seq g I => g
  | g       => g

/-- Identity-elimination preserves T-count exactly (since `tcount I = 0`). -/
theorem tcount_optimize_I_top (g : Gate) :
    tcount (optimize_I_top g) = tcount g := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | I => simp [optimize_I_top, tcount]
    | _ =>
      cases g₂ with
      | I => simp [optimize_I_top, tcount]
      | _ => rfl

/-- T-count monotonicity follows trivially from exact equality. -/
theorem tcount_optimize_I_top_le (g : Gate) :
    tcount (optimize_I_top g) ≤ tcount g :=
  Nat.le_of_eq (tcount_optimize_I_top g)

/-- Gate-count monotonicity for I-elimination: also exact preservation,
    since `gcount I = 0` (identity gates don't count). -/
theorem gcount_optimize_I_top (g : Gate) :
    gcount (optimize_I_top g) = gcount g := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | I => simp [optimize_I_top, gcount]
    | _ =>
      cases g₂ with
      | I => simp [optimize_I_top, gcount]
      | _ => rfl

theorem gcount_optimize_I_top_le (g : Gate) :
    gcount (optimize_I_top g) ≤ gcount g :=
  Nat.le_of_eq (gcount_optimize_I_top g)

/-- Smoke: chaining I-elimination with the deep CCX optimizer collapses
    a cascading pattern. `seq (CCX) (seq (CCX ; CCX) (CCX))` goes:
    deep → `seq (CCX) (seq I (CCX))` → I-elim doesn't fire at top-level
    yet, but if applied recursively it would. This smoke only checks
    top-level chaining behavior. -/
example : tcount (optimize_I_top (seq I (CCX 0 1 2))) = 7 := by decide

/-- Smoke: `seq (CCX) I` reduces to plain `CCX`. -/
example : optimize_I_top (seq (CCX 0 1 2) I) = CCX 0 1 2 := by decide

/-- Recursive deep identity-elimination: bottom-up, optimize children
    first, then apply the top-level rewrite. -/
def optimize_I_pairs_deep : Gate → Gate
  | seq g₁ g₂ =>
      optimize_I_top
        (seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂))
  | g => g

/-- Deep I-elimination preserves T-count exactly (every step is exact). -/
theorem tcount_optimize_I_pairs_deep (g : Gate) :
    tcount (optimize_I_pairs_deep g) = tcount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    show tcount (optimize_I_top
            (seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂)))
         = tcount g₁ + tcount g₂
    rw [tcount_optimize_I_top]
    show tcount (optimize_I_pairs_deep g₁)
         + tcount (optimize_I_pairs_deep g₂) = tcount g₁ + tcount g₂
    rw [ih₁, ih₂]

/-! ## Combined optimizer: CCX-pair removal then I-elimination -/

/-- The full single-pass optimizer: first reduce CCX pairs (which may
    introduce `I` placeholders), then sweep out the resulting `I`s. -/
def optimize_full (g : Gate) : Gate :=
  optimize_I_pairs_deep (optimize_ccx_pairs_deep g)

/-- The combined optimizer is also T-count-monotone-non-increasing.
    Since deep I-elimination preserves T-count exactly, the combined
    bound is just the deep CCX bound. -/
theorem tcount_optimize_full_le (g : Gate) :
    tcount (optimize_full g) ≤ tcount g := by
  show tcount (optimize_I_pairs_deep (optimize_ccx_pairs_deep g)) ≤ tcount g
  rw [tcount_optimize_I_pairs_deep]
  exact tcount_optimize_ccx_pairs_deep_le g

/-- Smoke: directly-adjacent CCX pair under an `I` wrapper. The CCX
    pair is detected by the deep CCX-elim (returns `seq I I`), then
    the I-elim collapses it to `I`. -/
example : tcount (optimize_full
    (seq I (seq (CCX 0 1 2) (CCX 0 1 2)))) = 0 := by decide

/-- Smoke: an un-adjacent CCX pair (separated by a seq wrapper) is
    NOT fully collapsed by a single `optimize_full` pass — the CCX
    elim only sees the inner `seq (CCX) I` after I-elim runs, which
    happens later. Documents the known limitation: one pass isn't a
    fixpoint. -/
example : tcount (optimize_full
    (seq (CCX 0 1 2) (seq (CCX 0 1 2) I))) = 14 := by decide

/-- Nat-fueled iteration of `optimize_full`. Each fuel step alternates
    CCX-pair removal and I-elimination, so two iterations suffice for
    the associativity-blocked example above. -/
def optimize_full_iter : Nat → Gate → Gate
  | 0,     g => g
  | n + 1, g => optimize_full_iter n (optimize_full g)

/-- Iterated combined optimization is monotone non-increasing in
    T-count. Inductive on fuel via `Nat.le_trans` and the single-pass
    bound. -/
theorem tcount_optimize_full_iter_le (n : Nat) (g : Gate) :
    tcount (optimize_full_iter n g) ≤ tcount g := by
  induction n generalizing g with
  | zero => exact Nat.le.refl
  | succ k ih =>
    show tcount (optimize_full_iter k (optimize_full g)) ≤ tcount g
    exact Nat.le_trans (ih _) (tcount_optimize_full_le g)

/-- Smoke: the associativity-blocked case from above now collapses to
    `I` (T-count 0) after 2 iterations. First iteration runs CCX-elim
    + I-elim, exposing a new top-level `seq (CCX) (CCX)` pair that
    the second iteration eliminates. -/
example : tcount (optimize_full_iter 2
    (seq (CCX 0 1 2) (seq (CCX 0 1 2) I))) = 0 := by decide

/-! ## gcount monotonicity for the recursive / iterated optimizers

    Companion to the previous batch of top-level gcount proofs. Same
    inductive structure as the tcount versions. -/

theorem gcount_optimize_ccx_pairs_deep_le (g : Gate) :
    gcount (optimize_ccx_pairs_deep g) ≤ gcount g := by
  induction g with
  | I => exact Nat.le.refl
  | X _ => exact Nat.le.refl
  | CX _ _ => exact Nat.le.refl
  | CCX _ _ _ => exact Nat.le.refl
  | seq g₁ g₂ ih₁ ih₂ =>
    show gcount (optimize_ccx_pair_top
            (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
         ≤ gcount g₁ + gcount g₂
    calc gcount (optimize_ccx_pair_top
            (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
        ≤ gcount (seq (optimize_ccx_pairs_deep g₁)
                       (optimize_ccx_pairs_deep g₂)) :=
            gcount_optimize_ccx_pair_top_le _
      _ = gcount (optimize_ccx_pairs_deep g₁)
          + gcount (optimize_ccx_pairs_deep g₂) := rfl
      _ ≤ gcount g₁ + gcount g₂ := Nat.add_le_add ih₁ ih₂

theorem gcount_optimize_I_pairs_deep (g : Gate) :
    gcount (optimize_I_pairs_deep g) = gcount g := by
  induction g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ ih₁ ih₂ =>
    show gcount (optimize_I_top
            (seq (optimize_I_pairs_deep g₁) (optimize_I_pairs_deep g₂)))
         = gcount g₁ + gcount g₂
    rw [gcount_optimize_I_top]
    show gcount (optimize_I_pairs_deep g₁)
         + gcount (optimize_I_pairs_deep g₂) = gcount g₁ + gcount g₂
    rw [ih₁, ih₂]

theorem gcount_optimize_full_le (g : Gate) :
    gcount (optimize_full g) ≤ gcount g := by
  show gcount (optimize_I_pairs_deep (optimize_ccx_pairs_deep g)) ≤ gcount g
  rw [gcount_optimize_I_pairs_deep]
  exact gcount_optimize_ccx_pairs_deep_le g

theorem gcount_optimize_full_iter_le (n : Nat) (g : Gate) :
    gcount (optimize_full_iter n g) ≤ gcount g := by
  induction n generalizing g with
  | zero => exact Nat.le.refl
  | succ k ih =>
    show gcount (optimize_full_iter k (optimize_full g)) ≤ gcount g
    exact Nat.le_trans (ih _) (gcount_optimize_full_le g)

/-! ## Strict-decrease witnesses (toward well-founded termination)

    For the wf-recursion approach to an unfueled fixpoint we need strict
    decrease on at least one cost metric whenever the optimizer can
    make progress. The simplest witness: a top-level CCX-CCX pair
    strictly reduces gcount from 2 to 0. This is the smallest seed for
    a future general strict-decrease lemma. -/

/-- If a CCX-CCX pair appears at the top level (same triple on both
    sides), the top-level optimizer strictly decreases gcount. -/
theorem gcount_optimize_ccx_pair_top_strict_on_pair (a b c : Nat) :
    gcount (optimize_ccx_pair_top (seq (CCX a b c) (CCX a b c))) <
      gcount (seq (CCX a b c) (CCX a b c)) := by
  simp [optimize_ccx_pair_top, gcount]

/-- Same statement for T-count: 14 → 0 is strict. -/
theorem tcount_optimize_ccx_pair_top_strict_on_pair (a b c : Nat) :
    tcount (optimize_ccx_pair_top (seq (CCX a b c) (CCX a b c))) <
      tcount (seq (CCX a b c) (CCX a b c)) := by
  simp [optimize_ccx_pair_top, tcount]

-- NOTE: I-elim is exact-preserving (`gcount_optimize_I_top : = `, not <),
-- so it does NOT contribute strict decrease. Only the CCX-pair rewrite
-- does. A future strict-decrease theorem on `optimize_full` will need to
-- assume "there exists at least one adjacent CCX-CCX pair somewhere in g".

/-- Decidable predicate: does `g` contain an adjacent CCX-CCX pair
    anywhere? Recurses into `seq` children. Used as the hypothesis for
    the future strict-decrease theorem. -/
def has_ccx_pair : Gate → Bool
  | seq (CCX a b c) (CCX a' b' c') =>
      (decide (a = a')) && (decide (b = b')) && (decide (c = c'))
  | seq g₁ g₂ => has_ccx_pair g₁ || has_ccx_pair g₂
  | _ => false

/-- Smoke: direct CCX pair is detected. -/
example : has_ccx_pair (seq (CCX 0 1 2) (CCX 0 1 2)) = true := by decide

/-- Smoke: nested CCX pair under X is detected via recursion. -/
example : has_ccx_pair (seq (X 0) (seq (CCX 0 1 2) (CCX 0 1 2))) = true := by
  decide

/-- Smoke: differing-triple CCX pair returns false. -/
example : has_ccx_pair (seq (CCX 0 1 2) (CCX 0 1 3)) = false := by decide

/-- Smoke: no CCX at all → false. -/
example : has_ccx_pair (seq (X 0) (CX 0 1)) = false := by decide

/-- Smoke: deeply nested CCX pair behind two X's. -/
example : has_ccx_pair
    (seq (X 0) (seq (X 1) (seq (CCX 0 1 2) (CCX 0 1 2)))) = true := by decide

/-- Strict-decrease witness for the deep optimizer at the simplest input
    shape: a top-level CCX-CCX pair. The deep optimizer recurses into
    each child (both CCXs return themselves), then top-level matches the
    pair → `I`. So gcount drops 2 → 0 strictly.
    This is the "easy" seed for the future general theorem
    `has_ccx_pair g = true → gcount (optimize_ccx_pairs_deep g) <
    gcount g`. -/
theorem gcount_optimize_ccx_pairs_deep_strict_on_pair (a b c : Nat) :
    gcount (optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c))) <
      gcount (seq (CCX a b c) (CCX a b c)) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, gcount]

/-- Same for T-count: deep optimizer drops 14 → 0 strictly on a pair. -/
theorem tcount_optimize_ccx_pairs_deep_strict_on_pair (a b c : Nat) :
    tcount (optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c))) <
      tcount (seq (CCX a b c) (CCX a b c)) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, tcount]

/-- Strict-decrease for a CCX pair nested under an X wrapper: the deep
    optimizer recurses, eliminates the inner CCX pair (replacing with
    `I`), then leaves `seq (X q) I` at the top. gcount drops 3 → 1.
    Demonstrates that strict-decrease propagates through the recursive
    structure of the deep optimizer when a pair exists anywhere below. -/
theorem gcount_optimize_ccx_pairs_deep_strict_seq_X_pair (q a b c : Nat) :
    gcount (optimize_ccx_pairs_deep
      (seq (X q) (seq (CCX a b c) (CCX a b c)))) <
    gcount (seq (X q) (seq (CCX a b c) (CCX a b c))) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, gcount]

/-- T-count strict-decrease for the same nested-under-X case:
    14 → 0 (the X has tcount 0; only the CCX pair contributes). -/
theorem tcount_optimize_ccx_pairs_deep_strict_seq_X_pair (q a b c : Nat) :
    tcount (optimize_ccx_pairs_deep
      (seq (X q) (seq (CCX a b c) (CCX a b c)))) <
    tcount (seq (X q) (seq (CCX a b c) (CCX a b c))) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, tcount]

/-- Symmetric form: CCX pair on the LEFT of an X wrapper. Deep optimizer
    reduces gcount 3 → 1 and tcount 14 → 0. -/
theorem gcount_optimize_ccx_pairs_deep_strict_pair_seq_X (a b c q : Nat) :
    gcount (optimize_ccx_pairs_deep
      (seq (seq (CCX a b c) (CCX a b c)) (X q))) <
    gcount (seq (seq (CCX a b c) (CCX a b c)) (X q)) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, gcount]

theorem tcount_optimize_ccx_pairs_deep_strict_pair_seq_X (a b c q : Nat) :
    tcount (optimize_ccx_pairs_deep
      (seq (seq (CCX a b c) (CCX a b c)) (X q))) <
    tcount (seq (seq (CCX a b c) (CCX a b c)) (X q)) := by
  simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top, tcount]

/-- Parametric: CCX pair on the LEFT, any gate `g` on the right. The
    deep optimizer collapses the pair to `I`, then leaves `seq I (deep g)`
    at top-level (no further match). Strict because the pair drops 2
    gcount; `g`-side is monotone non-increasing. -/
theorem gcount_optimize_ccx_pairs_deep_strict_pair_left (a b c : Nat) (g : Gate) :
    gcount (optimize_ccx_pairs_deep
      (seq (seq (CCX a b c) (CCX a b c)) g)) <
    gcount (seq (seq (CCX a b c) (CCX a b c)) g) := by
  -- After two layers of unfolding:
  -- LHS = gcount (optimize_ccx_pair_top (seq I (optimize_ccx_pairs_deep g)))
  -- The top-level pattern (seq CCX CCX) does NOT match (LHS is I, not CCX),
  -- so it returns seq I (deep g) → gcount = 0 + gcount (deep g)
  show gcount (optimize_ccx_pair_top
                 (seq (optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c)))
                      (optimize_ccx_pairs_deep g)))
       < gcount (seq (seq (CCX a b c) (CCX a b c)) g)
  have h_inner : optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c)) = I := by
    simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top]
  rw [h_inner]
  -- Goal: gcount (optimize_ccx_pair_top (seq I (deep g))) < gcount (seq (seq ...) g)
  -- optimize_ccx_pair_top (seq I X) = seq I X (since I is not CCX)
  show gcount (seq I (optimize_ccx_pairs_deep g))
       < gcount (seq (seq (CCX a b c) (CCX a b c)) g)
  -- gcount (seq I x) = 0 + gcount x = gcount x
  -- gcount (seq (seq CCX CCX) g) = (1+1) + gcount g = 2 + gcount g
  -- Need: gcount (deep g) < 2 + gcount g
  -- From monotonicity: gcount (deep g) ≤ gcount g
  have ih : gcount (optimize_ccx_pairs_deep g) ≤ gcount g :=
    gcount_optimize_ccx_pairs_deep_le g
  show gcount I + gcount (optimize_ccx_pairs_deep g)
       < gcount (CCX a b c) + gcount (CCX a b c) + gcount g
  simp [gcount]
  omega

/-- Symmetric parametric: CCX pair on the RIGHT, any gate `g` on the
    left. Same shape as the `_left` variant: collapse the inner pair to
    `I`. The top-level optimizer can't be definitionally reduced on
    `seq (deep g) I` (since `deep g` is opaque), but its universal
    monotonicity bound is enough. -/
theorem gcount_optimize_ccx_pairs_deep_strict_pair_right (g : Gate) (a b c : Nat) :
    gcount (optimize_ccx_pairs_deep
      (seq g (seq (CCX a b c) (CCX a b c)))) <
    gcount (seq g (seq (CCX a b c) (CCX a b c))) := by
  show gcount (optimize_ccx_pair_top
                 (seq (optimize_ccx_pairs_deep g)
                      (optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c)))))
       < gcount (seq g (seq (CCX a b c) (CCX a b c)))
  have h_inner : optimize_ccx_pairs_deep (seq (CCX a b c) (CCX a b c)) = I := by
    simp [optimize_ccx_pairs_deep, optimize_ccx_pair_top]
  rw [h_inner]
  have h_top_le : gcount (optimize_ccx_pair_top
                             (seq (optimize_ccx_pairs_deep g) I))
                  ≤ gcount (seq (optimize_ccx_pairs_deep g) I) :=
    gcount_optimize_ccx_pair_top_le _
  have ih : gcount (optimize_ccx_pairs_deep g) ≤ gcount g :=
    gcount_optimize_ccx_pairs_deep_le g
  -- gcount (seq (deep g) I) = gcount (deep g) + 0
  -- gcount (seq g (seq CCX CCX)) = gcount g + (1 + 1)
  -- Combine: deep_le + ih ≤ gcount g < gcount g + 2
  simp [gcount] at h_top_le ⊢
  omega

/-! ## Inductive-step helpers: strict decrease propagates through seq

    These are the two parametric lemmas that will close the seq case
    in the full `has_ccx_pair g → strict` induction. Each takes a
    recursive strict-decrease hypothesis and shows it propagates. -/

/-- If the LEFT child's deep optimization strictly decreases gcount,
    so does the seq's. -/
theorem gcount_optimize_ccx_pairs_deep_strict_via_left (g₁ g₂ : Gate)
    (ih₁ : gcount (optimize_ccx_pairs_deep g₁) < gcount g₁) :
    gcount (optimize_ccx_pairs_deep (seq g₁ g₂)) < gcount (seq g₁ g₂) := by
  show gcount (optimize_ccx_pair_top
                 (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
       < gcount (seq g₁ g₂)
  have h_top := gcount_optimize_ccx_pair_top_le
                  (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂))
  have h_g2 := gcount_optimize_ccx_pairs_deep_le g₂
  simp [gcount] at h_top ⊢
  omega

/-- Symmetric: if the RIGHT child's deep optimization strictly decreases
    gcount, so does the seq's. -/
theorem gcount_optimize_ccx_pairs_deep_strict_via_right (g₁ g₂ : Gate)
    (ih₂ : gcount (optimize_ccx_pairs_deep g₂) < gcount g₂) :
    gcount (optimize_ccx_pairs_deep (seq g₁ g₂)) < gcount (seq g₁ g₂) := by
  show gcount (optimize_ccx_pair_top
                 (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂)))
       < gcount (seq g₁ g₂)
  have h_top := gcount_optimize_ccx_pair_top_le
                  (seq (optimize_ccx_pairs_deep g₁) (optimize_ccx_pairs_deep g₂))
  have h_g1 := gcount_optimize_ccx_pairs_deep_le g₁
  simp [gcount] at h_top ⊢
  omega

/-! ## The full strict-decrease theorem

    Brings together the on_pair seed (top-level CCX-CCX) with the
    via_left/_right inductive helpers to give a full structural-
    induction proof. -/

/-- **Main strict-decrease theorem.** If a gate contains any adjacent
    CCX-CCX pair (anywhere — `has_ccx_pair` recursive detector), the
    deep optimizer strictly reduces gcount. This is the well-founded
    termination prerequisite for an unfueled fixpoint. -/
theorem gcount_optimize_ccx_pairs_deep_strict (g : Gate)
    (h : has_ccx_pair g = true) :
    gcount (optimize_ccx_pairs_deep g) < gcount g := by
  induction g with
  | I => simp [has_ccx_pair] at h
  | X _ => simp [has_ccx_pair] at h
  | CX _ _ => simp [has_ccx_pair] at h
  | CCX _ _ _ => simp [has_ccx_pair] at h
  | seq g₁ g₂ ih₁ ih₂ =>
    -- Case-split on whether either child contains a pair.
    cases hp1 : has_ccx_pair g₁ with
    | true => exact gcount_optimize_ccx_pairs_deep_strict_via_left
                      g₁ g₂ (ih₁ hp1)
    | false =>
      cases hp2 : has_ccx_pair g₂ with
      | true => exact gcount_optimize_ccx_pairs_deep_strict_via_right
                        g₁ g₂ (ih₂ hp2)
      | false =>
        -- Both children have no pair. The hypothesis `h` must therefore
        -- come from the TOP-LEVEL pattern in `has_ccx_pair`, which fires
        -- only when both children are CCX with matching triples.
        cases g₁ with
        | CCX a b c =>
          cases g₂ with
          | CCX a' b' c' =>
            -- Both CCX. Pattern 1 fires; h says triples match.
            -- Extract a = a', b = b', c = c' from h.
            simp [has_ccx_pair, decide_eq_true_eq] at h
            obtain ⟨⟨hab, hbc⟩, hcc⟩ := h
            subst hab; subst hbc; subst hcc
            exact gcount_optimize_ccx_pairs_deep_strict_on_pair a b c
          | _ => simp [has_ccx_pair, hp2] at h
        | _ => simp [has_ccx_pair, hp1, hp2] at h

/-- Strict-decrease lifted to `optimize_full = I-deep ∘ CCX-deep`.
    Since I-elim preserves gcount exactly, the strict drop comes
    entirely from the CCX-elim phase. Direct 3-line chain. -/
theorem gcount_optimize_full_strict (g : Gate)
    (h : has_ccx_pair g = true) :
    gcount (optimize_full g) < gcount g := by
  show gcount (optimize_I_pairs_deep (optimize_ccx_pairs_deep g)) < gcount g
  rw [gcount_optimize_I_pairs_deep]
  exact gcount_optimize_ccx_pairs_deep_strict g h

/-! ## Well-founded fixpoint optimizer (unfueled)

    Using the strict-decrease theorem as the termination certificate,
    we can define an unfueled `optimize_to_fixpoint` that iterates
    `optimize_full` until `has_ccx_pair` reports no remaining pair.
    Lean's WF-recursion machinery handles the termination via
    `termination_by gcount g` + `decreasing_by gcount_optimize_full_strict`. -/

/-- Iterate `optimize_full` until no adjacent CCX pair remains.
    Well-founded recursion on `gcount g`. The `_h` proof of
    `has_ccx_pair g = true` is unused inside the `then` branch but
    consumed by `decreasing_by` — Lean 4 allows the `_` prefix
    while still permitting references in proof-obligation blocks. -/
def optimize_to_fixpoint (g : Gate) : Gate :=
  if _h : has_ccx_pair g = true then
    optimize_to_fixpoint (optimize_full g)
  else
    g
  termination_by gcount g
  decreasing_by exact gcount_optimize_full_strict g _h

/-- Easy direction: when `g` has no pair, `optimize_to_fixpoint g = g`.
    Just unfolds the `else` branch of the wf-definition. -/
theorem optimize_to_fixpoint_eq_self_of_no_pair (g : Gate)
    (h : has_ccx_pair g = false) :
    optimize_to_fixpoint g = g := by
  rw [optimize_to_fixpoint]
  simp [h]

/-- One-step unfolding when `g` has a pair: `optimize_to_fixpoint g =
    optimize_to_fixpoint (optimize_full g)`. -/
theorem optimize_to_fixpoint_eq_recurse_of_pair (g : Gate)
    (h : has_ccx_pair g = true) :
    optimize_to_fixpoint g = optimize_to_fixpoint (optimize_full g) := by
  rw [optimize_to_fixpoint]
  simp [h]

/-- **Fixpoint property.** The optimizer terminates at an output with
    no remaining CCX pairs. Proved by well-founded recursion on
    `gcount g`, with `gcount_optimize_full_strict` as the decreasing
    bound. -/
theorem has_ccx_pair_optimize_to_fixpoint (g : Gate) :
    has_ccx_pair (optimize_to_fixpoint g) = false := by
  by_cases h : has_ccx_pair g = true
  · rw [optimize_to_fixpoint_eq_recurse_of_pair g h]
    exact has_ccx_pair_optimize_to_fixpoint (optimize_full g)
  · have hf : has_ccx_pair g = false := by
      cases hb : has_ccx_pair g with
      | true => exact absurd hb h
      | false => rfl
    rw [optimize_to_fixpoint_eq_self_of_no_pair g hf]
    exact hf
termination_by gcount g
decreasing_by exact gcount_optimize_full_strict g (by assumption)

/-- T-count monotonicity for the fixpoint operator. Same WF-recursive
    proof pattern as the fixpoint property, chaining the IH with
    `tcount_optimize_full_le` for the recursive step. -/
theorem tcount_optimize_to_fixpoint_le (g : Gate) :
    tcount (optimize_to_fixpoint g) ≤ tcount g := by
  by_cases h : has_ccx_pair g = true
  · rw [optimize_to_fixpoint_eq_recurse_of_pair g h]
    exact Nat.le_trans (tcount_optimize_to_fixpoint_le (optimize_full g))
                       (tcount_optimize_full_le g)
  · have hf : has_ccx_pair g = false := by
      cases hb : has_ccx_pair g with
      | true => exact absurd hb h
      | false => rfl
    rw [optimize_to_fixpoint_eq_self_of_no_pair g hf]
    exact Nat.le.refl
termination_by gcount g
decreasing_by exact gcount_optimize_full_strict g (by assumption)

/-- Same monotonicity for gate-count. -/
theorem gcount_optimize_to_fixpoint_le (g : Gate) :
    gcount (optimize_to_fixpoint g) ≤ gcount g := by
  by_cases h : has_ccx_pair g = true
  · rw [optimize_to_fixpoint_eq_recurse_of_pair g h]
    exact Nat.le_trans (gcount_optimize_to_fixpoint_le (optimize_full g))
                       (gcount_optimize_full_le g)
  · have hf : has_ccx_pair g = false := by
      cases hb : has_ccx_pair g with
      | true => exact absurd hb h
      | false => rfl
    rw [optimize_to_fixpoint_eq_self_of_no_pair g hf]
    exact Nat.le.refl
termination_by gcount g
decreasing_by exact gcount_optimize_full_strict g (by assumption)

/-! ## Associativity normalization: one right-rotation step

    To close the documented `seq MAJ UMA` limitation (where the
    natural CCX-CCX boundary sits at different nesting depths), we
    need to reassociate `seq` trees so adjacent CCXs appear as direct
    children of an outer `seq`. This is the first step: a single
    top-level right-rotation `(a;b);c → a;(b;c)`. -/

/-- Single top-level right-rotation: turns `seq (seq a b) c` into
    `seq a (seq b c)`. All other shapes pass through unchanged. -/
def assoc_right_step : Gate → Gate
  | seq (seq a b) c => seq a (seq b c)
  | g => g

/-- The rotation preserves T-count exactly. -/
theorem tcount_assoc_right_step (g : Gate) :
    tcount (assoc_right_step g) = tcount g := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | seq _ _ => simp [assoc_right_step, tcount]; omega
    | _ => rfl

/-- The rotation preserves gate count exactly. -/
theorem gcount_assoc_right_step (g : Gate) :
    gcount (assoc_right_step g) = gcount g := by
  cases g with
  | I => rfl
  | X _ => rfl
  | CX _ _ => rfl
  | CCX _ _ _ => rfl
  | seq g₁ g₂ =>
    cases g₁ with
    | seq _ _ => simp [assoc_right_step, gcount]; omega
    | _ => rfl

/-- Smoke: rotating `seq (seq A B) C` gives `seq A (seq B C)`. -/
example (a b c : Nat) (q : Nat) :
    assoc_right_step (seq (seq (CCX a b c) (CCX a b c)) (X q))
      = seq (CCX a b c) (seq (CCX a b c) (X q)) := rfl

/-- Smoke: rotating a non-left-leaning seq is a no-op. -/
example (q1 q2 : Nat) : assoc_right_step (seq (X q1) (X q2)) = seq (X q1) (X q2) :=
  rfl

/-- Nat-fueled iteration of `assoc_right_step` at the top level. With
    enough fuel, the outer seq tree becomes right-leaning. -/
def assoc_right_iter : Nat → Gate → Gate
  | 0, g => g
  | n + 1, g => assoc_right_iter n (assoc_right_step g)

/-- Iterating rotations preserves T-count exactly. Induction on fuel +
    each step's preservation. -/
theorem tcount_assoc_right_iter (n : Nat) (g : Gate) :
    tcount (assoc_right_iter n g) = tcount g := by
  induction n generalizing g with
  | zero => rfl
  | succ k ih =>
    show tcount (assoc_right_iter k (assoc_right_step g)) = tcount g
    rw [ih, tcount_assoc_right_step]

/-- Same exact preservation for gate count. -/
theorem gcount_assoc_right_iter (n : Nat) (g : Gate) :
    gcount (assoc_right_iter n g) = gcount g := by
  induction n generalizing g with
  | zero => rfl
  | succ k ih =>
    show gcount (assoc_right_iter k (assoc_right_step g)) = gcount g
    rw [ih, gcount_assoc_right_step]

end FormalRV.BQAlgo
