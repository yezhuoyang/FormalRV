/-
  FormalRV.Shor.CFS.MaskedAmplitude — T6: the masked-state amplitude identity (Gidney 2025
  eq:max-infidelity, main.tex line ~498–504) on ACTUAL CONSTRUCTED masked states, discharging the
  overlap hypothesis the abstract `masked_fidelity` had to assume.

  ## What this closes

  `ApproxPeriodFinding.lean` already proved the masked-state machinery for ABSTRACT supports
  `A B : Finset (Fin d)`:
    * `unifSuper W A`   — the actual uniform-superposition vector (amplitude `1/√W` on `A`);
    * `unifSuper_inner` — the amplitude identity `⟨u_A|u_B⟩ = |A ∩ B|/W` (proven on the real vectors);
    * `window_overlap_card`, `infidelity_ratio_bound` — the combinatorial / quantitative core.
  But its `masked_fidelity` still took the overlap `(A ∩ B).card = W − d` as a HYPOTHESIS over
  abstract `A, B`.  The paper's actual `|ψ₁⟩` (ideal) and `|ψ̃₁⟩` (approximate) are uniform
  superpositions over two width-`W` integer windows offset by the deviation `d` (line 498) — concrete
  objects, whose overlap is a COMPUTED fact, not an assumption.

  This file builds exactly those concrete window states and discharges the assumption:
    * `winFin D a W`              — the concrete support `{x : Fin D | a ≤ x < a + W}`;
    * `winFin_card`               — `= W` when the window fits (`a + W ≤ D`);
    * `winFin_inter_card`         — the overlap `|[a,a+W) ∩ [a+d, a+d+W)| = W − d` (COMPUTED, `d ≤ W`);
    * `maskedIdeal` / `maskedApprox` — the two concrete masked states `Fin D → ℂ`;
    * `maskedState_normalized`    — they are genuine UNIT vectors `⟨ψ|ψ⟩ = 1`;
    * `masked_amplitude_identity` — `⟨ψ₁|ψ̃₁⟩ = (W − d)/W` on the REAL states, NO overlap hypothesis;
    * `masked_amplitude_abs`      — the paper's literal `|⟨ψ₁|ψ̃₁⟩| = (W − d)/W`;
    * `masked_fidelity_ge`        — the overlap deficit bound `(W − d)/W ≥ 1 − ε/S` (paper line 499–500);
    * `masked_infidelity_sq_le`   — the LITERAL squared eq:max-infidelity `1 − |⟨⟩|² ≤ 2·(ε/S)` (honest
                                    constant: the paper's boxed `ε/S` is the linear deficit; the squared
                                    infidelity rigorously carries a benign factor ≤ 2 — flagged, not faked).

  The only inputs are the genuine geometric/algorithmic preconditions (the window fits `a + W ≤ D`,
  the offset `d ≤ W` is below the mask width, the deviation `d ≤ N·ε` of line 498, and the mask is
  wide enough `S·N ≤ W`).  No conclusion is assumed.  What remains (T5) is the CIRCUIT that PREPARES
  these specific window states — this file establishes that, once prepared, the overlap IS the
  paper's `(W − d)/W` fidelity, on real syntactic vectors.
-/
import FormalRV.Shor.CFS.ApproxPeriodFinding

namespace FormalRV.CFS

open scoped BigOperators ComplexConjugate

/-! ## §1. The concrete window support and its (computed) overlap. -/

/-- The concrete index window `{x : Fin D | a ≤ x < a + W}` — the support of a masked output state. -/
def winFin (D a W : ℕ) : Finset (Fin D) :=
  Finset.univ.filter (fun x : Fin D => a ≤ x.val ∧ x.val < a + W)

@[simp] theorem mem_winFin {D a W : ℕ} (x : Fin D) :
    x ∈ winFin D a W ↔ a ≤ x.val ∧ x.val < a + W := by
  simp [winFin]

/-- A window that fits in `[0, D)` has exactly `W` elements (bijection with `Finset.Ico a (a+W)`). -/
theorem winFin_card {D a W : ℕ} (h : a + W ≤ D) : (winFin D a W).card = W := by
  have heq : winFin D a W
      = (Finset.Ico a (a + W)).attachFin (fun m hm => by rw [Finset.mem_Ico] at hm; omega) := by
    ext x; simp only [mem_winFin, Finset.mem_attachFin, Finset.mem_Ico]
  rw [heq, Finset.card_attachFin, Nat.card_Ico]
  omega

/-- Two equal-width windows offset by `d ≤ W` intersect in the window `[a+d, a+W) = [a+d, (a+d)+(W−d))`. -/
theorem winFin_inter {D a d W : ℕ} (hd : d ≤ W) :
    winFin D a W ∩ winFin D (a + d) W = winFin D (a + d) (W - d) := by
  ext x
  simp only [Finset.mem_inter, mem_winFin]
  omega

/-- **The masked overlap is COMPUTED, not assumed**: `|[a,a+W) ∩ [a+d, a+d+W)| = W − d`
    (the discharge of `masked_fidelity`'s `hov`). -/
theorem winFin_inter_card {D a d W : ℕ} (hd : d ≤ W) (hfit : a + W ≤ D) :
    (winFin D a W ∩ winFin D (a + d) W).card = W - d := by
  rw [winFin_inter hd, winFin_card (by omega)]

/-! ## §2. The two concrete masked states and the amplitude identity. -/

/-- The **ideal** masked output state: uniform superposition over the window `[a, a+W)`. -/
noncomputable def maskedIdeal (D a W : ℕ) : Fin D → ℂ := unifSuper W (winFin D a W)

/-- The **approximate** masked output state: uniform superposition over the deviation-offset window
    `[a+d, a+d+W)` (offset by the modular deviation `d`, line 498). -/
noncomputable def maskedApprox (D a d W : ℕ) : Fin D → ℂ := unifSuper W (winFin D (a + d) W)

/-- **Both masked states are genuine unit vectors** (`⟨ψ|ψ⟩ = 1`): the amplitude identity on the
    self-overlap (`A ∩ A = A`, `|A| = W`) gives `W/W = 1`.  So the overlap below really is a fidelity. -/
theorem maskedState_normalized {D : ℕ} (a W : ℕ) (hW : 0 < W) (hfit : a + W ≤ D) :
    (∑ x, conj (maskedIdeal D a W x) * maskedIdeal D a W x) = 1 := by
  unfold maskedIdeal
  rw [unifSuper_inner W hW (winFin D a W) (winFin D a W), Finset.inter_self, winFin_card hfit,
      div_self (by exact_mod_cast (show W ≠ 0 by omega))]

/-- **T6 — the masked-state amplitude identity on REAL states** (Gidney 2025 eq:max-infidelity).
    The overlap of the concrete ideal and approximate masked states equals `(W − d)/W` — the paper's
    conditioned fidelity — with NO assumed overlap: the overlap is the COMPUTED `winFin_inter_card`.
    This is the discharge of the abstract `masked_fidelity`'s `hov` hypothesis. -/
theorem masked_amplitude_identity {D : ℕ} (a d W : ℕ) (hW : 0 < W) (hd : d ≤ W) (hfit : a + W ≤ D) :
    (∑ x, conj (maskedIdeal D a W x) * maskedApprox D a d W x) = ((W - d : ℕ) : ℂ) / W := by
  unfold maskedIdeal maskedApprox
  rw [unifSuper_inner W hW (winFin D a W) (winFin D (a + d) W), winFin_inter_card hd hfit]

/-- The paper's literal magnitude form `|⟨ψ₁|ψ̃₁⟩| = (W − d)/W` (the overlap is real and nonnegative). -/
theorem masked_amplitude_abs {D : ℕ} (a d W : ℕ) (hW : 0 < W) (hd : d ≤ W) (hfit : a + W ≤ D) :
    ‖∑ x, conj (maskedIdeal D a W x) * maskedApprox D a d W x‖ = ((W - d : ℕ) : ℝ) / W := by
  rw [masked_amplitude_identity a d W hW hd hfit, norm_div, Complex.norm_natCast,
      Complex.norm_natCast]

/-! ## §3. The eq:max-infidelity fidelity bound, fully discharged. -/

/-- **eq:max-infidelity, on real states (T6 headline).**  The conditioned fidelity of the concrete
    masked states is `(W − d)/W ≥ 1 − ε/S`, i.e. infidelity `≤ ε/S` — combining the COMPUTED overlap
    identity `(W − d)/W` (`masked_amplitude_identity`) with `infidelity_ratio_bound` (`d/W ≤ ε/S`).
    The offset `d ≤ N·ε` is the deviation (line 498), the mask width `W ≥ S·N`; no overlap assumed. -/
theorem masked_fidelity_ge {D : ℕ} (a d W N S eps : ℕ) (hd : d ≤ W) (_hfit : a + W ≤ D)
    (hN : 0 < N) (hS : 0 < S) (hdev : d ≤ N * eps) (hmask : S * N ≤ W) :
    (1 : ℚ) - (eps : ℚ) / S ≤ ((W - d : ℕ) : ℚ) / W := by
  have hov : (d : ℚ) / W ≤ (eps : ℚ) / S := infidelity_ratio_bound N S eps d W hN hS hdev hmask
  have hWpos : (0 : ℚ) < W := by
    have : (0 : ℚ) < ((S * N : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos hS hN
    exact lt_of_lt_of_le this (by exact_mod_cast hmask)
  have hsub : ((W - d : ℕ) : ℚ) = (W : ℚ) - d := by rw [Nat.cast_sub hd]
  rw [hsub, sub_div, div_self (ne_of_gt hWpos)]
  linarith [hov]

/-- **The literal squared infidelity** `1 − |⟨ψ₁|ψ̃₁⟩|² ≤ 2·(ε/S)` on the real states (the rigorous
    form of the paper's boxed eq:max-infidelity).  HONEST NOTE: the paper writes `≤ ε/S` (line 504),
    but that is the *linear* overlap deficit `1 − |⟨⟩|` it derives at line 499–500; the *squared*
    infidelity `1 − |⟨⟩|²  = (d/W)(2 − d/W)` rigorously carries a factor `≤ 2` (the standard
    linearized-infidelity looseness — benign, since the success analysis only needs the deficit small).
    We prove the honest constant `2·(ε/S)`, not the paper's dropped-factor `ε/S`. -/
theorem masked_infidelity_sq_le {D : ℕ} (a d W N S eps : ℕ) (hd : d ≤ W) (hfit : a + W ≤ D)
    (hN : 0 < N) (hS : 0 < S) (hdev : d ≤ N * eps) (hmask : S * N ≤ W) :
    (1 : ℚ) - (((W - d : ℕ) : ℚ) / W) ^ 2 ≤ 2 * ((eps : ℚ) / S) := by
  have hWpos : (0 : ℚ) < W := by
    have : (0 : ℚ) < ((S * N : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos hS hN
    exact lt_of_lt_of_le this (by exact_mod_cast hmask)
  have hx : (1 : ℚ) - (eps : ℚ) / S ≤ ((W - d : ℕ) : ℚ) / W :=
    masked_fidelity_ge a d W N S eps hd hfit hN hS hdev hmask
  have hx0 : (0 : ℚ) ≤ ((W - d : ℕ) : ℚ) / W := by positivity
  have hx1 : ((W - d : ℕ) : ℚ) / W ≤ 1 := by
    rw [div_le_one hWpos]; exact_mod_cast Nat.sub_le W d
  nlinarith [hx, hx0, hx1, sq_nonneg (1 - ((W - d : ℕ) : ℚ) / W)]

/-! ## The T6 masked-amplitude theorems pass the VERIFIER gate (axiom-clean, no overlap hypothesis). -/

#verify_clean winFin_card
#verify_clean winFin_inter_card
#verify_clean maskedState_normalized
#verify_clean masked_amplitude_identity
#verify_clean masked_amplitude_abs
#verify_clean masked_fidelity_ge
#verify_clean masked_infidelity_sq_le

end FormalRV.CFS
