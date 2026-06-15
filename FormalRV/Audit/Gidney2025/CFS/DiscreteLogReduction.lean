/-
  FormalRV.Audit.Gidney2025.CFS.DiscreteLogReduction — the DISCRETE-LOG REDUCTION lemma that
  DEFINES the Gidney 2025 (arXiv:2505.15917) OPTIMIZED residue arithmetic (main.tex
  §"Arithmetic Optimizations", L879-929).

  ## What the paper's optimization does
  The naive per-prime residue `V_p = (∏_{k<m} M_k^{e_k}) mod p` is computed by controlled
  MULTIPLICATIONS (the verified `residueAccumulate` of `ResidueCircuit.lean`).  The optimized
  algorithm instead:
    1. precomputes discrete logs `D_k = dlog(g_p, M_k) mod p`, i.e. `M_k ≡ g_p^{D_k} (mod p)`;
    2. accumulates `S_p = ∑_{k<m} D_k · e_k` by controlled ADDITIONS (cheap measured adders);
    3. computes `V_p = g_p^{S_p mod (p−1)} mod p` by ONE small windowed modexp.
  The claim — proved here at the VALUE level — is that this equals the controlled-multiply product.

  ## Deliverables (all axiom-clean, `#verify_clean`-gated)
    * `pow_mod_sub_one`  — Fermat exponent reduction: for `p` prime and `p ∤ gp`,
      `gp^S % p = gp^(S % (p−1)) % p`  (via `ZMod.pow_card_sub_one_eq_one`).
    * `prod_dlog`        — in `ZMod p`, `∏_{k<m} (M_k)^{e_k} = gp^(∑_{k<m} D_k · e_k)` given the dlog
      relation `M_k ≡ gp^{D_k}`  (via `Finset.prod_pow_eq_pow_sum`).
    * `modexpProd_eq_prod` — the recursive `modexpProd` equals the `Finset.range` product.
    * `dlog_reduction`   — **THE HEADLINE**: `gp^(S_p mod (p−1)) % p = modexpProd g N m e % p`.
    * `dlog_reduction_eq_residueAccumulate` — **THE BRIDGE**: chaining `residueAccumulate_eq`,
      `gp^(S_p mod (p−1)) % p = residueAccumulate g N p e m` — the optimized addition-based
      arithmetic computes EXACTLY the verified controlled-multiply residue.

  ## Scope (honest)
  This closes the Gidney2025 "dlog reduction" gap at the VALUE level: the controlled-additions-of-
  dlogs form equals the verified `residueAccumulate`.  The controlled-ADDER CIRCUIT that physically
  realises the additions is the measured Gidney adder (`FormalRV.Arithmetic.MeasuredAdder`,
  separate).  `phaseup` and the 2.5n modular adder remain the other two Gidney2025 gaps.
-/
import FormalRV.Audit.Gidney2025.CFS.ResidueCircuit
import FormalRV.Verifier.ProofGate

namespace FormalRV.CFS

open scoped BigOperators

/-! ## §1. Fermat exponent reduction (the `g_p^{S} = g_p^{S mod (p−1)}` step). -/

/-- **Fermat exponent reduction.**  For `p` prime and `gp` not divisible by `p` (`(gp : ZMod p) ≠ 0`),
    the exponent of `gp` may be reduced modulo `p − 1` without changing the residue:
    `gp ^ S % p = gp ^ (S % (p − 1)) % p`.

    Proof: in the field `ZMod p`, `(gp)^(p−1) = 1` (`ZMod.pow_card_sub_one_eq_one`); writing
    `S = (p−1)·(S/(p−1)) + S%(p−1)` (`Nat.div_add_mod`) gives `gp^S = (gp^(p−1))^… · gp^(S%(p−1))
    = gp^(S%(p−1))`; cast back to `% p` via `ZMod.natCast_eq_natCast_iff`. -/
theorem pow_mod_sub_one (p gp S : ℕ) (hp : p.Prime) (hgp : ¬ (p ∣ gp)) :
    gp ^ S % p = gp ^ (S % (p - 1)) % p := by
  haveI := Fact.mk hp
  -- The two sides agree in `ZMod p`, then descend to `% p` via the `Nat.ModEq` characterisation.
  have hne : (gp : ZMod p) ≠ 0 := fun h => hgp ((ZMod.natCast_eq_zero_iff gp p).mp h)
  have hcast : ((gp ^ S : ℕ) : ZMod p) = ((gp ^ (S % (p - 1)) : ℕ) : ZMod p) := by
    push_cast
    -- decompose `S = (p−1)·(S/(p−1)) + S%(p−1)`
    conv_lhs => rw [← Nat.div_add_mod S (p - 1)]
    rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow, one_mul]
  -- descend: `↑a = ↑b ↔ a ≡ b [MOD p]`, and `Nat.ModEq` is exactly `a % p = b % p`.
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact hmod

/-! ## §2. The product-of-powers step (`∏ M_k^{e_k} = g_p^{∑ D_k · e_k}` in `ZMod p`). -/

/-- **Product of dlog powers.**  In `ZMod p`, given the discrete-log relation
    `(M_k : ZMod p) = gp ^ (D k)` for every `k < m`, the product of the controlled-multiply factors
    equals a single power of the base:
    `∏_{k<m} (M_k)^{e_k} = gp ^ (∑_{k<m} D_k · e_k)`.

    Proof: rewrite each factor `(M_k)^{e_k} = (gp^{D_k})^{e_k} = gp^{D_k · e_k}`, then collapse the
    product of powers with `Finset.prod_pow_eq_pow_sum`. -/
theorem prod_dlog (g N p m : ℕ) (gp : ℕ) (D : ℕ → ℕ) (e : ℕ)
    (hD : ∀ k, k < m → (Mconst g N k : ZMod p) = (gp : ZMod p) ^ (D k)) :
    (∏ k ∈ Finset.range m, ((Mconst g N k : ZMod p)) ^ bit e k)
      = (gp : ZMod p) ^ (∑ k ∈ Finset.range m, D k * bit e k) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro k hk
  rw [hD k (Finset.mem_range.mp hk), ← pow_mul]

/-! ## §3. `modexpProd` as a `Finset.range` product. -/

/-- The recursive controlled-multiply product equals the `Finset.range` product
    `∏_{k<m} M_k^{e_k}`.  (Small induction matching `modexpProd`'s recursive definition.) -/
theorem modexpProd_eq_prod (g N e : ℕ) :
    ∀ m, modexpProd g N m e = ∏ k ∈ Finset.range m, Mconst g N k ^ bit e k
  | 0 => by simp [modexpProd]
  | m + 1 => by
      rw [Finset.prod_range_succ, ← modexpProd_eq_prod g N e m]
      rfl

/-! ## §4. THE HEADLINE — the discrete-log reduction. -/

/-- **The discrete-log reduction (Gidney 2025 optimized residue arithmetic).**

    Given the discrete-log precomputation `M_k ≡ gp^{D_k} (mod p)` (here `hD`, stated as a `% p`
    equality) and `p` prime with `p ∤ gp`, the optimized addition-based form
    `gp ^ (S_p mod (p−1)) % p`  (with `S_p = ∑_{k<m} D_k · e_k`)
    equals the controlled-multiply product `modexpProd g N m e % p`.

    Chain: (§3) `modexpProd = ∏ M_k^{e_k}`; (§2) that product `= gp^{S_p}` in `ZMod p`;
    (§1) Fermat reduces the exponent to `S_p mod (p−1)`. -/
theorem dlog_reduction (g N p m : ℕ) (hp : p.Prime) (gp : ℕ) (D : ℕ → ℕ) (e : ℕ)
    (hgp : ¬ (p ∣ gp))
    (hD : ∀ k, k < m → Mconst g N k % p = gp ^ (D k) % p) :
    gp ^ ((∑ k ∈ Finset.range m, D k * bit e k) % (p - 1)) % p = modexpProd g N m e % p := by
  haveI := Fact.mk hp
  set S := ∑ k ∈ Finset.range m, D k * bit e k with hS
  -- §1: reduce the exponent back UP first, so both sides are `gp ^ (something) % p` vs the product.
  rw [← pow_mod_sub_one p gp S hp hgp]
  -- Now prove `gp ^ S % p = modexpProd g N m e % p` by descending the `ZMod p` equality.
  -- Convert the `% p`-form hypothesis `hD` into a `ZMod p` equality.
  have hDcast : ∀ k, k < m → (Mconst g N k : ZMod p) = (gp : ZMod p) ^ (D k) := by
    intro k hk
    have h := (ZMod.natCast_eq_natCast_iff (Mconst g N k) (gp ^ (D k)) p).mpr (hD k hk)
    rw [Nat.cast_pow] at h
    exact h
  -- §2 + §3 give the product = gp^S in ZMod p; descend to % p.
  have hcast : ((modexpProd g N m e : ℕ) : ZMod p) = ((gp ^ S : ℕ) : ZMod p) := by
    rw [modexpProd_eq_prod g N e m]
    push_cast
    rw [prod_dlog g N p m gp D e hDcast, hS]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact hmod.symm

/-! ## §5. THE BRIDGE COROLLARY — optimized form = verified `residueAccumulate`. -/

/-- **The value-level bridge.**  Combining the discrete-log reduction with the verified
    controlled-multiply circuit (`residueAccumulate_eq`): the optimized, addition-of-dlogs
    per-prime arithmetic
      `gp ^ ((∑_{k<m} D_k · e_k) mod (p−1)) % p`
    equals EXACTLY the verified controlled-multiply residue `residueAccumulate g N p e m`.

    This is the value-level audit hook that makes Gidney 2025's optimized residue arithmetic
    trustworthy: the cheap controlled-ADD form is provably the same value as the verified
    controlled-MULTIPLY form. -/
theorem dlog_reduction_eq_residueAccumulate (g N p m : ℕ) (hp : p.Prime) (gp : ℕ) (D : ℕ → ℕ)
    (e : ℕ) (hgp : ¬ (p ∣ gp))
    (hD : ∀ k, k < m → Mconst g N k % p = gp ^ (D k) % p) :
    gp ^ ((∑ k ∈ Finset.range m, D k * bit e k) % (p - 1)) % p
      = residueAccumulate g N p e m := by
  rw [dlog_reduction g N p m hp gp D e hgp hD, residueAccumulate_eq g N p e m]

/-! ## §6. The discrete-log reduction passes the VERIFIER gate (sorry-free, axiom-clean). -/

#verify_clean pow_mod_sub_one
#verify_clean prod_dlog
#verify_clean modexpProd_eq_prod
#verify_clean dlog_reduction
#verify_clean dlog_reduction_eq_residueAccumulate

end FormalRV.CFS
