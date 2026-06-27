/-
  FormalRV.Shor.GidneyInPlace.E2RunwayShorClosure — Route B′ step 2 (discharge): the constructible
  `idealResidueFamily` satisfies the canonical capstone's residue-oracle hypotheses.
  ════════════════════════════════════════════════════════════════════════════

  `E2RunwayShorCanonical.gidney_inplace_coset_shor_succeeds_unconditional_canonical` takes the WEAKENED
  residue hypotheses `hf_res_can` (canonical multiply) and `hf_res_pres` (canonical preservation).
  Here we discharge `hf_res_can` for the concrete exact multiplier
  `IdealResidueOracle.idealResidueFamily` (with the squared-power table `mult k = a^(2^(revIndex m k)) % N`),
  by reading off the matrix entry of `uc_eval(family i)` from its `MultiplyCircuitProperty` (`.mmi`) via
  `Framework.mul_basis_vector_apply`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.Capstone.IdealResidueOracle
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayShorCanonical

namespace FormalRV.Shor.GidneyInPlace.E2RunwayShorClosure

open FormalRV.Framework (basis_vector mul_basis_vector_apply uc_eval_unitary_of_wellTyped
  kron_vec kron_vec_combine kron_vec_apply_combine qpe_phase_state)
open FormalRV.Shor.GidneyInPlace.IdealResidueOracle (idealResidueFamily)
open FormalRV.Shor.GidneyInPlace.ControlOracleLift (workMat)
open FormalRV.Shor.GidneyInPlace.InPlaceCosetGate (cosetAnc)
open FormalRV.Shor.GidneyInPlace.ControlStageBridge (workDim_eq cast_jointIdx_eq_combine)
open FormalRV.BQAlgo.MultiplierInstances (modInv modInv_spec)
open FormalRV.Shor.CosetMarginalShorBound (shorDvd)
open FormalRV.SQIRPort.ApproxTransfer (jointIdx)
open FormalRV.SQIRPort (revIndex Shor_final_state Shor_final_state_lsb QState ModMulImpl uc_well_typed
  modmult_eigenstate_combined modmult_eigenstate_combined_as_sum shor_orbit_state character_vector
  Shor_final_state_lsb_eq_shor_orbit_state)

/-- **Step 2a — `hf_res_can` for the constructible ideal residue family.**  With the squared-power
    table `mult k = a^(2^(revIndex m k)) % N`, the exact multiplier family `idealResidueFamily`
    realises the canonical residue layout multiply on every canonical column: the `workMat` entry at a
    canonical column `q` (residue `z = q.val/2^anc`) is `1` exactly at row `((mult k · z) % N)·2^anc`,
    else `0`.  Read off `uc_eval(family (revIndex m k))`'s matrix entry from `.mmi`
    (`MultiplyCircuitProperty`) via `mul_basis_vector_apply`. -/
theorem idealResidue_hf_res_can (w bits N a ainv0 : Nat)
    (hw2 : 2 ≤ w) (hb1 : 1 ≤ bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) (m kstep : Nat)
    (p q : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))
    (hq : q.val % 2 ^ (cosetAnc w bits) = 0 ∧ q.val / 2 ^ (cosetAnc w bits) < N) :
    workMat m bits (cosetAnc w bits) kstep
        (idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).family p q
      = if p.val = ((a ^ (2 ^ (revIndex m kstep)) % N * (q.val / 2 ^ (cosetAnc w bits))) % N)
            * 2 ^ (cosetAnc w bits)
          then 1 else 0 := by
  have hzN : q.val / 2 ^ (cosetAnc w bits) < N := hq.2
  have hqval : q.val = q.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits) :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq.1)).symm
  have hzlt : q.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits)
      < 2 ^ (bits + cosetAnc w bits) :=
    lt_of_eq_of_lt hqval.symm (lt_of_lt_of_eq q.isLt (workDim_eq m bits (cosetAnc w bits)))
  have hmcp := (idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).mmi (revIndex m kstep)
    (q.val / 2 ^ (cosetAnc w bits)) hzN
  unfold workMat
  have hcastq : (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q
        : Fin (2 ^ (bits + cosetAnc w bits)))
      = (⟨q.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits), hzlt⟩
          : Fin (2 ^ (bits + cosetAnc w bits))) := Fin.ext hqval
  rw [hcastq]
  rw [show FormalRV.Framework.uc_eval
            ((idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).family (revIndex m kstep))
            (Fin.cast (workDim_eq m bits (cosetAnc w bits)) p)
            ⟨q.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits), hzlt⟩
          = (FormalRV.SQIRPort.uc_eval
              ((idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).family (revIndex m kstep))
              (FormalRV.SQIRPort.basis_vector (2 ^ (bits + cosetAnc w bits))
                (q.val / 2 ^ (cosetAnc w bits) * 2 ^ (cosetAnc w bits))))
              (Fin.cast (workDim_eq m bits (cosetAnc w bits)) p) 0 from
        (mul_basis_vector_apply _ _ hzlt _).symm]
  have hmod : a ^ (2 ^ (revIndex m kstep)) * (q.val / 2 ^ (cosetAnc w bits)) % N
      = a ^ (2 ^ (revIndex m kstep)) % N * (q.val / 2 ^ (cosetAnc w bits)) % N := by
    conv_rhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [hmcp]
  simp only [FormalRV.SQIRPort.basis_vector, FormalRV.Framework.basis_vector, Fin.coe_cast, hmod]

/-- **Step 2b — `hf_res_pres` for the constructible ideal residue family.**  A non-canonical column
    has zero weight on a canonical row: `uc_eval(family i)` is unitary, and the canonical row `p`'s
    single `1` sits at the preimage-residue column `z₀` (via `.mmi`/MCP); column-orthogonality
    (`(uc_eval)ᴴ·uc_eval = 1`) forces every other entry in that row — in particular the non-canonical
    column `q` — to vanish. -/
theorem idealResidue_hf_res_pres (w bits N a ainv0 : Nat)
    (hw2 : 2 ≤ w) (hb1 : 1 ≤ bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1) (m kstep : Nat)
    (p q : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))
    (hp : p.val % 2 ^ (cosetAnc w bits) = 0 ∧ p.val / 2 ^ (cosetAnc w bits) < N)
    (hq : ¬ (q.val % 2 ^ (cosetAnc w bits) = 0 ∧ q.val / 2 ^ (cosetAnc w bits) < N)) :
    workMat m bits (cosetAnc w bits) kstep
        (idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).family p q = 0 := by
  set fam := idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0
  set i := revIndex m kstep
  have hN_pos : 0 < N := by omega
  have hNle : N ≤ 2 ^ bits := by omega
  have hpmod : p.val % 2 ^ (cosetAnc w bits) = 0 := hp.1
  have hpN : p.val / 2 ^ (cosetAnc w bits) < N := hp.2
  set p' := p.val / 2 ^ (cosetAnc w bits)
  have hpval : p.val = p' * 2 ^ (cosetAnc w bits) :=
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpmod)).symm
  -- Invertibility of a^(2^i) mod N
  have h_pow_inv : (a ^ (2 ^ i) * ainv0 ^ (2 ^ i)) % N = 1 := by
    rw [Nat.mul_mod]; exact FormalRV.BQAlgo.mul_pow_mod_one a ainv0 N (2 ^ i) hN1 h_inv0
  obtain ⟨_, h_modinv_eq⟩ := modInv_spec N (a ^ (2 ^ i)) hN_pos ⟨ainv0 ^ (2 ^ i), h_pow_inv⟩
  -- Preimage z₀
  set z₀ := modInv N (a ^ (2 ^ i)) * p' % N
  have hz₀_lt : z₀ < N := Nat.mod_lt _ hN_pos
  -- a^(2^i) * z₀ % N = p'
  have haz₀_eq : a ^ (2 ^ i) * z₀ % N = p' := by
    show a ^ (2 ^ i) * (modInv N (a ^ (2 ^ i)) * p' % N) % N = p'
    rw [Nat.mul_mod (a ^ _), Nat.mod_mod, ← Nat.mul_mod,
        show a ^ (2 ^ i) * (modInv N (a ^ (2 ^ i)) * p') =
             a ^ (2 ^ i) * modInv N (a ^ (2 ^ i)) * p' from by ring,
        Nat.mul_mod, h_modinv_eq, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hpN]
  -- Bound on z₀ * 2^anc
  have hz₀anc_lt : z₀ * 2 ^ (cosetAnc w bits) < 2 ^ (bits + cosetAnc w bits) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_le' (lt_of_lt_of_le hz₀_lt hNle)
      (le_refl _) (Nat.two_pow_pos _)
  -- MCP for preimage column
  have hmcp := fam.mmi i z₀ hz₀_lt
  -- Matrix M
  set M := FormalRV.Framework.uc_eval (fam.family i) with hM_def
  -- Column formula: M row ⟨z₀*2^anc⟩ = if row.val = p.val then 1 else 0
  have hcol : ∀ row : Fin (2 ^ (bits + cosetAnc w bits)),
      M row ⟨z₀ * 2 ^ (cosetAnc w bits), hz₀anc_lt⟩ = if row.val = p.val then 1 else 0 := by
    intro row
    rw [show M row ⟨z₀ * 2 ^ (cosetAnc w bits), hz₀anc_lt⟩
          = (M * FormalRV.Framework.basis_vector (2 ^ (bits + cosetAnc w bits))
              (z₀ * 2 ^ (cosetAnc w bits))) row 0 from
        (mul_basis_vector_apply M _ hz₀anc_lt row).symm]
    change (FormalRV.SQIRPort.uc_eval (fam.family i)
        (FormalRV.SQIRPort.basis_vector (2 ^ (bits + cosetAnc w bits))
          (z₀ * 2 ^ (cosetAnc w bits)))) row 0 = _
    rw [hmcp]
    simp only [FormalRV.SQIRPort.basis_vector, FormalRV.Framework.basis_vector]
    rw [haz₀_eq, ← hpval]
  -- Unitarity
  have hunitary : M.conjTranspose * M = 1 :=
    hM_def ▸ uc_eval_unitary_of_wellTyped (fam.family i) (fam.wellTyped i)
  -- q is not the z₀ column
  have hq_ne : (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q).val ≠ z₀ * 2 ^ (cosetAnc w bits) := by
    intro heq
    apply hq
    -- Fin.cast does not change val: (Fin.cast h q).val = q.val
    have hqval : q.val = z₀ * 2 ^ (cosetAnc w bits) := heq
    exact ⟨by rw [hqval]; exact Nat.mul_mod_left _ _,
           by rw [hqval, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; exact hz₀_lt⟩
  -- (Mᴴ*M)(cast q, z₀*2^anc) = 0
  have hunitary_entry :
      (M.conjTranspose * M) (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q)
        ⟨z₀ * 2 ^ (cosetAnc w bits), hz₀anc_lt⟩ = 0 := by
    rw [hunitary, Matrix.one_apply, if_neg (Fin.ne_of_val_ne hq_ne)]
  rw [Matrix.mul_apply] at hunitary_entry
  simp_rw [Matrix.conjTranspose_apply, hcol] at hunitary_entry
  -- hunitary_entry : ∑ row, star(M row (cast q)) * (if row.val = p.val then 1 else 0) = 0
  -- Extract p
  have hpcast_lt : p.val < 2 ^ (bits + cosetAnc w bits) :=
    lt_of_lt_of_eq p.isLt (workDim_eq m bits (cosetAnc w bits))
  set pcast : Fin (2 ^ (bits + cosetAnc w bits)) := ⟨p.val, hpcast_lt⟩
  -- The sum collapses to star(M pcast (cast q)) = 0
  have hstar_zero : star (M pcast (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q)) = 0 := by
    have hcollapse :
        ∑ row : Fin (2 ^ (bits + cosetAnc w bits)),
          star (M row (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q)) *
            (if row.val = p.val then (1 : ℂ) else 0)
        = star (M pcast (Fin.cast (workDim_eq m bits (cosetAnc w bits)) q)) := by
      rw [Finset.sum_eq_single pcast]
      · simp [pcast]
      · intro row _ hrow_ne; rw [if_neg (fun h => hrow_ne (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hcollapse]; exact hunitary_entry
  -- M pcast (cast q) = 0
  rw [star_eq_zero] at hstar_zero
  -- workMat unfolds to M (cast p) (cast q) = M pcast (cast q) = 0
  unfold workMat
  rw [show Fin.cast (workDim_eq m bits (cosetAnc w bits)) p = pcast from Fin.ext rfl]
  exact hstar_zero

/-- **Step 2c — `hsupp_res` for the constructible ideal residue family.**  The residue Shor final
    state vanishes at every non-canonical data position: for a `ModMulImpl` family the final state is
    `QState.cast (shor_orbit_state …)`, whose data factor is `modmult_eigenstate_combined` — a
    superposition over `{a^j%N · 2^anc}`, all canonical — so it is `0` at any non-canonical index. -/
theorem idealResidue_hsupp_res (w bits N a ainv0 r m : Nat)
    (hw2 : 2 ≤ w) (hb1 : 1 ≤ bits) (hN1 : 1 < N) (hN2 : 2 * N ≤ 2 ^ bits)
    (h_inv0 : a * ainv0 % N = 1)
    (h_basic : FormalRV.SQIRPort.BasicSetting a r N m bits)
    (x : Fin (2 ^ m))
    (b : Fin ((2 ^ m * 2 ^ bits * 2 ^ (cosetAnc w bits)) / 2 ^ m))
    (hb : ¬ (b.val % 2 ^ (cosetAnc w bits) = 0 ∧ b.val / 2 ^ (cosetAnc w bits) < N)) :
    FormalRV.SQIRPort.Shor_final_state m bits (cosetAnc w bits)
        (idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0).family
        (jointIdx (shorDvd m bits (cosetAnc w bits)) x b) 0 = 0 := by
  -- Abbreviate
  set fam := idealResidueFamily w bits N a ainv0 hw2 hb1 hN1 hN2 h_inv0 with hfam_def
  -- Extract BasicSetting components
  obtain ⟨⟨h_a_pos, h_a_lt⟩, h_ord, h_m_bounds, h_n_bounds⟩ := h_basic
  obtain ⟨h_r_pos, h_arN, h_min⟩ := h_ord
  have h_N_pos : 0 < N := by omega
  have h_N_lt : N ≤ 2 ^ bits := by omega
  have hm : 0 < m := by
    by_contra hm0; push Not at hm0; interval_cases m; simp at h_m_bounds; omega
  have hmanc : 0 < m + (bits + cosetAnc w bits) := by omega
  -- ModMulImpl and wellTyped for the family
  have h_mmi : ModMulImpl a N bits (cosetAnc w bits) fam.family := fam.mmi
  have h_wt : ∀ i, uc_well_typed (fam.family i) := fam.wellTyped
  -- Step 1: Shor_final_state = QState.cast ... (shor_orbit_state ...)
  have h_state_eq : Shor_final_state m bits (cosetAnc w bits) fam.family
      = QState.cast (by rw [pow_add, pow_add, mul_assoc])
          (shor_orbit_state a r N m bits (cosetAnc w bits)) := by
    show Shor_final_state_lsb m bits (cosetAnc w bits) fam.family
        = QState.cast _ (shor_orbit_state a r N m bits (cosetAnc w bits))
    exact Shor_final_state_lsb_eq_shor_orbit_state a r N m bits (cosetAnc w bits) hmanc hm
      h_r_pos h_arN h_min hN1 h_N_lt h_N_pos fam.family h_mmi
      (fun i _ => h_wt i)
  -- Step 2: read the state at jointIdx x b using QState.cast definition
  rw [h_state_eq]
  -- QState.cast h s idx 0 = s (Fin.cast h.symm idx) 0
  simp only [QState.cast]
  -- Now goal: shor_orbit_state ... (Fin.cast _ (jointIdx ... x b)) 0 = 0
  -- Step 3: the cast of jointIdx equals kron_vec_combine x (Fin.cast workDim_eq b)
  -- The cast used in QState.cast is (by rw [...]).symm : 2^m * ... = 2^(m+(...))
  -- = dim_assoc_eq m bits (cosetAnc w bits)
  conv_lhs =>
    rw [show Fin.cast (by rw [pow_add, pow_add, mul_assoc] : 2 ^ (m + (bits + cosetAnc w bits)) = _).symm
            (jointIdx (shorDvd m bits (cosetAnc w bits)) x b)
        = kron_vec_combine x (Fin.cast (workDim_eq m bits (cosetAnc w bits)) b) from
      cast_jointIdx_eq_combine m bits (cosetAnc w bits) x b]
  -- Step 4: unfold shor_orbit_state and evaluate at combined index
  simp only [shor_orbit_state, Matrix.sum_apply, kron_vec_apply_combine]
  -- Step 5: each summand has modmult_eigenstate_combined ... b_cast 0 = 0
  have h_mec_zero : ∀ k : Fin r,
      modmult_eigenstate_combined a r N bits (cosetAnc w bits) k
        (Fin.cast (workDim_eq m bits (cosetAnc w bits)) b) 0 = 0 := by
    intro k
    rw [modmult_eigenstate_combined_as_sum, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.smul_apply, smul_eq_mul]
    -- basis_vector evaluated at (Fin.cast ... b).val = b.val
    have hbval : (Fin.cast (workDim_eq m bits (cosetAnc w bits)) b).val = b.val := rfl
    -- a^j.val % N * 2^anc IS canonical
    have hcan : (a ^ j.val % N * 2 ^ (cosetAnc w bits)) % 2 ^ (cosetAnc w bits) = 0 ∧
                (a ^ j.val % N * 2 ^ (cosetAnc w bits)) / 2 ^ (cosetAnc w bits) < N := by
      exact ⟨Nat.mul_mod_left _ _, by
        rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
        exact Nat.mod_lt _ h_N_pos⟩
    -- b is not canonical, so b.val ≠ a^j.val % N * 2^anc
    have hne : b.val ≠ a ^ j.val % N * 2 ^ (cosetAnc w bits) := by
      intro heq
      apply hb
      exact ⟨by rw [heq]; exact hcan.1, by rw [heq]; exact hcan.2⟩
    rw [FormalRV.Framework.basis_vector, if_neg (by simpa [hbval] using hne)]
    ring
  simp_rw [h_mec_zero, mul_zero, Finset.sum_const_zero, mul_zero]
