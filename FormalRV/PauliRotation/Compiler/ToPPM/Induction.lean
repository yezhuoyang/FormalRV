/-
  FormalRV.PauliRotation.Compiler.ToPPM.Induction
  ──────────────────────────────────────
  **THE PRESERVATION INDUCTION — support layer.**

  `tensorAmps` builds `ψ ⊗ anc₁ ⊗ … ⊗ anc_k` by structural recursion whose
  widths line up DEFINITIONALLY (`ampsWidth m (a :: as) ≡ ampsWidth (m+1)
  as` — no `Nat.add`-associativity casts anywhere).  The lemmas:

    • linearity of `tensorAmps` (smul),
    • `stmtLow_mono` and `progDenote_tensorAmps` — a low program acts on
      the innermost factor through ALL outer ancilla splits,
    • `extendTrace`/`progDenote_append` — the outcome-trace threading of
      sequential composition,
    • `rotOf_mulVec_tensorHigh`/`seqDenote_tensorHigh` — the ROTATION
      layer's own semantics passes through a split (the data factor of
      the induction composes at the bottom width).
-/
import FormalRV.PauliRotation.Compiler.ToPPM.RotStep

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.BQCode
open Matrix

/-! ## §1. Iterated ancilla splits, cast-free. -/

/-- The width after adjoining one ancilla per listed amplitude. -/
def ampsWidth (m : Nat) : List ℂ → Nat
  | [] => m
  | _ :: as => ampsWidth (m + 1) as

/-- `ψ ⊗ (1, b₁) ⊗ … ⊗ (1, b_k)` with the WIDTH indexed by the skeleton
`skel` alone — so input and output states of the preservation theorem
(same skeleton, different amplitudes) share one type DEFINITIONALLY. -/
noncomputable def stateOver :
    (skel : List ℂ) → (amps : List ℂ) → (m : Nat) → (Fin (2 ^ m) → ℂ)
      → (Fin (2 ^ ampsWidth m skel) → ℂ)
  | [], _, _, ψ => ψ
  | _ :: skel, [], m, ψ => stateOver skel [] (m + 1) (tensorHigh m 1 0 ψ)
  | _ :: skel, b :: bs, m, ψ =>
      stateOver skel bs (m + 1) (tensorHigh m 1 b ψ)

theorem ampsWidth_le (as : List ℂ) : ∀ (m : Nat), m ≤ ampsWidth m as := by
  induction as with
  | nil => intro m; exact Nat.le_refl m
  | cons a as ih =>
      intro m
      exact Nat.le_trans (Nat.le_succ m) (ih (m + 1))

theorem stateOver_smul (skel : List ℂ) :
    ∀ (bs : List ℂ) (m : Nat) (c : ℂ) (ψ : Fin (2 ^ m) → ℂ),
      stateOver skel bs m (c • ψ) = c • stateOver skel bs m ψ := by
  induction skel with
  | nil => intro bs m c ψ; rfl
  | cons a skel ih =>
      intro bs m c ψ
      cases bs with
      | nil =>
          show stateOver skel [] (m + 1) (tensorHigh m 1 0 (c • ψ)) = _
          rw [tensorHigh_vec_smul, ih]
          rfl
      | cons b bs =>
          show stateOver skel bs (m + 1) (tensorHigh m 1 b (c • ψ)) = _
          rw [tensorHigh_vec_smul, ih]
          rfl

/-! ## §2. Low programs act through all outer splits. -/

theorem stmtLow_mono (n n' : Nat) (h : n ≤ n') (st : PPMStmt)
    (hst : stmtLow n st = true) : stmtLow n' st = true := by
  cases st <;>
    simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq] at hst ⊢
  · exact ⟨hst.1, by omega⟩
  · exact ⟨⟨⟨hst.1.1.1, by omega⟩, hst.1.2⟩, by omega⟩
  · exact ⟨⟨⟨⟨⟨⟨⟨hst.1.1.1.1.1.1.1, by omega⟩, hst.1.1.1.1.1.2⟩,
      by omega⟩, hst.1.1.1.2⟩, by omega⟩, hst.1.2⟩, by omega⟩
  · exact ⟨hst.1, by omega⟩
  · exact ⟨⟨⟨hst.1.1.1, by omega⟩, hst.1.2⟩, by omega⟩
  · exact ⟨⟨⟨hst.1.1.1, by omega⟩, hst.1.2⟩, by omega⟩

/-- **A low program acts on the innermost factor through every split.** -/
theorem progDenote_stateOver (skel : List ℂ) :
    ∀ (bs : List ℂ) (m : Nat) (p : PPMProg),
      (∀ st ∈ p, stmtLow m st = true) →
      ∀ (ω : Nat → Bool) (outs : List Bool) (ψ : Fin (2 ^ m) → ℂ),
        (progDenote (ampsWidth m skel) ω outs p).mulVec (stateOver skel bs m ψ)
          = stateOver skel bs m ((progDenote m ω outs p).mulVec ψ) := by
  induction skel with
  | nil => intro bs m p _ ω outs ψ; rfl
  | cons a skel ih =>
      intro bs m p hlow ω outs ψ
      cases bs with
      | nil =>
          show (progDenote (ampsWidth (m + 1) skel) ω outs p).mulVec
              (stateOver skel [] (m + 1) (tensorHigh m 1 0 ψ)) = _
          rw [ih [] (m + 1) p
                (fun st hst => stmtLow_mono m (m + 1) (Nat.le_succ m) st
                  (hlow st hst)) ω outs (tensorHigh m 1 0 ψ),
              progDenote_tensorHigh m ω p outs hlow 1 0 ψ]
          rfl
      | cons b bs =>
          show (progDenote (ampsWidth (m + 1) skel) ω outs p).mulVec
              (stateOver skel bs (m + 1) (tensorHigh m 1 b ψ)) = _
          rw [ih bs (m + 1) p
                (fun st hst => stmtLow_mono m (m + 1) (Nat.le_succ m) st
                  (hlow st hst)) ω outs (tensorHigh m 1 b ψ),
              progDenote_tensorHigh m ω p outs hlow 1 b ψ]
          rfl

/-! ## §3. Trace threading of sequential composition. -/

/-- Extend an outcome trace by `k` fresh samples of `ω`. -/
def extendTrace (ω : Nat → Bool) : List Bool → Nat → List Bool
  | outs, 0 => outs
  | outs, k + 1 => extendTrace ω (outs ++ [ω outs.length]) k

theorem extendTrace_length (ω : Nat → Bool) :
    ∀ (k : Nat) (outs : List Bool),
      (extendTrace ω outs k).length = outs.length + k := by
  intro k
  induction k with
  | zero => intro outs; rfl
  | succ k ih =>
      intro outs
      show (extendTrace ω (outs ++ [ω outs.length]) k).length = _
      rw [ih]
      simp
      omega

/-- **Sequential composition splits with the trace threaded.** -/
theorem progDenote_append' (d : Nat) (ω : Nat → Bool) :
    ∀ (p q : PPMProg) (outs : List Bool),
      progDenote d ω outs (p ++ q)
        = progDenote d ω (extendTrace ω outs (PPMProg.cwidth p)) q
            * progDenote d ω outs p := by
  intro p
  induction p with
  | nil =>
      intro q outs
      show progDenote d ω outs q = _
      rw [show progDenote d ω outs ([] : PPMProg) = 1 from rfl,
          Matrix.mul_one]
      rfl
  | cons st p ih =>
      intro q outs
      show progDenote d ω (outs ++ List.replicate st.binds (ω outs.length))
            (p ++ q) * stmtDenote d outs (ω outs.length) st = _
      rw [ih]
      show _ = progDenote d ω (extendTrace ω outs (st.binds + PPMProg.cwidth p)) q
          * (progDenote d ω (outs ++ List.replicate st.binds (ω outs.length)) p
              * stmtDenote d outs (ω outs.length) st)
      rw [← Matrix.mul_assoc]
      congr 2
      have hble : st.binds ≤ 1 := by
        cases st <;> simp [PPMStmt.binds]
      cases hst : st.binds with
      | zero =>
          rw [show List.replicate 0 (ω outs.length) = ([] : List Bool)
                from rfl,
              List.append_nil, Nat.zero_add]
      | succ b =>
          have hb0 : b = 0 := by omega
          subst hb0
          rw [Nat.add_comm 1 (PPMProg.cwidth p)]
          rfl

/-! ## §4. The rotation layer's semantics passes through a split. -/

theorem rotOf_mulVec_tensorHigh (n : Nat) (θ : ℝ) (P : PauliProduct)
    (hs : sortedStrict P = true) (hw : PauliProduct.width P ≤ n)
    (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ) :
    (rotOf θ (axisMat (n + 1) P)).mulVec (tensorHigh n α β ψ)
      = tensorHigh n α β ((rotOf θ (axisMat n P)).mulVec ψ) := by
  unfold rotOf
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, smul_mulVec, smul_mulVec,
      smul_mulVec, smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      mulVec_axis_tensorHigh' n P hs hw α β ψ, ← tensorHigh_vec_smul,
      ← tensorHigh_vec_smul]
  funext m
  show _ = (if (m : Nat).testBit n then β else α)
      * ((((Real.cos θ : ℂ) • ψ)
          - ((Real.sin θ : ℂ) * Complex.I)
              • ((axisMat n P).mulVec ψ)) (lowBits n m))
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tensorHigh]
  ring

/-- A rotation sequence on data wires passes through a split. -/
theorem seqDenote_tensorHigh (n : Nat) :
    ∀ (rs : List Rot),
      (∀ r ∈ rs, sortedStrict r.axis = true
        ∧ PauliProduct.width r.axis ≤ n) →
      ∀ (α β : ℂ) (ψ : Fin (2 ^ n) → ℂ),
        (seqDenote (n + 1) rs).mulVec (tensorHigh n α β ψ)
          = tensorHigh n α β ((seqDenote n rs).mulVec ψ)
  | [], _, α, β, ψ => by
      show (1 : Matrix _ _ ℂ).mulVec _ = _
      rw [Matrix.one_mulVec]
      show _ = tensorHigh n α β ((1 : Matrix _ _ ℂ).mulVec ψ)
      rw [Matrix.one_mulVec]
  | r :: rs, hyp, α, β, ψ => by
      show (seqDenote (n + 1) rs * Rot.denote (n + 1) r).mulVec _ = _
      rw [← Matrix.mulVec_mulVec,
          show Rot.denote (n + 1) r
            = rotOf r.theta (axisMat (n + 1) r.axis) from rfl,
          rotOf_mulVec_tensorHigh n r.theta r.axis
            (hyp r List.mem_cons_self).1 (hyp r List.mem_cons_self).2 α β ψ,
          seqDenote_tensorHigh n rs
            (fun s hs => hyp s (List.mem_cons_of_mem _ hs)) α β _]
      show _ = tensorHigh n α β
          ((seqDenote n rs * Rot.denote n r).mulVec ψ)
      rw [← Matrix.mulVec_mulVec]
      rfl

/-! ## §5. THE PRESERVATION THEOREM. -/

/-- The ancilla input amplitudes a rotation list consumes (in order). -/
noncomputable def ancAmps : List Rot → List ℂ
  | [] => []
  | r :: rs =>
      (match r.angle with
       | RAngle.piQuarter => [ancInAmp r]
       | RAngle.piEighth  => [ancInAmp r]
       | _ => []) ++ ancAmps rs

/-- The collapsed ancilla amplitudes, branch by branch. -/
noncomputable def ancOutAmps (ω : Nat → Bool) : List Rot → Nat → List ℂ
  | [], _ => []
  | r :: rs, c =>
      (match r.angle with
       | RAngle.piQuarter => [ancOutAmp r (ω c) (ω (c + 1))]
       | RAngle.piEighth  => [ancOutAmp r (ω c) (ω (c + 1))]
       | _ => []) ++ ancOutAmps ω rs (c + rotSlots r)

/-- The total branch scalar of a lowered rotation list. -/
noncomputable def branchScalar (ω : Nat → Bool) : List Rot → Nat → ℂ
  | [], _ => 1
  | r :: rs, c => rotScalar r (ω c) (ω (c + 1)) * branchScalar ω rs (c + rotSlots r)

/-- Sortedness survives appending the fresh top factor. -/
theorem sortedStrict_append_single :
    ∀ (P : PauliProduct) (a : Nat) (k : PKind),
      sortedStrict P = true → (∀ f ∈ P, f.qubit < a) →
      sortedStrict (P ++ [⟨a, k⟩]) = true
  | [], _, _, _, _ => rfl
  | [f], a, k, _, hq => by
      show (decide (f.qubit < a) && true) = true
      simp [hq f List.mem_cons_self]
  | f :: g :: P, a, k, hs, hq => by
      have hs' : sortedStrict (g :: P) = true := sorted_cons_tail hs
      have hfg : f.qubit < g.qubit := by
        have := hs
        simp only [sortedStrict, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      show (decide (f.qubit < g.qubit)
          && sortedStrict ((g :: P) ++ [⟨a, k⟩])) = true
      rw [sortedStrict_append_single (g :: P) a k hs'
            (fun f' hf' => hq f' (List.mem_cons_of_mem _ hf'))]
      simp [hfg]

/-- Width of an appended product. -/
theorem width_append :
    ∀ (P Q : PauliProduct),
      PauliProduct.width (P ++ Q)
        = max (PauliProduct.width P) (PauliProduct.width Q)
  | [], Q => by simp [PauliProduct.width]
  | f :: P, Q => by
      show max (f.qubit + 1) (PauliProduct.width (P ++ Q)) = _
      rw [width_append P Q]
      show _ = max (max (f.qubit + 1) (PauliProduct.width P))
          (PauliProduct.width Q)
      omega

/-- Every qubit of an axis sits below its width. -/
theorem qubit_lt_width :
    ∀ (P : PauliProduct), ∀ f ∈ P, f.qubit < PauliProduct.width P
  | f :: P, g, hg => by
      simp only [PauliProduct.width]
      rcases List.mem_cons.mp hg with h | h
      · subst h
        omega
      · have := qubit_lt_width P g h
        omega

/-- The lowered block's statements are all low for width `m + 1`. -/
theorem lowerRot_low (m c : Nat) (r : Rot)
    (hs : sortedStrict r.axis = true)
    (hw : PauliProduct.width r.axis ≤ m) :
    ∀ st ∈ lowerRot m c r, stmtLow (m + 1) st = true := by
  have hjs : sortedStrict (r.axis ++ [⟨m, .z⟩]) = true :=
    sortedStrict_append_single r.axis m .z hs
      (fun f hf => Nat.lt_of_lt_of_le (qubit_lt_width r.axis f hf) hw)
  have hjw : PauliProduct.width (r.axis ++ [⟨m, .z⟩]) ≤ m + 1 := by
    rw [width_append]
    show max _ (max (m + 1) 0) ≤ _
    omega
  intro st hst
  unfold lowerRot at hst
  cases hang : r.angle <;> rw [hang] at hst
  · simp at hst
  · simp at hst
    subst hst
    simp [stmtLow, hs]
    omega
  · rcases (by cases hneg : r.neg <;> rw [hneg] at hst <;> simp at hst <;>
        tauto :
        st = PPMStmt.measure c (r.axis ++ [⟨m, .z⟩])
        ∨ st = PPMStmt.measure (c + 1) [⟨m, .x⟩]
        ∨ st = PPMStmt.correct [c, c + 1] r.axis []
        ∨ st = PPMStmt.frame r.axis) with h | h | h | h <;> subst h <;>
      simp [stmtLow, hjs, hjw, hs, sortedStrict, PauliProduct.width] <;>
      omega
  · rcases (by simp at hst; tauto :
        st = PPMStmt.useT m
        ∨ st = PPMStmt.measure c (r.axis ++ [⟨m, .z⟩])
        ∨ st = PPMStmt.measureSel [c] (c + 1) [⟨m, .y⟩] [⟨m, .x⟩]
        ∨ st = PPMStmt.correct (if r.neg then [c, c + 1] else [c + 1])
            r.axis []) with h | h | h | h <;> subst h <;>
      simp [stmtLow, hjs, hjw, hs, sortedStrict, PauliProduct.width] <;>
      omega

/-! ## §6. THE PRESERVATION THEOREM. -/

/-- **EVERY ROTATION PROGRAM LOWERS TO PPM SEMANTICS-PRESERVINGLY**: on
each outcome branch, the lowered PPM program applied to
`ψ ⊗ (input ancillas)` equals the explicit branch scalar times
`(seqDenote m rs · ψ) ⊗ (collapsed ancillas)` — the rotation layer's OWN
matrix semantics on the data. -/
theorem lowerFlat_denote :
    ∀ (rs : List Rot) (m : Nat) (ψ : Fin (2 ^ m) → ℂ)
      (ω : Nat → Bool) (outs : List Bool),
      (∀ r ∈ rs, sortedStrict r.axis = true) →
      (∀ r ∈ rs, PauliProduct.width r.axis ≤ m) →
      (∀ r ∈ rs, ∀ f ∈ r.axis, f.kind = PKind.z ∨ f.kind = PKind.x) →
      (progDenote (ampsWidth m (ancAmps rs)) ω outs
          (lowerFlat m outs.length rs)).mulVec
        (stateOver (ancAmps rs) (ancAmps rs) m ψ)
      = branchScalar ω rs outs.length
          • stateOver (ancAmps rs) (ancOutAmps ω rs outs.length) m
              ((seqDenote m rs).mulVec ψ)
  | [], m, ψ, ω, outs, _, _, _ => by
      show (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ).mulVec ψ
          = (1 : ℂ) • ((1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ).mulVec ψ)
      rw [one_smul]
  | r :: rs, m, ψ, ω, outs, h1, h2, h3 => by
      obtain ⟨rneg, rang, rax⟩ := r
      have hs := h1 _ List.mem_cons_self
      have hw := h2 _ List.mem_cons_self
      have hk := h3 _ List.mem_cons_self
      have h1' := fun s hs' => h1 s (List.mem_cons_of_mem _ hs')
      have h2' := fun s hs' => h2 s (List.mem_cons_of_mem _ hs')
      have h3' := fun s hs' => h3 s (List.mem_cons_of_mem _ hs')
      cases rang with
      | pi =>
          show (progDenote (ampsWidth m (ancAmps rs)) ω outs
              (lowerFlat m outs.length rs)).mulVec
              (stateOver (ancAmps rs) (ancAmps rs) m ψ) = _
          rw [lowerFlat_denote rs m ψ ω outs h1' h2' h3']
          show _ = (rotScalar ⟨rneg, RAngle.pi, rax⟩ (ω outs.length)
                (ω (outs.length + 1)) * branchScalar ω rs outs.length)
              • stateOver (ancAmps rs) (ancOutAmps ω rs outs.length) m
                  ((seqDenote m rs
                    * Rot.denote m ⟨rneg, RAngle.pi, rax⟩).mulVec ψ)
          rw [show rotScalar ⟨rneg, RAngle.pi, rax⟩ (ω outs.length)
                (ω (outs.length + 1)) = -1 from rfl,
              ← Matrix.mulVec_mulVec]
          cases rneg <;>
            [rw [show Rot.denote m ⟨false, RAngle.pi, rax⟩
                  = rotOf Real.pi (axisMat m rax) from by
                unfold Rot.denote Rot.theta
                simp [RAngle.val],
              rotOf_pi];
             rw [show Rot.denote m ⟨true, RAngle.pi, rax⟩
                  = rotOf (-Real.pi) (axisMat m rax) from by
                unfold Rot.denote Rot.theta
                simp [RAngle.val],
              rotOf_neg_pi]] <;>
            rw [show (-1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
                  = -(1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) from rfl,
                Matrix.neg_mulVec, Matrix.one_mulVec,
                show -ψ = (-1 : ℂ) • ψ from by
                  funext x
                  simp,
                Matrix.mulVec_smul, stateOver_smul, smul_smul] <;>
            congr 1 <;>
            ring
      | piHalf =>
          show (progDenote (ampsWidth m (ancAmps rs)) ω outs
              ([PPMStmt.frame rax] ++ lowerFlat m outs.length rs)).mulVec
              (stateOver (ancAmps rs) (ancAmps rs) m ψ) = _
          rw [progDenote_append']
          show (progDenote (ampsWidth m (ancAmps rs)) ω outs
                (lowerFlat m outs.length rs)
              * progDenote (ampsWidth m (ancAmps rs)) ω outs
                [PPMStmt.frame rax]).mulVec
              (stateOver (ancAmps rs) (ancAmps rs) m ψ) = _
          rw [← Matrix.mulVec_mulVec,
              progDenote_stateOver (ancAmps rs) (ancAmps rs) m
                [PPMStmt.frame rax]
                (by
                  intro st hst
                  simp at hst
                  subst hst
                  simp only [stmtLow, Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hs, hw⟩) ω outs ψ,
              show progDenote m ω outs [PPMStmt.frame rax]
                = (1 : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
                    * stmtDenote m outs (ω outs.length)
                        (PPMStmt.frame rax) from rfl,
              Matrix.one_mul,
              show stmtDenote m outs (ω outs.length) (PPMStmt.frame rax)
                = axisMat m rax from rfl,
              lowerFlat_denote rs m ((axisMat m rax).mulVec ψ) ω outs
                h1' h2' h3']
          show _ = (rotScalar ⟨rneg, RAngle.piHalf, rax⟩ (ω outs.length)
                (ω (outs.length + 1)) * branchScalar ω rs outs.length)
              • stateOver (ancAmps rs) (ancOutAmps ω rs outs.length) m
                  ((seqDenote m rs
                    * Rot.denote m ⟨rneg, RAngle.piHalf, rax⟩).mulVec ψ)
          rw [← Matrix.mulVec_mulVec]
          cases rneg <;>
            [rw [show rotScalar ⟨false, RAngle.piHalf, rax⟩ (ω outs.length)
                  (ω (outs.length + 1)) = Complex.I from rfl,
              show Rot.denote m ⟨false, RAngle.piHalf, rax⟩
                  = rotOf (Real.pi / 2) (axisMat m rax) from by
                unfold Rot.denote Rot.theta
                simp [RAngle.val],
              rotOf_pi_div_two];
             rw [show rotScalar ⟨true, RAngle.piHalf, rax⟩ (ω outs.length)
                  (ω (outs.length + 1)) = -Complex.I from rfl,
              show Rot.denote m ⟨true, RAngle.piHalf, rax⟩
                  = rotOf (-(Real.pi / 2)) (axisMat m rax) from by
                unfold Rot.denote Rot.theta
                simp [RAngle.val],
              rotOf_neg_pi_div_two]] <;>
            rw [smul_mulVec, Matrix.mulVec_smul, stateOver_smul,
                smul_smul] <;>
            congr 1 <;>
            ring_nf <;>
            (try simp only [Complex.I_sq]) <;>
            (try ring)
      | piQuarter =>
          show (progDenote (ampsWidth (m + 1) (ancAmps rs)) ω outs
              (lowerRot m outs.length ⟨rneg, RAngle.piQuarter, rax⟩
                ++ lowerFlat (m + 1) (outs.length + 2) rs)).mulVec
              (stateOver (ancAmps rs) (ancAmps rs) (m + 1)
                (tensorHigh m 1 (ancInAmp ⟨rneg, RAngle.piQuarter, rax⟩) ψ))
            = _
          rw [progDenote_append',
              show PPMProg.cwidth (lowerRot m outs.length
                  ⟨rneg, RAngle.piQuarter, rax⟩) = 2 from by
                rw [lowerRot_cwidth]
                rfl,
              ← Matrix.mulVec_mulVec,
              progDenote_stateOver (ancAmps rs) (ancAmps rs) (m + 1) _
                (lowerRot_low m outs.length ⟨rneg, RAngle.piQuarter, rax⟩
                  hs hw) ω outs _,
              lowerRot_denote_quarter m ⟨rneg, RAngle.piQuarter, rax⟩ rfl
                hs hw hk ω outs ψ,
              stateOver_smul, Matrix.mulVec_smul]
          have hlen : (extendTrace ω outs 2).length = outs.length + 2 :=
            extendTrace_length ω 2 outs
          rw [← hlen,
              lowerFlat_denote rs (m + 1)
                (tensorHigh m 1
                  (ancOutAmp ⟨rneg, RAngle.piQuarter, rax⟩ (ω outs.length)
                    (ω (outs.length + 1)))
                  ((Rot.denote m ⟨rneg, RAngle.piQuarter, rax⟩).mulVec ψ))
                ω (extendTrace ω outs 2)
                h1' (fun s hs' => Nat.le_succ_of_le (h2' s hs')) h3',
              seqDenote_tensorHigh m rs
                (fun s hs' => ⟨h1' s hs', h2' s hs'⟩) 1 _ _,
              Matrix.mulVec_mulVec,
              show seqDenote m rs * Rot.denote m ⟨rneg, RAngle.piQuarter, rax⟩
                = seqDenote m (⟨rneg, RAngle.piQuarter, rax⟩ :: rs) from rfl,
              smul_smul, hlen]
          rfl
      | piEighth =>
          show (progDenote (ampsWidth (m + 1) (ancAmps rs)) ω outs
              (lowerRot m outs.length ⟨rneg, RAngle.piEighth, rax⟩
                ++ lowerFlat (m + 1) (outs.length + 2) rs)).mulVec
              (stateOver (ancAmps rs) (ancAmps rs) (m + 1)
                (tensorHigh m 1 (ancInAmp ⟨rneg, RAngle.piEighth, rax⟩) ψ))
            = _
          rw [progDenote_append',
              show PPMProg.cwidth (lowerRot m outs.length
                  ⟨rneg, RAngle.piEighth, rax⟩) = 2 from by
                rw [lowerRot_cwidth]
                rfl,
              ← Matrix.mulVec_mulVec,
              progDenote_stateOver (ancAmps rs) (ancAmps rs) (m + 1) _
                (lowerRot_low m outs.length ⟨rneg, RAngle.piEighth, rax⟩
                  hs hw) ω outs _,
              lowerRot_denote_eighth m ⟨rneg, RAngle.piEighth, rax⟩ rfl
                hs hw hk ω outs ψ,
              stateOver_smul, Matrix.mulVec_smul]
          have hlen : (extendTrace ω outs 2).length = outs.length + 2 :=
            extendTrace_length ω 2 outs
          rw [← hlen,
              lowerFlat_denote rs (m + 1)
                (tensorHigh m 1
                  (ancOutAmp ⟨rneg, RAngle.piEighth, rax⟩ (ω outs.length)
                    (ω (outs.length + 1)))
                  ((Rot.denote m ⟨rneg, RAngle.piEighth, rax⟩).mulVec ψ))
                ω (extendTrace ω outs 2)
                h1' (fun s hs' => Nat.le_succ_of_le (h2' s hs')) h3',
              seqDenote_tensorHigh m rs
                (fun s hs' => ⟨h1' s hs', h2' s hs'⟩) 1 _ _,
              Matrix.mulVec_mulVec,
              show seqDenote m rs * Rot.denote m ⟨rneg, RAngle.piEighth, rax⟩
                = seqDenote m (⟨rneg, RAngle.piEighth, rax⟩ :: rs) from rfl,
              smul_smul, hlen]
          rfl

end FormalRV.PauliRotation
