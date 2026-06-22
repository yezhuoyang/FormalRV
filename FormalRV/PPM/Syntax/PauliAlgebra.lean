/-
  FormalRV.PPM.Syntax.PauliAlgebra
  ────────────────────────────────
  Phase-free multiplication of sparse Pauli products — the algebra of the
  PAULI FRAME.  A frame is a Pauli operator *up to global phase* (phases are
  unobservable in frame tracking), so the product of two sparse products is a
  sorted merge: factors on distinct qubits interleave; factors on the same
  qubit combine by single-qubit Pauli multiplication, with `P·P = I` dropping
  the qubit entirely (sparse products never mention identity).

  Pure syntax-tree algebra (imports only the IR): this is what
  `Semantics/ProgramSemantics.lean` uses to fold `frame` / fired `correct`
  statements into a single accumulated frame, and what the frame-soundness
  theorem (deferred ≡ applied corrections) is stated over.
-/
import FormalRV.PPM.Syntax.Program

namespace FormalRV.PPM.Prog

/-! ## §1. Single-qubit kind multiplication (phase-free). -/

/-- Phase-free product of two non-identity Pauli kinds: equal kinds cancel to
identity (`none`); distinct kinds give the third (`X·Y ~ Z` up to phase). -/
def PKind.mulK : PKind → PKind → Option PKind
  | .x, .x => none
  | .y, .y => none
  | .z, .z => none
  | .x, .y => some .z
  | .y, .x => some .z
  | .x, .z => some .y
  | .z, .x => some .y
  | .y, .z => some .x
  | .z, .y => some .x

theorem PKind.mulK_comm (a b : PKind) : PKind.mulK a b = PKind.mulK b a := by
  cases a <;> cases b <;> rfl

theorem PKind.mulK_self (a : PKind) : PKind.mulK a a = none := by
  cases a <;> rfl

/-! ## §2. Sorted-merge multiplication of sparse products. -/

/-- Phase-free product of two sparse Pauli products (sorted merge; equal-qubit
factors combine by `mulK`, cancelling to nothing when equal). -/
def mulF : PauliProduct → PauliProduct → PauliProduct
  | [], Q => Q
  | P, [] => P
  | a :: P, b :: Q =>
      if a.qubit < b.qubit then a :: mulF P (b :: Q)
      else if b.qubit < a.qubit then b :: mulF (a :: P) Q
      else
        match PKind.mulK a.kind b.kind with
        | none   => mulF P Q
        | some k => ⟨a.qubit, k⟩ :: mulF P Q
  termination_by P Q => P.length + Q.length

@[simp] theorem mulF_nil_left (Q : PauliProduct) : mulF [] Q = Q := by
  cases Q <;> rw [mulF.eq_def]

@[simp] theorem mulF_nil_right (P : PauliProduct) : mulF P [] = P := by
  cases P <;> rw [mulF.eq_def]

/-- **Involution (cancellation): every product is its own frame-inverse.** -/
theorem mulF_self (P : PauliProduct) : mulF P P = [] := by
  induction P with
  | nil => rw [mulF.eq_def]
  | cons a t ih =>
      rw [mulF.eq_def]
      simp only [if_neg (Nat.lt_irrefl a.qubit), PKind.mulK_self]
      exact ih

/-! ## §3. Order/width preservation.

`mulF` preserves the canonical form: the product of two `sortedStrict`
products is `sortedStrict`, and its width never exceeds the wider factor —
so the executor's frame stays a well-formed sparse product on the program's
qubits.  Proofs by functional induction over the merge (`mulF.induct`),
driven by the four unfold lemmas below (the WF-compiled `mulF` does not
reduce definitionally). -/

theorem mulF_cons_lt {a b : PFactor} (P Q : PauliProduct) (h : a.qubit < b.qubit) :
    mulF (a :: P) (b :: Q) = a :: mulF P (b :: Q) := by
  rw [mulF.eq_def]; simp [h]

theorem mulF_cons_gt {a b : PFactor} (P Q : PauliProduct) (h : b.qubit < a.qubit) :
    mulF (a :: P) (b :: Q) = b :: mulF (a :: P) Q := by
  rw [mulF.eq_def]; simp [h, show ¬ a.qubit < b.qubit from by omega]

theorem mulF_cons_cancel {a b : PFactor} (P Q : PauliProduct)
    (h1 : ¬ a.qubit < b.qubit) (h2 : ¬ b.qubit < a.qubit)
    (hk : a.kind.mulK b.kind = none) :
    mulF (a :: P) (b :: Q) = mulF P Q := by
  rw [mulF.eq_def]; simp [h1, h2, hk]

theorem mulF_cons_combine {a b : PFactor} (P Q : PauliProduct) {k : PKind}
    (h1 : ¬ a.qubit < b.qubit) (h2 : ¬ b.qubit < a.qubit)
    (hk : a.kind.mulK b.kind = some k) :
    mulF (a :: P) (b :: Q) = ⟨a.qubit, k⟩ :: mulF P Q := by
  rw [mulF.eq_def]; simp [h1, h2, hk]

/-- **Width preservation**: a frame product never touches a qubit outside the
factors' span. -/
theorem mulF_width (P Q : PauliProduct) :
    PauliProduct.width (mulF P Q) ≤ max P.width Q.width := by
  induction P, Q using mulF.induct with
  | case1 Q => simp only [mulF_nil_left, PauliProduct.width]; omega
  | case2 P _ => simp only [mulF_nil_right, PauliProduct.width]; omega
  | case3 a P b Q h ih =>
      rw [mulF_cons_lt P Q h]
      simp only [PauliProduct.width] at ih ⊢
      omega
  | case4 a P b Q h1 h2 ih =>
      rw [mulF_cons_gt P Q h2]
      simp only [PauliProduct.width] at ih ⊢
      omega
  | case5 a P b Q h1 h2 hk ih =>
      rw [mulF_cons_cancel P Q h1 h2 hk]
      simp only [PauliProduct.width] at ih ⊢
      omega
  | case6 a P b Q h1 h2 k hk ih =>
      rw [mulF_cons_combine P Q h1 h2 hk]
      simp only [PauliProduct.width] at ih ⊢
      omega

/-- Every qubit index in the product is `≥ lo` — the strict-lower-bound
invariant that threads `sortedStrict` through the merge induction. -/
def lbound (lo : Nat) : PauliProduct → Bool
  | [] => true
  | f :: t => decide (lo ≤ f.qubit) && lbound lo t

theorem lbound_mono {lo lo' : Nat} (h : lo' ≤ lo) (P : PauliProduct)
    (hP : lbound lo P = true) : lbound lo' P = true := by
  induction P with
  | nil => rfl
  | cons f t ih =>
      simp only [lbound, Bool.and_eq_true, decide_eq_true_eq] at hP ⊢
      exact ⟨by omega, ih hP.2⟩

theorem sorted_cons_tail {a : PFactor} {t : PauliProduct}
    (h : sortedStrict (a :: t) = true) : sortedStrict t = true := by
  cases t with
  | nil => rfl
  | cons b t' =>
      simp only [sortedStrict, Bool.and_eq_true] at h
      exact h.2

theorem sorted_cons_lbound {a : PFactor} {t : PauliProduct}
    (h : sortedStrict (a :: t) = true) : lbound (a.qubit + 1) t = true := by
  induction t generalizing a with
  | nil => rfl
  | cons b t' ih =>
      simp only [sortedStrict, Bool.and_eq_true, decide_eq_true_eq] at h
      have hb := ih (a := b) h.2
      simp only [lbound, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, lbound_mono (by omega) t' hb⟩

theorem sorted_cons_intro {a : PFactor} {t : PauliProduct}
    (hl : lbound (a.qubit + 1) t = true) (ht : sortedStrict t = true) :
    sortedStrict (a :: t) = true := by
  cases t with
  | nil => rfl
  | cons b t' =>
      simp only [lbound, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [sortedStrict, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ht⟩

theorem mulF_lbound (lo : Nat) (P Q : PauliProduct) :
    lbound lo P = true → lbound lo Q = true → lbound lo (mulF P Q) = true := by
  induction P, Q using mulF.induct with
  | case1 Q => intro _ hQ; simpa using hQ
  | case2 P _ => intro hP _; simpa using hP
  | case3 a P b Q h ih =>
      intro hP hQ
      rw [mulF_cons_lt P Q h]
      simp only [lbound, Bool.and_eq_true] at hP ⊢
      exact ⟨hP.1, ih hP.2 hQ⟩
  | case4 a P b Q h1 h2 ih =>
      intro hP hQ
      rw [mulF_cons_gt P Q h2]
      simp only [lbound, Bool.and_eq_true] at hQ ⊢
      exact ⟨hQ.1, ih hP hQ.2⟩
  | case5 a P b Q h1 h2 hk ih =>
      intro hP hQ
      rw [mulF_cons_cancel P Q h1 h2 hk]
      simp only [lbound, Bool.and_eq_true] at hP hQ
      exact ih hP.2 hQ.2
  | case6 a P b Q h1 h2 k hk ih =>
      intro hP hQ
      rw [mulF_cons_combine P Q h1 h2 hk]
      simp only [lbound, Bool.and_eq_true, decide_eq_true_eq] at hP hQ ⊢
      exact ⟨hP.1, ih hP.2 hQ.2⟩

/-- **Order preservation: the product of two canonical (strictly sorted)
products is canonical** — the frame accumulated by the executor is always a
well-formed sparse Pauli product. -/
theorem mulF_sorted (P Q : PauliProduct) :
    sortedStrict P = true → sortedStrict Q = true → sortedStrict (mulF P Q) = true := by
  induction P, Q using mulF.induct with
  | case1 Q => intro _ hQ; simpa using hQ
  | case2 P _ => intro hP _; simpa using hP
  | case3 a P b Q h ih =>
      intro hP hQ
      rw [mulF_cons_lt P Q h]
      apply sorted_cons_intro
      · apply mulF_lbound
        · exact sorted_cons_lbound hP
        · simp only [lbound, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, lbound_mono (by omega) Q (sorted_cons_lbound hQ)⟩
      · exact ih (sorted_cons_tail hP) hQ
  | case4 a P b Q h1 h2 ih =>
      intro hP hQ
      rw [mulF_cons_gt P Q h2]
      apply sorted_cons_intro
      · apply mulF_lbound
        · simp only [lbound, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, lbound_mono (by omega) P (sorted_cons_lbound hP)⟩
        · exact sorted_cons_lbound hQ
      · exact ih hP (sorted_cons_tail hQ)
  | case5 a P b Q h1 h2 hk ih =>
      intro hP hQ
      rw [mulF_cons_cancel P Q h1 h2 hk]
      exact ih (sorted_cons_tail hP) (sorted_cons_tail hQ)
  | case6 a P b Q h1 h2 k hk ih =>
      intro hP hQ
      rw [mulF_cons_combine P Q h1 h2 hk]
      apply sorted_cons_intro (a := ⟨a.qubit, k⟩)
      · show lbound (a.qubit + 1) (mulF P Q) = true
        apply mulF_lbound
        · exact sorted_cons_lbound hP
        · exact lbound_mono (by omega) Q (sorted_cons_lbound hQ)
      · exact ih (sorted_cons_tail hP) (sorted_cons_tail hQ)

/-! ## §4. Smoke checks. -/

example : mulF [⟨0, .x⟩] [⟨0, .x⟩] = [] := by simp [mulF, PKind.mulK]
example : mulF [⟨0, .x⟩] [⟨0, .y⟩] = [⟨0, .z⟩] := by simp [mulF, PKind.mulK]
example : mulF [⟨0, .x⟩, ⟨2, .z⟩] [⟨1, .y⟩] = [⟨0, .x⟩, ⟨1, .y⟩, ⟨2, .z⟩] := by
  simp [mulF]
example :  -- X[0]Z[1] · Z[1]X[2] = X[0]X[2]  (the Z's cancel)
    mulF [⟨0, .x⟩, ⟨1, .z⟩] [⟨1, .z⟩, ⟨2, .x⟩] = [⟨0, .x⟩, ⟨2, .x⟩] := by
  simp [mulF, PKind.mulK]
example : mulF [] [⟨3, .y⟩] = [⟨3, .y⟩] := by simp

end FormalRV.PPM.Prog
