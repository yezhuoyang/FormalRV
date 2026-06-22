/-
  FormalRV.Framework.PPMUpdateInvariants — PARAMETRIC
  correctness invariants for the Gottesman PPM update.

  `PPMOperational.lean` defines the Gottesman update
  `apply_PPM_pos/neg` and verifies the "preserves commutativity"
  invariant only on CONCRETE instances by `decide` (it states at
  its `:182` that the general theorem "would require induction").

  This file closes that gap: the invariants are proven
  PARAMETRICALLY in the stabilizer state `s` and measured Pauli
  `P`, for ANY code (the proof is pure PauliString algebra and
  uses no code-specific structure). This is Level-A lemma A1 of
  the LDPC-PPM-correctness plan (`notes/topic-ldpc-ppm-correctness.md`):
  the code-independent foundation the surgery readout theorem
  (`surgery_extracts_logical`) folds `apply_PPM` over.

  Main results:
    * `commutes_mul_left` — symplectic bilinearity:
        commutes (a·b) c = (commutes a c == commutes b c)
      for equal-length strings. The load-bearing stabilizer fact.
    * `apply_PPM_pos_preserves_valid` / `_neg_` — the Gottesman
      update preserves the (length + pairwise-commuting) validity
      invariant.
    * `apply_PPM_pos_inserts_P` — after a non-deterministic
      measurement, `P` is in the new stabilizer group.

  No Mathlib.  Pure Bool / Nat / List + omega.
-/

import FormalRV.PPM.Semantics.PPMOperational

namespace FormalRV.Framework.PPMUpdate

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMOp

/-! ## Pointwise structure of `PauliString.mul` -/

/-- The single-qubit product Pauli (dropping the phase). -/
@[inline] def pmul2 (a b : Pauli) : Pauli := (Pauli.mul a b).2

/-- The `ops` of a product is the pointwise `zipWith` product of
    the factor `ops`.  The phase accumulator of the fold does not
    affect the `ops` component. -/
theorem foldl_mul_snd (l : List (Pauli × Pauli)) (ph0 : Phase) (acc0 : List Pauli) :
    (l.foldl
      (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
        let (a, b) := ab
        let (ph, c) := Pauli.mul a b
        (acc.1.mul ph, acc.2 ++ [c])) (ph0, acc0)).2
    = acc0 ++ l.map (fun ab => pmul2 ab.1 ab.2) := by
  induction l generalizing ph0 acc0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [pmul2, List.append_assoc]

/-- L1: `(p · q).ops` is the pointwise product over the zipped op
    lists. -/
theorem mul_ops (p q : PauliString) :
    (p.mul q).ops = (p.ops.zip q.ops).map (fun ab => pmul2 ab.1 ab.2) := by
  simp only [PauliString.mul, foldl_mul_snd, List.nil_append]

/-! ## L2: length preservation -/

theorem mul_length (p q : PauliString) :
    (p.mul q).ops.length = min p.ops.length q.ops.length := by
  rw [mul_ops]
  simp [List.length_zip]

theorem mul_length_eq (p q : PauliString) (n : Nat)
    (hp : p.ops.length = n) (hq : q.ops.length = n) :
    (p.mul q).ops.length = n := by
  rw [mul_length, hp, hq]; simp

/-! ## Single-qubit bilinearity (finite, by `decide`) -/

/-- Single-qubit symplectic bilinearity: commuting with a product
    is the XNOR of commuting with each factor. 4³ = 64 cases. -/
theorem pauli_commutes_mul (a b c : Pauli) :
    Pauli.commutes (pmul2 a b) c = (Pauli.commutes a c == Pauli.commutes b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## countP parity lemma -/

/-- Over a single list, the count of positions satisfying the XOR
    of two predicates is, mod 2, the sum of the two counts. -/
theorem countP_xor_mod2 {α : Type} (l : List α) (f g : α → Bool) :
    (l.countP (fun x => xor (f x) (g x))) % 2
      = (l.countP f + l.countP g) % 2 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons]
    cases hf : f hd <;> cases hg : g hd <;>
      simp_all [xor] <;> omega

/-! ## commutes: symmetry and self -/

theorem commutes_self (p : PauliString) : p.commutes p = true := by
  simp only [PauliString.commutes]
  have key : ∀ l : List Pauli,
      (l.zip l).countP (fun (a, b) => ! a.commutes b) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.zip_cons_cons, List.countP_cons, ih]
      cases x <;> rfl
  rw [key]; rfl

theorem commutes_symm (p q : PauliString) (h : p.ops.length = q.ops.length) :
    p.commutes q = q.commutes p := by
  simp only [PauliString.commutes]
  have key : ∀ la lb : List Pauli, la.length = lb.length →
      (la.zip lb).countP (fun (a, b) => ! a.commutes b)
      = (lb.zip la).countP (fun (a, b) => ! a.commutes b) := by
    intro la
    induction la with
    | nil => intro lb hl; cases lb <;> simp_all
    | cons x xs ih =>
      intro lb hl
      cases lb with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.zip_cons_cons, List.countP_cons]
        rw [ih ys (by simpa using hl)]
        have hxy : Pauli.commutes x y = Pauli.commutes y x := by
          cases x <;> cases y <;> rfl
        simp only [hxy]
  rw [key p.ops q.ops h]

/-! ## L4: symplectic bilinearity for PauliStrings -/

/-- The single-position anticommutation predicate, as a NAMED
    constant defdefinitionally equal to the pattern-lambda inside
    `PauliString.commutes`.  Naming it stops `simp` from rewriting
    it into projection form mid-induction (which would desync the
    induction hypothesis). -/
def antiP : Pauli × Pauli → Bool := fun (a, b) => ! a.commutes b

/-- `commutes` re-expressed through the named `antiP` (defeq, so
    `rfl`). -/
theorem commutes_eq (p q : PauliString) :
    p.commutes q = ((p.ops.zip q.ops).countP antiP % 2 == 0) := rfl

/-- Parity-of-sum to Bool-equality bridge. -/
theorem add_mod2_eq (x y : Nat) :
    ((x + y) % 2 == 0) = ((x % 2 == 0) == (y % 2 == 0)) := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hy : y % 2 = 0 ∨ y % 2 = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [Nat.add_mod, hx, hy]

/-- The pointwise anticommutation count is symplectic-bilinear:
    over equal-length lists, the anti-count of the product against
    `lc` is mod-2 the sum of the two factors' anti-counts. -/
theorem antiCount_mul_left :
    ∀ la lb lc : List Pauli, la.length = lb.length → la.length = lc.length →
      ((((la.zip lb).map (fun ab => pmul2 ab.1 ab.2)).zip lc).countP antiP) % 2
      = ((la.zip lc).countP antiP + (lb.zip lc).countP antiP) % 2 := by
  intro la
  induction la with
  | nil => intro lb lc h1 h2; cases lb <;> cases lc <;> simp_all
  | cons x xs ih =>
    intro lb lc h1 h2
    cases lb with
    | nil => simp at h1
    | cons y ys =>
      cases lc with
      | nil => simp at h2
      | cons z zs =>
        simp only [List.zip_cons_cons, List.map_cons, List.countP_cons]
        have hb : Pauli.commutes (pmul2 x y) z
            = (Pauli.commutes x z == Pauli.commutes y z) := pauli_commutes_mul x y z
        have IH := ih ys zs (by simpa using h1) (by simpa using h2)
        simp only [antiP, hb]
        rcases Bool.eq_false_or_eq_true (Pauli.commutes x z) with hxz | hxz <;>
          rcases Bool.eq_false_or_eq_true (Pauli.commutes y z) with hyz | hyz <;>
            simp [hxz, hyz] <;> omega

/-- The load-bearing stabilizer fact: a product commutes with `c`
    iff the two factors agree on whether they commute with `c`. -/
theorem commutes_mul_left (a b c : PauliString)
    (hab : a.ops.length = b.ops.length) (hac : a.ops.length = c.ops.length) :
    (a.mul b).commutes c = (a.commutes c == b.commutes c) := by
  rw [commutes_eq, commutes_eq, commutes_eq, mul_ops,
      antiCount_mul_left a.ops b.ops c.ops hab hac]
  exact add_mod2_eq _ _

/-! ## `neg` is phase-only: it leaves `commutes` (and `ops`) untouched -/

/-- `neg` only changes the phase, not the operator list. -/
theorem neg_ops (p : PauliString) : (p.neg).ops = p.ops := rfl

/-- `commutes` ignores the global phase, so `neg` on the left is invisible. -/
theorem neg_commutes_left (p q : PauliString) : (p.neg).commutes q = p.commutes q := by
  simp [PauliString.commutes, PauliString.neg]

/-- `commutes` ignores the global phase, so `neg` on the right is invisible. -/
theorem neg_commutes_right (p q : PauliString) : q.commutes (p.neg) = q.commutes p := by
  simp [PauliString.commutes, PauliString.neg]

/-! ## A1: apply_PPM preserves validity

    The Gottesman update replaces the first anticommuting generator
    `g_anti` by the measured operator (`P` for the `+` branch, `P.neg`
    for the `−` branch), and multiplies every OTHER anticommuting
    generator by `g_anti` so it commutes with `P`.  We prove the
    (length + pairwise-commuting) validity invariant is preserved.

    The two branches differ only in the inserted operator, and since
    `commutes` ignores the global phase (`neg_commutes_*`), the proof
    factors through a single engine `apply_generic_valid` parametric
    in the inserted value `V` (instantiated at `P` and `P.neg`). -/

/-- The 3×3 commutation case analysis at the heart of the update.

    Each generator of the new state is the `f`-image of an old
    generator `g` at position `j`: it is the inserted value `V` (if
    `j = i_anti`), the generator itself `g` (if it already commutes
    with `P`), or its product `g · g_anti` (otherwise).  This lemma
    shows ANY two such images commute, using only symplectic
    bilinearity (`commutes_mul_left`), symmetry, and the facts that
    `g_anti` anticommutes with `P` while `V` mirrors `P`'s commutation. -/
theorem pair_commutes
    (P V g_anti g1 g2 : PauliString) (n : Nat)
    (hP : P.ops.length = n) (hV : V.ops.length = n)
    (hga : g_anti.ops.length = n)
    (h1 : g1.ops.length = n) (h2 : g2.ops.length = n)
    (c12 : g1.commutes g2 = true)
    (cga1 : g_anti.commutes g1 = true)
    (cga2 : g_anti.commutes g2 = true)
    (hgaP : g_anti.commutes P = false)
    (hVcg2 : V.commutes g2 = P.commutes g2)
    (hVcga : V.commutes g_anti = P.commutes g_anti)
    (hg1V : g1.commutes V = g1.commutes P)
    (hg2V : g2.commutes V = g2.commutes P)
    (hVV : V.commutes V = true)
    (b1 b2 : Bool)
    (x y : PauliString)
    (hx : x = (if b1 then V else if g1.commutes P then g1 else g1.mul g_anti))
    (hy : y = (if b2 then V else if g2.commutes P then g2 else g2.mul g_anti)) :
    x.commutes y = true := by
  have hm1 : (g1.mul g_anti).ops.length = n := mul_length_eq _ _ _ h1 hga
  have hm2 : (g2.mul g_anti).ops.length = n := mul_length_eq _ _ _ h2 hga
  have c1ga : g1.commutes g_anti = true := by
    rw [commutes_symm g1 g_anti (by rw [h1, hga])]; exact cga1
  have c2ga : g2.commutes g_anti = true := by
    rw [commutes_symm g2 g_anti (by rw [h2, hga])]; exact cga2
  have c21 : g2.commutes g1 = true := by rw [commutes_symm g2 g1 (by rw [h2, h1])]; exact c12
  have hgaP' : P.commutes g_anti = false := by
    rw [commutes_symm P g_anti (by rw [hP, hga])]; exact hgaP
  have gaV : g_anti.commutes V = false := by
    rw [commutes_symm g_anti V (by rw [hga, hV]), hVcga]; exact hgaP'
  have hxval : x = V ∨ (x = g1 ∧ g1.commutes P = true)
      ∨ (x = g1.mul g_anti ∧ g1.commutes P = false) := by
    rw [hx]; by_cases hb1 : b1
    · left; simp [hb1]
    · simp only [hb1, Bool.false_eq_true, if_false]
      cases hg1P : g1.commutes P with
      | true => right; left; exact ⟨by simp, rfl⟩
      | false => right; right; exact ⟨by simp, rfl⟩
  have hyval : y = V ∨ (y = g2 ∧ g2.commutes P = true)
      ∨ (y = g2.mul g_anti ∧ g2.commutes P = false) := by
    rw [hy]; by_cases hb2 : b2
    · left; simp [hb2]
    · simp only [hb2, Bool.false_eq_true, if_false]
      cases hg2P : g2.commutes P with
      | true => right; left; exact ⟨by simp, rfl⟩
      | false => right; right; exact ⟨by simp, rfl⟩
  rcases hxval with hxv | ⟨hxv, hg1P⟩ | ⟨hxv, hg1P⟩ <;>
    rcases hyval with hyv | ⟨hyv, hg2P⟩ | ⟨hyv, hg2P⟩ <;>
    rw [hxv, hyv]
  · exact hVV
  · rw [hVcg2, commutes_symm P g2 (by rw [hP, h2])]; exact hg2P
  · rw [commutes_symm V (g2.mul g_anti) (by rw [hV, hm2]),
        commutes_mul_left g2 g_anti V (h2.trans hga.symm) (h2.trans hV.symm), hg2V, gaV, hg2P]; rfl
  · rw [hg1V]; exact hg1P
  · exact c12
  · rw [commutes_symm g1 (g2.mul g_anti) (by rw [h1, hm2]),
        commutes_mul_left g2 g_anti g1 (h2.trans hga.symm) (h2.trans h1.symm), c21, cga1]; rfl
  · rw [commutes_mul_left g1 g_anti V (h1.trans hga.symm) (h1.trans hV.symm), hg1V, gaV, hg1P]; rfl
  · rw [commutes_mul_left g1 g_anti g2 (h1.trans hga.symm) (h1.trans h2.symm), c12, cga2]; rfl
  · rw [commutes_mul_left g1 g_anti (g2.mul g_anti) (h1.trans hga.symm) (h1.trans hm2.symm),
        commutes_symm g1 (g2.mul g_anti) (by rw [h1, hm2]),
        commutes_mul_left g2 g_anti g1 (h2.trans hga.symm) (h2.trans h1.symm), c21, cga1,
        commutes_symm g_anti (g2.mul g_anti) (by rw [hga, hm2]),
        commutes_mul_left g2 g_anti g_anti (h2.trans hga.symm) (h2.trans hga.symm), c2ga,
        commutes_self g_anti]; rfl

/-- The validity-preservation engine, parametric in the inserted
    operator `V`.  `V` must mirror `P`'s commutation behaviour
    (`hVcomm`/`hVcomm'`) and self-commute (`hVV`); both `P` (the `+`
    branch) and `P.neg` (the `−` branch) satisfy these because
    `commutes` is phase-blind. -/
theorem apply_generic_valid
    (s : StabilizerState) (P V : PauliString) (n i_anti : Nat) (g_anti : PauliString)
    (hv : StabilizerState.valid s n = true) (hP : P.ops.length = n) (hV : V.ops.length = n)
    (hf : find_anticommuting s P = some i_anti) (hg : s[i_anti]? = some g_anti)
    (hVcomm : ∀ q : PauliString, V.commutes q = P.commutes q)
    (hVcomm' : ∀ q : PauliString, q.commutes V = q.commutes P)
    (hVV : V.commutes V = true)
    (result : StabilizerState)
    (hres : result = (s.zipIdx).map (fun (g, j) =>
              if decide (j = i_anti) then V
              else if g.commutes P then g else g.mul g_anti)) :
    StabilizerState.valid result n = true := by
  rw [StabilizerState.valid, Bool.and_eq_true] at hv
  obtain ⟨hvl, hvc⟩ := hv
  rw [StabilizerState.valid_length, List.all_eq_true] at hvl
  rw [StabilizerState.valid_commuting, List.all_eq_true] at hvc
  have hlen : ∀ g ∈ s, g.ops.length = n := by
    intro g hg; have := hvl g hg; simpa using this
  have hcomm : ∀ g1 ∈ s, ∀ g2 ∈ s, g1.commutes g2 = true := by
    intro g1 hg1 g2 hg2
    have := hvc g1 hg1; rw [List.all_eq_true] at this; exact this g2 hg2
  have hga_mem : g_anti ∈ s := List.mem_of_getElem? hg
  have hga_len : g_anti.ops.length = n := hlen g_anti hga_mem
  unfold find_anticommuting at hf
  have hpred := List.findIdx?_eq_some_iff_getElem.mp hf
  obtain ⟨hlt, hp_anti, _⟩ := hpred
  have hidx : s[i_anti] = g_anti := by
    have := List.getElem?_eq_getElem hlt; rw [hg] at this; exact (Option.some.injEq _ _ ▸ this).symm
  rw [hidx] at hp_anti
  have hgaP : g_anti.commutes P = false := by
    cases hc : g_anti.commutes P with
    | false => rfl
    | true => simp [hc] at hp_anti
  rw [hres, StabilizerState.valid, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- length preservation
    rw [StabilizerState.valid_length, List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨⟨g1, j1⟩, hgj1, hb1⟩ := hb
    have hg1mem : g1 ∈ s := (List.mem_zipIdx' hgj1).2 ▸ List.getElem_mem _
    have hg1len : g1.ops.length = n := hlen g1 hg1mem
    have hm1 : (g1.mul g_anti).ops.length = n := mul_length_eq _ _ _ hg1len hga_len
    simp only at hb1
    subst hb1
    split
    · simp [hV]
    · split <;> simp_all
  · -- pairwise commutation preservation
    rw [StabilizerState.valid_commuting, List.all_eq_true]
    intro b1 hb1
    rw [List.all_eq_true]
    intro b2 hb2
    rw [List.mem_map] at hb1 hb2
    obtain ⟨⟨g1, j1⟩, hgj1, he1⟩ := hb1
    obtain ⟨⟨g2, j2⟩, hgj2, he2⟩ := hb2
    have hg1mem : g1 ∈ s := (List.mem_zipIdx' hgj1).2 ▸ List.getElem_mem _
    have hg2mem : g2 ∈ s := (List.mem_zipIdx' hgj2).2 ▸ List.getElem_mem _
    have hg1len : g1.ops.length = n := hlen g1 hg1mem
    have hg2len : g2.ops.length = n := hlen g2 hg2mem
    simp only at he1 he2
    exact pair_commutes P V g_anti g1 g2 n hP hV hga_len hg1len hg2len
      (hcomm g1 hg1mem g2 hg2mem)
      (hcomm g_anti hga_mem g1 hg1mem) (hcomm g_anti hga_mem g2 hg2mem)
      hgaP (hVcomm g2) (hVcomm g_anti) (hVcomm' g1) (hVcomm' g2) hVV
      (decide (j1 = i_anti)) (decide (j2 = i_anti)) b1 b2 he1.symm he2.symm

theorem apply_PPM_pos_preserves_valid (s : StabilizerState) (P : PauliString) (n : Nat)
    (hv : StabilizerState.valid s n = true) (hP : P.ops.length = n) :
    StabilizerState.valid (apply_PPM_pos s P) n = true := by
  unfold apply_PPM_pos
  cases hf : find_anticommuting s P with
  | none => exact hv
  | some i_anti =>
    dsimp only [hf]
    cases hg : s[i_anti]? with
    | none => exact hv
    | some g_anti =>
      dsimp only [hg]
      exact apply_generic_valid s P P n i_anti g_anti hv hP hP hf hg
        (fun _ => rfl) (fun _ => rfl) (commutes_self P) _ rfl

theorem apply_PPM_neg_preserves_valid (s : StabilizerState) (P : PauliString) (n : Nat)
    (hv : StabilizerState.valid s n = true) (hP : P.ops.length = n) :
    StabilizerState.valid (apply_PPM_neg s P) n = true := by
  unfold apply_PPM_neg
  cases hf : find_anticommuting s P with
  | none => exact hv
  | some i_anti =>
    dsimp only [hf]
    cases hg : s[i_anti]? with
    | none => exact hv
    | some g_anti =>
      dsimp only [hg]
      exact apply_generic_valid s P P.neg n i_anti g_anti hv hP (by rw [neg_ops]; exact hP) hf hg
        (fun q => neg_commutes_left P q) (fun q => neg_commutes_right P q)
        (by rw [neg_commutes_left, neg_commutes_right]; exact commutes_self P) _ rfl

/-! ## A1′: after a non-deterministic measurement, `P` is inserted -/

/-- When the measured operator `P` anticommutes with some generator
    (so the outcome is non-deterministic), the `+` branch of the
    Gottesman update inserts `P` itself into the new stabilizer group:
    `P` occupies the `i_anti` slot of `apply_PPM_pos s P`.  This is the
    operational meaning of a stabilizer measurement — `±P` becomes a
    stabilizer afterwards. -/
theorem apply_PPM_pos_inserts_P (s : StabilizerState) (P : PauliString)
    (h : (find_anticommuting s P).isSome = true) : P ∈ apply_PPM_pos s P := by
  obtain ⟨i_anti, hf⟩ := Option.isSome_iff_exists.mp h
  unfold find_anticommuting at hf
  have hpred := List.findIdx?_eq_some_iff_getElem.mp hf
  obtain ⟨hlt, _, _⟩ := hpred
  have hg : s[i_anti]? = some s[i_anti] := List.getElem?_eq_getElem hlt
  unfold apply_PPM_pos
  rw [show find_anticommuting s P = some i_anti from hf]
  simp only [hg]
  rw [List.mem_map]
  refine ⟨(s[i_anti], i_anti), ?_, ?_⟩
  · rw [List.mk_mem_zipIdx_iff_getElem?]; exact hg
  · simp

end FormalRV.Framework.PPMUpdate
