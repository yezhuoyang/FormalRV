/-
  FormalRV.Shor.MeasuredLookupUncompute — Gidney's measurement-based
  LOOKUP-uncompute at the LOGICAL layer (density-matrix semantics on
  `Com`/`c_eval`), generalizing the single-ancilla AND case
  (`FormalRV.Shor.MeasuredANDUncompute`) to the W-bit word register of a
  QROM lookup.

  Gidney–Ekerå (arXiv:1905.09749 §C.3, Fig. C.2; Berry et al. arXiv:1902.02134):
  to uncompute a W-qubit QROM word register holding `T[addr]`, instead of
  paying a second full lookup, X-MEASURE each word qubit and apply a
  classically-controlled PHASE FIXUP on the address register (a phase lookup),
  then release the word qubits as `|0⟩`.

  This file is ADDER/LOOKUP-AGNOSTIC: the per-bit phase fixup is an ABSTRACT
  family of unitaries `P j : BaseUCom dim` with a diagonal-action hypothesis

      `uc_eval (P j) * |f⟩ = (-1)^(φ j f) • |f⟩`

  for an abstract per-bit phase predicate `φ j : (Nat → Bool) → Bool` that
  does NOT depend on the word-register bits.  In the QROM instance
  `φ j f = (T (decodeAddr f)).testBit j`, computed from the address only —
  the CONSTRUCTION of a concrete phase-lookup circuit realizing `P j`
  (and its Toffoli count) is the NEXT stage and is deliberately not built
  here; `measWordUncompute_qrom` is the thin instantiation it plugs into.

  The channel processes the word SEQUENTIALLY, one qubit at a time
  (avoiding a 2^W-branch measurement tree): for each `j = 0, 1, …, W-1`
  (increasing order; the recursion peels the LAST bit `W-1` off the back,
  so bit `W-1` runs last):

      `H (pos j) ; meas (pos j) (P j ; X (pos j)) skip`

  HEADLINE (`measWordUncompute_perfect`): on every state of the
  "lookup-computed family" `ψ = Σ_{i ∈ s} α_i |g i⟩` with
  `g i (pos j) = φ j (g i)` for all `j < W` on the support,

      `c_eval (measWordUncompute dim pos P W) (ψψᴴ) = ψ'ψ'ᴴ`

  where `ψ' = Σ_{i ∈ s} α_i |g i with ALL word bits cleared⟩` — the perfect
  uncompute: coefficients intact, word released as `|0…0⟩`.

  Proof architecture:
    * per-qubit step (`measBitUncompute_perfect`) — EXACTLY the
      `measANDUncompute_perfect` proof shape with abstract `φ j` in place
      of `f a && f b`;
    * induction over `W` — after clearing bit `j`, the family still
      satisfies the hypotheses for the remaining bits, via φ's
      word-independence (`phase_clearWord`) and update commutation
      (`clearWord_apply_ne`).

  Machinery REUSED from `MeasuredANDUncompute`: `conj_outer_product`,
  `smul_outer_product`, `sqrt2_half_mul_self/star`, `measAND_branch0`
  (the outcome-0 branch is φ-independent and is reused verbatim).
-/
import FormalRV.Shor.MeasuredANDUncompute

namespace FormalRV.Shor.MeasuredLookupUncompute

open FormalRV.Framework
open FormalRV.Framework.BaseCom
open FormalRV.Framework.BaseUCom (proj)
open FormalRV.Shor.MeasuredANDUncompute
open Matrix

noncomputable section

/-! ## The channel -/

/-- One word-qubit step of Gidney's measurement-based lookup-uncompute:
    `H q ; meas q (P ; X q) skip` — X-measure word qubit `q`; on outcome 1
    apply the (abstract) phase fixup `P` and reset `q` with `X q`
    (the measured qubit is in `|1⟩`, so `X` releases it as `|0⟩`);
    on outcome 0 do nothing.  With `P := CZ a b` this is literally
    `measANDUncompute`. -/
def measBitUncompute (dim q : Nat) (P : BaseUCom dim) : BaseCom dim :=
  Com.useq (Com.embedU (BaseUCom.H q))
    (Com.meas q
      (Com.useq (Com.embedU P) (Com.embedU (BaseUCom.X q)))
      Com.cskip)

/-- Gidney's measurement-based lookup-uncompute on a `W`-bit word register at
    positions `pos 0, …, pos (W-1)`, with per-bit phase fixups `P j`:
    the per-bit steps run sequentially in INCREASING `j` order
    (the recursion peels bit `W-1` off the back, so it runs last). -/
def measWordUncompute (dim : Nat) (pos : Nat → Nat) (P : Nat → BaseUCom dim) :
    Nat → BaseCom dim
  | 0 => Com.cskip
  | W + 1 =>
      Com.useq (measWordUncompute dim pos P W)
        (measBitUncompute dim (pos W) (P W))

/-! ## Clearing the word register, and its interaction with `φ` -/

/-- `clearWord pos W f` — `f` with word bits `pos 0, …, pos (W-1)` cleared,
    in the same order the channel clears them. -/
def clearWord (pos : Nat → Nat) : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, f => f
  | W + 1, f => update (clearWord pos W f) (pos W) false

/-- Positions outside the (first `W` bits of the) word register are untouched
    by `clearWord`. -/
theorem clearWord_apply_ne (pos : Nat → Nat) (W : Nat) (f : Nat → Bool) (q : Nat)
    (h : ∀ k, k < W → q ≠ pos k) :
    clearWord pos W f q = f q := by
  induction W with
  | zero => rfl
  | succ W ih =>
      simp only [clearWord]
      rw [update_neq _ _ _ _ (h W (Nat.lt_succ_self W)),
          ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- A word-independent phase predicate is invariant under clearing the word:
    `φj (clearWord pos W f) = φj f`. -/
theorem phase_clearWord (pos : Nat → Nat) (W : Nat) (φj : (Nat → Bool) → Bool)
    (hφ : ∀ k, k < W → ∀ f v, φj (update f (pos k) v) = φj f) (f : Nat → Bool) :
    φj (clearWord pos W f) = φj f := by
  induction W with
  | zero => rfl
  | succ W ih =>
      simp only [clearWord]
      rw [hφ W (Nat.lt_succ_self W),
          ih (fun k hk => hφ k (Nat.lt_succ_of_lt hk))]

/-! ## The outcome-1 branch on a single computed basis state

    (The outcome-0 branch is φ-independent: `measAND_branch0_basis` /
    `measAND_branch0` from the AND file are reused verbatim.) -/

/-- **Branch 1 (outcome 1, `P ; X q` fixup), basis state**: projecting the
    Hadamard-rotated word qubit onto `|1⟩` leaves the phase
    `(-1)^(f q) = (-1)^(φj f)` (this is where the lookup-computed constraint
    enters); the classically-controlled diagonal fixup `P` cancels it and
    `X q` resets the qubit — net result: the cleaned state with amplitude
    `√2/2`.  Generalizes `measAND_branch1_basis` from `φj f = f a && f b`
    to an abstract word-independent `φj`. -/
theorem measBit_branch1_basis {dim : Nat} (q : Nat) (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool)
    (hP : ∀ f, uc_eval P * f_to_vec dim f
            = (if φj f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ f v, φj (update f q v) = φj f)
    (f : Nat → Bool) (hf : f q = φj f) :
    uc_eval (BaseUCom.X q : BaseUCom dim)
        * (uc_eval P
          * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim) * f_to_vec dim f)))
      = (Real.sqrt 2 / 2 : ℂ) • f_to_vec dim (update f q false) := by
  rw [f_to_vec_H_uc_eval dim q hq f, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      proj_true_on_f_to_vec dim q hq, proj_true_on_f_to_vec dim q hq]
  simp only [update_eq, Bool.false_eq_true, if_true, if_false, smul_zero, zero_add]
  rw [Matrix.mul_smul, hP (update f q true), hφ f true]
  rw [Matrix.mul_smul, Matrix.mul_smul, f_to_vec_X_uc_eval dim q hq (update f q true)]
  simp only [update_idem, update_eq, Bool.not_true]
  rw [hf, smul_smul]
  cases h : φj f <;> simp

/-- **Outcome-1 branch on a computed superposition**:
    `(P ; X q) (P₁ (H_q ψ)) = (√2/2) • ψ'` — the classically-controlled
    fixup makes the outcome-1 post-state IDENTICAL to the outcome-0 one. -/
theorem measBit_branch1 {dim : Nat} {ι : Type*} (q : Nat) (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool)
    (hP : ∀ f, uc_eval P * f_to_vec dim f
            = (if φj f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ f v, φj (update f q v) = φj f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hbit : ∀ i ∈ s, g i q = φj (g i)) :
    uc_eval (BaseUCom.X q : BaseUCom dim)
        * (uc_eval P
          * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim)
            * ∑ i ∈ s, α i • f_to_vec dim (g i))))
      = (Real.sqrt 2 / 2 : ℂ) • ∑ i ∈ s, α i • f_to_vec dim (update (g i) q false) := by
  rw [Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum, Matrix.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      measBit_branch1_basis q hq P φj hP hφ (g i) (hbit i hi)]
  exact smul_comm _ _ _

/-! ## Density-matrix assembly for one word qubit -/

/-- Channel plumbing for one word-qubit step: if both measurement branches send
    the (vector) state `ψ` to `(√2/2) • ψ'`, then the step channel sends the
    density matrix `ψψᴴ` exactly to `ψ'ψ'ᴴ` — each branch contributes
    probability 1/2, and the two halves add up to the full pure target state.
    (= `measANDUncompute_pure_step` with abstract fixup `P`.) -/
theorem measBitUncompute_pure_step {dim : Nat} (q : Nat) (P : BaseUCom dim)
    (ψ ψ' : Matrix (Fin (2^dim)) (Fin 1) ℂ)
    (h0 : proj q dim false * (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ)
            = (Real.sqrt 2 / 2 : ℂ) • ψ')
    (h1 : uc_eval (BaseUCom.X q : BaseUCom dim)
            * (uc_eval P
              * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ)))
            = (Real.sqrt 2 / 2 : ℂ) • ψ') :
    c_eval (measBitUncompute dim q P) (ψ * ψᴴ) = ψ' * ψ'ᴴ := by
  simp only [measBitUncompute, c_eval_useq, c_eval_meas, c_eval_embedU, c_eval_skip]
  rw [conj_outer_product (uc_eval (BaseUCom.H q)) ψ,
      conj_outer_product (proj q dim true) (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ),
      conj_outer_product (proj q dim false) (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ),
      conj_outer_product (uc_eval P)
        (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ)),
      conj_outer_product (uc_eval (BaseUCom.X q))
        (uc_eval P
          * (proj q dim true * (uc_eval (BaseUCom.H q : BaseUCom dim) * ψ))),
      h0, h1, smul_outer_product, sqrt2_half_mul_star, ← add_smul]
  norm_num

/-- **Per-qubit step (the AND case with abstract φ)**: one `H + meas + fixup + X`
    step clears word bit `q` on every lookup-computed family whose bit `q`
    agrees with the word-independent phase predicate `φj`. -/
theorem measBitUncompute_perfect {dim : Nat} {ι : Type*} (q : Nat) (hq : q < dim)
    (P : BaseUCom dim) (φj : (Nat → Bool) → Bool)
    (hP : ∀ f, uc_eval P * f_to_vec dim f
            = (if φj f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ f v, φj (update f q v) = φj f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hbit : ∀ i ∈ s, g i q = φj (g i)) :
    c_eval (measBitUncompute dim q P)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (update (g i) q false))
          * (∑ i ∈ s, α i • f_to_vec dim (update (g i) q false))ᴴ :=
  measBitUncompute_pure_step q P _ _
    (measAND_branch0 q hq s α g)
    (measBit_branch1 q hq P φj hP hφ s α g hbit)

/-! ## HEADLINE: the W-fold word uncompute -/

/-- **HEADLINE (density level)**: Gidney's measurement-based LOOKUP-uncompute
    is the PERFECT uncompute on the lookup-computed family.  For every finite
    superposition `ψ = Σ_{i ∈ s} α_i |g i⟩` whose word bits hold the per-bit
    phase data — `g i (pos j) = φ j (g i)` for all `j < W` — with the word
    positions distinct and the phase predicates word-independent,

        `c_eval (measWordUncompute dim pos P W) (ψψᴴ) = ψ'ψ'ᴴ`

    where `ψ' = Σ_{i ∈ s} α_i |g i with all W word bits cleared⟩`: the
    address/data register is untouched (coefficients `α` intact) and the whole
    word register is released as `|0…0⟩` — with NO second lookup (the channel
    is H, X, measurement, plus the diagonal fixups `P j`).

    Induction over `W`: after the first `W` bits are cleared (IH), bit `W`
    still satisfies the per-qubit hypotheses — its value is untouched by the
    clearing (`clearWord_apply_ne`, positions distinct) and its phase
    predicate is invariant (`phase_clearWord`, word-independence). -/
theorem measWordUncompute_perfect {dim : Nat} {ι : Type*} (W : Nat)
    (pos : Nat → Nat) (P : Nat → BaseUCom dim) (φ : Nat → (Nat → Bool) → Bool)
    (hpos : ∀ j, j < W → pos j < dim)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (hP : ∀ j, j < W → ∀ f, uc_eval (P j) * f_to_vec dim f
            = (if φ j f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ j, j < W → ∀ k, k < W → ∀ f v, φ j (update f (pos k) v) = φ j f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hword : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = φ j (g i)) :
    c_eval (measWordUncompute dim pos P W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ := by
  induction W with
  | zero => simp only [measWordUncompute, clearWord, c_eval_skip]
  | succ W ih =>
      -- IH: the first W bits are cleared.
      have hψW := ih (fun j hj => hpos j (Nat.lt_succ_of_lt hj))
        (fun j hj k hk => hinj j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_of_lt hk))
        (fun j hj => hP j (Nat.lt_succ_of_lt hj))
        (fun j hj k hk => hφ j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_of_lt hk))
        (fun i hi j hj => hword i hi j (Nat.lt_succ_of_lt hj))
      simp only [measWordUncompute, c_eval_useq]
      rw [hψW]
      -- Per-qubit step on the partially-cleared family.
      have hstep := measBitUncompute_perfect (pos W)
        (hpos W (Nat.lt_succ_self W)) (P W) (φ W)
        (hP W (Nat.lt_succ_self W))
        (fun f v => hφ W (Nat.lt_succ_self W) W (Nat.lt_succ_self W) f v)
        s α (fun i => clearWord pos W (g i))
        (fun i hi => by
          -- The partially-cleared family still satisfies bit W's hypothesis:
          -- bit `pos W` is untouched by the clearing, φ W is invariant.
          show clearWord pos W (g i) (pos W) = φ W (clearWord pos W (g i))
          rw [clearWord_apply_ne pos W (g i) (pos W)
                (fun k hk => hinj W (Nat.lt_succ_self W) k (Nat.lt_succ_of_lt hk)
                  (Nat.ne_of_lt hk).symm),
              phase_clearWord pos W (φ W)
                (fun k hk f v =>
                  hφ W (Nat.lt_succ_self W) k (Nat.lt_succ_of_lt hk) f v)
                (g i)]
          exact hword i hi W (Nat.lt_succ_self W))
      simpa only [clearWord] using hstep

/-! ## QROM instantiation (thin: the concrete phase-lookup circuit plugs in here) -/

/-- **QROM-instance corollary**: given ANY phase-fixup family `P` realizing the
    table-lookup phase `φ j f = (T (decAddr f)).testBit j` — with the address
    decoder `decAddr` word-independent — the channel perfectly uncomputes a
    lookup-computed state (word bit `j` holding `T[addr].bit j` on the
    support).  This is the interface the NEXT stage (the concrete
    phase-lookup circuit construction, with its Toffoli count) plugs into:
    it only has to discharge `hP`/`hdec`. -/
theorem measWordUncompute_qrom {dim : Nat} {ι : Type*} (W : Nat)
    (pos : Nat → Nat) (P : Nat → BaseUCom dim)
    (T : Nat → Nat) (decAddr : (Nat → Bool) → Nat)
    (hpos : ∀ j, j < W → pos j < dim)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (hP : ∀ j, j < W → ∀ f, uc_eval (P j) * f_to_vec dim f
            = (if (T (decAddr f)).testBit j then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hdec : ∀ k, k < W → ∀ f v, decAddr (update f (pos k) v) = decAddr f)
    (s : Finset ι) (α : ι → ℂ) (g : ι → Nat → Bool)
    (hword : ∀ i ∈ s, ∀ j, j < W → g i (pos j) = (T (decAddr (g i))).testBit j) :
    c_eval (measWordUncompute dim pos P W)
        ((∑ i ∈ s, α i • f_to_vec dim (g i))
          * (∑ i ∈ s, α i • f_to_vec dim (g i))ᴴ)
      = (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))
          * (∑ i ∈ s, α i • f_to_vec dim (clearWord pos W (g i)))ᴴ :=
  measWordUncompute_perfect W pos P (fun j f => (T (decAddr f)).testBit j)
    hpos hinj hP
    (fun j _ k hk f v => by
      show (T (decAddr (update f (pos k) v))).testBit j = (T (decAddr f)).testBit j
      rw [hdec k hk f v])
    s α g hword

/-! ## Single-basis-state corollary and concrete smoke checks -/

/-- The single lookup-computed basis state `|f⟩` (word bit `j` holding
    `φ j f` for all `j < W`) is mapped to `|f with the word cleared⟩`. -/
theorem measWordUncompute_basis {dim : Nat} (W : Nat)
    (pos : Nat → Nat) (P : Nat → BaseUCom dim) (φ : Nat → (Nat → Bool) → Bool)
    (hpos : ∀ j, j < W → pos j < dim)
    (hinj : ∀ j, j < W → ∀ k, k < W → j ≠ k → pos j ≠ pos k)
    (hP : ∀ j, j < W → ∀ f, uc_eval (P j) * f_to_vec dim f
            = (if φ j f then (-1 : ℂ) else 1) • f_to_vec dim f)
    (hφ : ∀ j, j < W → ∀ k, k < W → ∀ f v, φ j (update f (pos k) v) = φ j f)
    (f : Nat → Bool) (hf : ∀ j, j < W → f (pos j) = φ j f) :
    c_eval (measWordUncompute dim pos P W)
        (f_to_vec dim f * (f_to_vec dim f)ᴴ)
      = f_to_vec dim (clearWord pos W f)
          * (f_to_vec dim (clearWord pos W f))ᴴ := by
  have h := measWordUncompute_perfect (ι := Unit) W pos P φ hpos hinj hP hφ
      Finset.univ (fun _ => (1 : ℂ)) (fun _ => f) (fun _ _ j hj => hf j hj)
  simpa using h

/-- Smoke check (W = 2, phases on): a 3-qubit register with the "address" at
    qubit 0 and a 2-bit word at qubits 1, 2; the phase data is `φ j f = f 0`
    (a 1-entry broadcast table), realized by the concrete diagonal fixup
    `P j = Z 0` (via `f_to_vec_Z_uc_eval`).  The computed state `|111⟩`
    (word bits `1 = f 0`) is uncomputed to `|100⟩`-shape: word cleared,
    address intact. -/
theorem measWordUncompute_smoke_ones :
    c_eval (measWordUncompute 3 (fun j => j + 1) (fun _ => BaseUCom.Z 0) 2)
        (f_to_vec 3 (fun _ => true) * (f_to_vec 3 (fun _ => true))ᴴ)
      = f_to_vec 3 (clearWord (fun j => j + 1) 2 (fun _ => true))
          * (f_to_vec 3 (clearWord (fun j => j + 1) 2 (fun _ => true)))ᴴ :=
  measWordUncompute_basis 2 (fun j => j + 1) (fun _ => BaseUCom.Z 0)
    (fun _ f => f 0)
    (fun j hj => by show j + 1 < 3; omega)
    (fun j _ k _ hjk => by show j + 1 ≠ k + 1; omega)
    (fun j _ f => f_to_vec_Z_uc_eval 3 0 (by norm_num) f)
    (fun j _ k _ f v => update_neq f (k + 1) 0 v (by omega))
    (fun _ => true) (fun _ _ => rfl)

/-- Smoke check (W = 2, phases off): the all-zeros computed state `|000⟩`
    (word bits `0 = f 0`) is a fixed point up to the (trivial) word clear. -/
theorem measWordUncompute_smoke_zeros :
    c_eval (measWordUncompute 3 (fun j => j + 1) (fun _ => BaseUCom.Z 0) 2)
        (f_to_vec 3 (fun _ => false) * (f_to_vec 3 (fun _ => false))ᴴ)
      = f_to_vec 3 (clearWord (fun j => j + 1) 2 (fun _ => false))
          * (f_to_vec 3 (clearWord (fun j => j + 1) 2 (fun _ => false)))ᴴ :=
  measWordUncompute_basis 2 (fun j => j + 1) (fun _ => BaseUCom.Z 0)
    (fun _ f => f 0)
    (fun j hj => by show j + 1 < 3; omega)
    (fun j _ k _ hjk => by show j + 1 ≠ k + 1; omega)
    (fun j _ f => f_to_vec_Z_uc_eval 3 0 (by norm_num) f)
    (fun j _ k _ f v => update_neq f (k + 1) 0 v (by omega))
    (fun _ => false) (fun _ _ => rfl)

end -- noncomputable section

end FormalRV.Shor.MeasuredLookupUncompute
