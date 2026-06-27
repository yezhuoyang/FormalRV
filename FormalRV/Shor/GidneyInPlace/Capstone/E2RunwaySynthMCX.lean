/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX —
  CLEAN-ancilla multi-controlled-X (n-control Toffoli) from CCX.
  ════════════════════════════════════════════════════════════════════════════

  Attempt **B**: a DIRECT structural recursion on the control list with an
  explicit compute / recurse / uncompute ladder, proved by induction.

  CONSTRUCTION (`mcxClean`).  Peel TWO controls at a time, replacing them by a
  single CLEAN accumulator wire that carries their AND:

    * `[]`                 → `X target`        (AND of no controls = `true`)
    * `[c]`                → `CX c target`     (AND = `f c`)
    * `c0 :: c1 :: rest` with `anc = a :: anc'`:
          CCX c0 c1 a ;                         -- a := c0 AND c1  (a clean ⇒ exact)
          mcxClean (a :: rest) target anc' ;    -- recurse: a now stands for AND(c0,c1)
          CCX c0 c1 a                           -- uncompute: restore a to false

  Because the ancilla starts CLEAN (all `false`), the compute step is an exact
  write (`xor false x = x`) and the uncompute step is exact cancellation
  (`xor x x = false`).  This makes the induction yield the FULL function
  equality, from which BOTH the "anc restored clean" and the "frame" clauses
  fall out for free (`update` only touches `target`).

  AND-FORM chosen: `controls.all (fun c => f c)` (Bool).  Recurrence used:
      (c0::c1::rest).all f = (f c0 && f c1) && rest.all f   (Bool.and_assoc),
  matching the accumulator `a := f c0 && f c1`.

  DISTINCTNESS hypothesis: `(controls ++ target :: anc).Nodup`
  (one package giving every pairwise inequality the proof needs), plus the
  length budget `controls.length ≤ anc.length + 1`.

  Kernel-clean target: no `sorry`, no `native_decide`;
  axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import FormalRV.Arithmetic.Correctness

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo

/-! ## §1. The construction. -/

/-- Clean-ancilla multi-controlled-X.  Flips `target` iff every wire in
    `controls` is set, using `anc` as CLEAN (`false`) scratch and RESTORING it. -/
def mcxClean : List Nat → Nat → List Nat → Gate
  | [],            target, _        => Gate.X target
  | [c],           target, _        => Gate.CX c target
  | c0 :: c1 :: rest, target, a :: anc' =>
      Gate.seq (Gate.CCX c0 c1 a)
        (Gate.seq (mcxClean (a :: rest) target anc') (Gate.CCX c0 c1 a))
  -- Degenerate case: ≥2 controls but no ancilla left.  Ruled out by the length
  -- hypothesis in the theorems; defined as a no-op so the function is total.
  | _ :: _ :: _,   _,      []       => Gate.I

/-! ## §2. The AND-form recurrence. -/

/-- `List.all` peels its head as a `Bool` `&&`. -/
theorem all_cons (c : Nat) (cs : List Nat) (f : Nat → Bool) :
    (c :: cs).all (fun x => f x) = (f c && cs.all (fun x => f x)) := by
  simp [List.all_cons]

/-- `List.all` only depends on the predicate at the list's members: if `g`
    and `h` agree on every element of `l`, the `all`s coincide.  (No such
    congruence ships in core/Mathlib for `Bool`-valued `List.all`.) -/
theorem all_congr_mem (l : List Nat) (g h : Nat → Bool)
    (hgh : ∀ x ∈ l, g x = h x) : l.all g = l.all h := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.all_cons, List.all_cons, hgh x (by simp),
        ih (fun y hy => hgh y (by simp [hy]))]

/-! ## §3. Frame: `mcxClean` only ever writes `target`.

    Stronger than needed but trivial to maintain through the induction, and it
    is exactly what discharges both the "anc restored" and "frame" clauses. -/

/-! ## §4. Main correctness — FULL function equality.

    **`mcxClean_apply`** (below).  On a CLEAN ancilla, `mcxClean` flips `target`
    by the AND of all controls and leaves everything else (in particular every
    ancilla wire) exactly as it was.  The single
    `Function.update f target (xor (f target) (controls.all …))` equality
    subsumes the "anc restored clean" and "frame" clauses: `update` agrees with
    `f` at every index `≠ target`. -/

/-- Fuel-bounded core of `mcxClean_apply`.  Strong induction on a length bound
    `n` (rather than structural induction on `controls`) because the recursive
    call peels the head PAIR `c0,c1` and re-prepends the SINGLE accumulator `a`,
    yielding `a :: rest` — same length as `c1 :: rest`, but strictly shorter than
    `c0 :: c1 :: rest`, so a length-bound IH applies where a structural one
    would not. -/
theorem mcxClean_apply_fuel :
    ∀ (n : Nat) (controls : List Nat) (target : Nat) (anc : List Nat)
      (f : Nat → Bool),
      controls.length ≤ n →
      (controls ++ target :: anc).Nodup →
      controls.length ≤ anc.length + 1 →
      (∀ a ∈ anc, f a = false) →
      Gate.applyNat (mcxClean controls target anc) f
        = update f target (xor (f target) (controls.all (fun c => f c))) := by
  intro n
  induction n with
  | zero =>
      intro controls target anc f hn _ _ _
      -- controls.length ≤ 0 ⇒ controls = []
      have : controls = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
      subst this
      simp [mcxClean, List.all_nil]
  | succ n ih =>
      intro controls target anc f hn hnodup hlen hclean
      match controls with
      | [] =>
          simp [mcxClean, List.all_nil]
      | [c] =>
          -- mcxClean [c] target _ = CX c target ; AND = f c
          simp [mcxClean, List.all_cons, List.all_nil, Bool.and_true]
      | c0 :: c1 :: rest =>
          -- anc must be nonempty by the length budget.
          match anc, hlen, hclean with
          | [],       hlen, _      => simp at hlen   -- 2 ≤ 0 + 1 is false
          | a :: anc', hlen, hclean =>
              -- ─── Distinctness atoms extracted from `hnodup` ───────────────
              -- All the pairwise (in)equalities the computation needs.
              have hdist :
                  (¬ c0 = c1 ∧ c0 ∉ rest ∧ ¬ c0 = target ∧ ¬ c0 = a ∧ c0 ∉ anc')
                  ∧ (c1 ∉ rest ∧ ¬ c1 = target ∧ ¬ c1 = a ∧ c1 ∉ anc')
                  ∧ rest.Nodup
                  ∧ ((¬ target = a ∧ target ∉ anc') ∧ a ∉ anc' ∧ anc'.Nodup)
                  ∧ (∀ x ∈ rest, ∀ b, b = target ∨ b = a ∨ b ∈ anc' → x ≠ b) := by
                simpa only [List.cons_append, List.nodup_cons, List.nodup_append,
                  List.mem_cons, List.mem_append, not_or] using hnodup
              obtain ⟨⟨hc0c1, hc0r, hc0t, hc0a, hc0anc⟩,
                      ⟨hc1r, hc1t, hc1a, hc1anc⟩,
                      hrest_nd, ⟨⟨hta, htanc⟩, haanc, hanc_nd⟩, hrest_disj⟩ := hdist
              -- `a ∉ rest` and `rest` disjoint from `target :: anc'` come from
              -- the `∀ x ∈ rest, …` disjointness clause.
              have ha_rest : a ∉ rest := fun h => (hrest_disj a h a (Or.inr (Or.inl rfl))) rfl
              -- ─── Nodup precondition for the IH (`a :: rest ++ target :: anc'`) ─
              have hnd2 : (a :: rest ++ target :: anc').Nodup := by
                have hraw : (rest ++ target :: a :: anc').Nodup := hnodup.of_cons.of_cons
                have hp : List.Perm ((rest ++ [target]) ++ a :: anc')
                      (a :: ((rest ++ [target]) ++ anc')) := List.perm_middle
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hp
                rw [List.cons_append]
                exact hp.nodup_iff.mp hraw
              -- ─── Length & cleanliness preconditions for the IH ────────────
              have hlen2 : (a :: rest).length ≤ anc'.length + 1 := by
                simp only [List.length_cons] at hlen ⊢; omega
              have hn2 : (a :: rest).length ≤ n := by
                simp only [List.length_cons] at hn ⊢; omega
              -- abbreviate the state after the first CCX (compute `a`).
              set f1 : Nat → Bool := update f a (f c0 && f c1) with hf1
              have hf1a : f a = false := hclean a (by simp)
              -- `f1` differs from `f` only at `a`.
              have hclean2 : ∀ x ∈ anc', f1 x = false := by
                intro x hx
                have hxa : x ≠ a := by
                  intro h; subst h; exact haanc hx
                rw [hf1, update_neq f a x _ hxa]
                exact hclean x (by simp [hx])
              -- ─── Apply the IH to the recursive call ───────────────────────
              have hIH := ih (a :: rest) target anc' f1 hn2 hnd2 hlen2 hclean2
              -- Evaluate `(a :: rest).all f1` and `f1 target`.
              have hf1_target : f1 target = f target := by
                rw [hf1, update_neq f a target _ (fun h => hta (h ▸ rfl))]
              have hrest_all : rest.all (fun x => f1 x) = rest.all (fun x => f x) := by
                apply all_congr_mem
                intro x hx
                have hxa : x ≠ a := fun h => ha_rest (h ▸ hx)
                rw [hf1, update_neq f a x _ hxa]
              -- `f1 a = f c0 && f c1` (the compute write).
              have hf1_a : f1 a = (f c0 && f c1) := by rw [hf1, update_eq]
              -- The recursive AND value collapses to the head-pair AND.
              have hall2 : ((a :: rest).all fun c => f1 c)
                  = ((f c0 && f c1) && rest.all (fun x => f x)) := by
                rw [List.all_cons, hf1_a, hrest_all]
              -- Rewrite the IH into a clean post-recursion state `f2`.
              rw [hf1_target, hall2] at hIH
              -- ─── Unfold the circuit and chain the three legs ──────────────
              show Gate.applyNat (Gate.CCX c0 c1 a)
                    (Gate.applyNat (mcxClean (a :: rest) target anc')
                      (Gate.applyNat (Gate.CCX c0 c1 a) f))
                  = update f target (f target ^^ ((c0 :: c1 :: rest).all fun c => f c))
              -- leg 1 (innermost): compute `a`.  `applyNat (CCX c0 c1 a) f = f1`.
              have hleg1 : Gate.applyNat (Gate.CCX c0 c1 a) f = f1 := by
                rw [Gate.applyNat_CCX, hf1a, Bool.false_xor, hf1]
              rw [hleg1, hIH]
              -- Now the goal is the OUTER (uncompute) CCX acting on
              -- `f2 := update f1 target X`.
              set X : Bool := (f target ^^ ((f c0 && f c1) && rest.all (fun x => f x)))
                with hX
              rw [Gate.applyNat_CCX]
              -- `f2 a = f1 a = f c0 && f c1` (a ≠ target).
              have hf2_a : (update f1 target X) a = (f c0 && f c1) := by
                rw [update_neq f1 target a X (fun h => hta (h ▸ rfl)), hf1_a]
              -- `f2 c0 = f c0`, `f2 c1 = f c1` (cᵢ ≠ target, cᵢ ≠ a).
              have hf2_c0 : (update f1 target X) c0 = f c0 := by
                rw [update_neq f1 target c0 X hc0t, hf1,
                  update_neq f a c0 _ hc0a]
              have hf2_c1 : (update f1 target X) c1 = f c1 := by
                rw [update_neq f1 target c1 X hc1t, hf1,
                  update_neq f a c1 _ hc1a]
              rw [hf2_a, hf2_c0, hf2_c1, Bool.xor_self]
              -- Final state: `update (update f1 target X) a false`.  Commute the
              -- two updates (target ≠ a) and collapse the pair at `a`.
              have htarget_ne_a : target ≠ a := fun h => hta (h ▸ rfl)
              rw [update_comm f1 target a X false htarget_ne_a, hf1, update_idem,
                ← hf1a, update_self]
              -- Goal now: `update f target X = update f target (f target ^^ AND)`.
              -- Reconcile the two AND-forms via `Bool.and_assoc`.
              rw [hX]
              congr 1
              rw [all_cons, all_cons, Bool.and_assoc]

theorem mcxClean_apply
    (controls : List Nat) (target : Nat) (anc : List Nat) (f : Nat → Bool)
    (hnodup : (controls ++ target :: anc).Nodup)
    (hlen : controls.length ≤ anc.length + 1)
    (hclean : ∀ a ∈ anc, f a = false) :
    Gate.applyNat (mcxClean controls target anc) f
      = update f target (xor (f target) (controls.all (fun c => f c))) :=
  mcxClean_apply_fuel controls.length controls target anc f (le_refl _)
    hnodup hlen hclean

/-! ## §5. Well-typedness. -/

/-- Fuel-bounded core of `mcxClean_wellTyped`.  Same length-bound induction as
    the correctness proof; each ladder `CCX c0 c1 a` is well-typed because the
    three wires are `< dim` and pairwise distinct (read off the `Nodup`), and the
    recursive call inherits its bounds. -/
theorem mcxClean_wellTyped_fuel :
    ∀ (n : Nat) (controls : List Nat) (target : Nat) (anc : List Nat) (dim : Nat),
      controls.length ≤ n →
      (controls ++ target :: anc).Nodup →
      controls.length ≤ anc.length + 1 →
      (∀ x ∈ controls, x < dim) → target < dim → (∀ x ∈ anc, x < dim) →
      Gate.WellTyped dim (mcxClean controls target anc) := by
  intro n
  induction n with
  | zero =>
      intro controls target anc dim hn _ _ _ htgt _
      have : controls = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hn)
      subst this
      -- mcxClean [] target _ = X target ; WellTyped = target < dim
      rw [mcxClean]; exact htgt
  | succ n ih =>
      intro controls target anc dim hn hnodup hlen hcb htgt hab
      match controls with
      | [] => rw [mcxClean]; exact htgt
      | [c] =>
          -- mcxClean [c] target _ = CX c target ; need c<dim, target<dim, c≠target.
          rw [mcxClean]
          refine ⟨hcb c (by simp), htgt, ?_⟩
          have := hnodup            -- (c :: target :: anc).Nodup
          simp only [List.cons_append, List.nil_append, List.nodup_cons,
            List.mem_cons] at this
          exact fun h => this.1 (Or.inl h)
      | c0 :: c1 :: rest =>
          match anc, hlen, hab with
          | [],        hlen, _   => simp at hlen
          | a :: anc', hlen, hab =>
              -- Distinctness atoms (same extraction as in `mcxClean_apply`).
              have hdist :
                  (¬ c0 = c1 ∧ c0 ∉ rest ∧ ¬ c0 = target ∧ ¬ c0 = a ∧ c0 ∉ anc')
                  ∧ (c1 ∉ rest ∧ ¬ c1 = target ∧ ¬ c1 = a ∧ c1 ∉ anc')
                  ∧ rest.Nodup
                  ∧ ((¬ target = a ∧ target ∉ anc') ∧ a ∉ anc' ∧ anc'.Nodup)
                  ∧ (∀ x ∈ rest, ∀ b, b = target ∨ b = a ∨ b ∈ anc' → x ≠ b) := by
                simpa only [List.cons_append, List.nodup_cons, List.nodup_append,
                  List.mem_cons, List.mem_append, not_or] using hnodup
              obtain ⟨⟨hc0c1, hc0r, _hc0t, hc0a, _hc0anc⟩,
                      ⟨_hc1r, _hc1t, hc1a, _hc1anc⟩,
                      _hrest_nd, ⟨⟨_hta, _htanc⟩, haanc, _hanc_nd⟩, hrest_disj⟩ := hdist
              have ha_rest : a ∉ rest :=
                fun h => (hrest_disj a h a (Or.inr (Or.inl rfl))) rfl
              -- Nodup for the recursive call.
              have hnd2 : (a :: rest ++ target :: anc').Nodup := by
                have hraw : (rest ++ target :: a :: anc').Nodup := hnodup.of_cons.of_cons
                have hp : List.Perm ((rest ++ [target]) ++ a :: anc')
                      (a :: ((rest ++ [target]) ++ anc')) := List.perm_middle
                simp only [List.append_assoc, List.cons_append, List.nil_append] at hp
                rw [List.cons_append]
                exact hp.nodup_iff.mp hraw
              have hlen2 : (a :: rest).length ≤ anc'.length + 1 := by
                simp only [List.length_cons] at hlen ⊢; omega
              have hn2 : (a :: rest).length ≤ n := by
                simp only [List.length_cons] at hn ⊢; omega
              have ha_dim : a < dim := hab a (by simp)
              have hc0_dim : c0 < dim := hcb c0 (by simp)
              have hc1_dim : c1 < dim := hcb c1 (by simp)
              -- Bounds for the recursive control list `a :: rest`.
              have hcb2 : ∀ x ∈ (a :: rest), x < dim := by
                intro x hx
                rcases List.mem_cons.mp hx with h | h
                · subst h; exact ha_dim
                · exact hcb x (by simp [h])
              have hab2 : ∀ x ∈ anc', x < dim := fun x hx => hab x (by simp [hx])
              rw [mcxClean]
              refine ⟨⟨hc0_dim, hc1_dim, ha_dim, hc0c1, hc0a, hc1a⟩, ?_,
                ⟨hc0_dim, hc1_dim, ha_dim, hc0c1, hc0a, hc1a⟩⟩
              exact ih (a :: rest) target anc' dim hn2 hnd2 hlen2 hcb2 htgt hab2

/-- **`mcxClean_wellTyped`.**  When every control, the target, and every ancilla
    is `< dim` (and they are distinct with enough ancillae), `mcxClean` is a
    well-typed `dim`-qubit circuit. -/
theorem mcxClean_wellTyped
    (controls : List Nat) (target : Nat) (anc : List Nat) (dim : Nat)
    (hnodup : (controls ++ target :: anc).Nodup)
    (hlen : controls.length ≤ anc.length + 1)
    (hcb : ∀ x ∈ controls, x < dim) (htgt : target < dim)
    (hab : ∀ x ∈ anc, x < dim) :
    Gate.WellTyped dim (mcxClean controls target anc) :=
  mcxClean_wellTyped_fuel controls.length controls target anc dim (le_refl _)
    hnodup hlen hcb htgt hab

/-! ## §6. Smoke checks (definitional). -/

-- 0 controls → `X target`; 1 control → `CX`.
example (t : Nat) : mcxClean [] t [] = Gate.X t := rfl
example (c t : Nat) : mcxClean [c] t [] = Gate.CX c t := rfl
-- 2 controls `[c0, c1]` match the ladder clause with `rest = []`, so they need
-- one ancilla `a`; the inner recursive call `mcxClean [a] t []` is `CX a t`.
example (c0 c1 t a : Nat) :
    mcxClean [c0, c1] t [a]
      = Gate.seq (Gate.CCX c0 c1 a)
          (Gate.seq (Gate.CX a t) (Gate.CCX c0 c1 a)) := rfl

-- 3 controls with two ancillae: the full compute / recurse / uncompute ladder.
example (c0 c1 c2 t a0 a1 : Nat) :
    mcxClean [c0, c1, c2] t [a0, a1]
      = Gate.seq (Gate.CCX c0 c1 a0)
          (Gate.seq
            (Gate.seq (Gate.CCX a0 c2 a1)
              (Gate.seq (Gate.CX a1 t) (Gate.CCX a0 c2 a1)))
            (Gate.CCX c0 c1 a0)) := rfl

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwaySynthMCX
