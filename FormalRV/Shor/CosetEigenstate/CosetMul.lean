/-
  FormalRV.Shor.CosetEigenstate.CosetMul — the out-of-place coset multiplier as a
  fold of (controlled) coset additions, with subadditive total deviation.
  ════════════════════════════════════════════════════════════════════════════

  The windowed coset multiplier computes `a·x mod N` by a sequence of `numAdds`
  modular additions into a coset-encoded accumulator (each addition adds a windowed
  lookup value `< N`, conditioned on a control bit of the multiplicand/exponent).

  This file composes the per-addition deviation (`cosetState_addConst_deviation`)
  over the whole fold.  The engine is `normSqDist_fold_accum`:

      dev(t+1) ≤ normSqDist (op_t act_t) (op_t idl_t)         -- triangle
                   + normSqDist (op_t idl_t) idl_{t+1}
               ≤ dev(t)                                       -- op_t NON-EXPANSIVE
                   + (2/2^m)                                  -- per-step deviation
               ⟹ dev(T) ≤ T·(2/2^m).

  The accumulation runs the ACTUAL (non-modular `shiftState`) chain against the
  IDEAL (reduced, mod-`N`) chain.  Because `shiftState` is non-expansive
  (`shiftState_normSqDist_nonexpansive`), overflow in the actual chain is absorbed,
  so the bound needs ONLY the per-step fit `N + 2^m·N ≤ dim` — never a running-sum
  fit.  This is exactly the Gidney subadditivity (arXiv:1905.08488, Thms 2.11–2.12)
  realized on the real coset states.

  This is the per-control-branch deviation; lifting it across a superposition over
  the control register is `ControlledLift.normSqDist_controlled_lift*`.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp
import FormalRV.Shor.CosetEigenstate.ControlledLift

namespace FormalRV.Shor.CosetEigenstate.CosetMul

open FormalRV.SQIRPort
open FormalRV.SQIRPort.ApproxTransfer
open FormalRV.Shor.CosetEigenstate.ApproxOp
open FormalRV.Shor.CosetEigenstate.ControlledLift (branchOf normSqDist_controlled_lift_subnormalized)

/-- **The general fold-accumulation engine (Gidney subadditivity).**  Given an
    ACTUAL chain `act` (each step `op t`), an IDEAL chain `idl`, where every `op t`
    is non-expansive in `normSqDist` and the ideal step deviation is `≤ d`, and the
    chains agree at the start, the endpoint deviation after `T` steps is `≤ T·d`. -/
theorem normSqDist_fold_accum {dim : Nat} (act idl : Nat → QState dim)
    (op : Nat → QState dim → QState dim) (d : ℝ)
    (hact : ∀ t, act (t + 1) = op t (act t))
    (hnonexp : ∀ t s₁ s₂, normSqDist (op t s₁) (op t s₂) ≤ normSqDist s₁ s₂)
    (hstep : ∀ t, normSqDist (op t (idl t)) (idl (t + 1)) ≤ d)
    (hbase : act 0 = idl 0) :
    ∀ T, normSqDist (act T) (idl T) ≤ (T : ℝ) * d := by
  intro T
  induction T with
  | zero => rw [hbase]; simp [normSqDist]
  | succ n ih =>
      have htri : normSqDist (act (n + 1)) (idl (n + 1))
          ≤ normSqDist (op n (act n)) (op n (idl n))
            + normSqDist (op n (idl n)) (idl (n + 1)) := by
        rw [hact n]; exact normSqDist_triangle _ _ _
      calc normSqDist (act (n + 1)) (idl (n + 1))
          ≤ normSqDist (op n (act n)) (op n (idl n))
            + normSqDist (op n (idl n)) (idl (n + 1)) := htri
        _ ≤ normSqDist (act n) (idl n) + d := by
            have := hnonexp n (act n) (idl n); have := hstep n; linarith
        _ ≤ (n : ℝ) * d + d := by linarith [ih]
        _ = ((n + 1 : Nat) : ℝ) * d := by push_cast; ring

/-! ## §2. The coset multiplier fold (per control branch). -/

/-- The IDEAL modular accumulator: start at `k₀`, fold the addends `cs` mod `N`. -/
def idealAcc (N k₀ : Nat) (cs : Nat → Nat) : Nat → Nat
  | 0 => k₀
  | t + 1 => (idealAcc N k₀ cs t + cs t) % N

/-- The ACTUAL (non-modular) accumulator state: fold `shiftState (cs t)` over the
    initial coset state.  (The real reversible adder, in the no-overflow regime.) -/
noncomputable def actualAcc (dim N m k₀ : Nat) (cs : Nat → Nat) : Nat → QState dim
  | 0 => cosetState dim N m k₀
  | t + 1 => shiftState dim (cs t) (actualAcc dim N m k₀ cs t)

/-- The ideal accumulator stays a canonical residue `< N`. -/
theorem idealAcc_lt (N k₀ : Nat) (cs : Nat → Nat) (hN : 0 < N) (hk₀ : k₀ < N) :
    ∀ t, idealAcc N k₀ cs t < N
  | 0 => hk₀
  | _ + 1 => Nat.mod_lt _ hN

/-- **THE OUT-OF-PLACE COSET MULTIPLIER DEVIATION (per control branch).**  After
    `T` non-modular additions (each addend `< N`) into a coset-encoded accumulator,
    the ACTUAL state is within `T·(2/2^m)` (in `normSqDist`) of the IDEAL reduced
    coset state `cosetState N m (idealAcc T)`.  This is the windowed multiply's total
    deviation `numAdds·(2/2^m)`, proved by subadditive accumulation of the
    single-addition deviation — needing only the per-step fit `N + 2^m·N ≤ dim`. -/
theorem cosetMulOutOfPlace_deviation (dim N m k₀ : Nat) (cs : Nat → Nat)
    (hN : 0 < N) (hk₀ : k₀ < N) (hcs : ∀ t, cs t < N) (hfit : N + 2 ^ m * N ≤ dim)
    (T : Nat) :
    normSqDist (actualAcc dim N m k₀ cs T) (cosetState dim N m (idealAcc N k₀ cs T))
      ≤ (T : ℝ) * (2 / 2 ^ m) := by
  refine normSqDist_fold_accum
    (act := actualAcc dim N m k₀ cs)
    (idl := fun t => cosetState dim N m (idealAcc N k₀ cs t))
    (op := fun t => shiftState dim (cs t)) (d := 2 / 2 ^ m)
    (fun t => rfl)
    (fun t s₁ s₂ => shiftState_normSqDist_nonexpansive _ _ _)
    (fun t => ?_)
    rfl T
  exact cosetState_addConst_deviation dim N m (idealAcc N k₀ cs t) (cs t) hN
    (idealAcc_lt N k₀ cs hN hk₀ t) (hcs t) hfit

/-! ## §3. The superposition capstone (lift over the control register). -/

/-- **THE OUT-OF-PLACE COSET MULTIPLIER ON A SUPERPOSITION (the capstone).**  The
    full multiplier acts on an arbitrary (sub-normalized) superposition over the
    control register: in each control branch `x`, the data register runs the coset
    fold with addend sequence `cs x` (a control=0 step is the no-op addend `0`:
    `shiftState 0 = id`, `(acc+0)%N = acc`), so every branch runs `numAdds` steps
    with per-branch deviation `≤ numAdds·(2/2^m)` by `cosetMulOutOfPlace_deviation`.
    The control register is preserved, so the sub-normalized controlled lift keeps
    the WHOLE-REGISTER Born-L1 deviation at `≤ numAdds·(2/2^m)` — the per-branch
    bound, UNAMPLIFIED by superposing over the control.  This is the windowed coset
    multiplier's total deviation, valid on quantum superpositions, not just classical
    basis controls. -/
theorem cosetMul_superposition_deviation
    {m_dim full_dim : Nat} (h : m_dim ∣ full_dim)
    (s_act s_idl : QState full_dim) (active : Finset (Fin m_dim)) (β : Fin m_dim → ℂ)
    (N m k₀ numAdds : Nat) (cs : Fin m_dim → Nat → Nat)
    (hN : 0 < N) (hk₀ : k₀ < N) (hcs : ∀ x t, cs x t < N)
    (hfit : N + 2 ^ m * N ≤ full_dim / m_dim)
    (hzero : ∀ x, x ∉ active → branchOf h s_act x = branchOf h s_idl x)
    (hfac_act : ∀ x, x ∈ active →
        branchOf h s_act x
          = fun i z => β x * actualAcc (full_dim / m_dim) N m k₀ (cs x) numAdds i z)
    (hfac_idl : ∀ x, x ∈ active →
        branchOf h s_idl x
          = fun i z => β x * cosetState (full_dim / m_dim) N m (idealAcc N k₀ (cs x) numAdds) i z)
    (hweight : ∑ x ∈ active, Complex.normSq (β x) ≤ 1) :
    normSqDist s_act s_idl ≤ (numAdds : ℝ) * (2 / 2 ^ m) := by
  refine normSqDist_controlled_lift_subnormalized h s_act s_idl active β
    ((numAdds : ℝ) * (2 / 2 ^ m)) (by positivity)
    (fun x => actualAcc (full_dim / m_dim) N m k₀ (cs x) numAdds)
    (fun x => cosetState (full_dim / m_dim) N m (idealAcc N k₀ (cs x) numAdds))
    hzero hfac_act hfac_idl (fun x _ => ?_) hweight
  exact cosetMulOutOfPlace_deviation (full_dim / m_dim) N m k₀ (cs x) hN hk₀ (hcs x) hfit numAdds

end FormalRV.Shor.CosetEigenstate.CosetMul
