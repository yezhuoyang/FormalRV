/-
  FormalRV.Shor.WindowedComposed — the FULL modular exponentiation, composed end-to-end
  from the *actual lookup-addition primitive Gidney implements*.

  Gidney–Ekerå (arXiv:1905.09749) line 594: each table lookup is "Babbush et al.'s QROM read
  (section 3A of [babbush2018])", costing `2^{g_mul+g_exp}` Toffolis, and line 593: each
  addition uses "Cuccaro et al.'s adder", costing `2n`.  That lookup-addition is *exactly*
  `MeasUncompute.babbushLookupAdd` (unary QROM read · Cuccaro add · measure-clear).

  The paper's cost decomposition (lines 693–697):
    • an exponentiation = `numMults` windowed modular multiplications  (line 693)
    • each multiplication = 2 multiply-adds                            (line 694)
    • each multiply-add  = `numWin` lookup-additions                   (lines 696–697)
  Here we BUILD that nesting as one `EGate` and read off ONE structural Toffoli count
    `toffoli_modExp = numMults · 2 · numWin · ((2^w − 1) + 2·bits)`,
  composed from `babbushLookupAdd` — not three separate isolated counts.  The bridge from
  this structural count to the paper's reported `0.3 n³` total (and the precisely-named gap)
  is in `WindowedComposedCost.lean`.

  (Counts only; each primitive's *semantics* is verified separately — `WindowedCircuitExec`
  for the multiplier value, `MeasUncomputeExec` for the QROM read.  Per-window qubit layout is
  a parameter and does not affect the Toffoli count.)
-/
import FormalRV.Shor.MeasUncompute
import FormalRV.Arithmetic.Windowed.WindowedCircuit

namespace FormalRV.Shor.WindowedComposed

open FormalRV.Framework FormalRV.BQAlgo FormalRV.Shor.MeasUncompute

/-! ### Folding a sequence of sub-circuits, with additive Toffoli accounting -/

/-- Sequence a list of `EGate`s left-to-right (identity seed). -/
def seqAll (gs : List EGate) : EGate := gs.foldl EGate.seq (EGate.base Gate.I)

/-- `EGate.tcount` of a left fold with a constant per-element T-count. -/
theorem tcount_foldl_seq_const (seed : EGate) (gs : List EGate) (c : Nat)
    (h : ∀ g ∈ gs, EGate.tcount g = c) :
    EGate.tcount (gs.foldl EGate.seq seed) = EGate.tcount seed + gs.length * c := by
  induction gs generalizing seed with
  | nil => simp
  | cons g gs ih =>
      have hg : EGate.tcount g = c := h g (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ x ∈ gs, EGate.tcount x = c := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (EGate.seq seed g) hrest]
      simp only [EGate.tcount, hg]
      ring

/-- `EGate.tcount` of `seqAll` over a list whose elements all have T-count `c`. -/
theorem tcount_seqAll_const (gs : List EGate) (c : Nat) (h : ∀ g ∈ gs, EGate.tcount g = c) :
    EGate.tcount (seqAll gs) = gs.length * c := by
  unfold seqAll
  rw [tcount_foldl_seq_const _ _ c h]
  simp [EGate.tcount, Gate.tcount]

/-! ### The lookup-addition primitive's exact T-count -/

/-- `babbushLookupAdd` has T-count `7·((2^w − 1) + 2·bits)` — i.e. Toffoli `(2^w−1)+2·bits`:
    the babbush unary read (`2^w−1`) plus the Cuccaro adder (`2·bits`), measure-uncompute free. -/
theorem tcount_babbushLookupAdd (w W : Nat) (T : Nat → Nat)
    (bits addrBase ancBase outBase q_start : Nat) :
    EGate.tcount (babbushLookupAdd w W T bits addrBase ancBase outBase q_start)
      = 7 * ((2 ^ w - 1) + 2 * bits) := by
  unfold babbushLookupAdd
  simp only [EGate.tcount, tcount_mzList, tcount_unaryQROM, tcount_cuccaro_n_bit_adder_full]
  ring

/-! ### The composed circuit: multiply-add → multiplication → exponentiation -/

/-- The `k`-th window's lookup-addition, placed in its own qubit region (layout is a parameter;
    the Toffoli count is layout-independent). -/
def laK (w W bits : Nat) (T : Nat → Nat) (base k : Nat) : EGate :=
  let b := base + k * (4 * w + 2 * bits + 1)
  babbushLookupAdd w W T bits b (b + w) (b + 2 * w) (b + 3 * w)

theorem tcount_laK (w W bits : Nat) (T : Nat → Nat) (base k : Nat) :
    EGate.tcount (laK w W bits T base k) = 7 * ((2 ^ w - 1) + 2 * bits) := by
  unfold laK; exact tcount_babbushLookupAdd _ _ _ _ _ _ _ _

/-- **A multiply-add** = `numWin` babbush lookup-additions (paper lines 696–697). -/
def multiplyAdd (w W bits : Nat) (T : Nat → Nat) (base numWin : Nat) : EGate :=
  seqAll ((List.range numWin).map (laK w W bits T base))

theorem tcount_multiplyAdd (w W bits : Nat) (T : Nat → Nat) (base numWin : Nat) :
    EGate.tcount (multiplyAdd w W bits T base numWin)
      = numWin * (7 * ((2 ^ w - 1) + 2 * bits)) := by
  unfold multiplyAdd
  rw [tcount_seqAll_const _ (7 * ((2 ^ w - 1) + 2 * bits))]
  · simp [List.length_map, List.length_range]
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, _, rfl⟩ := hg
    exact tcount_laK _ _ _ _ _ _

/-- **A windowed modular multiplication** = two multiply-adds (paper line 694). -/
def multiplication (w W bits : Nat) (T : Nat → Nat) (base numWin : Nat) : EGate :=
  EGate.seq (multiplyAdd w W bits T base numWin) (multiplyAdd w W bits T base numWin)

theorem tcount_multiplication (w W bits : Nat) (T : Nat → Nat) (base numWin : Nat) :
    EGate.tcount (multiplication w W bits T base numWin)
      = 2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))) := by
  unfold multiplication
  simp only [EGate.tcount, tcount_multiplyAdd]
  ring

/-- **The full modular exponentiation** = `numMults` windowed multiplications (paper line 693),
    composed from `babbushLookupAdd`. -/
def modExp (w W bits : Nat) (T : Nat → Nat) (numMults numWin : Nat) : EGate :=
  seqAll ((List.range numMults).map (fun j => multiplication w W bits T j numWin))

theorem tcount_modExp (w W bits : Nat) (T : Nat → Nat) (numMults numWin : Nat) :
    EGate.tcount (modExp w W bits T numMults numWin)
      = numMults * (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits)))) := by
  unfold modExp
  rw [tcount_seqAll_const _ (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))))]
  · simp [List.length_map, List.length_range]
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨j, _, rfl⟩ := hg
    exact tcount_multiplication _ _ _ _ _ _

/-- **★ END-TO-END STRUCTURAL TOFFOLI COUNT ★** of the full modular exponentiation,
    composed from the babbush lookup-addition Gidney actually implements:
      `numMults · 2 · numWin · ((2^w − 1) + 2·bits)`. -/
theorem toffoli_modExp (w W bits : Nat) (T : Nat → Nat) (numMults numWin : Nat) :
    EGate.toffoli (modExp w W bits T numMults numWin)
      = numMults * 2 * numWin * ((2 ^ w - 1) + 2 * bits) := by
  unfold EGate.toffoli
  rw [tcount_modExp,
      show numMults * (2 * (numWin * (7 * ((2 ^ w - 1) + 2 * bits))))
         = (numMults * 2 * numWin * ((2 ^ w - 1) + 2 * bits)) * 7 by ring]
  exact Nat.mul_div_cancel _ (by norm_num)

/-- The number of lookup-additions in the composed exponentiation, structurally. -/
def lookupAddCount (numMults numWin : Nat) : Nat := numMults * 2 * numWin

/-- The structural count, expressed as (lookup-addition count) · (per-lookup-addition cost) —
    the same factored shape as the paper's `ToffoliCount = LookupAdditionCount · perLookup`. -/
theorem toffoli_modExp_factored (w W bits : Nat) (T : Nat → Nat) (numMults numWin : Nat) :
    EGate.toffoli (modExp w W bits T numMults numWin)
      = lookupAddCount numMults numWin * ((2 ^ w - 1) + 2 * bits) := by
  rw [toffoli_modExp]; unfold lookupAddCount; ring

end FormalRV.Shor.WindowedComposed
