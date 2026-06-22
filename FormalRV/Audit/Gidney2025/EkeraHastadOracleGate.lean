/-
  FormalRV.Audit.Gidney2025.EkeraHastadOracleGate — the CONCRETE reversible gate circuit for the
  Ekerå–Håstad oracle `|x⟩|y⟩|0⟩_T ↦ |x⟩|y⟩|x − y·d + 2^(ℓ+m)⟩_T`, built from the verified Cuccaro
  constant-add / controlled-add gadgets, with its T-count (resource) computed in closed form.

  The oracle is the affine integer map `x − y·d + 2^(ℓ+m)` (no modular reduction), realized as a
  uniform sequence of conditional constant additions on a target block of width `w = ℓ+m+1`:
    * `+ 2^(ℓ+m)`                                   (the offset, uncontrolled)
    * for each control bit `x_i` (i < ℓ+m):  `+ 2^i`  controlled on qubit `i`           (adds `x`)
    * for each control bit `y_i` (i < ℓ):    `− d·2^i` controlled on qubit `(ℓ+m)+i`     (subtracts `y·d`)

  This file establishes the GATE and its **resource count** (`ehOracleGate_tcount`):
    `tcount (ehOracleGate ℓ m d) = 14 · (ℓ+m+1) · (2ℓ+m+1)`.

  The Boolean correctness (`Gate.applyNat` = the encoding), the layout transport to the QFT's
  contiguous control⊗target tensor structure, and the clean-ancilla composition into the measured
  `≥ 1/8` bound are the subsequent milestones (the multiply-accumulate is the substantial proof).

  No `sorry`, no `native_decide`.
-/
import FormalRV.Arithmetic.Cuccaro.CuccaroAddConst
import FormalRV.Arithmetic.Cuccaro.CuccaroSubConst
import FormalRV.Arithmetic.Cuccaro.CuccaroSQIRCondAdd
import FormalRV.Arithmetic.Cuccaro.CuccaroVariantsResource
import FormalRV.Verifier.ProofGate

namespace FormalRV.Audit.Gidney2025.EkeraHastadOracleGate

open FormalRV.Framework
open FormalRV.Framework.Gate (tcount)
open FormalRV.BQAlgo

/-- Target/scratch register width: holds `x − y·d + 2^(ℓ+m) ∈ [0, 2^(ℓ+m+1))`. -/
def ehW (ℓ m : ℕ) : ℕ := ℓ + m + 1

/-- The Cuccaro gadget block starts just above the two control registers (`A : ℓ+m`, `B : ℓ`). -/
def ehQStart (ℓ m : ℕ) : ℕ := (ℓ + m) + ℓ

/-- The list of gadget circuits the oracle is composed of: the offset add, the `ℓ+m` controlled adds
realizing `+x`, and the `ℓ` controlled subtracts realizing `− y·d`. -/
def ehGadgets (ℓ m d : ℕ) : List Gate :=
  cuccaro_addConstGate (ehW ℓ m) (ehQStart ℓ m) (2 ^ (ℓ + m))
    :: ((List.range (ℓ + m)).map
          (fun i => sqir_conditionalAddConstGate (ehW ℓ m) (ehQStart ℓ m) (2 ^ i) i)
        ++ (List.range ℓ).map
          (fun i => sqir_conditionalSubConstGate (ehW ℓ m) (ehQStart ℓ m) (d * 2 ^ i) ((ℓ + m) + i)))

/-- **The concrete Ekerå–Håstad oracle gate** — sequential composition of the gadget list. -/
def ehOracleGate (ℓ m d : ℕ) : Gate :=
  (ehGadgets ℓ m d).foldr Gate.seq Gate.I

/-! ## §1. Per-gadget T-counts -/

/-- The masked-prepare step is Clifford (CX/X only) — zero T-count. -/
theorem tcount_sqir_prepareMaskedConstRead (bits q_start N flagPos : ℕ) :
    tcount (sqir_prepareMaskedConstRead bits q_start N flagPos) = 0 := by
  induction bits with
  | zero => rfl
  | succ k ih =>
      have e : sqir_prepareMaskedConstRead (k + 1) q_start N flagPos
          = Gate.seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I) := rfl
      rw [e]
      have hseq : tcount (Gate.seq (sqir_prepareMaskedConstRead k q_start N flagPos)
              (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I))
          = tcount (sqir_prepareMaskedConstRead k q_start N flagPos)
              + tcount (cond (N.testBit k) (Gate.CX flagPos (q_start + 2 * k + 2)) Gate.I) := rfl
      rw [hseq, ih]
      cases N.testBit k <;> rfl

/-- The controlled add-constant gadget has the adder's T-count (the masks are free). -/
theorem tcount_condAdd (bits q_start N flagPos : ℕ) :
    tcount (sqir_conditionalAddConstGate bits q_start N flagPos) = 14 * bits := by
  have e : sqir_conditionalAddConstGate bits q_start N flagPos
      = Gate.seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
          (Gate.seq (cuccaro_n_bit_adder_full bits q_start)
            (sqir_prepareMaskedConstRead bits q_start N flagPos)) := rfl
  rw [e]
  have hseq : tcount (Gate.seq (sqir_prepareMaskedConstRead bits q_start N flagPos)
          (Gate.seq (cuccaro_n_bit_adder_full bits q_start)
            (sqir_prepareMaskedConstRead bits q_start N flagPos)))
      = tcount (sqir_prepareMaskedConstRead bits q_start N flagPos)
          + (tcount (cuccaro_n_bit_adder_full bits q_start)
              + tcount (sqir_prepareMaskedConstRead bits q_start N flagPos)) := rfl
  rw [hseq, tcount_sqir_prepareMaskedConstRead, tcount_cuccaro_n_bit_adder_full]
  omega

/-- The controlled sub-constant gadget = controlled add of the complement; same T-count. -/
theorem tcount_condSub (bits q_start N flagPos : ℕ) :
    tcount (sqir_conditionalSubConstGate bits q_start N flagPos) = 14 * bits := by
  have e : sqir_conditionalSubConstGate bits q_start N flagPos
      = sqir_conditionalAddConstGate bits q_start (2 ^ bits - N) flagPos := rfl
  rw [e, tcount_condAdd]

/-! ## §2. The oracle's resource count -/

/-- T-count of a `foldr Gate.seq Gate.I` over a gadget list = sum of the gadgets' T-counts. -/
theorem tcount_foldr_seq (L : List Gate) :
    tcount (L.foldr Gate.seq Gate.I) = (L.map tcount).sum := by
  induction L with
  | nil => rfl
  | cons g rest ih =>
      have hseq : tcount (Gate.seq g (rest.foldr Gate.seq Gate.I))
          = tcount g + tcount (rest.foldr Gate.seq Gate.I) := rfl
      show tcount (Gate.seq g (rest.foldr Gate.seq Gate.I)) = _
      rw [hseq, ih, List.map_cons, List.sum_cons]

/-- Every gadget in the oracle has T-count `14 · (ℓ+m+1)`. -/
theorem tcount_ehGadgets_uniform (ℓ m d : ℕ) :
    ∀ g ∈ ehGadgets ℓ m d, tcount g = 14 * ehW ℓ m := by
  intro g hg
  rcases List.mem_cons.mp hg with h | h
  · subst h; exact tcount_cuccaro_addConstGate _ _ _
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_map.mp h with ⟨i, _, rfl⟩; exact tcount_condAdd _ _ _ _
    · rcases List.mem_map.mp h with ⟨i, _, rfl⟩; exact tcount_condSub _ _ _ _

/-- **★ The Ekerå–Håstad oracle gate's T-count. ★**
`tcount (ehOracleGate ℓ m d) = 14 · (ℓ+m+1) · (2ℓ+m+1)` — one offset add, `ℓ+m` controlled adds, and
`ℓ` controlled subtracts, each a width-`(ℓ+m+1)` Cuccaro adder (`14·(ℓ+m+1)` T-gates). -/
theorem ehOracleGate_tcount (ℓ m d : ℕ) :
    tcount (ehOracleGate ℓ m d) = 14 * (ℓ + m + 1) * (2 * ℓ + m + 1) := by
  unfold ehOracleGate
  rw [tcount_foldr_seq, List.map_congr_left (tcount_ehGadgets_uniform ℓ m d),
      List.map_const', List.sum_replicate, smul_eq_mul]
  unfold ehGadgets ehW
  simp only [List.length_cons, List.length_append, List.length_map, List.length_range]
  ring

/-! ## §3. Well-typedness -/

/-- Total register width: the two control registers (`A : ℓ+m`, `B : ℓ`) plus the Cuccaro gadget
block (`2·(ℓ+m+1) + 1` qubits: scratch read + target `T` + carry). -/
def ehDim (ℓ m : ℕ) : ℕ := ehQStart ℓ m + 2 * ehW ℓ m + 1

/-- `WellTyped` is preserved by `foldr Gate.seq Gate.I` when every gadget is well-typed. -/
theorem wellTyped_foldr_seq (dim : ℕ) (hdim : 0 < dim) (L : List Gate)
    (h : ∀ g ∈ L, Gate.WellTyped dim g) :
    Gate.WellTyped dim (L.foldr Gate.seq Gate.I) := by
  induction L with
  | nil => exact hdim
  | cons g rest ih =>
      exact ⟨h g (by simp),
             ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))⟩

/-- **★ The Ekerå–Håstad oracle gate is well-typed on `ehDim` qubits. ★** -/
theorem ehOracleGate_wellTyped (ℓ m d : ℕ) :
    Gate.WellTyped (ehDim ℓ m) (ehOracleGate ℓ m d) := by
  unfold ehOracleGate
  have hws : ehQStart ℓ m + 2 * ehW ℓ m + 1 ≤ ehDim ℓ m := le_refl _
  refine wellTyped_foldr_seq _ (by unfold ehDim; omega) _ ?_
  intro g hg
  rcases List.mem_cons.mp hg with h | h
  · subst h
    exact cuccaro_addConstGate_wellTyped (ehW ℓ m) (ehQStart ℓ m) (2 ^ (ℓ + m)) (ehDim ℓ m) hws
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
      have hi' : i < ℓ + m := List.mem_range.mp hi
      refine sqir_conditionalAddConstGate_wellTyped (ehW ℓ m) (ehQStart ℓ m) (2 ^ i) i (ehDim ℓ m)
        hws (by unfold ehDim ehQStart; omega) (fun j _ => by unfold ehQStart; omega)
    · rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
      have hi' : i < ℓ := List.mem_range.mp hi
      refine sqir_conditionalSubConstGate_wellTyped (ehW ℓ m) (ehQStart ℓ m) (d * 2 ^ i)
        ((ℓ + m) + i) (ehDim ℓ m) hws (by unfold ehDim ehQStart; omega)
        (fun j _ => by unfold ehQStart; omega)

end FormalRV.Audit.Gidney2025.EkeraHastadOracleGate

#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleGate.tcount_condAdd
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleGate.ehOracleGate_tcount
#verify_clean FormalRV.Audit.Gidney2025.EkeraHastadOracleGate.ehOracleGate_wellTyped
