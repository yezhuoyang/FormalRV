/-
  FormalRV.BQAlgo.CuccaroCorrectness — semantic correctness of the
  Cuccaro MAJ and UMA gadgets, proved against the Framework's RCIR-level
  bit-vector semantics.

  This is the SQIR analogue of `Lemma MAJ_correct` in `RCIR.v` — but
  Lean-native, computable, and small enough that `decide` discharges
  every case.

  The key correctness fact: applied to bits (a, b, c), the MAJ gate
  writes the **majority** of a, b, c into bit c, while transforming
  bit a → a ⊕ c and bit b → b ⊕ c (so MAJ is reversible: UMA undoes it).
-/
import FormalRV.Core.Gate
import FormalRV.Core.Semantics
import FormalRV.Core.Boolean
import FormalRV.Arithmetic.Cuccaro.Cuccaro
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.GateToUCom

namespace FormalRV.BQAlgo

open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.Framework.Boolean

/-! ## Correctness of `cuccaro_MAJ` on qubits (0, 1, 2) of a 3-bit state -/

/-- After MAJ a b c, bit `a` becomes `a ⊕ c` (XOR with the original c). -/
theorem cuccaro_MAJ_writes_xor_a (a b c : Bool) :
    apply (cuccaro_MAJ 0 1 2) (mkState3 a b c) 0 = xor a c := by
  cases a <;> cases b <;> cases c <;> decide

/-- After MAJ a b c, bit `b` becomes `b ⊕ c`. -/
theorem cuccaro_MAJ_writes_xor_b (a b c : Bool) :
    apply (cuccaro_MAJ 0 1 2) (mkState3 a b c) 1 = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

/-- After MAJ a b c, bit `c` becomes the **majority** of (a, b, c). -/
theorem cuccaro_MAJ_writes_majority (a b c : Bool) :
    apply (cuccaro_MAJ 0 1 2) (mkState3 a b c) 2 = majority a b c := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## Correctness of `cuccaro_UMA`: it inverts MAJ and adds.

    Specifically, applied AFTER MAJ on the same qubits, UMA restores
    the original (a, b, c) and adds the majority into b. The two
    gadgets together implement a single full-adder bit. -/

/-- UMA after MAJ on the same triple restores bit 0 (a ⊕ c → a). -/
theorem MAJ_then_UMA_restores_a (a b c : Bool) :
    apply (seq (cuccaro_MAJ 0 1 2) (cuccaro_UMA 0 1 2)) (mkState3 a b c) 0 = a := by
  cases a <;> cases b <;> cases c <;> decide

/-- UMA after MAJ writes the **sum bit** `a ⊕ b ⊕ c` into qubit 1.
    This is the per-bit output of a full adder. -/
theorem MAJ_then_UMA_writes_sum (a b c : Bool) :
    apply (seq (cuccaro_MAJ 0 1 2) (cuccaro_UMA 0 1 2)) (mkState3 a b c) 1
      = xor (xor a b) c := by
  cases a <;> cases b <;> cases c <;> decide

/-- UMA after MAJ restores bit 2 (the carry-in). -/
theorem MAJ_then_UMA_restores_c (a b c : Bool) :
    apply (seq (cuccaro_MAJ 0 1 2) (cuccaro_UMA 0 1 2)) (mkState3 a b c) 2 = c := by
  cases a <;> cases b <;> cases c <;> decide

/-! ## Headline: framework-verified algorithm correctness

    These three theorems together establish that **the Cuccaro MAJ gadget
    correctly computes the majority function**, formally, by case analysis
    over all 8 input bit patterns. Any future review can grep
    `cuccaro_MAJ_writes_majority` and trust the claim. -/

/-! ## Tick 41 — Gate.applyNat-level local semantics for Cuccaro MAJ/UMA.

The above lemmas use `apply`/`State 3` (3-bit explicit state).  For
chain-level reasoning we need `Gate.applyNat`-level lemmas on
`Nat → Bool` state functions, with explicit qubit-index hypotheses.

### Local formulas (derived by direct trace through `Gate.applyNat`)

For `cuccaro_MAJ a b c = CX c b ; CX c a ; CCX a b c`:
- at `a`: `f a ⊕ f c`.
- at `b`: `f b ⊕ f c`.
- at `c`: `f c ⊕ ((f a ⊕ f c) AND (f b ⊕ f c)) = majority (f a) (f b) (f c)`.
- at other `q`: `f q` (identity).

For `cuccaro_UMA a b c = CCX a b c ; CX c a ; CX a b`:
- at `a`: `f a ⊕ f c ⊕ (f a AND f b)`.
- at `b`: `f b ⊕ f a ⊕ f c ⊕ (f a AND f b)`.
- at `c`: `f c ⊕ (f a AND f b)`.
- at other `q`: `f q`.

These give the SYMBOLIC formulas needed to compose into chain-level
invariants. -/

/-- **MAJ local semantics at the `a` wire.**  Applied to `f`, the
gate writes `f a ⊕ f c` at position `a`. -/
theorem cuccaro_MAJ_at_a
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ a b c) f a = xor (f a) (f c) := by
  unfold cuccaro_MAJ
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ac, h_ab, Ne.symm h_bc]

/-- **MAJ local semantics at the `b` wire.**  Applied to `f`, the
gate writes `f b ⊕ f c` at position `b`. -/
theorem cuccaro_MAJ_at_b
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ a b c) f b = xor (f b) (f c) := by
  unfold cuccaro_MAJ
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_bc, Ne.symm h_ab]

/-- **MAJ local semantics at the `c` wire.**  Applied to `f`, the
gate writes the boolean majority of `(f a, f b, f c)` at position `c`. -/
theorem cuccaro_MAJ_at_c
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ a b c) f c
      = majority (f a) (f b) (f c) := by
  unfold cuccaro_MAJ
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ab, h_ac, h_bc, Ne.symm h_ac, Ne.symm h_bc, Ne.symm h_ab]
  -- Boolean identity: f c ⊕ ((f a ⊕ f c) ∧ (f b ⊕ f c)) = majority f a f b f c.
  unfold majority
  cases f a <;> cases f b <;> cases f c <;> rfl

/-- **MAJ local semantics at any unrelated wire.**  Applied to `f`,
the gate is identity at positions outside `{a, b, c}`. -/
theorem cuccaro_MAJ_at_other
    (a b c q : Nat) (h_qa : q ≠ a) (h_qb : q ≠ b) (h_qc : q ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_MAJ a b c) f q = f q := by
  unfold cuccaro_MAJ
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_qc, h_qa, h_qb]

/-- **UMA local semantics at the `c` wire.**  Applied to `f`, the
gate writes `f c ⊕ (f a AND f b)` at position `c` (the CCX action). -/
theorem cuccaro_UMA_at_c
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c) f c
      = xor (f c) (f a && f b) := by
  unfold cuccaro_UMA
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [Ne.symm h_bc, Ne.symm h_ac]

/-- **UMA local semantics at the `a` wire.**  After UMA, position
`a` holds `f a ⊕ f c ⊕ (f a AND f b)`. -/
theorem cuccaro_UMA_at_a
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c) f a
      = xor (f a) (xor (f c) (f a && f b)) := by
  unfold cuccaro_UMA
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [Ne.symm h_ab, h_ac, h_ab]

/-- **UMA local semantics at the `b` wire.**  After UMA, position
`b` holds `f b ⊕ f a ⊕ f c ⊕ (f a AND f b)`. -/
theorem cuccaro_UMA_at_b
    (a b c : Nat) (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c) f b
      = xor (f b) (xor (f a) (xor (f c) (f a && f b))) := by
  unfold cuccaro_UMA
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_ab, h_ac, h_bc, Ne.symm h_ab]

/-- **UMA local semantics at any unrelated wire.** -/
theorem cuccaro_UMA_at_other
    (a b c q : Nat) (h_qa : q ≠ a) (h_qb : q ≠ b) (h_qc : q ≠ c) (f : Nat → Bool) :
    Gate.applyNat (cuccaro_UMA a b c) f q = f q := by
  unfold cuccaro_UMA
  simp only [Gate.applyNat_seq, Gate.applyNat_CX, Gate.applyNat_CCX, update]
  simp [h_qb, h_qa, h_qc]

/-! ## Deliverable E: WellTyped for MAJ and UMA. -/

/-- **WellTyped for `cuccaro_MAJ`.** -/
theorem cuccaro_MAJ_wellTyped
    (dim a b c : Nat) (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) :
    Gate.WellTyped dim (cuccaro_MAJ a b c) := by
  refine ⟨⟨hc, hb, ?_⟩, ⟨hc, ha, ?_⟩, ⟨ha, hb, hc, h_ab, h_ac, h_bc⟩⟩
  · exact fun h => h_bc h.symm
  · exact fun h => h_ac h.symm

/-- **WellTyped for `cuccaro_UMA`.** -/
theorem cuccaro_UMA_wellTyped
    (dim a b c : Nat) (ha : a < dim) (hb : b < dim) (hc : c < dim)
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_bc : b ≠ c) :
    Gate.WellTyped dim (cuccaro_UMA a b c) := by
  refine ⟨⟨ha, hb, hc, h_ab, h_ac, h_bc⟩, ⟨hc, ha, ?_⟩, ⟨ha, hb, h_ab⟩⟩
  · exact fun h => h_ac h.symm

/-! ## Deliverable A — Cuccaro register-level input encoding.

The standard Cuccaro layout for an n-bit adder uses `2n + 1` qubits:
- pos 0: `c_0` — carry-in.
- pos 1: `b_0`.
- pos 2: `a_0`.
- pos 3: `b_1`.
- pos 4: `a_1`.
- ...
- pos `2i + 1`: `b_i`.
- pos `2i + 2`: `a_i`.
- ...
- pos `2n - 1`: `b_{n-1}`.
- pos `2n`: `a_{n-1}`.

This is EXACTLY the index pattern used by the existing `cuccaro_maj_chain`
recursion (MAJ_i acts on positions `q_start + 2i, q_start + 2i + 1,
q_start + 2i + 2`).

Total qubit count `2n + 1` matches SQIR's `modmult_rev_anc n = 2n + 1`
EXACTLY, making this the natural exact-budget layout. -/

/-- **Cuccaro register-level input encoding.**  Given `a`, `b : Nat`
(the two inputs as binary numbers) and `c_in : Bool` (the carry-in),
produces the initial bit-function over `Nat → Bool` per the layout
above. -/
def cuccaro_input_F (q_start : Nat) (c_in : Bool) (a b : Nat) (q : Nat) : Bool :=
  if q < q_start then false
  else
    let i := q - q_start
    if i = 0 then c_in
    else if i % 2 = 1 then b.testBit ((i - 1) / 2)
    else a.testBit ((i - 2) / 2)

/-- **Cuccaro spec: integer-level sum-modulo-2^bits.**  The Boolean
specification of an n-bit addition. -/
def cuccaroAdderSpec (bits a b : Nat) : Nat :=
  (a + b) % 2^bits

/-- **Sanity: decoder at the carry-in position.** -/
theorem cuccaro_input_F_at_c_in (q_start : Nat) (c_in : Bool) (a b : Nat) :
    cuccaro_input_F q_start c_in a b q_start = c_in := by
  unfold cuccaro_input_F
  simp

/-- **Sanity: decoder at the i-th `b` position (q_start + 2i + 1). -/
theorem cuccaro_input_F_at_b
    (q_start i : Nat) (c_in : Bool) (a b : Nat) :
    cuccaro_input_F q_start c_in a b (q_start + 2 * i + 1) = b.testBit i := by
  unfold cuccaro_input_F
  have h1 : ¬ (q_start + 2 * i + 1 < q_start) := by omega
  rw [if_neg h1]
  have h2 : q_start + 2 * i + 1 - q_start = 2 * i + 1 := by omega
  rw [h2]
  have h3 : ¬ (2 * i + 1 = 0) := by omega
  rw [if_neg h3]
  have h4 : (2 * i + 1) % 2 = 1 := by omega
  rw [if_pos h4]
  have h5 : (2 * i + 1 - 1) / 2 = i := by omega
  rw [h5]

/-- **Sanity: decoder at the i-th `a` position (q_start + 2i + 2). -/
theorem cuccaro_input_F_at_a
    (q_start i : Nat) (c_in : Bool) (a b : Nat) :
    cuccaro_input_F q_start c_in a b (q_start + 2 * i + 2) = a.testBit i := by
  unfold cuccaro_input_F
  have h1 : ¬ (q_start + 2 * i + 2 < q_start) := by omega
  rw [if_neg h1]
  have h2 : q_start + 2 * i + 2 - q_start = 2 * i + 2 := by omega
  rw [h2]
  have h3 : ¬ (2 * i + 2 = 0) := by omega
  rw [if_neg h3]
  have h4 : ¬ ((2 * i + 2) % 2 = 1) := by omega
  rw [if_neg h4]
  have h5 : (2 * i + 2 - 2) / 2 = i := by omega
  rw [h5]

end FormalRV.BQAlgo
