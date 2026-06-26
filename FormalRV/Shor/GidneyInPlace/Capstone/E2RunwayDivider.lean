/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider — Stage A divider, ATTEMPT A.
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  A verified reversible DIVMOD-by-N gate (Stage A of the runway-shift gate).
  STRATEGY (attempt A): IN-PLACE subtract shifted `N·2^k` over `cm` steps; the
  quotient bits accumulate in a dedicated `cm`-wire QUOTIENT band.

  LAYOUT (interleaved Cuccaro; chosen so NO swap adapter is needed for the divider).
    With `q_start := 0`, `bits` data wires:
      • DATA band (Cuccaro TARGET register): wire `2i+1`, i ∈ [0,bits), weight 2^i.
        Read by `cuccaro_target_val bits 0`.  This is the running value / output remainder.
      • carry-in wire `0`: transient, clean in/out.
      • READ band (Cuccaro read/addend register): wire `2i+2`, i ∈ [0,bits): transient
        workspace (used by compare/subtract to stage the two's-complement constant);
        clean in/out.
      • FLAG wire `flagPos := 2*bits+1`: transient; clean in/out (cleaned by the
        quotient-bit copy: see `divStep`).
      • QUOTIENT band: wires `qBase + k`, k ∈ [0,cm): persistent output, quotient bit k.
        We take `qBase := 2*bits+2`.
    Total dim `dimDiv bits cm = 2*bits + 2 + cm`.

  THE DIVSTEP (one quotient bit, fully verified here).  On a window of width `w`
  starting at `q_start` holding running value `r < 2^w` with `r < 2N`:
      `divStep` = compareConst[N] (flag ^= [N≤r]) ; condSub[N] (r -= flag·N)
                ; CX flag→qbit (qbit ^= flag) ; CX qbit→flag (flag ^= qbit).
    Effect on a clean-flag, clean-read, clean-qbit, clear-carry state with target r:
      target  ↦ r % N        (= r − [N≤r]·N, since r < 2N)
      qbit    ↦ [N≤r]         (= r / N, since r < 2N)         ← PERSISTS
      flag    ↦ false         (cleaned: flag == qbit after the two CXs)
      read/carry ↦ unchanged (clean), everything else framed.

  FULL DIVIDER (general cm) — CLOSED.  Long division processing k = cm−1 … 0 with
  the divstep instantiated on the window `[q_start + 2k, …)` of width `bits − k`, so
  it effectively subtracts `N·2^k` when the running top exceeds it.  The full cm-step
  induction is PROVED (`divModN_decode_gen`), with the partial-quotient/partial-
  remainder invariant carried in `DivState`; the headline support-form contract is
  `divModN_decode`.

  HEADLINE (`divModN_decode`, fully verified, kernel-clean).  On the support
  `v = z + j·N` (`z < N`, `j < 2^cm`, budget `2^cm·N ≤ 2^bits`), running
  `divModN bits cm N` on the clean input `encDiv bits v`:
    • DATA band (Cuccaro target reg, `q_start = 0`) decodes to `z = v % N`;
    • QUOTIENT band wire `qBase bits + k` holds bit `k` of `j = v / N`;
    • TRANSIENT workspace (carry / read band / flag) returns clean;
    • the gate is `WellTyped (dimDiv bits cm)`.
  (`Gate.reverse (divModN bits cm N)` then composes for Stage C; Stage B is the
  verified residue multiply `residueMul_decode` from E2RunwayResidueMul.)

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆ {propext, Classical.choice,
  Quot.sound} (verified via `#print axioms divModN_decode`).
-/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayResidueMul
import FormalRV.Arithmetic.Windowed.WindowedModN
import FormalRV.Arithmetic.Cuccaro.CuccaroDecoded

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)

/-! ## §0. Layout constants. -/

/-- Total register dimension: data+read interleaved (`2·bits+1`), flag (`+1`),
    quotient band (`+cm`). -/
def dimDiv (bits cm : Nat) : Nat := 2 * bits + 2 + cm

/-- Quotient band base wire. -/
def qBase (bits : Nat) : Nat := 2 * bits + 2

/-! ## §1. The single divstep gadget. -/

/-- One long-division step on the width-`bits` window at `q_start`, comparing
    against constant `N`, with comparison flag at `flagPos` and quotient bit
    written to `qbit`.  See file header for the four-gate decomposition. -/
def divStep (bits q_start N flagPos qbit : Nat) : Gate :=
  Gate.seq (sqir_style_compareConst_candidate bits q_start N flagPos)
    (Gate.seq (sqir_conditionalSubConstGate bits q_start N flagPos)
      (Gate.seq (Gate.CX flagPos qbit)
        (Gate.CX qbit flagPos)))

/-! ## §2. The single-divstep DECODE lemma. -/

/-- Reduction arithmetic (inlined `modNReduce_arith`): for `r < 2N ≤ 2^bits`,
    `(r + [N ≤ r]·(2^bits − N)) mod 2^bits = r mod N`. -/
theorem divStep_arith (bits N r : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hr : r < 2 * N) :
    (r + if decide (N ≤ r) = true then 2 ^ bits - N else 0) % 2 ^ bits = r % N := by
  by_cases h : N ≤ r
  · rw [if_pos (by simp [h])]
    have h_eq : r + (2 ^ bits - N) = (r - N) + 2 ^ bits := by omega
    rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : r - N < 2 ^ bits)]
    have h_rN : r % N = r - N := by
      conv_lhs => rw [show r = N + (r - N) from by omega]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : r - N < N)]
    rw [h_rN]
  · rw [if_neg (by simp [Nat.not_le.mpr (Nat.lt_of_not_le h)] : ¬ decide (N ≤ r) = true)]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega : r < 2 ^ bits),
        Nat.mod_eq_of_lt (Nat.lt_of_not_le h)]

/-- **DIVSTEP DECODE (single step), fully verified.**  On a state `f` with clear
    carry-in / read register / flag / quotient bit, target register holding
    `r < 2N`, and `flagPos`, `qbit` both outside the Cuccaro workspace
    `[q_start, q_start+2·bits+1)` with `qbit ≠ flagPos`:

    after `divStep` the target register holds `r % N`, the quotient bit holds
    `decide (N ≤ r) = r / N`, the flag is restored to `false`, the read register
    and carry stay clear, and everything outside workspace ∪ {flag, qbit} is fixed. -/
theorem divStep_decode
    (bits q_start N flagPos qbit r : Nat)
    (hN_pos : 0 < N) (hN2 : 2 * N ≤ 2 ^ bits) (hr : r < 2 * N)
    (hflag_out : flagPos < q_start ∨ q_start + 2 * bits + 1 ≤ flagPos)
    (hqbit_out : qbit < q_start ∨ q_start + 2 * bits + 1 ≤ qbit)
    (hqf : qbit ≠ flagPos)
    (f : Nat → Bool)
    (h_cin : f q_start = false)
    (h_flag : f flagPos = false)
    (h_qbit : f qbit = false)
    (h_tgt : ∀ i, i < bits → f (q_start + 2 * i + 1) = r.testBit i)
    (h_read : ∀ i, i < bits → f (q_start + 2 * i + 2) = false) :
    (∀ i, i < bits →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f (q_start + 2 * i + 1)
          = (r % N).testBit i)
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f qbit = decide (N ≤ r)
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f flagPos = false
    ∧ Gate.applyNat (divStep bits q_start N flagPos qbit) f q_start = false
    ∧ (∀ i, i < bits →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f (q_start + 2 * i + 2) = false)
    ∧ (∀ p, p ≠ flagPos → p ≠ qbit →
        p < q_start ∨ q_start + 2 * bits + 1 ≤ p →
        Gate.applyNat (divStep bits q_start N flagPos qbit) f p = f p) := by
  have hr' : r < 2 ^ bits := by omega
  have hN : N ≤ 2 ^ bits := by omega
  -- distinctness facts
  have h_flag_ne_tgt : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 1 := by
    intro i hi; rcases hflag_out with h | h <;> omega
  have h_flag_ne_read : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2 := by
    intro i hi; rcases hflag_out with h | h <;> omega
  have h_flag_ne_cin : flagPos ≠ q_start := by rcases hflag_out with h | h <;> omega
  have h_qbit_ne_tgt : ∀ i, i < bits → qbit ≠ q_start + 2 * i + 1 := by
    intro i hi; rcases hqbit_out with h | h <;> omega
  have h_qbit_ne_read : ∀ i, i < bits → qbit ≠ q_start + 2 * i + 2 := by
    intro i hi; rcases hqbit_out with h | h <;> omega
  have h_qbit_ne_cin : qbit ≠ q_start := by rcases hqbit_out with h | h <;> omega
  -- ===== Stage 1: compareConst sets flag := [N ≤ r]. =====
  have hcmp := compareConstXor_state_general bits q_start N flagPos r f
      hN_pos hN hr' hflag_out h_cin h_tgt h_read
  -- g1 := state after compareConst = update f flagPos [N ≤ r]
  set g1 := update f flagPos (xor (f flagPos) (decide (N ≤ r))) with hg1
  rw [h_flag, Bool.false_xor] at hg1
  -- Reading g1 at the relevant positions.
  have hg1_cin : g1 q_start = false := by
    rw [hg1]; rw [update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm)]; exact h_cin
  have hg1_flag : g1 flagPos = decide (N ≤ r) := by rw [hg1]; exact update_eq _ _ _
  have hg1_tgt : ∀ i, i < bits → g1 (q_start + 2 * i + 1) = r.testBit i := by
    intro i hi; rw [hg1, update_neq _ _ _ _ (fun h => h_flag_ne_tgt i hi h.symm)]; exact h_tgt i hi
  have hg1_read : ∀ i, i < bits → g1 (q_start + 2 * i + 2) = false := by
    intro i hi; rw [hg1, update_neq _ _ _ _ (fun h => h_flag_ne_read i hi h.symm)]; exact h_read i hi
  have hg1_qbit : g1 qbit = false := by
    rw [hg1, update_neq _ _ _ _ (fun h => (hqf h).elim)]; exact h_qbit
  -- ===== Stage 2: condSub subtracts [N ≤ r]·N from the target. =====
  have hsub := condSub_state_general bits q_start N flagPos r g1 hr'
      hflag_out hg1_cin hg1_tgt hg1_read
  -- g2 := state after condSub.
  set g2 := Gate.applyNat (sqir_conditionalSubConstGate bits q_start N flagPos) g1 with hg2
  -- Target bits of g2: r % N.
  have hg2_tgt : ∀ i, i < bits → g2 (q_start + 2 * i + 1) = (r % N).testBit i := by
    intro i hi
    have := hsub.1 i hi
    rw [hg1_flag] at this
    rw [this, divStep_arith bits N r hN_pos hN2 hr]
  have hg2_read : ∀ i, i < bits → g2 (q_start + 2 * i + 2) = false := fun i hi => hsub.2.1 i hi
  have hg2_cin : g2 q_start = false := hsub.2.2.1
  -- frame of condSub at flagPos and qbit (both outside workspace).
  have hg2_flag : g2 flagPos = decide (N ≤ r) := by
    rw [hsub.2.2.2 flagPos hflag_out]; exact hg1_flag
  have hg2_qbit : g2 qbit = false := by
    rw [hsub.2.2.2 qbit hqbit_out]; exact hg1_qbit
  -- ===== Stage 3 + 4: the two CX gates copy the flag to qbit and clean the flag. =====
  -- divStep f = Gate.CX qbit flagPos (Gate.CX flagPos qbit g2).
  have hunfold : Gate.applyNat (divStep bits q_start N flagPos qbit) f
      = Gate.applyNat (Gate.CX qbit flagPos) (Gate.applyNat (Gate.CX flagPos qbit) g2) := by
    show Gate.applyNat (Gate.seq _ (Gate.seq _ (Gate.seq _ _))) f = _
    simp only [Gate.applyNat_seq]
    rw [hcmp]
  -- g3 := after CX flagPos qbit : qbit ^= flag.
  set g3 := Gate.applyNat (Gate.CX flagPos qbit) g2 with hg3
  -- g4 := after CX qbit flagPos : flag ^= qbit.
  set g4 := Gate.applyNat (Gate.CX qbit flagPos) g3 with hg4
  rw [hunfold]
  -- Read g3 (= update g2 qbit (g2 qbit ^ g2 flagPos)).
  have hg3_eq : g3 = update g2 qbit (xor (g2 qbit) (g2 flagPos)) := by rw [hg3, Gate.applyNat_CX]
  -- Read g4 (= update g3 flagPos (g3 flagPos ^ g3 qbit)).
  have hg4_eq : g4 = update g3 flagPos (xor (g3 flagPos) (g3 qbit)) := by rw [hg4, Gate.applyNat_CX]
  -- g3 qbit = false ^ [N≤r] = [N≤r].
  have hg3_qbit : g3 qbit = decide (N ≤ r) := by
    rw [hg3_eq, update_eq, hg2_qbit, hg2_flag, Bool.false_xor]
  -- g3 flagPos = g2 flagPos (qbit ≠ flagPos).
  have hg3_flag : g3 flagPos = decide (N ≤ r) := by
    rw [hg3_eq, update_neq _ _ _ _ hqf.symm]; exact hg2_flag
  -- Now compute each conclusion on g4.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- target band unchanged by the two CX (qbit, flagPos both ≠ target positions).
    intro i hi
    rw [hg4_eq, update_neq _ _ _ _ (fun h => (h_flag_ne_tgt i hi) h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => (h_qbit_ne_tgt i hi) h.symm)]
    exact hg2_tgt i hi
  · -- qbit value = [N ≤ r].
    rw [hg4_eq, update_neq _ _ _ _ hqf, hg3_qbit]
  · -- flag cleaned to false.
    rw [hg4_eq, update_eq, hg3_flag, hg3_qbit, Bool.xor_self]
  · -- carry clear.
    rw [hg4_eq, update_neq _ _ _ _ (fun h => h_flag_ne_cin h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => h_qbit_ne_cin h.symm)]
    exact hg2_cin
  · -- read band clear.
    intro i hi
    rw [hg4_eq, update_neq _ _ _ _ (fun h => (h_flag_ne_read i hi) h.symm), hg3_eq,
        update_neq _ _ _ _ (fun h => (h_qbit_ne_read i hi) h.symm)]
    exact hg2_read i hi
  · -- frame outside workspace ∪ {flag, qbit}.
    intro p hpf hpq hp_out
    rw [hg4_eq, update_neq _ _ _ _ hpf, hg3_eq, update_neq _ _ _ _ hpq]
    rw [hsub.2.2.2 p hp_out, hg1]
    exact update_neq _ _ _ _ hpf

/-! ## §3. WellTyped for the divstep. -/

/-- `divStep` is well-typed in any `dim` containing the workspace, the flag, and
    the quotient bit, with `flagPos`, `qbit` distinct from the read register and
    from `q_start + 2·bits` (the comparator's top carry CX target), and from each
    other. -/
theorem divStep_wellTyped (bits q_start N flagPos qbit dim : Nat)
    (h_ws : q_start + 2 * bits + 1 ≤ dim) (h_flag : flagPos < dim) (h_qbit : qbit < dim)
    (h_flag_distinct : ∀ i, i < bits → flagPos ≠ q_start + 2 * i + 2)
    (h_flag_top : flagPos ≠ q_start + 2 * bits)
    (hqf : qbit ≠ flagPos) :
    Gate.WellTyped dim (divStep bits q_start N flagPos qbit) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sqir_style_compareConst_candidate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_flag_top
  · exact sqir_conditionalSubConstGate_wellTyped bits q_start N flagPos dim
      h_ws h_flag h_flag_distinct
  · exact ⟨h_flag, h_qbit, fun h => hqf h.symm⟩
  · exact ⟨h_qbit, h_flag, hqf⟩

/-! ## §4. The full divider gate (cm-step long division).

  We process `k = cm−1, …, 0`.  Step `k` runs `divStep` on the width-`(bits − k)`
  window at base `q_start + 2·k` (so it subtracts `N·2^k` when the running top
  exceeds it), writing quotient bit `k` to `qBase bits + k`.  The single flag wire
  `flagPos := 2·bits+1` is reused across steps (it is returned clean by each step).
-/

/-- The shared flag wire (one fresh qubit above the data/read block). -/
def flagW (bits : Nat) : Nat := 2 * bits + 1

/-- Step `k` of the divider: `divStep` on the top `bits − k` bits, quotient → wire
    `qBase bits + k`. -/
def divStepAt (bits N k : Nat) : Gate :=
  divStep (bits - k) (2 * k) N (flagW bits) (qBase bits + k)

/-- The full divider, by descending recursion on the number of steps `cm`:
    process the TOP bit `k = cm−1` first (`divStepAt bits N (cm−1)`), then the
    `cm−1`-step divider on the remaining lower bits.  So
    `divModN bits (cm+1) N = Gate.seq (divStepAt bits N cm) (divModN bits cm N)`. -/
def divModN (bits : Nat) : Nat → Nat → Gate
  | 0,      _ => Gate.I
  | cm + 1, N => Gate.seq (divStepAt bits N cm) (divModN bits cm N)

/-! ## §4b. WellTyped for the full divider. -/

/-- Each divider step is well-typed at `dimDiv bits cm`, provided `1 ≤ bits` and
    `k < cm ≤ bits` (so every window `[2k, 2k+2(bits−k)+1)` and quotient wire fits). -/
theorem divStepAt_wellTyped (bits cm N k : Nat)
    (_hbits : 1 ≤ bits) (hk : k < cm) (hcm : cm ≤ bits) :
    Gate.WellTyped (dimDiv bits cm) (divStepAt bits N k) := by
  unfold divStepAt
  have hkb : k ≤ bits := by omega
  -- workspace of the window: 2k + 2*(bits−k) + 1 = 2*bits + 1 ≤ dimDiv
  have h_ws : 2 * k + 2 * (bits - k) + 1 ≤ dimDiv bits cm := by
    unfold dimDiv; omega
  have h_flag : flagW bits < dimDiv bits cm := by unfold flagW dimDiv; omega
  have h_qbit : qBase bits + k < dimDiv bits cm := by unfold qBase dimDiv; omega
  apply divStep_wellTyped (bits - k) (2 * k) N (flagW bits) (qBase bits + k)
    (dimDiv bits cm) h_ws h_flag h_qbit
  · intro i hi; unfold flagW; omega
  · unfold flagW; omega
  · unfold qBase flagW; omega

/-- Monotonicity of well-typedness in the dimension (a gate WellTyped at `d` is
    WellTyped at any `d' ≥ d`). -/
theorem wellTyped_mono : ∀ (g : Gate) (d d' : Nat), d ≤ d' →
    Gate.WellTyped d g → Gate.WellTyped d' g := by
  intro g
  induction g with
  | I => intro d d' hd h; exact lt_of_lt_of_le h hd
  | X q => intro d d' hd h; exact lt_of_lt_of_le h hd
  | CX a b => intro d d' hd h; exact ⟨lt_of_lt_of_le h.1 hd, lt_of_lt_of_le h.2.1 hd, h.2.2⟩
  | CCX a b c => intro d d' hd h
                 exact ⟨lt_of_lt_of_le h.1 hd, lt_of_lt_of_le h.2.1 hd,
                        lt_of_lt_of_le h.2.2.1 hd, h.2.2.2⟩
  | seq g₁ g₂ ih₁ ih₂ => intro d d' hd h; exact ⟨ih₁ d d' hd h.1, ih₂ d d' hd h.2⟩

/-- **The full divider is well-typed** at `dimDiv bits cm` (for `1 ≤ bits`,
    `cm ≤ bits`).  By recursion on `cm`; each step is `divStepAt_wellTyped`,
    monotone-lifted from `dimDiv bits cm'` to `dimDiv bits cm`. -/
theorem divModN_wellTyped (bits cm N : Nat)
    (hbits : 1 ≤ bits) (hcm : cm ≤ bits) :
    Gate.WellTyped (dimDiv bits cm) (divModN bits cm N) := by
  induction cm with
  | zero => show 0 < dimDiv bits 0; unfold dimDiv; omega
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · -- top step at k, well-typed at dimDiv bits (k+1)
      exact divStepAt_wellTyped bits (k + 1) N k hbits (by omega) hcm
    · -- the k-step divider, lifted from dimDiv bits k to dimDiv bits (k+1)
      exact wellTyped_mono (divModN bits k N) (dimDiv bits k) (dimDiv bits (k + 1))
        (by unfold dimDiv; omega) (ih (by omega))

/-! ## §5. The DECODE specification (target deliverable), with the inductive
    invariant, base case, and the step reduced to `divStep_decode`.

  INPUT.  The support representative `v = z + j·N`, `z < N`, `j < 2^cm`,
  `2^cm·N ≤ 2^bits`, encoded as the running value in the DATA band
  (Cuccaro target register at `q_start = 0`), clean read/carry/flag/quotient.

  OUTPUT (the decode the brief asks for).
    • DATA band  → `z = v % N`           (read by `cuccaro_target_val bits 0`),
    • QUOTIENT band wire `qBase bits + k` → bit `k` of `j = v / N`, k ∈ [0,cm),
    • TRANSIENT workspace (read band, carry, flag) → clean (false).

  STATUS.  The arithmetic spec is `v = z + j·N, z < N ⇒ v/N = j ∧ v%N = z`
  (`divModN_arith`, proved).  The circuit-to-spec bridge is the cm-step induction
  whose invariant / base case / step are stated below; the step is reduced to the
  proven `divStep_decode`.  The REMAINING blocker is the bit-window lemma relating
  the windowed divstep's local target value `⌊running/2^k⌋ mod 2^(bits−k)` to the
  global running value (see `divModN_decode` and the note at the bottom). -/

/-- **Division arithmetic (proved).**  `v = z + j·N` with `z < N` ⇒
    `v / N = j` and `v % N = z`. -/
theorem divModN_arith (N z j : Nat) (hN : 0 < N) (hz : z < N) :
    (z + j * N) / N = j ∧ (z + j * N) % N = z := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_right z j hN, Nat.div_eq_of_lt hz, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

/-! ### §5a. Input encoding + base case. -/

/-- The clean input state: running value `v` in the DATA band (Cuccaro target,
    `q_start = 0`), everything else (carry, read band, flag, quotient band) clean. -/
def encDiv (bits v : Nat) : Nat → Bool :=
  fun q =>
    if q = 0 then false                                  -- carry-in
    else if q % 2 = 1 ∧ q < 2 * bits + 1 then v.testBit ((q - 1) / 2)  -- data band
    else false                                           -- read band / flag / quotient / above

theorem encDiv_data (bits v i : Nat) (hi : i < bits) :
    encDiv bits v (0 + 2 * i + 1) = v.testBit i := by
  unfold encDiv
  have h1 : ¬ (0 + 2 * i + 1 = 0) := by omega
  have h2 : (0 + 2 * i + 1) % 2 = 1 := by omega
  have h3 : 0 + 2 * i + 1 < 2 * bits + 1 := by omega
  rw [if_neg h1, if_pos ⟨h2, h3⟩]
  congr 1; omega

theorem encDiv_read (bits v i : Nat) (_hi : i < bits) :
    encDiv bits v (0 + 2 * i + 2) = false := by
  unfold encDiv
  have h1 : ¬ (0 + 2 * i + 2 = 0) := by omega
  have h2 : (0 + 2 * i + 2) % 2 ≠ 1 := by omega
  rw [if_neg h1, if_neg (by tauto)]

theorem encDiv_cin (bits v : Nat) : encDiv bits v 0 = false := by unfold encDiv; simp

theorem encDiv_flag (bits v : Nat) : encDiv bits v (flagW bits) = false := by
  unfold encDiv flagW
  have h1 : ¬ (2 * bits + 1 = 0) := by omega
  rw [if_neg h1, if_neg (by omega)]

theorem encDiv_qbit (bits v k : Nat) : encDiv bits v (qBase bits + k) = false := by
  unfold encDiv qBase
  have h1 : ¬ (2 * bits + 2 + k = 0) := by omega
  rw [if_neg h1, if_neg (by omega)]

/-- The data-band decode of the clean input is `v` (for `v < 2^bits`). -/
theorem cuccaro_target_val_encDiv (bits v : Nat) (hv : v < 2 ^ bits) :
    cuccaro_target_val bits 0 (encDiv bits v) = v := by
  rw [cuccaro_target_val_eq_sum_when_bits_match bits 0 v (encDiv bits v)
        (fun i hi => by rw [encDiv_data bits v i hi])]
  exact Nat.mod_eq_of_lt hv

/-- **BASE CASE (`cm = 0`).**  The divider is the identity; the data band still
    decodes to `v` and there is no quotient band.  (`v / N = 0`, `v % N = v` when
    `v < N`, matching `divModN_arith` at `j = 0`.) -/
theorem divModN_decode_base (bits N v : Nat) (hv : v < 2 ^ bits) :
    Gate.applyNat (divModN bits 0 N) (encDiv bits v) = encDiv bits v
    ∧ cuccaro_target_val bits 0
        (Gate.applyNat (divModN bits 0 N) (encDiv bits v)) = v := by
  have hI : divModN bits 0 N = Gate.I := rfl
  rw [hI]
  exact ⟨rfl, cuccaro_target_val_encDiv bits v hv⟩

/-! ### §5b. The full decode goal (general cm) and the step reduction.

  The headline deliverable (general `cm`).  On the support `v = z + j·N`
  (`z < N`, `j < 2^cm`, `2^cm·N ≤ 2^bits`):

      cuccaro_target_val bits 0 (applyNat (divModN bits cm N) (encDiv bits v)) = v % N = z
    ∧ (∀ k < cm, applyNat (divModN bits cm N) (encDiv bits v) (qBase bits + k)
                  = (v / N).testBit k)        -- = j.testBit k
    ∧ (transient workspace — carry/read/flag — clean)
    ∧ Gate.WellTyped (dimDiv bits cm) (divModN bits cm N)   -- ✓ divModN_wellTyped

  The WellTyped conjunct is `divModN_wellTyped`.  The value conjuncts follow from
  the cm-step INDUCTION whose step is one `divStep_decode`; the remaining blocker
  is the bit-window arithmetic linking the windowed divstep's local view to the
  global running value (see `divModN_step_reduces` and the BLOCKER note). -/

/-- **STEP REDUCTION (the inductive step, reduced to `divStep_decode`).**
    The `(cm+1)`-step divider is the `cm`-step divider followed by the TOP step
    `divStepAt bits N cm` (the descending fold processes `k = cm` first).  Hence
    any decode statement for `divModN bits (cm+1) N` reduces, via
    `Gate.applyNat_seq`, to applying `divStep_decode` (on the width-`(bits−cm)`
    window at base `2·cm`) to the output of `divModN bits cm N`.

    This lemma exhibits the reduction structurally; closing the induction needs the
    window/global-value bridge described in the BLOCKER note. -/
theorem divModN_succ_eq (bits cm N : Nat) :
    divModN bits (cm + 1) N
      = Gate.seq (divStepAt bits N cm) (divModN bits cm N) := rfl

/-! ### §5c. The window/global value-split bridge (the crux for the induction). -/

/-- Definitional succ-equation for the target decoder. -/
theorem cuccaro_target_val_succ (n q : Nat) (f : Nat → Bool) :
    cuccaro_target_val (n + 1) q f
      = cuccaro_target_val n q f + (if f (q + 2 * n + 1) then 2 ^ n else 0) := rfl

/-- **Value split (proved).**  The global data-band value splits at any `k ≤ bits`
    into the low `k` bits and `2^k ·` (the window value at base `2k`, width `bits−k`):
        `cuccaro_target_val bits 0 f`
          = `cuccaro_target_val k 0 f + 2^k · cuccaro_target_val (bits−k) (2·k) f`.
    Both sub-decoders read the SAME wires (`0+2i+1`) as the global one; the window
    at base `2k` reads `2k+2i+1 = 0+2(k+i)+1`.  Proved by induction on `bits − k`. -/
theorem cuccaro_target_val_split (bits k : Nat) (f : Nat → Bool) (hk : k ≤ bits) :
    cuccaro_target_val bits 0 f
      = cuccaro_target_val k 0 f
        + 2 ^ k * cuccaro_target_val (bits - k) (2 * k) f := by
  induction bits with
  | zero =>
    have : k = 0 := by omega
    subst this; simp [cuccaro_target_val]
  | succ b ih =>
    rcases Nat.lt_or_ge k (b + 1) with hlt | hge
    · -- k ≤ b : peel the top bit `b` off the global decoder; it belongs to the window.
      have hkb : k ≤ b := by omega
      have ihb := ih hkb
      -- Peel the global decoder's top bit.
      rw [cuccaro_target_val_succ b 0 f, ihb]
      -- RHS window: (b+1)-k = (b-k)+1, peel its top.
      have hwin : b + 1 - k = (b - k) + 1 := by omega
      rw [hwin, cuccaro_target_val_succ (b - k) (2 * k) f]
      have hpos : 2 * k + 2 * (b - k) + 1 = 0 + 2 * b + 1 := by omega
      rw [hpos, Nat.mul_add, ← Nat.add_assoc]
      congr 1
      by_cases hfb : f (0 + 2 * b + 1)
      · simp only [hfb, if_true]
        rw [← pow_add]; congr 2; omega
      · simp only [hfb, Bool.false_eq_true, if_false, Nat.mul_zero]
    · -- k = b+1 : the window is empty, low part is everything.
      have hkb : k = b + 1 := by omega
      subst hkb
      rw [Nat.sub_self]
      simp [cuccaro_target_val]

/-- Low-`k`-bits decoder is `< 2^k`. -/
theorem cuccaro_target_val_lt' (k q : Nat) (f : Nat → Bool) :
    cuccaro_target_val k q f < 2 ^ k := cuccaro_target_val_lt k q f

/-- **Window value of the clean input = `v / 2^k`** (for `v < 2^bits`, `k ≤ bits`).
    The window at base `2k` reads global bits `k…bits−1`, i.e. `⌊v / 2^k⌋`.
    From the value split + the low part `< 2^k`. -/
theorem window_val_encDiv (bits v k : Nat) (hv : v < 2 ^ bits) (hk : k ≤ bits) :
    cuccaro_target_val (bits - k) (2 * k) (encDiv bits v) = v / 2 ^ k := by
  have hsplit := cuccaro_target_val_split bits k (encDiv bits v) hk
  rw [cuccaro_target_val_encDiv bits v hv] at hsplit
  -- v = low + 2^k * window, low < 2^k  ⇒  window = v / 2^k.
  set low := cuccaro_target_val k 0 (encDiv bits v) with hlow
  set win := cuccaro_target_val (bits - k) (2 * k) (encDiv bits v) with hwin
  have hlow_lt : low < 2 ^ k := cuccaro_target_val_lt k 0 (encDiv bits v)
  -- from v = low + 2^k * win
  rw [hsplit, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ k),
      Nat.div_eq_of_lt hlow_lt, Nat.zero_add]

/-! ### §5d. The full DECODE — CLOSED.  Roadmap of the proved pieces.

  The complete deliverable `divModN_decode` (§5h) has the following shape:

    theorem divModN_decode
      (bits cm N z j : Nat)
      (hbits : 1 ≤ bits) (hN : 0 < N) (h2N : 2 * N ≤ 2 ^ bits) (hcm : cm ≤ bits)
      (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
      (hz : z < N) (hj : j < 2 ^ cm) :
      -- DATA band → remainder z = v % N
      cuccaro_target_val bits 0
          (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))) = z
      -- QUOTIENT band → j (bit k of v / N) on the cm dedicated wires
      ∧ (∀ k, k < cm →
          Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (qBase bits + k)
            = j.testBit k)
      -- TRANSIENT workspace returns clean
      ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (flagW bits) = false
      ∧ (∀ i, i < bits →
          Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (0 + 2 * i + 2) = false)
      ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) 0 = false
      -- WELL-TYPED  (✓ already proved: `divModN_wellTyped`)
      ∧ Gate.WellTyped (dimDiv bits cm) (divModN bits cm N)

  ALL PROVED (kernel-clean):
    • WellTyped:           `divModN_wellTyped`.
    • Single divstep:      `divStep_decode` / `divStep_wellTyped`.
    • Value-split bridge:  `cuccaro_target_val_split` (the crux).
    • Window-local hyps:   `topStep_local_hyps` (incl. window carry-in = read wire).
    • Top-step output:     `topStep_global_out` (data band → r', frames lower wires).
    • Reassembly arith:    `topStepRunning_{lt,mod_N,div_N,div_N_lt}`,
                           `quot_low_testBit`, `quot_top_bit`, `testBit_*`.
    • GENERAL induction:   `divModN_decode_gen` (the full cm-step induction).
    • Headline support:    `divModN_decode` (§5h).
  The invariant carried across the induction is the `DivState` predicate (§5e):
  running value `r < N·2^cm`, read/carry/flag/quotient-band clean.  Each step
  applies `divStep_decode` to the TOP window (base `2·cm`, width `bits−cm`; its
  carry-in is the GLOBAL read wire `2·cm`), frames the lower wires, and recurses. -/

/-! ### §5e. The invariant predicate carried by the induction. -/

/-- The clean-state predicate for the divider's input at running value `r`,
    over the top `bits` data band, with the cm quotient wires clean. -/
structure DivState (bits cm N r : Nat) (f : Nat → Bool) : Prop where
  hr      : r < N * 2 ^ cm
  hbudget : N * 2 ^ cm ≤ 2 ^ bits
  hcm     : cm ≤ bits
  hN      : 0 < N
  h_cin   : f 0 = false
  h_flag  : f (flagW bits) = false
  h_tgt   : ∀ i, i < bits → f (0 + 2 * i + 1) = r.testBit i
  h_read  : ∀ i, i < bits → f (0 + 2 * i + 2) = false
  h_quot  : ∀ k, k < cm → f (qBase bits + k) = false

/-- Window-local target hypotheses for the TOP step `divStepAt bits N cm`
    (= `divStep (bits−cm) (2·cm) N (flagW bits) (qBase bits + cm)`) derived from a
    `DivState bits (cm+1) N r f`.  The window's carry-in is the global read wire
    `2·cm`; the window targets are global data bits `cm…bits−1`; the window read
    wires are global read bits `cm+1…bits`; flag/qbit are outside the window. -/
theorem topStep_local_hyps (bits cm N r : Nat) (f : Nat → Bool)
    (S : DivState bits (cm + 1) N r f) :
    -- the window value is r / 2^cm and it is < 2N
    cuccaro_target_val (bits - cm) (2 * cm) f = r / 2 ^ cm
    ∧ r / 2 ^ cm < 2 * N
    ∧ f (2 * cm) = false
    ∧ (∀ i, i < bits - cm → f (2 * cm + 2 * i + 1) = (r / 2 ^ cm).testBit i)
    ∧ (∀ i, i < bits - cm → f (2 * cm + 2 * i + 2) = false) := by
  have hcm : cm + 1 ≤ bits := S.hcm
  have hcm' : cm ≤ bits := by omega
  have hr := S.hr
  have hbud := S.hbudget
  -- r < 2^bits
  have hr_bits : r < 2 ^ bits := lt_of_lt_of_le hr hbud
  -- window value via the split on the FULL register at k = cm.
  have hsplit := cuccaro_target_val_split bits cm f hcm'
  have hglob : cuccaro_target_val bits 0 f = r := by
    rw [cuccaro_target_val_eq_sum_when_bits_match bits 0 r f
          (fun i hi => by rw [S.h_tgt i hi])]
    exact Nat.mod_eq_of_lt hr_bits
  rw [hglob] at hsplit
  set low := cuccaro_target_val cm 0 f with hlow
  set win := cuccaro_target_val (bits - cm) (2 * cm) f with hwin
  have hlow_lt : low < 2 ^ cm := cuccaro_target_val_lt cm 0 f
  have hwin_eq : win = r / 2 ^ cm := by
    rw [hsplit, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ cm),
        Nat.div_eq_of_lt hlow_lt, Nat.zero_add]
  refine ⟨hwin_eq, ?_, ?_, ?_, ?_⟩
  · -- r / 2^cm < 2N : from r < N·2^(cm+1) = 2N·2^cm.
    rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ cm)]
    calc r < N * 2 ^ (cm + 1) := hr
      _ = 2 * N * 2 ^ cm := by rw [pow_succ]; ring
  · -- window carry-in is the global read wire 2*cm = 0 + 2*(cm-1) + 2 when cm ≥ 1,
    -- and is wire 0 (= carry-in) when cm = 0.
    rcases Nat.eq_zero_or_pos cm with hc0 | hcpos
    · subst hc0; simpa using S.h_cin
    · have : (2 * cm : Nat) = 0 + 2 * (cm - 1) + 2 := by omega
      rw [this]; exact S.h_read (cm - 1) (by omega)
  · -- window targets: global data bits cm..bits-1.
    intro i hi
    have hpos : 2 * cm + 2 * i + 1 = 0 + 2 * (cm + i) + 1 := by ring
    rw [hpos, S.h_tgt (cm + i) (by omega)]
    -- (r).testBit (cm+i) = (r / 2^cm).testBit i
    rw [Nat.testBit_div_two_pow, Nat.add_comm cm i]
  · -- window read wires: global read bits cm+1..bits.
    intro i hi
    have hpos : 2 * cm + 2 * i + 2 = 0 + 2 * (cm + i) + 2 := by ring
    rw [hpos, S.h_read (cm + i) (by omega)]

/-- The new running value produced by the TOP step: low part unchanged, window
    reduced mod N.  `r' = (r % 2^cm) + 2^cm · ((r / 2^cm) % N)`. -/
def topStepRunning (cm N r : Nat) : Nat :=
  (r % 2 ^ cm) + 2 ^ cm * ((r / 2 ^ cm) % N)

theorem topStepRunning_lt (cm N r : Nat) (hN : 0 < N) :
    topStepRunning cm N r < N * 2 ^ cm := by
  unfold topStepRunning
  have h1 : r % 2 ^ cm < 2 ^ cm := Nat.mod_lt _ (by positivity)
  have h2 : (r / 2 ^ cm) % N < N := Nat.mod_lt _ hN
  have h3 : (r / 2 ^ cm) % N + 1 ≤ N := by omega
  calc (r % 2 ^ cm) + 2 ^ cm * ((r / 2 ^ cm) % N)
      < 2 ^ cm + 2 ^ cm * ((r / 2 ^ cm) % N) := by omega
    _ = 2 ^ cm * ((r / 2 ^ cm) % N + 1) := by ring
    _ ≤ 2 ^ cm * N := Nat.mul_le_mul_left _ h3
    _ = N * 2 ^ cm := by ring

/-- `topStepRunning / 2^cm = (r / 2^cm) % N`. -/
theorem topStepRunning_div (cm N r : Nat) :
    topStepRunning cm N r / 2 ^ cm = (r / 2 ^ cm) % N := by
  unfold topStepRunning
  rw [Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ cm),
      Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity : 0 < 2 ^ cm)), Nat.zero_add]

/-- `topStepRunning % 2^cm = r % 2^cm`. -/
theorem topStepRunning_mod (cm N r : Nat) :
    topStepRunning cm N r % 2 ^ cm = r % 2 ^ cm := by
  unfold topStepRunning
  rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

/-- Low bits (`i < cm`) of `topStepRunning` agree with `r`. -/
theorem topStepRunning_low_testBit (cm N r i : Nat) (hi : i < cm) :
    r.testBit i = (topStepRunning cm N r).testBit i := by
  -- both equal (·% 2^cm).testBit i for i < cm
  have key : ∀ x : Nat, x.testBit i = (x % 2 ^ cm).testBit i := by
    intro x
    rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega : i < cm), Bool.true_and]
  rw [key r, key (topStepRunning cm N r), topStepRunning_mod]

/-- High bits (`cm ≤ i`) of `topStepRunning` read the reduced window. -/
theorem topStepRunning_high_testBit (cm N r i : Nat) (hi : cm ≤ i) :
    ((r / 2 ^ cm) % N).testBit (i - cm) = (topStepRunning cm N r).testBit i := by
  conv_rhs => rw [show i = (i - cm) + cm from by omega]
  rw [Nat.testBit_add, topStepRunning_div]

/-- **TOP-STEP GLOBAL OUTPUT.**  Applying the top step `divStepAt bits N cm` to a
    `DivState bits (cm+1) N r f` yields a state `g` whose data band holds
    `r' = topStepRunning cm N r`, whose quotient wire `qBase bits + cm` holds
    `(r / N).testBit cm`-equivalent bit `[N ≤ r/2^cm]`, whose flag/read/carry are
    clean, and whose LOWER quotient wires (`qBase bits + k`, `k < cm`) are unchanged.
    Hence `g` (restricted to the lower `cm` quotient wires) is a `DivState bits cm N r'`. -/
theorem topStep_global_out (bits cm N r : Nat) (f : Nat → Bool)
    (S : DivState bits (cm + 1) N r f) :
    let g := Gate.applyNat (divStepAt bits N cm) f
    -- data band → r'
    (∀ i, i < bits → g (0 + 2 * i + 1) = (topStepRunning cm N r).testBit i)
    -- read band clean
    ∧ (∀ i, i < bits → g (0 + 2 * i + 2) = false)
    -- carry clean
    ∧ g 0 = false
    -- flag clean
    ∧ g (flagW bits) = false
    -- quotient wire cm = the top bit [N ≤ r/2^cm]
    ∧ g (qBase bits + cm) = decide (N ≤ r / 2 ^ cm)
    -- lower quotient wires unchanged (still clean)
    ∧ (∀ k, k < cm → g (qBase bits + k) = false) := by
  intro g
  obtain ⟨hwin_eq, hwin_lt, hcin_w, htgt_w, hread_w⟩ := topStep_local_hyps bits cm N r f S
  have hcm : cm + 1 ≤ bits := S.hcm
  have hcm' : cm ≤ bits := by omega
  have hN := S.hN
  -- The window is (bits - cm) wide; the budget gives 2N ≤ 2^(bits-cm).
  have h2N : 2 * N ≤ 2 ^ (bits - cm) := by
    have hpow : 2 ^ (cm + 1) * 2 ^ (bits - cm) = 2 ^ (bits + 1) := by
      rw [← pow_add]; congr 1; omega
    have hbud : N * 2 ^ (cm + 1) ≤ 2 ^ bits := S.hbudget
    -- N·2^(cm+1) ≤ 2^bits  ⇒  2N·2^cm ≤ 2^bits  ⇒  2N ≤ 2^(bits-cm)
    have h1 : 2 * N * 2 ^ cm ≤ 2 ^ bits := by
      have : 2 * N * 2 ^ cm = N * 2 ^ (cm + 1) := by rw [pow_succ]; ring
      rw [this]; exact hbud
    have h2 : 2 ^ bits = 2 ^ (bits - cm) * 2 ^ cm := by rw [← pow_add]; congr 1; omega
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  -- divStep_decode on the window q_start = 2*cm, bits = bits - cm.
  have hflag_out : flagW bits < 2 * cm ∨ 2 * cm + 2 * (bits - cm) + 1 ≤ flagW bits := by
    right; show 2 * cm + 2 * (bits - cm) + 1 ≤ flagW bits; unfold flagW; omega
  have hqbit_out : qBase bits + cm < 2 * cm ∨ 2 * cm + 2 * (bits - cm) + 1 ≤ qBase bits + cm := by
    right; show 2 * cm + 2 * (bits - cm) + 1 ≤ qBase bits + cm; unfold qBase; omega
  have hqf : qBase bits + cm ≠ flagW bits := by unfold qBase flagW; omega
  have hwin_lt' : r / 2 ^ cm < 2 * N := hwin_lt
  have hdec := divStep_decode (bits - cm) (2 * cm) N (flagW bits) (qBase bits + cm)
      (r / 2 ^ cm) hN h2N hwin_lt' hflag_out hqbit_out hqf f
      hcin_w S.h_flag (S.h_quot cm (by omega)) htgt_w hread_w
  obtain ⟨hd_tgt, hd_qbit, hd_flag, hd_cin, hd_read, hd_frame⟩ := hdec
  -- unfold g = applyNat (divStep (bits-cm) (2cm) N (flagW) (qBase+cm)) f
  have hg : g = Gate.applyNat (divStep (bits - cm) (2 * cm) N (flagW bits) (qBase bits + cm)) f := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- data band = r'.testBit
    intro i hi
    rw [hg]
    by_cases hic : i < cm
    · -- low data bit i: framed by the divstep (position 0+2i+1 < 2cm), so = r.testBit i.
      have hframe := hd_frame (0 + 2 * i + 1) (by unfold flagW; omega)
        (by unfold qBase; omega) (by left; omega)
      rw [hframe, S.h_tgt i hi]
      -- r.testBit i = (topStepRunning cm N r).testBit i for i < cm (low parts agree).
      rw [topStepRunning_low_testBit cm N r i hic]
    · -- high data bit i ≥ cm: window target index i' = i - cm.
      have hi' : i - cm < bits - cm := by omega
      have hpos : (0 : Nat) + 2 * i + 1 = 2 * cm + 2 * (i - cm) + 1 := by omega
      rw [hpos, hd_tgt (i - cm) hi']
      -- ((r/2^cm) % N).testBit (i-cm) = (topStepRunning).testBit i.
      rw [topStepRunning_high_testBit cm N r i (by omega)]
  · intro i hi
    rw [hg]
    by_cases hic : i < cm
    · -- low read wire.  Wire 0+2i+2 = 2cm is the WINDOW carry-in (q_start) iff i = cm-1.
      by_cases hov : (0 : Nat) + 2 * i + 2 = 2 * cm
      · -- this wire is the window's carry-in; cleaned by hd_cin.
        rw [hov]; exact hd_cin
      · have hframe := hd_frame (0 + 2 * i + 2) (by unfold flagW; omega)
          (by unfold qBase; omega) (by left; omega)
        rw [hframe]; exact S.h_read i hi
    · have hi' : i - cm < bits - cm := by omega
      have hpos : (0 : Nat) + 2 * i + 2 = 2 * cm + 2 * (i - cm) + 2 := by omega
      rw [hpos, hd_read (i - cm) hi']
  · -- carry wire 0.
    rw [hg]
    rcases Nat.eq_zero_or_pos cm with hc0 | hcpos
    · subst hc0; simpa using hd_cin
    · have hframe := hd_frame 0 (by unfold flagW; omega) (by unfold qBase; omega) (by left; omega)
      rw [hframe]; exact S.h_cin
  · rw [hg]; exact hd_flag
  · rw [hg]; exact hd_qbit
  · -- lower quotient wires k < cm unchanged.
    intro k hk
    rw [hg]
    have hframe := hd_frame (qBase bits + k)
      (by show qBase bits + k ≠ flagW bits; unfold qBase flagW; omega)
      (by show qBase bits + k ≠ qBase bits + cm; omega)
      (by right; show 2 * cm + 2 * (bits - cm) + 1 ≤ qBase bits + k; unfold qBase; omega)
    rw [hframe]; exact S.h_quot k (by omega)

/-! ### §5f. Reassembly arithmetic (`r` vs `r' = topStepRunning`). -/

/-- `r` and `r'` differ by a multiple of `N`, so they share the remainder. -/
theorem topStepRunning_mod_N (cm N r : Nat) :
    topStepRunning cm N r % N = r % N := by
  unfold topStepRunning
  -- The middle factor is congruent mod N: (r/2^cm)%N ≡ r/2^cm [MOD N].
  have hmod : (r % 2 ^ cm + 2 ^ cm * (r / 2 ^ cm % N))
      ≡ (r % 2 ^ cm + 2 ^ cm * (r / 2 ^ cm)) [MOD N] := by
    apply Nat.ModEq.add_left
    apply Nat.ModEq.mul_left
    exact Nat.mod_modEq _ _
  -- and r%2^cm + 2^cm*(r/2^cm) = r.
  rw [Nat.mod_add_div] at hmod
  exact hmod

/-- Quotient reassembly: `r / N = r'/N + 2^cm · ((r/2^cm)/N)` with `r' = topStepRunning`. -/
theorem topStepRunning_div_N (cm N r : Nat) (hN : 0 < N) :
    r / N = topStepRunning cm N r / N + 2 ^ cm * (r / 2 ^ cm / N) := by
  -- r = r' + N · M, with M := 2^cm · ((r/2^cm)/N).
  set M := 2 ^ cm * (r / 2 ^ cm / N) with hM
  have hrr : r = N * M + topStepRunning cm N r := by
    show r = N * (2 ^ cm * (r / 2 ^ cm / N)) + topStepRunning cm N r
    unfold topStepRunning
    conv_lhs => rw [← Nat.mod_add_div r (2 ^ cm)]
    have hq : r / 2 ^ cm = r / 2 ^ cm % N + N * (r / 2 ^ cm / N) :=
      (Nat.mod_add_div (r / 2 ^ cm) N).symm
    conv_lhs => rw [hq]
    ring
  -- r / N = (N*M + r')/N = M + r'/N.
  conv_lhs => rw [hrr]
  rw [Nat.mul_add_div hN, Nat.add_comm]

/-- `r' / N < 2^cm` (the lower-quotient part fits in `cm` bits). -/
theorem topStepRunning_div_N_lt (cm N r : Nat) (hN : 0 < N) :
    topStepRunning cm N r / N < 2 ^ cm := by
  have h := topStepRunning_lt cm N r hN
  rw [Nat.div_lt_iff_lt_mul hN]
  calc topStepRunning cm N r < N * 2 ^ cm := h
    _ = 2 ^ cm * N := by ring

/-- Adding a multiple of `2^cm` does not change bits below `cm`. -/
theorem testBit_add_mul_two_pow_low (x t cm k : Nat) (hk : k < cm) :
    (x + 2 ^ cm * t).testBit k = x.testBit k := by
  have h1 : (x + 2 ^ cm * t).testBit k = ((x + 2 ^ cm * t) % 2 ^ cm).testBit k := by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
  have h2 : x.testBit k = (x % 2 ^ cm).testBit k := by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]
  rw [h1, h2, Nat.add_mul_mod_self_left]

/-- Low quotient bits (`k < cm`): `(r/N).testBit k = (r'/N).testBit k`. -/
theorem quot_low_testBit (cm N r k : Nat) (hN : 0 < N) (hk : k < cm) :
    (r / N).testBit k = (topStepRunning cm N r / N).testBit k := by
  rw [topStepRunning_div_N cm N r hN]
  exact testBit_add_mul_two_pow_low _ _ cm k hk

/-- Top quotient bit (`= cm`): `(r/N).testBit cm`-equivalent value is `[N ≤ r/2^cm]`,
    using `r/2^cm < 2N`. -/
theorem quot_top_bit (cm N r : Nat) (_hN : 0 < N) (hlt : r / 2 ^ cm < 2 * N) :
    (r / 2 ^ cm) / N = (if N ≤ r / 2 ^ cm then 1 else 0) := by
  by_cases h : N ≤ r / 2 ^ cm
  · rw [if_pos h]
    -- N ≤ r/2^cm < 2N  ⇒  (r/2^cm)/N = 1
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [if_neg h, Nat.div_eq_of_lt (by omega)]

/-- Bit `cm` of `(low + 2^cm·M)` with `low < 2^cm` reads `M.testBit 0`. -/
theorem testBit_add_two_pow_mul_high (cm N r : Nat) :
    (topStepRunning cm N r / N + 2 ^ cm * (r / 2 ^ cm / N)).testBit cm
      = (r / 2 ^ cm / N).testBit 0 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- N = 0: both sides reduce via x/0 = 0.
    subst hN0; simp [Nat.div_zero, topStepRunning]
  · have hlow : topStepRunning cm N r / N < 2 ^ cm := topStepRunning_div_N_lt cm N r hN
    -- testBit at cm = (·/2^cm).testBit 0, and (low + 2^cm·M)/2^cm = M.
    have h1 : (topStepRunning cm N r / N + 2 ^ cm * (r / 2 ^ cm / N)).testBit (0 + cm)
        = ((topStepRunning cm N r / N + 2 ^ cm * (r / 2 ^ cm / N)) / 2 ^ cm).testBit 0 :=
      Nat.testBit_add _ 0 cm
    rw [Nat.zero_add] at h1
    rw [h1, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ cm),
        Nat.div_eq_of_lt hlow, Nat.zero_add]

/-! ### §5g. THE GENERAL DECODE (full induction). -/

/-- **GENERAL DECODE (full induction over `cm`).**  From any `DivState bits cm N r f`,
    after the divider `divModN bits cm N` the state `g`:
      • DATA band (target reg, `q_start = 0`) holds `r % N`,
      • QUOTIENT wire `qBase bits + k` holds `(r / N).testBit k` for `k < cm`,
      • TRANSIENT workspace (carry / read band / flag) is clean,
    and lifts a `DivState`.  Closes the divider's decode contract. -/
theorem divModN_decode_gen :
    ∀ (cm bits N r : Nat) (f : Nat → Bool), DivState bits cm N r f →
      let g := Gate.applyNat (divModN bits cm N) f
      (∀ i, i < bits → g (0 + 2 * i + 1) = (r % N).testBit i)
      ∧ (∀ k, k < cm → g (qBase bits + k) = (r / N).testBit k)
      ∧ g 0 = false
      ∧ g (flagW bits) = false
      ∧ (∀ i, i < bits → g (0 + 2 * i + 2) = false) := by
  intro cm
  induction cm with
  | zero =>
    intro bits N r f S
    -- divModN bits 0 N = I, so g = f; r < N (r < N*2^0 = N) ⇒ r%N = r.
    have hrN : r < N := by have := S.hr; simpa using this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      show f (0 + 2 * i + 1) = (r % N).testBit i
      rw [Nat.mod_eq_of_lt hrN]; exact S.h_tgt i hi
    · intro k hk; omega
    · exact S.h_cin
    · exact S.h_flag
    · intro i hi; exact S.h_read i hi
  | succ cm ih =>
    intro bits N r f S
    -- divModN bits (cm+1) N = seq (divStepAt bits N cm) (divModN bits cm N).
    -- g = applyNat (divModN bits cm N) (applyNat (divStepAt bits N cm) f).
    show
      let g := Gate.applyNat (Gate.seq (divStepAt bits N cm) (divModN bits cm N)) f
      (∀ i, i < bits → g (0 + 2 * i + 1) = (r % N).testBit i)
      ∧ (∀ k, k < cm + 1 → g (qBase bits + k) = (r / N).testBit k)
      ∧ g 0 = false
      ∧ g (flagW bits) = false
      ∧ (∀ i, i < bits → g (0 + 2 * i + 2) = false)
    simp only [Gate.applyNat_seq]
    -- top step output state f1.
    set f1 := Gate.applyNat (divStepAt bits N cm) f with hf1
    obtain ⟨ho_tgt, ho_read, ho_cin, ho_flag, ho_qcm, ho_qlow⟩ := topStep_global_out bits cm N r f S
    -- the tail input is a DivState for r' = topStepRunning cm N r.
    set r' := topStepRunning cm N r with hr'
    have hN := S.hN
    have S' : DivState bits cm N r' f1 := by
      refine ⟨?_, ?_, ?_, hN, ho_cin, ho_flag, ?_, ?_, ?_⟩
      · exact topStepRunning_lt cm N r hN
      · -- N*2^cm ≤ 2^bits  (from N*2^(cm+1) ≤ 2^bits)
        have := S.hbudget
        calc N * 2 ^ cm ≤ N * 2 ^ (cm + 1) := by
              apply Nat.mul_le_mul_left; exact Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ 2 ^ bits := this
      · have := S.hcm; omega
      · exact ho_tgt
      · exact ho_read
      · intro k hk; exact ho_qlow k hk
    -- apply IH to the tail on f1.
    obtain ⟨ht_tgt, ht_quot, ht_cin, ht_flag, ht_read⟩ := ih bits N r' f1 S'
    refine ⟨?_, ?_, ht_cin, ht_flag, ht_read⟩
    · -- DATA band: tail gives r'%N = r%N.
      intro i hi
      rw [ht_tgt i hi, topStepRunning_mod_N cm N r]
    · -- QUOTIENT band.
      intro k hk
      rcases Nat.lt_or_ge k cm with hklt | hkge
      · -- lower bit k < cm: from the tail (r'/N), then quot_low_testBit.
        rw [ht_quot k hklt, ← quot_low_testBit cm N r k hN hklt]
      · -- top bit k = cm.
        have hkeq : k = cm := by omega
        rw [hkeq]
        -- the tail frames qBase+cm (cm-step divider only touches qBase+0..qBase+(cm-1)).
        have hframe : Gate.applyNat (divModN bits cm N) f1 (qBase bits + cm) = f1 (qBase bits + cm) := by
          apply FormalRV.Shor.GidneyInPlace.GatePerm.applyNat_frame (divModN bits cm N) (dimDiv bits cm)
            (divModN_wellTyped bits cm N (by have := S.hcm; omega) (by have := S.hcm; omega : cm ≤ bits))
          unfold dimDiv qBase; omega
        rw [hframe, hf1, ho_qcm]
        -- (r/N).testBit cm = decide (N ≤ r/2^cm).
        obtain ⟨_, hwin_lt, _, _, _⟩ := topStep_local_hyps bits cm N r f S
        -- (r/N).testBit cm = ((r/2^cm)/N) bit 0 = [N ≤ r/2^cm]
        have hbit : (r / N).testBit cm
            = (if N ≤ r / 2 ^ cm then 1 else 0 : Nat).testBit 0 := by
          rw [topStepRunning_div_N cm N r hN]
          rw [testBit_add_two_pow_mul_high cm N r]
          rw [quot_top_bit cm N r hN hwin_lt]
        rw [hbit]
        by_cases h : N ≤ r / 2 ^ cm <;> simp [h]

/-! ### §5h. HEADLINE: the support-form decode (the deliverable). -/

/-- The clean input `encDiv bits v` is a `DivState bits cm N v` whenever `v < N·2^cm`,
    `N·2^cm ≤ 2^bits`, `cm ≤ bits`, `0 < N`. -/
theorem encDiv_DivState (bits cm N v : Nat)
    (hr : v < N * 2 ^ cm) (hbud : N * 2 ^ cm ≤ 2 ^ bits) (hcm : cm ≤ bits) (hN : 0 < N) :
    DivState bits cm N v (encDiv bits v) :=
  { hr := hr, hbudget := hbud, hcm := hcm, hN := hN
    h_cin := encDiv_cin bits v
    h_flag := encDiv_flag bits v
    h_tgt := fun i hi => encDiv_data bits v i hi
    h_read := fun i hi => encDiv_read bits v i hi
    h_quot := fun k _ => encDiv_qbit bits v k }

/-- **HEADLINE — the reversible DIVMOD-by-N decode (Stage A), fully verified.**
    On the support `v = z + j·N` (`z < N`, `j < 2^cm`, budget `2^cm·N ≤ 2^bits`),
    running `divModN bits cm N` on the clean input `encDiv bits v`:
      • the DATA band (Cuccaro target reg, `q_start = 0`) decodes to `z = v % N`,
      • the QUOTIENT band wire `qBase bits + k` holds bit `k` of `j = v / N`,
      • the TRANSIENT workspace (carry / read band / flag) returns clean,
      • the gate is WellTyped at `dimDiv bits cm`.
    (`Gate.reverse (divModN bits cm N)` then composes for Stage C.) -/
theorem divModN_decode
    (bits cm N z j : Nat)
    (hbits : 1 ≤ bits) (hN : 0 < N) (hcm : cm ≤ bits)
    (hbudget : 2 ^ cm * N ≤ 2 ^ bits)
    (hz : z < N) (hj : j < 2 ^ cm) :
    -- DATA band → remainder z = v % N
    cuccaro_target_val bits 0
        (Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N))) = z
    -- QUOTIENT band → bit k of j = v / N
    ∧ (∀ k, k < cm →
        Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (qBase bits + k)
          = j.testBit k)
    -- TRANSIENT clean: flag, read band, carry
    ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (flagW bits) = false
    ∧ (∀ i, i < bits →
        Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) (0 + 2 * i + 2) = false)
    ∧ Gate.applyNat (divModN bits cm N) (encDiv bits (z + j * N)) 0 = false
    -- WELL-TYPED
    ∧ Gate.WellTyped (dimDiv bits cm) (divModN bits cm N) := by
  set v := z + j * N with hv
  -- budget in the convenient orientation, and v < N*2^cm.
  have hbud' : N * 2 ^ cm ≤ 2 ^ bits := by rw [Nat.mul_comm]; exact hbudget
  have hv_lt : v < N * 2 ^ cm := by
    rw [hv]
    calc z + j * N < N + j * N := by omega
      _ = (j + 1) * N := by ring
      _ ≤ 2 ^ cm * N := Nat.mul_le_mul_right _ (by omega)
      _ = N * 2 ^ cm := by ring
  have hv_bits : v < 2 ^ bits := lt_of_lt_of_le hv_lt hbud'
  -- the general decode on the DivState of encDiv.
  obtain ⟨hd_tgt, hd_quot, hd_cin, hd_flag, hd_read⟩ :=
    divModN_decode_gen cm bits N v (encDiv bits v)
      (encDiv_DivState bits cm N v hv_lt hbud' hcm hN)
  -- arithmetic: v % N = z, v / N = j.
  obtain ⟨hjdiv, hzmod⟩ := divModN_arith N z j hN hz
  rw [← hv] at hjdiv hzmod
  refine ⟨?_, ?_, hd_flag, hd_read, hd_cin, ?_⟩
  · -- DATA band decode = v % N = z.
    have hz_bits : z < 2 ^ bits := by
      have hNle : N ≤ 2 ^ bits := le_trans (Nat.le_mul_of_pos_right N (by positivity : 0 < 2 ^ cm)) hbud'
      omega
    rw [cuccaro_target_val_eq_sum_when_bits_match bits 0 (v % N) _
          (fun i hi => by rw [hd_tgt i hi])]
    rw [hzmod]
    exact Nat.mod_eq_of_lt hz_bits
  · -- QUOTIENT band → bit k of v/N = j.
    intro k hk; rw [hd_quot k hk, hjdiv]
  · exact divModN_wellTyped bits cm N hbits hcm

end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
