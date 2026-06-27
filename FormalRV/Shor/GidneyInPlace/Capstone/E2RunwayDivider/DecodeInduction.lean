/- E2RunwayDivider — Â§5d-5g invariant + reassembly + general decode induction.  Part of the `E2RunwayDivider` re-export shim (same namespace). -/
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.DecodeBase

namespace FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider

open FormalRV.Framework FormalRV.Framework.Gate
open FormalRV.BQAlgo
open FormalRV.Shor.WindowedCircuit
  (compareConstXor_state_general condSub_state_general)


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


end FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider
