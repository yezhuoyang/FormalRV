import FormalRV.Core.Gate
import FormalRV.Framework.PaperClaims
import FormalRV.Arithmetic.Correctness
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupDefinitions
import FormalRV.Arithmetic.UnaryLookup.UnaryLookupGateDerivations

namespace FormalRV.BQAlgo
open FormalRV.Framework
open FormalRV.Framework.Gate
open FormalRV.PaperClaims

/-- **CNOT layer with word-register targets preserves any and-bit** at
    `ulookup_and_idx k` for `k < n_addr`. By the frame lemma (Iter 224)
    + disjointness `and_idx k = 2 + 2*k < 1 + 2*n_addr ≤ word_idx _ j`. -/
theorem Lookup.cnot_layer_post_state_preserves_and_bit
    (n_addr : Nat) (ctrl_idx : Nat) (word_cnot_idxs : List Nat)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) (k : Nat) (hk : k < n_addr) :
    Lookup.cnot_layer_post_state ctrl_idx word_cnot_idxs f (ulookup_and_idx k)
      = f (ulookup_and_idx k) := by
  apply Lookup.cnot_layer_post_state_frame
  intro h_in
  have h := h_word _ h_in
  unfold ulookup_and_idx at h
  omega

/-- **CNOT layer with word targets preserves the ctrl qubit** (qubit 0).
    Special case of the general ctrl-preservation lemma; the layer's
    declared control is `and_idx (n_addr - 1)` which is NOT
    `ulookup_ctrl_idx = 0`, and word targets all exceed 0. -/
theorem Lookup.cnot_layer_post_state_preserves_ctrl
    (n_addr : Nat) (ctrl_idx : Nat) (word_cnot_idxs : List Nat)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) :
    Lookup.cnot_layer_post_state ctrl_idx word_cnot_idxs f ulookup_ctrl_idx
      = f ulookup_ctrl_idx := by
  apply Lookup.cnot_layer_post_state_frame
  intro h_in
  have h := h_word _ h_in
  unfold ulookup_ctrl_idx at h
  omega

/-- **CNOT layer with word targets preserves each address qubit**
    `ulookup_address_idx i` for `i < n_addr`. Word indices start at
    `1 + 2*n_addr`, while address indices are `1 + 2*i ≤ 1 + 2*(n_addr - 1) < 1 + 2*n_addr`. -/
theorem Lookup.cnot_layer_post_state_preserves_address
    (n_addr : Nat) (ctrl_idx : Nat) (word_cnot_idxs : List Nat)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) (i : Nat) (hi : i < n_addr) :
    Lookup.cnot_layer_post_state ctrl_idx word_cnot_idxs f (ulookup_address_idx i)
      = f (ulookup_address_idx i) := by
  apply Lookup.cnot_layer_post_state_frame
  intro h_in
  have h := h_word _ h_in
  unfold ulookup_address_idx at h
  omega

/-- **Decide-witness**: with n_addr=3 and word_cnot_idxs = [7, 8, 12]
    (all valid word indices ≥ 1 + 2*3 = 7), the and-bit at position
    `ulookup_and_idx 2 = 6` is preserved by the CNOT layer. -/
example :
    let f : Nat → Bool := fun i => i = 6  -- and_2 is initially true
    Lookup.cnot_layer_post_state (ulookup_and_idx 2) [7, 8, 12] f 6 = f 6 := by
  decide

/-! ## Cascade + uncompute frame lemmas (ctrl, address, word) (Iter 231, 2026-05-13)

    Iter 221 proved frames for the FORWARD cascade at ctrl and address.
    This tick adds the SYMMETRIC frames for the REVERSE uncompute,
    plus WORD-index frames for both (since cascade and uncompute only
    write to and-bits, which are disjoint from the word register).

    With these in place, the Iter 232 headline assembly will have a
    complete frame-condition toolkit: every register (ctrl, address,
    word) is provably preserved by the cascade-and-uncompute pair
    (modulo and-bit writes, which the cascade·uncompute = id from
    Iter 229 cancels). -/

/-- **Uncompute frame at ctrl_idx**: the n-step uncompute post-state
    preserves `ulookup_ctrl_idx`. Direct analog of Iter 221's
    `prefix_and_cascade_post_state_frame_ctrl`. -/
theorem prefix_and_uncompute_post_state_frame_ctrl
    (n : Nat) (f : Nat → Bool) :
    prefix_and_uncompute_post_state n f ulookup_ctrl_idx = f ulookup_ctrl_idx := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_uncompute_post_state k (prefix_and_step_post_state k f)
            ulookup_ctrl_idx = f ulookup_ctrl_idx
    rw [ih]
    exact prefix_and_step_post_state_frame k f ulookup_ctrl_idx
            (by unfold ulookup_ctrl_idx ulookup_and_idx; omega)

/-- **Uncompute frame at every address bit**: preserves
    `ulookup_address_idx j` for any `j`. -/
theorem prefix_and_uncompute_post_state_frame_addr
    (n : Nat) (f : Nat → Bool) (j : Nat) :
    prefix_and_uncompute_post_state n f (ulookup_address_idx j)
      = f (ulookup_address_idx j) := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_uncompute_post_state k (prefix_and_step_post_state k f)
            (ulookup_address_idx j) = f (ulookup_address_idx j)
    rw [ih]
    exact prefix_and_step_post_state_frame k f (ulookup_address_idx j)
            (by unfold ulookup_address_idx ulookup_and_idx; omega)

/-- **Cascade frame at every word bit**: preserves `ulookup_word_idx n_addr j`
    for any `j` (word indices `≥ 1 + 2·n_addr` are disjoint from
    and-indices `≤ 2·n` for the cascade's n-many writes). -/
theorem prefix_and_cascade_post_state_frame_word
    (n n_addr : Nat) (f : Nat → Bool) (j : Nat) (hn : n ≤ n_addr) :
    prefix_and_cascade_post_state n f (ulookup_word_idx n_addr j)
      = f (ulookup_word_idx n_addr j) := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_step_post_state k (prefix_and_cascade_post_state k f)
            (ulookup_word_idx n_addr j) = f (ulookup_word_idx n_addr j)
    rw [prefix_and_step_post_state_frame k _ (ulookup_word_idx n_addr j)
          (by unfold ulookup_word_idx ulookup_and_idx; omega)]
    exact ih f (by omega)

/-- **Uncompute frame at every word bit**: symmetric to the cascade
    word-frame. -/
theorem prefix_and_uncompute_post_state_frame_word
    (n n_addr : Nat) (f : Nat → Bool) (j : Nat) (hn : n ≤ n_addr) :
    prefix_and_uncompute_post_state n f (ulookup_word_idx n_addr j)
      = f (ulookup_word_idx n_addr j) := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_uncompute_post_state k (prefix_and_step_post_state k f)
            (ulookup_word_idx n_addr j) = f (ulookup_word_idx n_addr j)
    rw [ih (prefix_and_step_post_state k f) (by omega)]
    exact prefix_and_step_post_state_frame k f (ulookup_word_idx n_addr j)
            (by unfold ulookup_word_idx ulookup_and_idx; omega)

/-! ## Iteration body: ctrl + address preservation (Iter 232, 2026-05-13)

    First two pieces of the headline. The ctrl qubit is preserved by
    EVERY stage of the iteration body (since neither X-flip nor cascade
    nor CNOT-on-word touches it). The address bits are restored by the
    outer X-flip layers' involution + the inner cascade/cnot/uncompute
    frames preserving them. -/

/-- **Iteration preserves ctrl**. Requires `ctrl_idx ∉ addr_flip_idxs`
    (X-flip layers don't touch ctrl) and `AllWordIdx n_addr word_cnot_idxs`
    (CNOT-on-word doesn't touch ctrl, which has index 0 < 1 + 2·n_addr). -/
theorem Lookup.iteration_post_state_preserves_ctrl
    (n_addr : Nat) (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_ctrl_not_flip : ulookup_ctrl_idx ∉ addr_flip_idxs)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) :
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        ulookup_ctrl_idx = f ulookup_ctrl_idx := by
  unfold Lookup.iteration_post_state
  -- Walk through the 5 stages outermost-to-innermost via the frame chain:
  -- Stage 5 (outer x_flip) preserves ctrl.
  rw [Lookup.x_flip_post_state_frame _ _ ulookup_ctrl_idx h_ctrl_not_flip]
  -- Stage 4 (uncompute) preserves ctrl.
  rw [prefix_and_uncompute_post_state_frame_ctrl]
  -- Stage 3 (cnot on word) preserves ctrl.
  rw [Lookup.cnot_layer_post_state_preserves_ctrl n_addr _ _ h_word]
  -- Stage 2 (cascade) preserves ctrl.
  rw [prefix_and_cascade_post_state_frame_ctrl]
  -- Stage 1 (inner x_flip) preserves ctrl.
  rw [Lookup.x_flip_post_state_frame _ _ ulookup_ctrl_idx h_ctrl_not_flip]

/-- **Iteration preserves every address bit** `ulookup_address_idx i` for
    `i < n_addr`. The two outer X-flip layers cancel by involution
    (Iter 226), and the inner 3 stages each preserve address bits via
    register-level frame lemmas. -/
theorem Lookup.iteration_post_state_preserves_address
    (n_addr : Nat) (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_flip_nodup : addr_flip_idxs.Nodup)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) (i : Nat) (hi : i < n_addr) :
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        (ulookup_address_idx i) = f (ulookup_address_idx i) := by
  unfold Lookup.iteration_post_state
  -- Strategy: show the intermediate "after stages 1-4" state at address
  -- i equals the state "after stage 1" (since stages 2-4 all preserve
  -- address bits). Then stage 5 = X-flip applied to this, and X-flip
  -- applied to (X-flip f) at address i = f at address i by involution
  -- (or by case-split on whether addr_idx i ∈ flips).
  -- Let g denote the input to the outer x_flip (stage 5).
  -- g (addr i) = cascade · cnot · uncompute applied to (x_flip f) at addr i
  --           = (x_flip f) (addr i)   [by stages 2-4 frames]
  -- Then x_flip flips g (addr i) = x_flip flips (x_flip flips f) (addr i)
  --                              = f (addr i)   [by x_flip involution]
  -- But we need this pointwise at addr_idx i, not as a function equation.
  -- Use case-split on addr_idx i ∈ flips.
  set g := prefix_and_uncompute_post_state n_addr
            (Lookup.cnot_layer_post_state (ulookup_and_idx (n_addr - 1))
              word_cnot_idxs
              (prefix_and_cascade_post_state n_addr
                (Lookup.x_flip_post_state addr_flip_idxs f)))
  have h_g_at_addr : g (ulookup_address_idx i)
                       = Lookup.x_flip_post_state addr_flip_idxs f
                           (ulookup_address_idx i) := by
    show prefix_and_uncompute_post_state n_addr _ (ulookup_address_idx i) = _
    rw [prefix_and_uncompute_post_state_frame_addr,
        Lookup.cnot_layer_post_state_preserves_address n_addr _ _ h_word _ i hi,
        prefix_and_cascade_post_state_frame_addr]
  by_cases h_in : ulookup_address_idx i ∈ addr_flip_idxs
  · rw [Lookup.x_flip_post_state_at addr_flip_idxs h_flip_nodup g _ h_in]
    rw [h_g_at_addr]
    rw [Lookup.x_flip_post_state_at addr_flip_idxs h_flip_nodup f _ h_in]
    cases f (ulookup_address_idx i) <;> rfl
  · rw [Lookup.x_flip_post_state_frame addr_flip_idxs g _ h_in]
    rw [h_g_at_addr]
    rw [Lookup.x_flip_post_state_frame addr_flip_idxs f _ h_in]

/-! ## General frames for cascade + uncompute (Iter 233, 2026-05-14)

    The cascade and uncompute post-states write ONLY to and-bits (i.e.,
    positions `ulookup_and_idx k` for `k < n`). The previously proven
    register-specific frames (Iter 221 ctrl/address, Iter 231 word) are
    special cases of the following general frames: positions outside
    {and_0, ..., and_{n-1}} are unchanged.

    These general frames are the cleaner tool for the Iter 234 and-bit
    preservation argument, where we need to argue that the middle CNOT
    layer's writes are invisible to the uncompute (since they go to
    word indices outside the and-register). -/

/-- **General cascade frame**: positions outside `{ulookup_and_idx k : k < n}`
    are unchanged by the n-step forward cascade. -/
theorem prefix_and_cascade_post_state_frame_general
    (n : Nat) (f : Nat → Bool) (j : Nat)
    (h : ∀ k, k < n → j ≠ ulookup_and_idx k) :
    prefix_and_cascade_post_state n f j = f j := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_step_post_state k (prefix_and_cascade_post_state k f) j = f j
    rw [prefix_and_step_post_state_frame k _ j (h k (Nat.lt_succ_self _))]
    exact ih f (fun m hm => h m (Nat.lt_succ_of_lt hm))

/-- **General uncompute frame**: positions outside `{ulookup_and_idx k : k < n}`
    are unchanged by the n-step reverse uncompute. Symmetric to the
    cascade general frame above. -/
theorem prefix_and_uncompute_post_state_frame_general
    (n : Nat) (f : Nat → Bool) (j : Nat)
    (h : ∀ k, k < n → j ≠ ulookup_and_idx k) :
    prefix_and_uncompute_post_state n f j = f j := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_uncompute_post_state k (prefix_and_step_post_state k f) j = f j
    rw [ih (prefix_and_step_post_state k f) (fun m hm => h m (Nat.lt_succ_of_lt hm))]
    exact prefix_and_step_post_state_frame k f j (h k (Nat.lt_succ_self _))

/-! ## Iteration body: word-NOT-in-targets preserved (Iter 235, 2026-05-14)

    Third of the 4 headline components. Word-register positions
    OUTSIDE `word_cnot_idxs` are unchanged by every stage of the
    iteration body — a pure frame chain. This is the EASIEST of
    the 4 components (per Iter 234's risk plan) and gets us to
    3/4 toward the headline.

    The remaining and-bit preservation (Iter 234 plan medium-high
    risk, requires uncompute congruence lemma) is deferred to
    Iter 236+. -/

/-- **Iteration preserves any word-register position not in CNOT
    targets**. Requires:
    - `addr_flip_idxs` are all valid address indices (so they don't
      include word positions).
    - `word_cnot_idxs` consist of word indices (`AllWordIdx`).
    - `p` is in the word register (`1 + 2·n_addr ≤ p`) and not in the
      CNOT target list. -/
theorem Lookup.iteration_post_state_preserves_outside_word_targets
    (n_addr : Nat) (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_flip_addr : ∀ x ∈ addr_flip_idxs,
                       ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (f : Nat → Bool) (p : Nat) (h_p_word : 1 + 2 * n_addr ≤ p)
    (h_not_target : p ∉ word_cnot_idxs) :
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f p = f p := by
  unfold Lookup.iteration_post_state
  -- Sub-fact 1: p ∉ addr_flip_idxs (since flips are address indices,
  -- which are all < 1 + 2*n_addr).
  have h_p_not_flip : p ∉ addr_flip_idxs := by
    intro h_in
    obtain ⟨i, hi, hpi⟩ := h_flip_addr p h_in
    rw [hpi] at h_p_word
    unfold ulookup_address_idx at h_p_word
    omega
  -- Sub-fact 2: p ≠ ulookup_and_idx k for any k < n_addr
  -- (and indices are 2 + 2k ≤ 2*n_addr < 1 + 2*n_addr ≤ p).
  have h_p_not_and : ∀ k, k < n_addr → p ≠ ulookup_and_idx k := by
    intro k hk h_eq
    rw [h_eq] at h_p_word
    unfold ulookup_and_idx at h_p_word
    omega
  -- Chain the 5 stages' frame conditions:
  -- Stage 5 (outer x_flip): p ∉ addr_flip_idxs → preserved.
  rw [Lookup.x_flip_post_state_frame _ _ p h_p_not_flip]
  -- Stage 4 (uncompute): general frame at p.
  rw [prefix_and_uncompute_post_state_frame_general n_addr _ p h_p_not_and]
  -- Stage 3 (CNOT layer): p ∉ word_cnot_idxs → preserved.
  rw [Lookup.cnot_layer_post_state_frame _ _ _ p h_not_target]
  -- Stage 2 (cascade): general frame at p.
  rw [prefix_and_cascade_post_state_frame_general n_addr _ p h_p_not_and]
  -- Stage 1 (inner x_flip): p ∉ addr_flip_idxs → preserved.
  rw [Lookup.x_flip_post_state_frame _ _ p h_p_not_flip]

/-! ## Iteration body: word-in-targets trigger XOR (Iter 236, 2026-05-14)

    The fourth (and last) headline component: word-register positions
    that ARE in `word_cnot_idxs` receive an XOR with the cascade's top
    bit (the "trigger" — `address_and ctrl effective_addr n_addr` per
    Iter 223 once unfolded).

    The result is stated abstractly: the iteration post-state at any
    `p ∈ word_cnot_idxs` equals `f p XOR trigger`, where the trigger
    is the cascade-applied-to-x-flipped-input's value at `and_{n_addr - 1}`.
    Connecting the trigger to `Lookup.address_and ctrl effective_addr n_addr`
    is then a clean corollary using Iter 223. -/

/-- **Iteration's trigger XOR at word targets**. For any `p ∈ word_cnot_idxs`
    (a target of the middle CNOT layer), the iteration post-state is
    `f p XOR T`, where `T = prefix_and_cascade_post_state n_addr
    (x_flip_post_state addr_flip_idxs f) (ulookup_and_idx (n_addr - 1))`
    is the cascade's top-bit trigger. -/
theorem Lookup.iteration_post_state_at_word_target
    (n_addr : Nat) (hn : 0 < n_addr)
    (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_word_nodup : word_cnot_idxs.Nodup)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (h_flip_addr : ∀ x ∈ addr_flip_idxs,
                       ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (f : Nat → Bool) (p : Nat) (h_in : p ∈ word_cnot_idxs) :
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f p
      = xor (f p)
            (prefix_and_cascade_post_state n_addr
              (Lookup.x_flip_post_state addr_flip_idxs f)
              (ulookup_and_idx (n_addr - 1))) := by
  unfold Lookup.iteration_post_state
  -- p is a word index (≥ 1 + 2·n_addr)
  have h_p_word : 1 + 2 * n_addr ≤ p := h_word p h_in
  -- p ∉ addr_flip_idxs (flips are address indices, all < 1 + 2·n_addr)
  have h_p_not_flip : p ∉ addr_flip_idxs := by
    intro h_in_flip
    obtain ⟨i, hi, hpi⟩ := h_flip_addr p h_in_flip
    rw [hpi] at h_p_word
    unfold ulookup_address_idx at h_p_word
    omega
  -- p ≠ ulookup_and_idx k for k < n_addr (and indices ≤ 2·n_addr < 1 + 2·n_addr)
  have h_p_not_and : ∀ k, k < n_addr → p ≠ ulookup_and_idx k := by
    intro k hk h_eq
    rw [h_eq] at h_p_word
    unfold ulookup_and_idx at h_p_word
    omega
  -- The CNOT-layer control bit `ulookup_and_idx (n_addr - 1)` is NOT in
  -- word_cnot_idxs (it's an and-bit, < 1 + 2·n_addr).
  have h_ctrl_for_cnot_not_in : ulookup_and_idx (n_addr - 1) ∉ word_cnot_idxs := by
    intro h_in_cnot
    have := h_word _ h_in_cnot
    unfold ulookup_and_idx at this
    omega
  -- Chain the 5 stages' post-state values at p:
  -- Stage 5 (outer x_flip): preserved at p (p ∉ addr_flip_idxs).
  rw [Lookup.x_flip_post_state_frame _ _ p h_p_not_flip]
  -- Stage 4 (uncompute): preserved at p (general frame).
  rw [prefix_and_uncompute_post_state_frame_general n_addr _ p h_p_not_and]
  -- Stage 3 (CNOT): value-at-element fires (p ∈ word_cnot_idxs).
  rw [Lookup.cnot_layer_post_state_at _ word_cnot_idxs h_word_nodup
        h_ctrl_for_cnot_not_in _ p h_in]
  -- Now the inner f at p (the post-state from stages 1-2 at p) collapses
  -- to `f p` via the cascade word-frame and inner x_flip frame.
  rw [prefix_and_cascade_post_state_frame_general n_addr _ p h_p_not_and]
  rw [Lookup.x_flip_post_state_frame _ _ p h_p_not_flip]

/-! ## Step commutes with update at word positions (Iter 237, 2026-05-14)

    Foundation for the and-bit preservation argument. The cascade step
    only reads from/writes to positions in the ctrl/address/and-register
    range `[0, 2 + 2k]`. A word-register update at p ≥ 1 + 2·n_addr (where
    k < n_addr) doesn't intersect the step's read/write set, so the
    update commutes through the step.

    This is the per-step commutation that lifts to uncompute commutation
    (Iter 238) and then to the and-bit preservation in the iteration. -/

/-- **Step commutes with word-update**: if `p ≥ 1 + 2·n_addr` (a word
    position) and `k < n_addr`, then applying step `k` after an update
    at `p` is the same as updating after step `k`. -/
theorem prefix_and_step_post_state_commute_update_word
    (k n_addr : Nat) (hk : k < n_addr)
    (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p : 1 + 2 * n_addr ≤ p) :
    prefix_and_step_post_state k (Function.update f p v)
      = Function.update (prefix_and_step_post_state k f) p v := by
  have h_p_ne_and_k : p ≠ ulookup_and_idx k := by
    unfold ulookup_and_idx; omega
  have h_p_ne_addr_k : p ≠ ulookup_address_idx k := by
    unfold ulookup_address_idx; omega
  have h_p_ne_ctrl : p ≠ ulookup_ctrl_idx := by
    unfold ulookup_ctrl_idx; omega
  have h_p_ne_and_pred : p ≠ ulookup_and_idx (k - 1) := by
    unfold ulookup_and_idx; omega
  funext j
  by_cases hjp : j = p
  · -- j = p: both sides equal v.
    rw [hjp]
    rw [Function.update_self]
    rw [prefix_and_step_post_state_frame k _ p h_p_ne_and_k]
    rw [Function.update_self]
  · -- j ≠ p: case-split on j = and_k vs j ≠ and_k.
    rw [Function.update_of_ne hjp]
    by_cases hj_and : j = ulookup_and_idx k
    · -- j = and_k: step writes here; the new value depends only on
      -- f at ctrl/and_{k-1}, addr_k, and_k — all ≠ p.
      rw [hj_and]
      -- Use the per-position helper (analog of the private lemmas in
      -- the involution proof).
      by_cases hk0 : k = 0
      · subst hk0
        rw [prefix_and_step_post_state_at_and_zero,
            prefix_and_step_post_state_at_and_zero]
        rw [Function.update_of_ne (Ne.symm h_p_ne_and_k),
            Function.update_of_ne (Ne.symm h_p_ne_ctrl),
            Function.update_of_ne (Ne.symm h_p_ne_addr_k)]
      · rw [prefix_and_step_post_state_at_and_succ k hk0,
            prefix_and_step_post_state_at_and_succ k hk0]
        rw [Function.update_of_ne (Ne.symm h_p_ne_and_k),
            Function.update_of_ne (Ne.symm h_p_ne_and_pred),
            Function.update_of_ne (Ne.symm h_p_ne_addr_k)]
    · -- j ≠ p AND j ≠ and_k: step doesn't write here. Frame both sides.
      rw [prefix_and_step_post_state_frame k _ j hj_and]
      rw [prefix_and_step_post_state_frame k f j hj_and]
      rw [Function.update_of_ne hjp]

/-! ## Uncompute commutes with word-update + CNOT layer invariance at and-bits
    (Iter 238, 2026-05-14)

    Lift Iter 237's step commutation to the full n-step uncompute via
    induction, then specialize to the CNOT-layer case via list induction.
    The endpoint: uncompute's value at and-bits is invariant under
    arbitrary CNOT-layer modifications (whose targets are word indices). -/

/-- **Uncompute commutes with word-update**: applying uncompute to an
    update at a word position equals updating after the uncompute.
    Direct induction on `n` using Iter 237's step commutation. -/
theorem prefix_and_uncompute_post_state_commute_update_word
    (n n_addr : Nat) (hn : n ≤ n_addr)
    (f : Nat → Bool) (p : Nat) (v : Bool)
    (h_p : 1 + 2 * n_addr ≤ p) :
    prefix_and_uncompute_post_state n (Function.update f p v)
      = Function.update (prefix_and_uncompute_post_state n f) p v := by
  induction n generalizing f with
  | zero => rfl
  | succ k ih =>
    show prefix_and_uncompute_post_state k
            (prefix_and_step_post_state k (Function.update f p v))
          = Function.update
              (prefix_and_uncompute_post_state k (prefix_and_step_post_state k f)) p v
    rw [prefix_and_step_post_state_commute_update_word k n_addr hn f p v h_p]
    exact ih (by omega) (prefix_and_step_post_state k f)

/-- **CNOT-layer invariance at and-bits**: the n-step uncompute output
    at any and-bit position is unchanged when the input is preprocessed
    by a CNOT layer with word-register targets.

    Proof: induction on the CNOT target list, using
    `prefix_and_uncompute_post_state_commute_update_word` at each
    list step. -/
theorem prefix_and_uncompute_post_state_at_and_invariant_under_cnot_layer
    (n n_addr : Nat) (hn : n ≤ n_addr)
    (ctrl_idx : Nat) (cnots : List Nat)
    (h_cnots_word : Lookup.AllWordIdx n_addr cnots)
    (f : Nat → Bool) (k : Nat) (hk : k < n_addr) :
    prefix_and_uncompute_post_state n
      (Lookup.cnot_layer_post_state ctrl_idx cnots f) (ulookup_and_idx k)
      = prefix_and_uncompute_post_state n f (ulookup_and_idx k) := by
  induction cnots with
  | nil => rfl
  | cons t rest ih =>
    -- cnot_layer (t::rest) f = update (cnot_layer rest f) t (xor (rec t) (rec ctrl))
    -- Apply update-commutation via uncompute, then recurse.
    show prefix_and_uncompute_post_state n
            (Function.update (Lookup.cnot_layer_post_state ctrl_idx rest f) t
              (xor (Lookup.cnot_layer_post_state ctrl_idx rest f t)
                   (Lookup.cnot_layer_post_state ctrl_idx rest f ctrl_idx)))
            (ulookup_and_idx k)
          = prefix_and_uncompute_post_state n f (ulookup_and_idx k)
    -- Step 1: hd is a word index (h_cnots_word applied to t ∈ t::rest).
    have h_t_word : 1 + 2 * n_addr ≤ t :=
      h_cnots_word t (List.mem_cons_self)
    -- Step 2: rest also satisfies AllWordIdx.
    have h_rest_word : Lookup.AllWordIdx n_addr rest :=
      fun x hx => h_cnots_word x (List.mem_cons_of_mem t hx)
    -- Step 3: uncompute commutes with the update at t.
    rw [prefix_and_uncompute_post_state_commute_update_word n n_addr hn _ t _ h_t_word]
    -- Step 4: and_k ≠ t (and indices ≤ 2*n_addr < 1+2*n_addr ≤ t).
    have h_andk_ne_t : ulookup_and_idx k ≠ t := by
      unfold ulookup_and_idx; omega
    rw [Function.update_of_ne h_andk_ne_t]
    -- Step 5: recurse.
    exact ih h_rest_word

/-! ## Iteration body: and-bit preservation — FINAL HEADLINE COMPONENT
    (Iter 239, 2026-05-14)

    The fifth and final headline component. The and-bit register
    (positions `ulookup_and_idx k` for `k < n_addr`) is returned to its
    INPUT value by the iteration body, thanks to:
    1. X-flip layers don't touch and-bits (flips are address indices).
    2. CNOT layer doesn't affect uncompute output at and-bits (Iter 238).
    3. cascade · uncompute = id (Iter 229) on the post-x_flip state. -/

/-- **Iteration preserves every and-bit** at `ulookup_and_idx k` for
    `k < n_addr`. The proof composes Iter 226 X-flip frame +
    Iter 238 CNOT-uncompute congruence + Iter 229 cascade·uncompute=id. -/
theorem Lookup.iteration_post_state_preserves_and
    (n_addr : Nat) (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_flip_addr : ∀ x ∈ addr_flip_idxs,
                       ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (f : Nat → Bool) (k : Nat) (hk : k < n_addr) :
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        (ulookup_and_idx k) = f (ulookup_and_idx k) := by
  unfold Lookup.iteration_post_state
  -- and_k ∉ addr_flip_idxs (parity: flips are address = 1+2i, and_k = 2+2k).
  have h_andk_not_flip : ulookup_and_idx k ∉ addr_flip_idxs := by
    intro h_in
    obtain ⟨i, hi, hki⟩ := h_flip_addr _ h_in
    unfold ulookup_and_idx ulookup_address_idx at hki
    omega
  -- Stage 5 (outer x_flip): preserves and_k.
  rw [Lookup.x_flip_post_state_frame _ _ _ h_andk_not_flip]
  -- Stage 4 (uncompute applied to cnot ∘ cascade ∘ x_flip):
  --   by Iter 238's congruence, the CNOT layer doesn't affect uncompute
  --   output at and-bits.
  rw [prefix_and_uncompute_post_state_at_and_invariant_under_cnot_layer
        n_addr n_addr (Nat.le_refl _) _ _ h_word _ k hk]
  -- Now: uncompute (cascade (x_flip f)) at and_k. By Iter 229, this = x_flip f.
  rw [prefix_and_cascade_uncompute_post_state_eq_id]
  -- Stage 1 (inner x_flip): preserves and_k.
  rw [Lookup.x_flip_post_state_frame _ _ _ h_andk_not_flip]

/-! ## Bundled headline: `unary_lookup_iteration_correct` (Iter 241, 2026-05-14)

    A SINGLE theorem bundling all 5 component characterizations of the
    iteration body. This is the formal statement of "the unary lookup
    iteration has the expected classical action": at every position p,
    the post-state is determined by p's register membership.

    Lookup analog of Iter 213's `gidney_classical_action_with_reverse`
    for the adder. -/

/-- **Headline: `unary_lookup_iteration` classical action**. For valid
    inputs (flip indices are address; word_cnot_idxs are word-register
    indices), the iteration post-state has the following form at every
    position:

    1. `p ∈ word_cnot_idxs`: `xor (f p) trigger` — written by the CNOT
       layer with the cascade-top-bit trigger.
    2. `p = ulookup_ctrl_idx`: preserved.
    3. `p = ulookup_address_idx i` for `i < n_addr`: restored to `f p`
       (X-flip layers cancel by involution).
    4. `p = ulookup_and_idx k` for `k < n_addr`: returned to clean
       (cascade · uncompute = id, modulo CNOT-layer-invariance at and-bits).
    5. `p` a word index, `p ∉ word_cnot_idxs`: preserved. -/
theorem Lookup.unary_lookup_iteration_correct
    (n_addr : Nat) (hn : 0 < n_addr)
    (addr_flip_idxs word_cnot_idxs : List Nat)
    (h_flip_addr : ∀ x ∈ addr_flip_idxs,
                       ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_flip_nodup : addr_flip_idxs.Nodup)
    (h_word : Lookup.AllWordIdx n_addr word_cnot_idxs)
    (h_word_nodup : word_cnot_idxs.Nodup)
    (f : Nat → Bool) :
    -- (1) Word targets get XOR'd with the trigger.
    (∀ p, p ∈ word_cnot_idxs →
      Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f p
        = xor (f p)
              (prefix_and_cascade_post_state n_addr
                (Lookup.x_flip_post_state addr_flip_idxs f)
                (ulookup_and_idx (n_addr - 1)))) ∧
    -- (2) ctrl is preserved.
    Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        ulookup_ctrl_idx = f ulookup_ctrl_idx ∧
    -- (3) Every address bit is restored.
    (∀ i, i < n_addr →
      Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        (ulookup_address_idx i) = f (ulookup_address_idx i)) ∧
    -- (4) Every and-bit is returned to clean.
    (∀ k, k < n_addr →
      Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f
        (ulookup_and_idx k) = f (ulookup_and_idx k)) ∧
    -- (5) Word indices not in CNOT targets are preserved.
    (∀ p, 1 + 2 * n_addr ≤ p → p ∉ word_cnot_idxs →
      Lookup.iteration_post_state n_addr addr_flip_idxs word_cnot_idxs f p = f p) := by
  -- Derive: ctrl_idx ∉ addr_flip_idxs (flips are address indices ≥ 1).
  have h_ctrl_not_flip : ulookup_ctrl_idx ∉ addr_flip_idxs := by
    intro h_in
    obtain ⟨i, _, hpi⟩ := h_flip_addr _ h_in
    unfold ulookup_ctrl_idx ulookup_address_idx at hpi
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p h_in
    exact Lookup.iteration_post_state_at_word_target n_addr hn
            addr_flip_idxs word_cnot_idxs h_word_nodup h_word h_flip_addr f p h_in
  · exact Lookup.iteration_post_state_preserves_ctrl n_addr
            addr_flip_idxs word_cnot_idxs h_ctrl_not_flip h_word f
  · intro i hi
    exact Lookup.iteration_post_state_preserves_address n_addr
            addr_flip_idxs word_cnot_idxs h_flip_nodup h_word f i hi
  · intro k hk
    exact Lookup.iteration_post_state_preserves_and n_addr
            addr_flip_idxs word_cnot_idxs h_flip_addr h_word f k hk
  · intro p h_p_word h_not_target
    exact Lookup.iteration_post_state_preserves_outside_word_targets n_addr
            addr_flip_idxs word_cnot_idxs h_flip_addr f p h_p_word h_not_target

/-! ## Trigger value at the X-flipped state (Iter 242, 2026-05-14)

    The headline's "trigger" — the cascade's top and-bit applied to the
    X-flipped input — can be unfolded via Iter 223's
    `prefix_and_cascade_top_bit_eq_address_and` to
    `Lookup.address_and ctrl effective_addr n_addr`, where
    `effective_addr` is the X-flipped bit pattern.

    The user supplies `effective_addr` as a Nat and proves the
    correspondence at each address position; the proof punts the
    bit-mask construction. -/

/-- **Trigger value under X-flip = `address_and` at effective address**.
    Specialization of Iter 223's `prefix_and_cascade_top_bit_eq_address_and`
    to the X-flipped state used in `unary_lookup_iteration`. -/
theorem Lookup.cascade_top_bit_under_x_flip
    (n_addr : Nat) (hn : 0 < n_addr)
    (addr_flip_idxs : List Nat)
    (h_flip_addr : ∀ x ∈ addr_flip_idxs,
                       ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (ctrl : Bool) (effective_addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_eff_addr : ∀ i, i < n_addr →
        Lookup.x_flip_post_state addr_flip_idxs f (ulookup_address_idx i)
          = effective_addr.testBit i)
    (h_clean : ∀ i, i < n_addr → f (ulookup_and_idx i) = false) :
    prefix_and_cascade_post_state n_addr
      (Lookup.x_flip_post_state addr_flip_idxs f)
      (ulookup_and_idx (n_addr - 1))
      = Lookup.address_and ctrl effective_addr n_addr := by
  -- Apply Iter 223 to the X-flipped state, verifying its preconditions.
  have h_ctrl_not_flip : ulookup_ctrl_idx ∉ addr_flip_idxs := by
    intro h_in
    obtain ⟨i, _, hpi⟩ := h_flip_addr _ h_in
    unfold ulookup_ctrl_idx ulookup_address_idx at hpi
    omega
  have h_andk_not_flip : ∀ k, k < n_addr → ulookup_and_idx k ∉ addr_flip_idxs := by
    intro k hk h_in
    obtain ⟨i, _, hpi⟩ := h_flip_addr _ h_in
    unfold ulookup_and_idx ulookup_address_idx at hpi
    omega
  apply prefix_and_cascade_top_bit_eq_address_and n_addr hn ctrl effective_addr
        (Lookup.x_flip_post_state addr_flip_idxs f)
  · -- ctrl carries through x_flip.
    rw [Lookup.x_flip_post_state_frame _ _ _ h_ctrl_not_flip]
    exact h_ctrl
  · -- address testBits at effective_addr by hypothesis.
    exact h_eff_addr
  · -- and bits are clean (x_flip frame at and positions).
    intro i hi
    rw [Lookup.x_flip_post_state_frame _ _ _ (h_andk_not_flip i hi)]
    exact h_clean i hi

/-! ## Decide-witnesses validating the bundled headline at small instances
    (Iter 243, 2026-05-14)

    Concrete instantiations of `Lookup.iteration_post_state` validating
    its post-state values against the bundled headline characterization.
    These are smoke tests — the parametric theorem `unary_lookup_iteration_correct`
    is already proven, but decide-witnesses on small (n_addr=3) instances
    confirm intuition + protect against statement-level bugs. -/


/-- **Multi-iteration post-state frame**: positions p with `1 + 2*n_addr ≤ p`
    and outside the UNION of every iter's `cnots` are preserved. By
    induction on the iter list, using `iteration_post_state_preserves_outside_word_targets`
    (Iter 235) at each step. -/
theorem Lookup.multi_iteration_post_state_preserves_outside_all_cnots
    (n_addr : Nat) (iters : List (List Nat × List Nat))
    (h_flip_addr_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (f : Nat → Bool) (p : Nat) (h_p_word : 1 + 2 * n_addr ≤ p)
    (h_not_in_any : ∀ flips cnots, (flips, cnots) ∈ iters → p ∉ cnots) :
    Lookup.multi_iteration_post_state n_addr iters f p = f p := by
  induction iters with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show Lookup.iteration_post_state n_addr flips cnots
            (Lookup.multi_iteration_post_state n_addr rest f) p = f p
    have h_flip_head : ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i :=
      h_flip_addr_all flips cnots List.mem_cons_self
    have h_not_in_head : p ∉ cnots :=
      h_not_in_any flips cnots List.mem_cons_self
    rw [Lookup.iteration_post_state_preserves_outside_word_targets n_addr
          flips cnots h_flip_head (Lookup.multi_iteration_post_state n_addr rest f)
          p h_p_word h_not_in_head]
    apply ih
    · intro flips' cnots' h_in_rest x h_in_flips
      exact h_flip_addr_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest) x h_in_flips
    · intro flips' cnots' h_in_rest
      exact h_not_in_any flips' cnots' (List.mem_cons_of_mem _ h_in_rest)


/-- **Effective address is bounded by 2^n_addr**. By induction on n_addr,
    using `Nat.bitwise_lt_two_pow` (`x, y < 2^n → bitwise f x y < 2^n`). -/
theorem Lookup.effective_addr_lt_two_pow
    (addr : Nat) (flips : List Nat) (n_addr : Nat) :
    Lookup.effective_addr addr flips n_addr < 2 ^ n_addr := by
  induction n_addr with
  | zero => exact (by decide : (0 : Nat) < 1)
  | succ k ih =>
    unfold Lookup.effective_addr
    split
    · -- if-branch: lower ||| 2^k < 2^(k+1).
      -- Both lower and 2^k are < 2^(k+1); bitwise OR stays bounded.
      have h_lower : Lookup.effective_addr addr flips k < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
      -- Refactored 2026-05-15 08:53: replaced `Nat.pow_lt_pow_right` (tier 4,
      -- depends on Classical.choice) with manual proof via Nat.two_pow_succ +
      -- Nat.lt_add_of_pos_left. This is the root-cause-chain tier reduction
      -- targeting `Lookup.unary_lookup_multi_iteration_correct` tier 4 → tier 3.
      have h_pow : 2 ^ k < 2 ^ (k + 1) := by
        rw [Nat.two_pow_succ]
        exact Nat.lt_add_of_pos_left (Nat.two_pow_pos k)
      exact Nat.bitwise_lt_two_pow h_lower h_pow
    · -- else-branch: lower stays. Need lower < 2^(k+1).
      exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))


/-- **testBit characterization of effective_addr** (Iter 254). For
    `i < n_addr`, the i-th bit of `effective_addr addr flips n_addr`
    equals the X-flipped i-th bit pattern.

    Direct induction on `n_addr` using `Nat.testBit_or`, `Nat.testBit_two_pow`,
    and `Nat.testBit_lt_two_pow` (via `effective_addr_lt_two_pow` from Iter 253). -/
theorem Lookup.effective_addr_testBit
    (addr : Nat) (flips : List Nat) (n_addr i : Nat) (hi : i < n_addr) :
    (Lookup.effective_addr addr flips n_addr).testBit i
      = xor (addr.testBit i) (decide (ulookup_address_idx i ∈ flips)) := by
  induction n_addr with
  | zero => omega
  | succ k ih =>
    unfold Lookup.effective_addr
    by_cases hik : i < k
    · -- i < k: testBit i comes from `lower` only.
      have h_two_pow_i_false : (2 ^ k).testBit i = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
      split
      · rw [Nat.testBit_or, h_two_pow_i_false, Bool.or_false]
        exact ih hik
      · exact ih hik
    · -- i = k (since i < k+1 and ¬ i < k).
      have hi_eq : i = k := by omega
      subst hi_eq
      have h_lower_bit : (Lookup.effective_addr addr flips i).testBit i = false :=
        Nat.testBit_lt_two_pow (Lookup.effective_addr_lt_two_pow addr flips i)
      have h_two_pow_i_true : (2 ^ i).testBit i = true := by
        rw [Nat.testBit_two_pow]; exact decide_eq_true rfl
      split
      · -- if-branch: condition (bit_i) is true.
        rename_i hbit
        rw [Nat.testBit_or, h_lower_bit, h_two_pow_i_true, Bool.false_or]
        exact hbit.symm
      · -- else-branch: condition (bit_i) is false.
        rename_i hbit
        rw [h_lower_bit]
        exact (Bool.not_eq_true _).mp hbit |>.symm


/-! ## Generic chaining lemma at the iteration level (Iter 251, 2026-05-14)

    Combines Iter 236 (iteration_post_state_at_word_target) with
    Iter 242 (cascade_top_bit_under_x_flip) to give a single chaining
    lemma: at a word target `p ∈ cnots`, the iteration post-state
    equals `xor (g p) (address_and ctrl effective_addr n_addr)`.

    The `effective_addr` is passed in (with its testBit characterization
    as a hypothesis `h_eff_addr`). This sidesteps the need for an
    explicit Nat.testBit-based bridge theorem from `Lookup.iter_triggers`,
    while still providing a clean statement for the multi-iter
    headline composition in Iter 252+. -/

/-- **Iteration at word target via address_and** (Iter 251). For
    `p ∈ cnots` and a user-supplied `effective_addr` matching the
    X-flipped address pattern, the post-state at p is
    `xor (g p) (address_and ctrl effective_addr n_addr)`. -/
theorem Lookup.iteration_post_state_at_word_target_via_address_and
    (n_addr : Nat) (hn : 0 < n_addr)
    (flips cnots : List Nat)
    (h_flip_addr : ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_cnots_nodup : cnots.Nodup)
    (h_word : Lookup.AllWordIdx n_addr cnots)
    (ctrl : Bool) (addr effective_addr : Nat) (g : Nat → Bool)
    (h_ctrl : g ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n_addr → g (ulookup_address_idx i) = addr.testBit i)
    (h_eff_addr : ∀ i, i < n_addr →
        Lookup.x_flip_post_state flips g (ulookup_address_idx i)
          = effective_addr.testBit i)
    (h_clean : ∀ i, i < n_addr → g (ulookup_and_idx i) = false)
    (p : Nat) (h_p_in : p ∈ cnots) :
    Lookup.iteration_post_state n_addr flips cnots g p
      = xor (g p) (Lookup.address_and ctrl effective_addr n_addr) := by
  -- Step 1: apply Iter 236 to extract the cascade-top-bit XOR.
  rw [Lookup.iteration_post_state_at_word_target n_addr hn flips cnots
        h_cnots_nodup h_word h_flip_addr g p h_p_in]
  -- Step 2: apply Iter 242 to unfold cascade-top to address_and.
  rw [Lookup.cascade_top_bit_under_x_flip n_addr hn flips h_flip_addr
        ctrl effective_addr g h_ctrl h_eff_addr h_clean]


/-! ## Multi-iter preservation lemmas (Iter 255, 2026-05-14)

    Lift per-iter preservation lemmas (Iter 232, 239) to the multi-iter
    level by induction on the iter list. These are the hypotheses the
    multi-iter chaining lemma (Iter 256) needs to invoke Iter 251
    at the head iter with the state `multi_iteration_post_state rest f`. -/

/-- **Multi-iter preserves ctrl** at every position. -/
theorem Lookup.multi_iteration_post_state_preserves_ctrl
    (n_addr : Nat) (iters : List (List Nat × List Nat))
    (h_flip_addr_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_word_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        Lookup.AllWordIdx n_addr cnots)
    (f : Nat → Bool) :
    Lookup.multi_iteration_post_state n_addr iters f ulookup_ctrl_idx
      = f ulookup_ctrl_idx := by
  induction iters with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show Lookup.iteration_post_state n_addr flips cnots
            (Lookup.multi_iteration_post_state n_addr rest f) ulookup_ctrl_idx
            = f ulookup_ctrl_idx
    have h_flip_head : ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i :=
      h_flip_addr_all flips cnots List.mem_cons_self
    have h_word_head : Lookup.AllWordIdx n_addr cnots :=
      h_word_all flips cnots List.mem_cons_self
    have h_ctrl_not_flip : ulookup_ctrl_idx ∉ flips := by
      intro h_in
      obtain ⟨i, _, hpi⟩ := h_flip_head _ h_in
      unfold ulookup_ctrl_idx ulookup_address_idx at hpi
      omega
    rw [Lookup.iteration_post_state_preserves_ctrl n_addr flips cnots
          h_ctrl_not_flip h_word_head _]
    apply ih
    · intro flips' cnots' h_in_rest x h_in_flips
      exact h_flip_addr_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest) x h_in_flips
    · intro flips' cnots' h_in_rest
      exact h_word_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)

/-- **Multi-iter preserves every address bit** for `i < n_addr`. -/
theorem Lookup.multi_iteration_post_state_preserves_address
    (n_addr : Nat) (iters : List (List Nat × List Nat))
    (h_flip_nodup_all : ∀ flips cnots, (flips, cnots) ∈ iters → flips.Nodup)
    (h_word_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        Lookup.AllWordIdx n_addr cnots)
    (f : Nat → Bool) (i : Nat) (hi : i < n_addr) :
    Lookup.multi_iteration_post_state n_addr iters f (ulookup_address_idx i)
      = f (ulookup_address_idx i) := by
  induction iters with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show Lookup.iteration_post_state n_addr flips cnots
            (Lookup.multi_iteration_post_state n_addr rest f) (ulookup_address_idx i)
            = f (ulookup_address_idx i)
    have h_flip_nodup_head : flips.Nodup :=
      h_flip_nodup_all flips cnots List.mem_cons_self
    have h_word_head : Lookup.AllWordIdx n_addr cnots :=
      h_word_all flips cnots List.mem_cons_self
    rw [Lookup.iteration_post_state_preserves_address n_addr flips cnots
          h_flip_nodup_head h_word_head _ i hi]
    apply ih
    · intro flips' cnots' h_in_rest
      exact h_flip_nodup_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)
    · intro flips' cnots' h_in_rest
      exact h_word_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)

/-- **X-flip post-state as XOR with membership** (utility): for `xs.Nodup`,
    `x_flip_post_state xs f j = xor (f j) (decide (j ∈ xs))`. Unifies the
    Iter 224 frame + Iter 225 value-at-element under a single expression. -/
theorem Lookup.x_flip_post_state_xor
    (xs : List Nat) (h_nodup : xs.Nodup) (f : Nat → Bool) (j : Nat) :
    Lookup.x_flip_post_state xs f j = xor (f j) (decide (j ∈ xs)) := by
  by_cases hj : j ∈ xs
  · rw [Lookup.x_flip_post_state_at xs h_nodup f j hj, decide_eq_true hj]
    cases f j <;> rfl
  · rw [Lookup.x_flip_post_state_frame xs f j hj, decide_eq_false hj]
    cases f j <;> rfl

/-- **Multi-iter preserves every and-bit** for `k < n_addr`. -/
theorem Lookup.multi_iteration_post_state_preserves_and
    (n_addr : Nat) (iters : List (List Nat × List Nat))
    (h_flip_addr_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_word_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        Lookup.AllWordIdx n_addr cnots)
    (f : Nat → Bool) (k : Nat) (hk : k < n_addr) :
    Lookup.multi_iteration_post_state n_addr iters f (ulookup_and_idx k)
      = f (ulookup_and_idx k) := by
  induction iters with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    show Lookup.iteration_post_state n_addr flips cnots
            (Lookup.multi_iteration_post_state n_addr rest f) (ulookup_and_idx k)
            = f (ulookup_and_idx k)
    have h_flip_head : ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i :=
      h_flip_addr_all flips cnots List.mem_cons_self
    have h_word_head : Lookup.AllWordIdx n_addr cnots :=
      h_word_all flips cnots List.mem_cons_self
    rw [Lookup.iteration_post_state_preserves_and n_addr flips cnots
          h_flip_head h_word_head _ k hk]
    apply ih
    · intro flips' cnots' h_in_rest x h_in_flips
      exact h_flip_addr_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest) x h_in_flips
    · intro flips' cnots' h_in_rest
      exact h_word_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)

/-! ## Multi-iter chaining lemma at word target (Iter 256, 2026-05-14)

    Combines Iter 251 (per-iter chaining) + Iter 254 (testBit bridge) +
    Iter 255 (multi-iter preservations) into a one-step chaining
    statement: at a word target in the HEAD iter's cnots, the multi-iter
    post-state equals the rest's post-state XOR'd with the head iter's
    trigger value. -/

/-- **Multi-iter chaining at word target**: at a word target `p` in the
    HEAD iter's `head_cnots`, the multi-iter post-state on `(head_flips,
    head_cnots) :: rest` equals the rest's post-state XOR'd with
    `Lookup.address_and ctrl (Lookup.effective_addr addr head_flips n_addr) n_addr`. -/
theorem Lookup.multi_iteration_post_state_at_word_target_in_head_iter
    (n_addr : Nat) (hn : 0 < n_addr)
    (head_flips head_cnots : List Nat)
    (rest : List (List Nat × List Nat))
    (h_head_flip_addr : ∀ x ∈ head_flips,
                            ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_head_flip_nodup : head_flips.Nodup)
    (h_head_cnots_nodup : head_cnots.Nodup)
    (h_head_word : Lookup.AllWordIdx n_addr head_cnots)
    (h_flip_addr_all : ∀ flips cnots, (flips, cnots) ∈ rest →
        ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_flip_nodup_all : ∀ flips cnots, (flips, cnots) ∈ rest → flips.Nodup)
    (h_word_all : ∀ flips cnots, (flips, cnots) ∈ rest →
        Lookup.AllWordIdx n_addr cnots)
    (ctrl : Bool) (addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n_addr → f (ulookup_address_idx i) = addr.testBit i)
    (h_clean : ∀ i, i < n_addr → f (ulookup_and_idx i) = false)
    (p : Nat) (h_p_in : p ∈ head_cnots) :
    Lookup.multi_iteration_post_state n_addr
      ((head_flips, head_cnots) :: rest) f p
      = xor (Lookup.multi_iteration_post_state n_addr rest f p)
            (Lookup.address_and ctrl
              (Lookup.effective_addr addr head_flips n_addr) n_addr) := by
  show Lookup.iteration_post_state n_addr head_flips head_cnots
          (Lookup.multi_iteration_post_state n_addr rest f) p
        = xor (Lookup.multi_iteration_post_state n_addr rest f p)
              (Lookup.address_and ctrl
                (Lookup.effective_addr addr head_flips n_addr) n_addr)
  -- Derive Iter 251's preconditions on g := multi_iteration_post_state rest f.
  set g := Lookup.multi_iteration_post_state n_addr rest f
  have h_ctrl_g : g ulookup_ctrl_idx = ctrl := by
    show Lookup.multi_iteration_post_state n_addr rest f ulookup_ctrl_idx = ctrl
    rw [Lookup.multi_iteration_post_state_preserves_ctrl n_addr rest
          h_flip_addr_all h_word_all f]
    exact h_ctrl
  have h_addr_g : ∀ i, i < n_addr →
      g (ulookup_address_idx i) = addr.testBit i := by
    intro i hi
    show Lookup.multi_iteration_post_state n_addr rest f (ulookup_address_idx i)
          = addr.testBit i
    rw [Lookup.multi_iteration_post_state_preserves_address n_addr rest
          h_flip_nodup_all h_word_all f i hi]
    exact h_addr i hi
  have h_clean_g : ∀ i, i < n_addr →
      g (ulookup_and_idx i) = false := by
    intro i hi
    show Lookup.multi_iteration_post_state n_addr rest f (ulookup_and_idx i)
          = false
    rw [Lookup.multi_iteration_post_state_preserves_and n_addr rest
          h_flip_addr_all h_word_all f i hi]
    exact h_clean i hi
  have h_eff_addr_g : ∀ i, i < n_addr →
      Lookup.x_flip_post_state head_flips g (ulookup_address_idx i)
        = (Lookup.effective_addr addr head_flips n_addr).testBit i := by
    intro i hi
    rw [Lookup.x_flip_post_state_xor head_flips h_head_flip_nodup g
          (ulookup_address_idx i)]
    rw [h_addr_g i hi]
    rw [Lookup.effective_addr_testBit addr head_flips n_addr i hi]
  exact Lookup.iteration_post_state_at_word_target_via_address_and
          n_addr hn head_flips head_cnots h_head_flip_addr
          h_head_cnots_nodup h_head_word
          ctrl addr (Lookup.effective_addr addr head_flips n_addr) g
          h_ctrl_g h_addr_g h_eff_addr_g h_clean_g p h_p_in

/-- **HEADLINE: multi-iteration unary lookup classical action**.
    For a word position `p` in some iter's cnots, the multi-iter
    post-state is `xor (f p) (cumulative_xor_value)`, where the
    cumulative value sums the trigger contributions from each iter
    whose cnots include `p`. -/
theorem Lookup.unary_lookup_multi_iteration_correct
    (n_addr : Nat) (hn : 0 < n_addr)
    (iters : List (List Nat × List Nat))
    (h_flip_addr_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i)
    (h_flip_nodup_all : ∀ flips cnots, (flips, cnots) ∈ iters → flips.Nodup)
    (h_cnots_nodup_all : ∀ flips cnots, (flips, cnots) ∈ iters → cnots.Nodup)
    (h_word_all : ∀ flips cnots, (flips, cnots) ∈ iters →
        Lookup.AllWordIdx n_addr cnots)
    (ctrl : Bool) (addr : Nat) (f : Nat → Bool)
    (h_ctrl : f ulookup_ctrl_idx = ctrl)
    (h_addr : ∀ i, i < n_addr → f (ulookup_address_idx i) = addr.testBit i)
    (h_clean : ∀ i, i < n_addr → f (ulookup_and_idx i) = false)
    (p : Nat) (h_p_word : 1 + 2 * n_addr ≤ p) :
    Lookup.multi_iteration_post_state n_addr iters f p
      = xor (f p) (Lookup.multi_iteration_xor_value_via_address_and
                     ctrl addr n_addr iters p) := by
  induction iters with
  | nil =>
    show f p = xor (f p) false
    cases f p <;> rfl
  | cons head rest ih =>
    obtain ⟨flips, cnots⟩ := head
    have h_flip_head : ∀ x ∈ flips, ∃ i, i < n_addr ∧ x = ulookup_address_idx i :=
      h_flip_addr_all flips cnots List.mem_cons_self
    have h_flip_nodup_head : flips.Nodup :=
      h_flip_nodup_all flips cnots List.mem_cons_self
    have h_cnots_nodup_head : cnots.Nodup :=
      h_cnots_nodup_all flips cnots List.mem_cons_self
    have h_word_head : Lookup.AllWordIdx n_addr cnots :=
      h_word_all flips cnots List.mem_cons_self
    have h_flip_addr_rest : ∀ flips' cnots', (flips', cnots') ∈ rest →
        ∀ x ∈ flips', ∃ i, i < n_addr ∧ x = ulookup_address_idx i :=
      fun flips' cnots' h_in_rest =>
        h_flip_addr_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)
    have h_flip_nodup_rest : ∀ flips' cnots', (flips', cnots') ∈ rest →
        flips'.Nodup :=
      fun flips' cnots' h_in_rest =>
        h_flip_nodup_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)
    have h_cnots_nodup_rest : ∀ flips' cnots', (flips', cnots') ∈ rest →
        cnots'.Nodup :=
      fun flips' cnots' h_in_rest =>
        h_cnots_nodup_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)
    have h_word_rest : ∀ flips' cnots', (flips', cnots') ∈ rest →
        Lookup.AllWordIdx n_addr cnots' :=
      fun flips' cnots' h_in_rest =>
        h_word_all flips' cnots' (List.mem_cons_of_mem _ h_in_rest)
    have h_ih := ih h_flip_addr_rest h_flip_nodup_rest h_cnots_nodup_rest
                 h_word_rest
    -- Unfold multi_iteration_xor_value_via_address_and on the cons-cell.
    show Lookup.multi_iteration_post_state n_addr ((flips, cnots) :: rest) f p
        = xor (f p)
            (xor (decide (p ∈ cnots) &&
                  Lookup.address_and ctrl
                    (Lookup.effective_addr addr flips n_addr) n_addr)
                 (Lookup.multi_iteration_xor_value_via_address_and ctrl addr
                    n_addr rest p))
    by_cases h_p_in : p ∈ cnots
    · -- p ∈ head_cnots: apply Iter 256, then IH, then Bool case analysis.
      rw [Lookup.multi_iteration_post_state_at_word_target_in_head_iter n_addr hn
            flips cnots rest h_flip_head h_flip_nodup_head h_cnots_nodup_head
            h_word_head h_flip_addr_rest h_flip_nodup_rest h_word_rest
            ctrl addr f h_ctrl h_addr h_clean p h_p_in]
      rw [h_ih]
      rw [decide_eq_true h_p_in, Bool.true_and]
      cases f p <;>
        cases (Lookup.multi_iteration_xor_value_via_address_and
                 ctrl addr n_addr rest p) <;>
        cases (Lookup.address_and ctrl
                 (Lookup.effective_addr addr flips n_addr) n_addr) <;> rfl
    · -- p ∉ head_cnots: head iter is frame-preserved at p; apply IH.
      show Lookup.iteration_post_state n_addr flips cnots
              (Lookup.multi_iteration_post_state n_addr rest f) p
            = _
      rw [Lookup.iteration_post_state_preserves_outside_word_targets n_addr
            flips cnots h_flip_head
            (Lookup.multi_iteration_post_state n_addr rest f)
            p h_p_word h_p_in]
      rw [h_ih]
      rw [decide_eq_false h_p_in, Bool.false_and, Bool.false_xor]

/-! ## RSA-2048-scale instantiation decide-witnesses (Iter 262, 2026-05-14)

    With all 3 BQ-Algo review pillars Verified (Iter 213 adder, Iter 241
    single-iter lookup, Iter 257 multi-iter lookup), the parametric
    T-count theorems can now be instantiated at the concrete RSA-2048
    parameters (q_A=33 for the adder, q_a=6 for the lookup) to give
    verified-correctness cost claims that map directly to qianxu p. 22-23.

    These are not just symbolic count theorems on un-verified
    constructions; they are concrete numerical claims under the
    semantic-correctness theorems already proven. -/

/-- **RSA-2048 lookup single-iteration T-count = 84** (Iter 262).
    For q_a = 6 (qianxu p. 22 max table-row size for RSA-2048),
    `tcount (unary_lookup_iteration 6 _ _) = 14·6 = 84`. -/
example (addr_flip_idxs word_cnot_idxs : List Nat) :
    tcount (unary_lookup_iteration 6 addr_flip_idxs word_cnot_idxs) = 84 :=
  tcount_unary_lookup_iteration 6 addr_flip_idxs word_cnot_idxs

/-- **RSA-2048 lookup multi-iteration T-count = 5376** (Iter 262)
    for the full 2^6 = 64 iterations covering all addresses.
    This is the **no-measurement, no-Gray-code upper bound**;
    qianxu's optimized claim of 2^q_a Toffolis = 56 T requires
    BOTH the Gidney measurement trick (factor 2) AND Gray-code
    amortization (factor q_a = 6). See Iter 28 review finding for the
    factor-of-12 = 5376/448 ≈ 12 gap analysis. -/
example :
    tcount (unary_lookup_multi_iteration 6
              (List.replicate 64 ([], []))) = 5376 := by
  rw [tcount_unary_lookup_multi_iteration, List.length_replicate]

/-- **RSA-2048 lookup multi-iteration symbolic form** (Iter 262):
    parametric `14 · n_addr · |iters|` instantiated at (6, 64). -/
example :
    tcount (unary_lookup_multi_iteration 6
              (List.replicate 64 ([], [])))
    = 14 * 6 * (List.replicate 64 (([] : List Nat), ([] : List Nat))).length := by
  rw [tcount_unary_lookup_multi_iteration]

/-- **Bridge: verified single-iter T-count matches the RSA-2048
    paper-claim anchor** (Iter 263). -/
example (addr_flip_idxs word_cnot_idxs : List Nat) :
    tcount (unary_lookup_iteration
              qianxu_E9_q_a_RSA2048
              addr_flip_idxs word_cnot_idxs)
      = unary_lookup_iteration_RSA2048_T_count_verified := by
  unfold unary_lookup_iteration_RSA2048_T_count_verified
  exact tcount_unary_lookup_iteration
    qianxu_E9_q_a_RSA2048 addr_flip_idxs word_cnot_idxs

/-- **Bridge: verified multi-iter T-count matches the RSA-2048
    no-measurement paper-claim anchor** (Iter 263). -/
example :
    tcount (unary_lookup_multi_iteration
              qianxu_E9_q_a_RSA2048
              (List.replicate (2 ^ qianxu_E9_q_a_RSA2048)
                ([], [])))
      = unary_lookup_multi_RSA2048_no_meas_T_count_verified := by
  unfold unary_lookup_multi_RSA2048_no_meas_T_count_verified
        qianxu_E9_q_a_RSA2048
  rw [tcount_unary_lookup_multi_iteration, List.length_replicate]

end FormalRV.BQAlgo
