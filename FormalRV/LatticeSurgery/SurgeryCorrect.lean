/-
  FormalRV.LatticeSurgery.SurgeryCorrect — operational correctness of a
  qLDPC code-surgery gadget: it implements the logical Pauli measurement
  of its target operator.  This completes Step 2 of the LDPC-PPM plan
  beyond the operator-support readout of `SurgeryReadout`.

  Two operational obligations, grounded verbatim in qianxu App. C
  (`~/Downloads/qianxuLatex/main.tex`):

  * **(R) Eigenvalue extraction** (`main.tex:544`): "the outcomes of the
    target logical operators ℒ [are] extracted from the parities of the
    merged-code X-checks in the first stabilizer measurement cycle."
    Formalized as `surgery_eigenvalue`: the product of the
    `span_witness`-selected SIGNED merged X-checks equals the target
    logical operator, signed by the XOR-parity of those checks' outcomes.

  * **(N) Non-disturbance** (`main.tex:544`): the data logical operators
    that commute with ℒ are preserved ("the k−t logical Z̄ operators of
    the data code that commute with ℒ").  Formalized as
    `surgery_preserves_commuting_logical`: any operator commuting with all
    merged X-checks survives the merge measurement (folded `apply_PPM`).

  The fault-tolerance triple (`main.tex:435` (i) merged distance Θ(d),
  (ii) merged qLDPC, (iii) τ_s = Θ(d)) is the delimited residue:
  (ii)/(iii) are decidable in `LDPCSurgery.verify_surgery_gadget`; the
  merged distance (i) is the single Cheeger-backed external axiom.

  No Mathlib.  Pure Bool / Nat / List + the PauliString algebra.
-/

import FormalRV.LatticeSurgery.SurgeryReadout

namespace FormalRV.Framework.SurgeryCorrect

open FormalRV.Framework.PauliSem
open FormalRV.Framework.PPMUpdate
open FormalRV.Framework.PPMOp
open FormalRV.Framework.LDPC
open FormalRV.Framework.SurgeryReadout

/-! ## Signed X-row: a measured merged X-check carrying its ±1 outcome -/

/-- An X-type check / logical lowered to a `PauliString`, with phase
    encoding a measurement outcome (`s = true` ↦ `−1` ↦ `Phase.minus`). -/
def signedXRow (s : Bool) (l : BoolVec) : PauliString :=
  ⟨if s then Phase.minus else Phase.plus, l.map xBit⟩

@[simp] theorem signedXRow_ops (s : Bool) (l : BoolVec) :
    (signedXRow s l).ops = l.map xBit := rfl

@[simp] theorem signedXRow_phase (s : Bool) (l : BoolVec) :
    (signedXRow s l).phase = (if s then Phase.minus else Phase.plus) := rfl

/-- An unsigned `xRow` is the `s = false` signed row. -/
theorem xRow_eq_signedXRow_false (l : BoolVec) : xRow l = signedXRow false l := rfl

/-! ## Single-qubit X/I products carry trivial phase

    `X·X = +I`, `X·I = +X`, `I·X = +X`, `I·I = +I`: the phase is always
    `+`.  This is why the *only* sign in a product of X/I strings comes
    from the strings' own phases (the measurement outcomes). -/

theorem pmul_xBit_phase (a b : Bool) :
    (Pauli.mul (xBit a) (xBit b)).1 = Phase.plus := by
  cases a <;> cases b <;> rfl

/-! ## Phase-component of the product fold

    Companion to `PPMUpdate.foldl_mul_snd` (which tracks the `.ops`
    accumulator): this tracks the `.1` (phase) accumulator of the same
    fold, collapsing it to a single `foldl` over phases.  Mirrors the
    proof of `foldl_mul_snd` verbatim. -/
theorem foldl_mul_fst (l : List (Pauli × Pauli)) (ph0 : Phase) (acc0 : List Pauli) :
    (l.foldl
      (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
        let (a, b) := ab
        let (ph, c) := Pauli.mul a b
        (acc.1.mul ph, acc.2 ++ [c])) (ph0, acc0)).1
    = l.foldl (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) ph0 := by
  induction l generalizing ph0 acc0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.foldl_cons]
    rw [ih]

/-- If every zipped pair multiplies to phase `+`, the phase fold is the
    identity on its seed.  This is the engine that proves the *only*
    sign in a product of X/I strings comes from the strings' own
    phases (their measurement outcomes). -/
theorem foldl_phase_plus (l : List (Pauli × Pauli)) (ph0 : Phase)
    (hall : ∀ ab ∈ l, (Pauli.mul ab.1 ab.2).1 = Phase.plus) :
    l.foldl (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) ph0 = ph0 := by
  induction l generalizing ph0 with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [hall hd List.mem_cons_self]
    have hp : ph0.mul Phase.plus = ph0 := Phase.mul_plus ph0
    rw [hp]
    exact ih ph0 (fun ab hab => hall ab (List.mem_cons_of_mem _ hab))

/-! ## Multiplication of signed X-rows: outcomes XOR, supports XOR -/

/-- The phase fold over a zip of `xBit`-lowered lists is trivial, since
    every X/I single-qubit product carries phase `+` (`pmul_xBit_phase`). -/
theorem foldl_phase_plus_xBit (a b : BoolVec) :
    ((a.map xBit).zip (b.map xBit)).foldl
        (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) Phase.plus
      = Phase.plus := by
  apply foldl_phase_plus
  intro ab hab
  -- `ab` is a zipped pair of `xBit`-images, so each component is `xBit _`.
  have ha : ab.1 ∈ a.map xBit := List.of_mem_zip hab |>.1
  have hb : ab.2 ∈ b.map xBit := List.of_mem_zip hab |>.2
  obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
  rw [← hx, ← hy]
  exact pmul_xBit_phase x y

/-- The `.ops` of a product of two signed X-rows is the support-XOR row,
    identical to the unsigned `xRow` case (phase lives only in `.phase`). -/
theorem signedXRow_mul_ops (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    ((signedXRow sa a).mul (signedXRow sb b)).ops = (xRow (vec_xor a b)).ops := by
  rw [mul_ops]
  simp only [signedXRow_ops, xRow_ops]
  exact zipmap_pmul_xBit a b h

/-- The `.phase` of a product of two signed X-rows is the XOR of the two
    outcome signs: `(-1)^sa · (-1)^sb = (-1)^(sa⊕sb)`.  All single-qubit
    X/I products are phase-trivial, so no extra sign is produced. -/
theorem signedXRow_mul_phase (sa sb : Bool) (a b : BoolVec) :
    ((signedXRow sa a).mul (signedXRow sb b)).phase
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
  show ((signedXRow sa a).phase.mul (signedXRow sb b).phase).mul
        (((signedXRow sa a).ops.zip (signedXRow sb b).ops).foldl
          (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
            let (x, y) := ab
            let (ph, c) := Pauli.mul x y
            (acc.1.mul ph, acc.2 ++ [c]))
          (Phase.plus, ([] : List Pauli))).1
      = (if (sa != sb) then Phase.minus else Phase.plus)
  rw [foldl_mul_fst]
  simp only [signedXRow_ops, signedXRow_phase]
  rw [foldl_phase_plus_xBit a b]
  have hp : ((if sa then Phase.minus else Phase.plus).mul
        (if sb then Phase.minus else Phase.plus)).mul Phase.plus
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
    cases sa <;> cases sb <;> rfl
  exact hp

/-- **Signed multiplication law.**  Multiplying two signed X-rows XORs
    both their outcome signs and their supports.  This is the algebra
    that lets a product of measured merged X-checks carry the XOR-parity
    of their individual ±1 outcomes. -/
theorem signedXRow_mul (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    (signedXRow sa a).mul (signedXRow sb b) = signedXRow (sa != sb) (vec_xor a b) := by
  have hops : ((signedXRow sa a).mul (signedXRow sb b)).ops
      = (signedXRow (sa != sb) (vec_xor a b)).ops := by
    rw [signedXRow_mul_ops sa sb a b h, signedXRow_ops, xRow_ops]
  have hphase : ((signedXRow sa a).mul (signedXRow sb b)).phase
      = (signedXRow (sa != sb) (vec_xor a b)).phase := by
    rw [signedXRow_mul_phase sa sb a b, signedXRow_phase]
  -- Reconstruct the structure equality from the two field equalities.
  cases hps : (signedXRow sa a).mul (signedXRow sb b) with
  | mk ph ops =>
    cases hrhs : signedXRow (sa != sb) (vec_xor a b) with
    | mk ph' ops' =>
      rw [hps, hrhs] at hphase hops
      simp only at hphase hops
      rw [hphase, hops]

/-! ## Selected signed product mirroring `row_combination` -/

/-- The XOR-parity of the outcome signs `ss` over exactly the rows
    selected by `sel`, mirroring the recursion of `row_combination`. -/
def selectedParity : BoolVec → List Bool → Bool
  | [],          _       => false
  | _,           []      => false
  | false :: ts, _ :: ss => selectedParity ts ss
  | true :: ts,  s :: ss => s != selectedParity ts ss

/-- The signed Pauli-string product of the merged X-checks selected by
    `sel`, with each selected check carrying its measurement-outcome sign
    from `ss`.  Mirrors `selectedXProduct`/`row_combination` (including
    the empty-accumulator special case) so all three stay in lockstep. -/
def selectedSignedProduct : BoolVec → BoolMat → List Bool → PauliString
  | [],          _,         _       => xRow []
  | _,           [],        _       => xRow []
  | _,           _,         []      => xRow []
  | false :: ts, _ :: tm,   _ :: ss => selectedSignedProduct ts tm ss
  | true :: ts,  row :: tm, s :: ss =>
      let acc := selectedSignedProduct ts tm ss
      match acc.ops with
      | []       => signedXRow s row
      | _        => (signedXRow s row).mul acc

/-! ## Lockstep: the signed product mirrors `row_combination` -/

/-- **Operator-support lockstep for the signed product.**  The `.ops` of
    `selectedSignedProduct` is the lowering of the GF(2) `row_combination`
    of the same selection — identical to `selectedXProduct_ops`, since the
    signs live only in `.phase`.  Proved by induction mirroring the shared
    recursion, using `signedXRow_mul_ops` in the key case. -/
theorem selectedSignedProduct_ops (n : Nat) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      (selectedSignedProduct sel mat ss).ops = (xRow (row_combination sel mat)).ops := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedProduct, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          simp only [selectedSignedProduct, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at ihe
            have hacc : (selectedSignedProduct ts tm ss).ops = [] := by
              rw [ihe]; rfl
            rw [hacc]
            rfl
          | cons c cs =>
            rw [hrc] at ihe
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            -- The accumulator's `.ops` is `(c::cs).map xBit`, hence nonempty.
            have hacc : (selectedSignedProduct ts tm ss).ops = (c :: cs).map xBit := by
              rw [ihe]; rfl
            rw [hacc]
            show ((signedXRow sgn row).mul (selectedSignedProduct ts tm ss)).ops
                = (xRow (vec_xor row (c :: cs))).ops
            rw [mul_ops, signedXRow_ops, hacc]
            show ((xRow row).ops.zip (xRow (c :: cs)).ops).map (fun ab => pmul2 ab.1 ab.2)
                = (xRow (vec_xor row (c :: cs))).ops
            rw [← mul_ops]
            exact xRow_vec_xor_ops row (c :: cs) hlen

/-- When the rows have positive width `n`, an empty GF(2) `row_combination`
    forces the selected outcome-parity to be `false`: no `true` is selected
    (a selected positive-width row would make the combination nonempty), so
    `selectedParity` XORs over the empty selected set.  This is the
    invariant that justifies the empty-accumulator branch of
    `selectedSignedProduct` discarding the accumulator's (necessarily `+`)
    sign. -/
theorem parity_false_of_combo_nil (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length → row_combination sel mat = [] →
      selectedParity sel ss = false := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen hcombo
    cases mat with
    | nil =>
      cases ss with
      | nil => rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedParity]
          simp only [row_combination] at hcombo
          exact ih tm ss htm hslen' hcombo
        | true =>
          exfalso
          -- A `true` selection of a width-`n` row cannot yield an empty combo.
          have hrow : row.length = n := hmat row List.mem_cons_self
          simp only [row_combination] at hcombo
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at hcombo
            simp only at hcombo
            rw [hcombo] at hrow
            simp at hrow
            omega
          | cons c cs =>
            rw [hrc] at hcombo
            simp only at hcombo
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hvx : (vec_xor row (c :: cs)).length = n := by
              rw [vec_xor_length, hrow, hcs]; omega
            rw [hcombo] at hvx
            simp at hvx
            omega

/-- **Full lockstep theorem (sign-aware).**  The signed product of the
    `sel`-selected merged X-checks equals the lowering of the GF(2)
    `row_combination` of the same selection, signed by the XOR-parity of
    the selected outcome bits.  This refines `selectedXProduct_ops` from
    the operator-support level to the full `PauliString` (phase included).
    Proved by induction mirroring the shared recursion; the key
    `true :: ts` case uses `signedXRow_mul` to combine, and
    `selectedSignedProduct_ops` to detect the empty-accumulator branch
    (whose parity is pinned to `false` by `parity_false_of_combo_nil`). -/
theorem selectedSignedProduct_eq (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      selectedSignedProduct sel mat ss
        = signedXRow (selectedParity sel ss) (row_combination sel mat) := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedProduct, selectedParity, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          have ihops := selectedSignedProduct_ops n ts tm ss htm hslen'
          simp only [selectedSignedProduct, selectedParity, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            -- Accumulator support empty ⇒ `signedXRow sgn row` branch.
            rw [hrc] at ihops
            have hacc : (selectedSignedProduct ts tm ss).ops = [] := by
              rw [ihops]; rfl
            rw [hacc]
            -- Parity of the tail selection is `false` (no `true` selected).
            have hpar : selectedParity ts ss = false :=
              parity_false_of_combo_nil n hn ts tm ss htm hslen' hrc
            rw [hpar, Bool.bne_false]
          | cons c cs =>
            -- Accumulator support nonempty ⇒ `(signedXRow sgn row).mul acc`.
            rw [hrc] at ihops ihe
            have hacc : (selectedSignedProduct ts tm ss).ops = (c :: cs).map xBit := by
              rw [ihops]; rfl
            rw [hacc]
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            -- Replace the accumulator by its IH normal form, then combine.
            show (signedXRow sgn row).mul (selectedSignedProduct ts tm ss)
                = signedXRow (sgn != selectedParity ts ss) (vec_xor row (c :: cs))
            rw [ihe, signedXRow_mul sgn (selectedParity ts ss) row (c :: cs) hlen]

/-! ## The eigenvalue-extraction statement -/

/-- **Surgery eigenvalue extraction (qianxu App. C, `main.tex:544`).**
    If the merged X-check matrix is rectangular (all rows of positive
    width `n`), the outcome-sign list is aligned with it, and the gadget
    passes its decidable kernel condition `targets_logical_correctly`
    (qianxu's `⟨ℒ⟩ = f_X'^T ker(H_X'^T)`), then the signed product of the
    `span_witness`-selected merged X-checks equals the target logical
    operator `P̄`, signed by the XOR-parity of those checks' measurement
    outcomes.  This is "the outcome of P̄ = parity of the merged X-checks
    in cycle 1": the operator support is fixed (`surgery_readout_operator`)
    and the phase carries the XOR of the individual ±1 outcomes. -/
theorem surgery_eigenvalue (g : SurgeryGadget) (n : Nat) (hn : 0 < n) (signs : List Bool)
    (hshape : ∀ r ∈ g.merged_hx, r.length = n) (hsig : signs.length = g.merged_hx.length)
    (hker : g.targets_logical_correctly = true) :
    selectedSignedProduct g.span_witness g.merged_hx signs
      = signedXRow (selectedParity g.span_witness signs) g.target_pauli := by
  have hcombo : row_combination g.span_witness g.merged_hx = g.target_pauli :=
    of_decide_eq_true (by simpa [SurgeryGadget.targets_logical_correctly] using hker)
  rw [selectedSignedProduct_eq n hn g.span_witness g.merged_hx signs hshape hsig, hcombo]

/-! ## The non-disturbance statement (qianxu App. C, `main.tex:544`)

    The companion to `surgery_eigenvalue`.  Where the eigenvalue half (R)
    extracts the target operator from the merged X-checks' parities, the
    non-disturbance half (N) certifies that a data logical operator which
    *commutes* with the measured merged X-checks SURVIVES the merge
    measurement: "the k−t logical Z̄ operators of the data code that
    commute with ℒ" are preserved.

    The argument is purely algebraic: every merged X-check is an X/I
    string, so the measured set commutes pairwise (`merged_X_checks_commute`);
    and any operator `L` that commutes with each measured check `P` is
    preserved generator-by-generator under the Gottesman `+`-branch
    update `apply_PPM_pos` (`apply_PPM_pos_preserves_mem_of_commutes`),
    hence under the whole folded merge (`mem_measureChecks_of_commutesAll`). -/

/-- Single-qubit X/I operators always commute: `X/X`, `X/I`, `I/X`, `I/I`
    are all commuting pairs.  This is why any two X-rows commute. -/
theorem xBit_commutes (x y : Bool) : Pauli.commutes (xBit x) (xBit y) = true := by
  cases x <;> cases y <;> rfl

/-- **Any two X/I strings commute.**  No position of `(xRow a).ops.zip
    (xRow b).ops` anticommutes (every entry is a pair of `xBit`-images,
    commuting by `xBit_commutes`), so the anticommuting-position count is
    `0`, which is even.  This is the algebraic basis for the measured
    merged X-check family being simultaneously measurable. -/
theorem xRow_commutes (a b : BoolVec) : (xRow a).commutes (xRow b) = true := by
  unfold PauliString.commutes
  simp only [xRow_ops]
  rw [Nat.beq_eq_true_eq]
  have hzero : ((a.map xBit).zip (b.map xBit)).countP
      (fun p => ! (Pauli.commutes p.1 p.2)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    have h1 : p.1 ∈ a.map xBit := List.of_mem_zip hp |>.1
    have h2 : p.2 ∈ b.map xBit := List.of_mem_zip hp |>.2
    obtain ⟨x, _, hx⟩ := List.mem_map.mp h1
    obtain ⟨y, _, hy⟩ := List.mem_map.mp h2
    rw [← hx, ← hy, xBit_commutes]
    decide
  rw [hzero]

/-- **The measured merged X-check family commutes pairwise.**  Each
    element of `merged_stabilizers_X g = g.merged_hx.map xRow` is an
    `xRow _`, so any two commute by `xRow_commutes`.  This certifies the
    set is a valid simultaneously-measurable commuting family — the
    precondition for the surgery merge to be a well-defined PPM step. -/
theorem merged_X_checks_commute (g : SurgeryGadget) :
    ∀ p ∈ merged_stabilizers_X g, ∀ q ∈ merged_stabilizers_X g, p.commutes q = true := by
  intro p hp q hq
  unfold merged_stabilizers_X at hp hq
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hp
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hq
  rw [← ha, ← hb]
  exact xRow_commutes a b

/-- **Core membership preservation under one Gottesman `+`-update.**  If
    `L` is in the stabilizer group `s` and commutes with the measured
    operator `P`, then `L` is still in `apply_PPM_pos s P`.

    The Gottesman map replaces the first anticommuting generator by `P`,
    multiplies the other anticommuting generators by it, and leaves the
    commuting generators (including `L`) untouched.  Concretely: take the
    index `j` with `s[j]? = some L`; the only branch that would alter `L`
    is `j = i_anti`, but that would force `L = g_anti`, where `g_anti`
    *anticommutes* with `P` (from the `find_anticommuting` witness),
    contradicting `L.commutes P = true`.  Hence `j ≠ i_anti` and the map
    sends `(L, j)` to `L`. -/
theorem apply_PPM_pos_preserves_mem_of_commutes
    (s : StabilizerState) (P L : PauliString) (hmem : L ∈ s) (hcomm : L.commutes P = true) :
    L ∈ apply_PPM_pos s P := by
  unfold apply_PPM_pos
  cases hf : find_anticommuting s P with
  | none => exact hmem
  | some i_anti =>
    dsimp only [hf]
    cases hg : s[i_anti]? with
    | none => exact hmem
    | some g_anti =>
      dsimp only [hg]
      -- Extract an index `j` with `s[j]? = some L` from membership.
      obtain ⟨j, hjlt, hjeq⟩ := List.getElem_of_mem hmem
      have hjget : s[j]? = some L := by rw [List.getElem?_eq_getElem hjlt, hjeq]
      -- The selected generator `g_anti` anticommutes with `P`.
      unfold find_anticommuting at hf
      have hpred := List.findIdx?_eq_some_iff_getElem.mp hf
      obtain ⟨hlt, hp_anti, _⟩ := hpred
      have hidx : s[i_anti] = g_anti := by
        have := List.getElem?_eq_getElem hlt; rw [hg] at this
        exact (Option.some.injEq _ _ ▸ this).symm
      rw [hidx] at hp_anti
      have hgaP : g_anti.commutes P = false := by
        cases hc : g_anti.commutes P with
        | false => rfl
        | true => simp [hc] at hp_anti
      -- `j ≠ i_anti`: else `L = g_anti`, contradicting `L.commutes P = true`.
      have hjne : j ≠ i_anti := by
        intro heq
        rw [heq] at hjget
        rw [hg] at hjget
        have hLga : L = g_anti := (Option.some.injEq _ _).mp hjget.symm
        rw [hLga, hgaP] at hcomm
        exact absurd hcomm (by decide)
      -- `L` survives: the `(L, j)` entry of the `zipIdx.map` is `L`.
      rw [List.mem_map]
      refine ⟨(L, j), ?_, ?_⟩
      · rw [List.mk_mem_zipIdx_iff_getElem?]; exact hjget
      · simp only [hjne, decide_false, if_false, Bool.false_eq_true]
        rw [if_pos hcomm]

/-- The merge measurement as a left fold of `apply_PPM_pos` over the
    measured merged X-checks (the first stabilizer cycle of the merge). -/
def measureChecks (checks : List PauliString) (s : StabilizerState) : StabilizerState :=
  checks.foldl (fun st P => apply_PPM_pos st P) s

/-- **Fold preservation.**  An operator `L` in `s` that commutes with
    *every* check in `checks` is preserved through the whole folded merge
    `measureChecks checks s`.  Proved by induction on `checks`
    (generalizing `s`), threading `apply_PPM_pos_preserves_mem_of_commutes`
    through each step. -/
theorem mem_measureChecks_of_commutesAll (checks : List PauliString) (L : PauliString)
    (s : StabilizerState) (hmem : L ∈ s) (hcomm : ∀ P ∈ checks, L.commutes P = true) :
    L ∈ measureChecks checks s := by
  induction checks generalizing s with
  | nil => exact hmem
  | cons P rest ih =>
    unfold measureChecks
    simp only [List.foldl_cons]
    have hP : L.commutes P = true := hcomm P List.mem_cons_self
    have hmem' : L ∈ apply_PPM_pos s P :=
      apply_PPM_pos_preserves_mem_of_commutes s P L hmem hP
    have hrest : ∀ Q ∈ rest, L.commutes Q = true :=
      fun Q hQ => hcomm Q (List.mem_cons_of_mem _ hQ)
    exact ih (apply_PPM_pos s P) hmem' hrest

/-- **Surgery non-disturbance (qianxu App. C, `main.tex:544`).**  This is
    the (N) half of qLDPC code-surgery correctness: any logical operator
    `L ∈ s` that commutes with all the measured merged X-checks
    (`merged_stabilizers_X g`) survives the merge measurement — it remains
    in the post-merge stabilizer group `measureChecks (merged_stabilizers_X g) s`.

    This is qianxu's "the k−t logical Z̄ operators of the data code that
    commute with ℒ" are preserved.  Combined with `surgery_eigenvalue`
    (the R half: the readout extracts P̄ signed by the checks' XOR-parity)
    and `merged_X_checks_commute` (the measured set is a valid
    simultaneously-measurable commuting family), this gives the full
    (R ∧ N) logical correctness of the surgery gadget. -/
theorem surgery_preserves_commuting_logical (g : SurgeryGadget) (L : PauliString)
    (s : StabilizerState) (hmem : L ∈ s)
    (hcomm : ∀ P ∈ merged_stabilizers_X g, L.commutes P = true) :
    L ∈ measureChecks (merged_stabilizers_X g) s :=
  mem_measureChecks_of_commutesAll (merged_stabilizers_X g) L s hmem hcomm

/-! ## Fault-tolerance residue (delimited) -/

/-- The structural fault-tolerance conditions of qianxu App. C
    (`main.tex:435`).  Of the triple, (ii) the merged code is qLDPC and
    (iii) `τ_s = Θ(d)` are DECIDABLE and discharged by
    `verify_surgery_gadget`; (i) the merged-code distance `d̃ = Θ(d)` is the
    DELIMITED residue, recorded here as the explicit input `merged_dist` with
    the bound `merged_dist ≥ g.data_code.d`.  Its value comes from the boundary
    Cheeger-constant lower bound for graph ancillas (Swaroop et al.) or a
    QDistRnd numerical search (per the paper) — it is the single external,
    non-derived quantity, made structurally visible here rather than baked into
    a blanket axiom.

    Crucially, the LOGICAL-correctness theorem
    `surgery_implements_logical_measurement` below does NOT depend on this:
    distance governs error SUPPRESSION (fault tolerance under a noise model),
    not the noiseless logical action.  Error suppression and decoder runtime are
    out of scope per the project taxonomy. -/
def SurgeryFaultTolerant (g : SurgeryGadget) (merged_dist : Nat) : Prop :=
  g.verify_surgery_gadget = true ∧ merged_dist ≥ g.data_code.d

/-! ## Top-level logical correctness (R ∧ N), axiom-free -/

/-- **A structurally-verified qLDPC code-surgery gadget implements the logical
    Pauli measurement of its target operator.**  Given the decidable structural
    verifier (`verify_surgery_gadget` = dimensions + qLDPC + τ_s + the kernel
    condition `⟨ℒ⟩ = f_X'ᵀ ker(H_X'ᵀ)`) and well-shaped merged checks of
    positive width, the gadget satisfies BOTH halves of surgery correctness:

    * **(R) readout / eigenvalue** — the product of the `span_witness`-selected
      signed merged X-checks equals the target logical operator signed by the
      XOR-parity of those checks' ±1 outcomes (qianxu `main.tex:544`: the
      outcome of `P̄` is the parity of the merged X-checks in the first cycle);
    * **(N) non-disturbance** — every logical commuting with the measured set
      survives the merge measurement; and
    * the measured set is a valid simultaneously-measurable commuting family.

    Proved CODE-GENERALLY (any data code) and AXIOM-FREE (only Lean's
    `propext`/`Classical.choice`/`Quot.sound`; no project axioms, no `sorry`).
    This is exactly the obligation the sibling QMeas language axiomatizes per
    code tag (`transversal_X_is_logical_X`); here it is discharged for the
    qLDPC merged-code construction.  Fault tolerance (the merged-distance
    residue) is delimited separately in `SurgeryFaultTolerant`. -/
theorem surgery_implements_logical_measurement
    (g : SurgeryGadget) (n : Nat) (signs : List Bool)
    (hn : 0 < n) (hshape : ∀ r ∈ g.merged_hx, r.length = n)
    (hsig : signs.length = g.merged_hx.length)
    (hverify : g.verify_surgery_gadget = true) :
    -- (R) the measured eigenvalue of the target logical = parity of the
    -- selected merged-X-check outcomes
    (selectedSignedProduct g.span_witness g.merged_hx signs
        = signedXRow (selectedParity g.span_witness signs) g.target_pauli)
    -- (N) any logical commuting with the measured set is preserved
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
        (∀ P ∈ merged_stabilizers_X g, L.commutes P = true) →
        L ∈ measureChecks (merged_stabilizers_X g) s)
    -- the measured set is a valid commuting family
    ∧ (∀ p ∈ merged_stabilizers_X g, ∀ q ∈ merged_stabilizers_X g,
        p.commutes q = true) := by
  have hker : g.targets_logical_correctly = true := by
    simp only [SurgeryGadget.verify_surgery_gadget, Bool.and_eq_true] at hverify
    exact hverify.2
  refine ⟨surgery_eigenvalue g n hn signs hshape hsig hker, ?_, merged_X_checks_commute g⟩
  exact fun L s hmem hcomm => surgery_preserves_commuting_logical g L s hmem hcomm

/-! ## Concrete smoke test of the eigenvalue computation -/

/-- Selecting both rows of a 2×3 merged-X-check matrix with outcomes
    `(+1, −1)` yields their support-XOR `[X,X,I]` signed by the outcome parity
    `−1`: `selectedSignedProduct` computes the measured signed operator. -/
example :
    selectedSignedProduct [true, true] [[true, false, true], [false, true, true]]
        [false, true]
      = signedXRow true [true, true, false] := by decide

/-! ##########################################################################
    ## Z-TYPE MIRROR
    ##########################################################################

    Everything below is the exact dual of the X-type development above,
    obtained by the substitution `xBit ↦ zBit`, `xRow ↦ zRow`,
    `merged_hx ↦ merged_hz`, and (for the readout/eigenvalue statements)
    the gadget's stored X-kernel `span_witness / target_pauli /
    targets_logical_correctly` ↦ explicit Z-parameters `zwitness /
    ztarget` with the Z-kernel identity `row_combination zwitness
    merged_hz = ztarget` supplied as a hypothesis (the gadget stores
    only the X-kernel).

    The duality is exact at the single-qubit-algebra level: Z/I Paulis
    have the identical multiplication / commutation / phase table to X/I
    (`Z·Z = +I`, `Z·I = +Z`, `I·Z = +Z`, `I·I = +I`; all phases `+`; any
    two Z/I strings commute).  Z-type logical measurement reads from the
    merged Z-checks `g.merged_hz` instead of the X-checks `g.merged_hx`.

    Many supporting lemmas (`PPMUpdate.mul_ops`, `foldl_mul_snd`,
    `foldl_mul_fst`, `foldl_phase_plus`, `apply_PPM_pos_preserves_mem_of_commutes`,
    `measureChecks`, `mem_measureChecks_of_commutesAll`, `vec_xor_length`,
    `row_combination_length`) are already letter-generic and are REUSED
    verbatim below — only the X-specific lowerings are re-proved for Z. -/

/-! ## Lowering Z-support bitvectors to Pauli strings -/

/-- A Z-support bit lowered to a single-qubit Pauli (`true ↦ Z`). -/
@[inline] def zBit (b : Bool) : Pauli := if b then Pauli.Z else Pauli.I

/-- Lower a Z-type check / logical support vector to a `PauliString`
    (phase `+`; `true ↦ Z`, `false ↦ I`). -/
def zRow (l : BoolVec) : PauliString := ⟨Phase.plus, l.map zBit⟩

@[simp] theorem zRow_ops (l : BoolVec) : (zRow l).ops = l.map zBit := rfl

/-! ## The GF(2)→Pauli homomorphism (operator-support level), Z-type -/

/-- Pointwise: the Z/I product (dropping phase) of two Z-support bits
    is the XOR of the bits.  `Z·Z = I`, `Z·I = Z`, `I·Z = Z`, `I·I = I`. -/
theorem pmul2_zBit (a b : Bool) : pmul2 (zBit a) (zBit b) = zBit (a != b) := by
  cases a <;> cases b <;> rfl

/-- Pure-list core of the Z-type homomorphism: zipping two Z-support lists
    and taking pointwise products equals XOR-ing then lowering. -/
theorem zipmap_pmul_zBit (a b : List Bool) (h : a.length = b.length) :
    ((a.map zBit).zip (b.map zBit)).map (fun p => pmul2 p.1 p.2)
      = (vec_xor a b).map zBit := by
  induction a generalizing b with
  | nil => simp [vec_xor]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.zip_cons_cons, vec_xor, pmul2_zBit,
        ih ys (by simpa using h)]

/-- **Key homomorphism (Z-type).**  GF(2) addition of Z-supports = Pauli
    multiplication of the corresponding Z-strings, at the operator
    (`ops`) level. -/
theorem zRow_vec_xor_ops (a b : List Bool) (h : a.length = b.length) :
    ((zRow a).mul (zRow b)).ops = (zRow (vec_xor a b)).ops := by
  rw [mul_ops, zRow_ops]
  simp only [zRow_ops]
  exact zipmap_pmul_zBit a b h

/-! ## Merged-code Z-stabilizers as Pauli strings -/

/-- The Z-type stabilizers of the merged code, lowered to Pauli strings.
    These are the operators measured during a Z-type surgery merge — the
    dual of `merged_stabilizers_X`. -/
def merged_stabilizers_Z (g : SurgeryGadget) : List PauliString :=
  g.merged_hz.map zRow

/-! ## Selected Z-product mirroring `row_combination` -/

/-- The Pauli-string product of the merged Z-checks selected by `sel`,
    mirroring the recursion of `LDPC.row_combination` — the dual of
    `selectedXProduct`. -/
def selectedZProduct (sel : List Bool) (mat : BoolMat) : PauliString :=
  match sel, mat with
  | [],          _         => zRow []
  | _,           []        => zRow []
  | false :: ts, _ :: tm   => selectedZProduct ts tm
  | true :: ts,  row :: tm =>
      let acc := selectedZProduct ts tm
      match acc.ops with
      | []       => zRow row
      | _        => (zRow row).mul acc

/-- **Lockstep theorem (Z-type).**  The operator support of the
    `sel`-selected product of merged Z-checks equals the lowering of the
    GF(2) `row_combination` of the same selection — the dual of
    `selectedXProduct_ops`. -/
theorem selectedZProduct_ops (n : Nat) :
    ∀ (sel : List Bool) (mat : BoolMat), (∀ r ∈ mat, r.length = n) →
      (selectedZProduct sel mat).ops = (zRow (row_combination sel mat)).ops := by
  intro sel
  induction sel with
  | nil => intro mat _; rfl
  | cons s ts ih =>
    intro mat hmat
    cases mat with
    | nil =>
      cases s <;> rfl
    | cons row tm =>
      have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
      cases s with
      | false =>
        simp only [selectedZProduct, row_combination]
        exact ih tm htm
      | true =>
        have ihe := ih tm htm
        simp only [selectedZProduct, row_combination]
        cases hrc : row_combination ts tm with
        | nil =>
          rw [hrc] at ihe
          have hacc : (selectedZProduct ts tm).ops = [] := by
            rw [ihe]; rfl
          rw [hacc]
        | cons c cs =>
          rw [hrc] at ihe
          have hrow : row.length = n := hmat row List.mem_cons_self
          have hcs : (c :: cs).length = n := by
            have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
            rw [hrc] at this; exact this
          have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
          rw [ihe]
          show ((zRow row).mul (selectedZProduct ts tm)).ops
              = (zRow (vec_xor row (c :: cs))).ops
          rw [mul_ops, ihe, ← mul_ops]
          exact zRow_vec_xor_ops row (c :: cs) hlen

/-! ## Signed Z-row: a measured merged Z-check carrying its ±1 outcome -/

/-- A Z-type check / logical lowered to a `PauliString`, with phase
    encoding a measurement outcome (`s = true` ↦ `−1` ↦ `Phase.minus`) —
    the dual of `signedXRow`. -/
def signedZRow (s : Bool) (l : BoolVec) : PauliString :=
  ⟨if s then Phase.minus else Phase.plus, l.map zBit⟩

@[simp] theorem signedZRow_ops (s : Bool) (l : BoolVec) :
    (signedZRow s l).ops = l.map zBit := rfl

@[simp] theorem signedZRow_phase (s : Bool) (l : BoolVec) :
    (signedZRow s l).phase = (if s then Phase.minus else Phase.plus) := rfl

/-- An unsigned `zRow` is the `s = false` signed row. -/
theorem zRow_eq_signedZRow_false (l : BoolVec) : zRow l = signedZRow false l := rfl

/-! ## Single-qubit Z/I products carry trivial phase

    `Z·Z = +I`, `Z·I = +Z`, `I·Z = +Z`, `I·I = +I`: the phase is always
    `+`.  The Z-dual of `pmul_xBit_phase`. -/

theorem pmul_zBit_phase (a b : Bool) :
    (Pauli.mul (zBit a) (zBit b)).1 = Phase.plus := by
  cases a <;> cases b <;> rfl

/-- The phase fold over a zip of `zBit`-lowered lists is trivial, since
    every Z/I single-qubit product carries phase `+` (`pmul_zBit_phase`).
    The Z-dual of `foldl_phase_plus_xBit`; reuses the generic
    `foldl_phase_plus`. -/
theorem foldl_phase_plus_zBit (a b : BoolVec) :
    ((a.map zBit).zip (b.map zBit)).foldl
        (fun (ph : Phase) ab => ph.mul (Pauli.mul ab.1 ab.2).1) Phase.plus
      = Phase.plus := by
  apply foldl_phase_plus
  intro ab hab
  have ha : ab.1 ∈ a.map zBit := List.of_mem_zip hab |>.1
  have hb : ab.2 ∈ b.map zBit := List.of_mem_zip hab |>.2
  obtain ⟨x, _, hx⟩ := List.mem_map.mp ha
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
  rw [← hx, ← hy]
  exact pmul_zBit_phase x y

/-! ## Multiplication of signed Z-rows: outcomes XOR, supports XOR -/

/-- The `.ops` of a product of two signed Z-rows is the support-XOR row,
    identical to the unsigned `zRow` case (phase lives only in `.phase`).
    The Z-dual of `signedXRow_mul_ops`. -/
theorem signedZRow_mul_ops (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    ((signedZRow sa a).mul (signedZRow sb b)).ops = (zRow (vec_xor a b)).ops := by
  rw [mul_ops]
  simp only [signedZRow_ops, zRow_ops]
  exact zipmap_pmul_zBit a b h

/-- The `.phase` of a product of two signed Z-rows is the XOR of the two
    outcome signs: `(-1)^sa · (-1)^sb = (-1)^(sa⊕sb)`.  The Z-dual of
    `signedXRow_mul_phase`; reuses the generic `foldl_mul_fst`. -/
theorem signedZRow_mul_phase (sa sb : Bool) (a b : BoolVec) :
    ((signedZRow sa a).mul (signedZRow sb b)).phase
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
  show ((signedZRow sa a).phase.mul (signedZRow sb b).phase).mul
        (((signedZRow sa a).ops.zip (signedZRow sb b).ops).foldl
          (fun (acc : Phase × List Pauli) (ab : Pauli × Pauli) =>
            let (x, y) := ab
            let (ph, c) := Pauli.mul x y
            (acc.1.mul ph, acc.2 ++ [c]))
          (Phase.plus, ([] : List Pauli))).1
      = (if (sa != sb) then Phase.minus else Phase.plus)
  rw [foldl_mul_fst]
  simp only [signedZRow_ops, signedZRow_phase]
  rw [foldl_phase_plus_zBit a b]
  have hp : ((if sa then Phase.minus else Phase.plus).mul
        (if sb then Phase.minus else Phase.plus)).mul Phase.plus
      = (if (sa != sb) then Phase.minus else Phase.plus) := by
    cases sa <;> cases sb <;> rfl
  exact hp

/-- **Signed multiplication law (Z-type).**  Multiplying two signed Z-rows
    XORs both their outcome signs and their supports.  The Z-dual of
    `signedXRow_mul`. -/
theorem signedZRow_mul (sa sb : Bool) (a b : BoolVec) (h : a.length = b.length) :
    (signedZRow sa a).mul (signedZRow sb b) = signedZRow (sa != sb) (vec_xor a b) := by
  have hops : ((signedZRow sa a).mul (signedZRow sb b)).ops
      = (signedZRow (sa != sb) (vec_xor a b)).ops := by
    rw [signedZRow_mul_ops sa sb a b h, signedZRow_ops, zRow_ops]
  have hphase : ((signedZRow sa a).mul (signedZRow sb b)).phase
      = (signedZRow (sa != sb) (vec_xor a b)).phase := by
    rw [signedZRow_mul_phase sa sb a b, signedZRow_phase]
  cases hps : (signedZRow sa a).mul (signedZRow sb b) with
  | mk ph ops =>
    cases hrhs : signedZRow (sa != sb) (vec_xor a b) with
    | mk ph' ops' =>
      rw [hps, hrhs] at hphase hops
      simp only at hphase hops
      rw [hphase, hops]

/-! ## Selected signed Z-product mirroring `row_combination` -/

/-- The XOR-parity of the outcome signs `ss` over exactly the rows
    selected by `sel`, mirroring the recursion of `row_combination` —
    the Z-dual of `selectedParity`. -/
def selectedZParity : BoolVec → List Bool → Bool
  | [],          _       => false
  | _,           []      => false
  | false :: ts, _ :: ss => selectedZParity ts ss
  | true :: ts,  s :: ss => s != selectedZParity ts ss

/-- The signed Pauli-string product of the merged Z-checks selected by
    `sel`, with each selected check carrying its measurement-outcome sign
    from `ss`.  The Z-dual of `selectedSignedProduct`. -/
def selectedSignedZProduct : BoolVec → BoolMat → List Bool → PauliString
  | [],          _,         _       => zRow []
  | _,           [],        _       => zRow []
  | _,           _,         []      => zRow []
  | false :: ts, _ :: tm,   _ :: ss => selectedSignedZProduct ts tm ss
  | true :: ts,  row :: tm, s :: ss =>
      let acc := selectedSignedZProduct ts tm ss
      match acc.ops with
      | []       => signedZRow s row
      | _        => (signedZRow s row).mul acc

/-- **Operator-support lockstep for the signed Z-product.**  The `.ops` of
    `selectedSignedZProduct` is the lowering of the GF(2) `row_combination`
    of the same selection.  The Z-dual of `selectedSignedProduct_ops`. -/
theorem selectedSignedZProduct_ops (n : Nat) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      (selectedSignedZProduct sel mat ss).ops = (zRow (row_combination sel mat)).ops := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedZProduct, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          simp only [selectedSignedZProduct, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at ihe
            have hacc : (selectedSignedZProduct ts tm ss).ops = [] := by
              rw [ihe]; rfl
            rw [hacc]
            rfl
          | cons c cs =>
            rw [hrc] at ihe
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            have hacc : (selectedSignedZProduct ts tm ss).ops = (c :: cs).map zBit := by
              rw [ihe]; rfl
            rw [hacc]
            show ((signedZRow sgn row).mul (selectedSignedZProduct ts tm ss)).ops
                = (zRow (vec_xor row (c :: cs))).ops
            rw [mul_ops, signedZRow_ops, hacc]
            show ((zRow row).ops.zip (zRow (c :: cs)).ops).map (fun ab => pmul2 ab.1 ab.2)
                = (zRow (vec_xor row (c :: cs))).ops
            rw [← mul_ops]
            exact zRow_vec_xor_ops row (c :: cs) hlen

/-- The Z-dual of `parity_false_of_combo_nil`: an empty GF(2)
    `row_combination` over positive-width rows forces the selected
    outcome-parity to be `false`. -/
theorem parity_false_of_combo_nil_Z (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length → row_combination sel mat = [] →
      selectedZParity sel ss = false := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen hcombo
    cases mat with
    | nil =>
      cases ss with
      | nil => rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedZParity]
          simp only [row_combination] at hcombo
          exact ih tm ss htm hslen' hcombo
        | true =>
          exfalso
          have hrow : row.length = n := hmat row List.mem_cons_self
          simp only [row_combination] at hcombo
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at hcombo
            simp only at hcombo
            rw [hcombo] at hrow
            simp at hrow
            omega
          | cons c cs =>
            rw [hrc] at hcombo
            simp only at hcombo
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hvx : (vec_xor row (c :: cs)).length = n := by
              rw [vec_xor_length, hrow, hcs]; omega
            rw [hcombo] at hvx
            simp at hvx
            omega

/-- **Full lockstep theorem (sign-aware, Z-type).**  The signed product of
    the `sel`-selected merged Z-checks equals the lowering of the GF(2)
    `row_combination` of the same selection, signed by the XOR-parity of
    the selected outcome bits.  The Z-dual of `selectedSignedProduct_eq`. -/
theorem selectedSignedZProduct_eq (n : Nat) (hn : 0 < n) :
    ∀ (sel : BoolVec) (mat : BoolMat) (ss : List Bool), (∀ r ∈ mat, r.length = n) →
      ss.length = mat.length →
      selectedSignedZProduct sel mat ss
        = signedZRow (selectedZParity sel ss) (row_combination sel mat) := by
  intro sel
  induction sel with
  | nil => intro mat ss _ _; rfl
  | cons s ts ih =>
    intro mat ss hmat hslen
    cases mat with
    | nil =>
      cases ss with
      | nil => cases s <;> rfl
      | cons sgn ss => simp at hslen
    | cons row tm =>
      cases ss with
      | nil => simp at hslen
      | cons sgn ss =>
        have htm : ∀ r ∈ tm, r.length = n := fun r hr => hmat r (List.mem_cons_of_mem _ hr)
        have hslen' : ss.length = tm.length := by simpa using hslen
        cases s with
        | false =>
          simp only [selectedSignedZProduct, selectedZParity, row_combination]
          exact ih tm ss htm hslen'
        | true =>
          have ihe := ih tm ss htm hslen'
          have ihops := selectedSignedZProduct_ops n ts tm ss htm hslen'
          simp only [selectedSignedZProduct, selectedZParity, row_combination]
          cases hrc : row_combination ts tm with
          | nil =>
            rw [hrc] at ihops
            have hacc : (selectedSignedZProduct ts tm ss).ops = [] := by
              rw [ihops]; rfl
            rw [hacc]
            have hpar : selectedZParity ts ss = false :=
              parity_false_of_combo_nil_Z n hn ts tm ss htm hslen' hrc
            rw [hpar, Bool.bne_false]
          | cons c cs =>
            rw [hrc] at ihops ihe
            have hacc : (selectedSignedZProduct ts tm ss).ops = (c :: cs).map zBit := by
              rw [ihops]; rfl
            rw [hacc]
            have hrow : row.length = n := hmat row List.mem_cons_self
            have hcs : (c :: cs).length = n := by
              have := (row_combination_length n ts tm htm).resolve_left (by rw [hrc]; simp)
              rw [hrc] at this; exact this
            have hlen : row.length = (c :: cs).length := by rw [hrow, hcs]
            show (signedZRow sgn row).mul (selectedSignedZProduct ts tm ss)
                = signedZRow (sgn != selectedZParity ts ss) (vec_xor row (c :: cs))
            rw [ihe, signedZRow_mul sgn (selectedZParity ts ss) row (c :: cs) hlen]

/-! ## The Z-type readout / eigenvalue-extraction statements -/

/-- **Surgery readout operator (Z-type).**  If the merged Z-check matrix is
    rectangular (all rows of width `n`) and the supplied Z-kernel identity
    `row_combination zwitness merged_hz = ztarget` holds (the gadget stores
    only the X-kernel, so this is an explicit hypothesis — the Z-dual of
    `targets_logical_correctly`), then the product of the `zwitness`-selected
    merged Z-checks acts, at the operator-support level, as exactly the
    target logical Z-operator `ztarget`.  The Z-dual of
    `surgery_readout_operator`. -/
theorem surgery_readout_operator_Z (g : SurgeryGadget) (n : Nat)
    (zwitness ztarget : BoolVec)
    (hshape : ∀ r ∈ g.merged_hz, r.length = n)
    (hzker : row_combination zwitness g.merged_hz = ztarget) :
    (selectedZProduct zwitness g.merged_hz).ops = (zRow ztarget).ops := by
  rw [selectedZProduct_ops n zwitness g.merged_hz hshape, hzker]

/-- **Surgery eigenvalue extraction (Z-type).**  The signed product of the
    `zwitness`-selected merged Z-checks equals the target logical operator
    `ztarget`, signed by the XOR-parity of those checks' measurement
    outcomes.  The Z-dual of `surgery_eigenvalue`; the Z-kernel identity is
    supplied as the explicit hypothesis `hzker`. -/
theorem surgery_eigenvalue_Z (g : SurgeryGadget) (n : Nat) (hn : 0 < n)
    (zwitness ztarget : BoolVec) (signs : List Bool)
    (hshape : ∀ r ∈ g.merged_hz, r.length = n) (hsig : signs.length = g.merged_hz.length)
    (hzker : row_combination zwitness g.merged_hz = ztarget) :
    selectedSignedZProduct zwitness g.merged_hz signs
      = signedZRow (selectedZParity zwitness signs) ztarget := by
  rw [selectedSignedZProduct_eq n hn zwitness g.merged_hz signs hshape hsig, hzker]

/-! ## The Z-type non-disturbance statement -/

/-- Single-qubit Z/I operators always commute: `Z/Z`, `Z/I`, `I/Z`, `I/I`
    are all commuting pairs.  The Z-dual of `xBit_commutes`. -/
theorem zBit_commutes (x y : Bool) : Pauli.commutes (zBit x) (zBit y) = true := by
  cases x <;> cases y <;> rfl

/-- **Any two Z/I strings commute.**  The Z-dual of `xRow_commutes`. -/
theorem zRow_commutes (a b : BoolVec) : (zRow a).commutes (zRow b) = true := by
  unfold PauliString.commutes
  simp only [zRow_ops]
  rw [Nat.beq_eq_true_eq]
  have hzero : ((a.map zBit).zip (b.map zBit)).countP
      (fun p => ! (Pauli.commutes p.1 p.2)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    have h1 : p.1 ∈ a.map zBit := List.of_mem_zip hp |>.1
    have h2 : p.2 ∈ b.map zBit := List.of_mem_zip hp |>.2
    obtain ⟨x, _, hx⟩ := List.mem_map.mp h1
    obtain ⟨y, _, hy⟩ := List.mem_map.mp h2
    rw [← hx, ← hy, zBit_commutes]
    decide
  rw [hzero]

/-- **The measured merged Z-check family commutes pairwise.**  Each element
    of `merged_stabilizers_Z g = g.merged_hz.map zRow` is a `zRow _`, so any
    two commute by `zRow_commutes`.  The Z-dual of `merged_X_checks_commute`. -/
theorem merged_Z_checks_commute (g : SurgeryGadget) :
    ∀ p ∈ merged_stabilizers_Z g, ∀ q ∈ merged_stabilizers_Z g, p.commutes q = true := by
  intro p hp q hq
  unfold merged_stabilizers_Z at hp hq
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hp
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hq
  rw [← ha, ← hb]
  exact zRow_commutes a b

/-- **Surgery non-disturbance (Z-type).**  Any logical operator `L ∈ s` that
    commutes with all the measured merged Z-checks (`merged_stabilizers_Z g`)
    survives the merge measurement.  The Z-dual of
    `surgery_preserves_commuting_logical`; reuses the generic fold lemma
    `mem_measureChecks_of_commutesAll` verbatim. -/
theorem surgery_preserves_commuting_logical_Z (g : SurgeryGadget) (L : PauliString)
    (s : StabilizerState) (hmem : L ∈ s)
    (hcomm : ∀ P ∈ merged_stabilizers_Z g, L.commutes P = true) :
    L ∈ measureChecks (merged_stabilizers_Z g) s :=
  mem_measureChecks_of_commutesAll (merged_stabilizers_Z g) L s hmem hcomm

/-! ## Top-level Z-type logical correctness (R ∧ N), axiom-free -/

/-- **A structurally-verified qLDPC code-surgery gadget implements the logical
    Z-type Pauli measurement of its target operator** — the Z-type dual of
    `surgery_implements_logical_measurement`, reading from the merged Z-checks
    `g.merged_hz` instead of the merged X-checks.

    Given well-shaped merged Z-checks of positive width and the Z-kernel
    identity `row_combination zwitness merged_hz = ztarget` (the gadget stores
    only the X-kernel, so this is an explicit hypothesis), the gadget satisfies
    BOTH halves of surgery correctness:

    * **(R) readout / eigenvalue** — the product of the `zwitness`-selected
      signed merged Z-checks equals the target logical operator signed by the
      XOR-parity of those checks' ±1 outcomes;
    * **(N) non-disturbance** — every logical commuting with the measured set
      survives the merge measurement; and
    * the measured set is a valid simultaneously-measurable commuting family.

    Proved CODE-GENERALLY (any data code) and AXIOM-FREE (only Lean's
    `propext`/`Classical.choice`/`Quot.sound`).  Fault tolerance (the
    merged-distance residue) is delimited separately in `SurgeryFaultTolerant`,
    exactly as for the X-type theorem. -/
theorem surgery_implements_logical_measurement_Z
    (g : SurgeryGadget) (n : Nat) (zwitness ztarget : BoolVec) (signs : List Bool)
    (hn : 0 < n) (hshape : ∀ r ∈ g.merged_hz, r.length = n)
    (hsig : signs.length = g.merged_hz.length)
    (hzker : row_combination zwitness g.merged_hz = ztarget) :
    -- (R) the measured eigenvalue of the target logical = parity of the
    -- selected merged-Z-check outcomes
    (selectedSignedZProduct zwitness g.merged_hz signs
        = signedZRow (selectedZParity zwitness signs) ztarget)
    -- (N) any logical commuting with the measured set is preserved
    ∧ (∀ (L : PauliString) (s : StabilizerState), L ∈ s →
        (∀ P ∈ merged_stabilizers_Z g, L.commutes P = true) →
        L ∈ measureChecks (merged_stabilizers_Z g) s)
    -- the measured set is a valid commuting family
    ∧ (∀ p ∈ merged_stabilizers_Z g, ∀ q ∈ merged_stabilizers_Z g,
        p.commutes q = true) := by
  refine ⟨surgery_eigenvalue_Z g n hn zwitness ztarget signs hshape hsig hzker, ?_,
    merged_Z_checks_commute g⟩
  exact fun L s hmem hcomm => surgery_preserves_commuting_logical_Z g L s hmem hcomm

/-! ## Concrete smoke test of the Z-type eigenvalue computation -/

/-- Selecting both rows of a 2×3 merged-Z-check matrix with outcomes
    `(+1, −1)` yields their support-XOR `[Z,Z,I]` signed by the outcome parity
    `−1`: `selectedSignedZProduct` computes the measured signed operator. -/
example :
    selectedSignedZProduct [true, true] [[true, false, true], [false, true, true]]
        [false, true]
      = signedZRow true [true, true, false] := by decide

end FormalRV.Framework.SurgeryCorrect
