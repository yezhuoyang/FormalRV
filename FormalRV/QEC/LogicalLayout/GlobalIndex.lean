/-
  FormalRV.QEC.LogicalLayout.GlobalIndex
  ──────────────────────────────────────
  **THE CONSECUTIVE LOGICAL-QUBIT NUMBERING of declared code blocks.**

  The user declares an ORDERED list of code blocks (each hosting `k`
  indexed logical qubits, grounded by a user-provided `LogicalBasis` —
  the per-slot logical-Z̄/X̄ operators in one fixed basis).  PPM wires are
  labeled CONSECUTIVELY in declaration order:

      blocks = [LP (k=14), BB (k=6)]
      wires 0‥13  ↦  LP slots 0‥13
      wires 14‥19 ↦  BB slots 0‥5      (wire 14 = BB's first logical qubit)

  `addrOf` is the labeler, `globalIndex` its exact inverse; the round-trip
  theorems make the labeling a bijection `[0, capacity) ≃ valid addresses`
  — every PPM wire IS exactly one logical qubit of exactly one block.
-/
import FormalRV.QEC.BlockAddressing
import Mathlib.Data.List.Nodup

namespace FormalRV.QEC.LogicalLayout

open FormalRV.QEC

/-! ## §1. Capacity, offsets, the labeler, the inverse. -/

/-- Logical capacity of a block list (`Σ kᵢ`). -/
def capacityOf : List CodeBlock → Nat
  | [] => 0
  | blk :: rest => blk.k + capacityOf rest

/-- Start of block `b` in the consecutive numbering (`Σ_{j<b} kⱼ`). -/
def offsetOf : List CodeBlock → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | blk :: rest, b + 1 => blk.k + offsetOf rest b

/-- **THE LABELER**: which block-local logical qubit a PPM wire is, under
consecutive numbering.  (Total for convenience; meaningful for
`g < capacityOf blocks` — see the round-trip theorems.) -/
def addrOf : List CodeBlock → Nat → LogicalAddr
  | [], g => ⟨0, g⟩
  | blk :: rest, g =>
      if g < blk.k then ⟨0, g⟩
      else
        let a := addrOf rest (g - blk.k)
        ⟨a.block + 1, a.idx⟩

/-- The global wire of a block-local address (the labeler's inverse). -/
def globalIndex (blocks : List CodeBlock) (a : LogicalAddr) : Nat :=
  offsetOf blocks a.block + a.idx

/-- An address is valid: names an existing block and an in-range slot. -/
def validAddr (blocks : List CodeBlock) (a : LogicalAddr) : Bool :=
  match blocks[a.block]? with
  | some b => decide (a.idx < b.k)
  | none   => false

/-! ## §2. The bijection: both round trips. -/

/-- **Round-trip 1**: the label of a valid address's wire is the address. -/
theorem addrOf_globalIndex :
    ∀ (blocks : List CodeBlock) (a : LogicalAddr),
      validAddr blocks a = true →
      addrOf blocks (globalIndex blocks a) = a := by
  intro blocks
  induction blocks with
  | nil =>
      intro a ha
      unfold validAddr at ha
      simp at ha
  | cons blk0 rest ih =>
      intro a ha
      unfold validAddr at ha
      obtain ⟨b, i⟩ := a
      cases b with
      | zero =>
          simp only [List.getElem?_cons_zero, decide_eq_true_eq] at ha
          show addrOf (blk0 :: rest) (0 + i) = _
          unfold addrOf
          rw [if_pos (by omega)]
          simp
      | succ b =>
          simp only [List.getElem?_cons_succ] at ha
          show addrOf (blk0 :: rest) (blk0.k + offsetOf rest b + i) = _
          unfold addrOf
          rw [if_neg (by omega)]
          have hrec : addrOf rest (blk0.k + offsetOf rest b + i - blk0.k)
              = ⟨b, i⟩ := by
            rw [show blk0.k + offsetOf rest b + i - blk0.k
                  = offsetOf rest b + i from by omega]
            exact ih ⟨b, i⟩ ha
          simp only [hrec]

/-- **Round-trip 2a**: every in-capacity wire labels to a VALID address. -/
theorem validAddr_addrOf :
    ∀ (blocks : List CodeBlock) (g : Nat),
      g < capacityOf blocks →
      validAddr blocks (addrOf blocks g) = true := by
  intro blocks
  induction blocks with
  | nil =>
      intro g hg
      simp [capacityOf] at hg
  | cons blk0 rest ih =>
      intro g hg
      unfold addrOf
      by_cases h : g < blk0.k
      · rw [if_pos h]
        unfold validAddr
        simp only [List.getElem?_cons_zero, decide_eq_true_eq]
        exact h
      · rw [if_neg h]
        have hrec := ih (g - blk0.k) (by
          unfold capacityOf at hg
          omega)
        unfold validAddr at hrec ⊢
        simp only [List.getElem?_cons_succ]
        exact hrec

/-- **Round-trip 2b**: the labeled address's wire is the wire. -/
theorem globalIndex_addrOf :
    ∀ (blocks : List CodeBlock) (g : Nat),
      g < capacityOf blocks →
      globalIndex blocks (addrOf blocks g) = g := by
  intro blocks
  induction blocks with
  | nil =>
      intro g hg
      simp [capacityOf] at hg
  | cons blk0 rest ih =>
      intro g hg
      unfold addrOf
      by_cases h : g < blk0.k
      · rw [if_pos h]
        show (0 : Nat) + g = g
        omega
      · rw [if_neg h]
        have hrec := ih (g - blk0.k) (by
          unfold capacityOf at hg
          omega)
        show offsetOf (blk0 :: rest) ((addrOf rest (g - blk0.k)).block + 1)
            + (addrOf rest (g - blk0.k)).idx = g
        show blk0.k + offsetOf rest (addrOf rest (g - blk0.k)).block
            + (addrOf rest (g - blk0.k)).idx = g
        unfold globalIndex at hrec
        omega

/-- A valid address's wire is within capacity. -/
theorem globalIndex_lt_capacity :
    ∀ (blocks : List CodeBlock) (a : LogicalAddr),
      validAddr blocks a = true →
      globalIndex blocks a < capacityOf blocks := by
  intro blocks
  induction blocks with
  | nil =>
      intro a ha
      unfold validAddr at ha
      simp at ha
  | cons blk0 rest ih =>
      intro a ha
      unfold validAddr at ha
      obtain ⟨b, i⟩ := a
      cases b with
      | zero =>
          simp only [List.getElem?_cons_zero, decide_eq_true_eq] at ha
          show offsetOf (blk0 :: rest) 0 + i < blk0.k + capacityOf rest
          show 0 + i < blk0.k + capacityOf rest
          omega
      | succ b =>
          simp only [List.getElem?_cons_succ] at ha
          have h1 := ih ⟨b, i⟩ ha
          have h2 : offsetOf rest b + i < capacityOf rest := h1
          show blk0.k + offsetOf rest b + i < blk0.k + capacityOf rest
          omega

/-- **The labeling is injective**: distinct wires are distinct logical
qubits. -/
theorem addrOf_inj (blocks : List CodeBlock) (g g' : Nat)
    (hg : g < capacityOf blocks) (hg' : g' < capacityOf blocks)
    (h : addrOf blocks g = addrOf blocks g') : g = g' := by
  have h1 := globalIndex_addrOf blocks g hg
  have h2 := globalIndex_addrOf blocks g' hg'
  rw [← h1, ← h2, h]

/-- **Exactly-one**: for every in-capacity wire, the label is THE unique
valid address whose wire it is. -/
theorem addrOf_unique (blocks : List CodeBlock) (g : Nat)
    (a : LogicalAddr)
    (ha : validAddr blocks a = true) (hga : globalIndex blocks a = g) :
    a = addrOf blocks g := by
  rw [← hga, addrOf_globalIndex blocks a ha]

/-! ## §3. `BlockLayout` interop: the canonical consecutive layout. -/

/-- The consecutive wire→address map as explicit `BlockLayout` data. -/
def consecutiveMap (blocks : List CodeBlock) : List LogicalAddr :=
  (List.range (capacityOf blocks)).map (addrOf blocks)

/-- **The canonical consecutive layout** of an ordered block list — the
`BlockLayout` whose map is the honest consecutive labeling (interops with
all of `BlockAddressing`: `resolve`, `render`, `wf`, …). -/
def consecutive (blocks : List CodeBlock) : BlockLayout :=
  ⟨blocks, consecutiveMap blocks⟩

/-- The consecutive layout is ALWAYS structurally well-formed (in-range +
injective) — no user obligation beyond the block declarations. -/
theorem consecutive_wfStructural (blocks : List CodeBlock) :
    (consecutive blocks).wfStructural = true := by
  unfold BlockLayout.wfStructural
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro a ha
    simp only [consecutive, consecutiveMap, List.mem_map,
      List.mem_range] at ha
    obtain ⟨g, hg, rfl⟩ := ha
    show BlockLayout.wfAddr _ _ = true
    unfold BlockLayout.wfAddr
    have := validAddr_addrOf blocks g hg
    unfold validAddr at this
    exact this
  · rw [decide_eq_true_eq]
    show (consecutiveMap blocks).Nodup
    unfold consecutiveMap
    refine List.Nodup.map_on ?_ List.nodup_range
    intro g hg g' hg' h
    exact addrOf_inj blocks g g'
      (List.mem_range.mp hg) (List.mem_range.mp hg') h

/-! ## §4. Segment algebra: block FARMS (`blocks 1024 of sc`).

Layouts with replicated segments (`List.replicate n blk ++ rest`) get
CLOSED-FORM indexing — division and modulo, no list walk — so a
1024-patch surface-code farm is as cheap to reason about as one block. -/

theorem capacityOf_append (bs cs : List CodeBlock) :
    capacityOf (bs ++ cs) = capacityOf bs + capacityOf cs := by
  induction bs with
  | nil => simp [capacityOf]
  | cons blk rest ih =>
      show blk.k + capacityOf (rest ++ cs) = blk.k + capacityOf rest + _
      rw [ih]
      omega

theorem capacityOf_replicate (n : Nat) (blk : CodeBlock) :
    capacityOf (List.replicate n blk) = n * blk.k := by
  induction n with
  | zero =>
      show (0 : Nat) = 0 * blk.k
      omega
  | succ n ih =>
      show blk.k + capacityOf (List.replicate n blk) = (n + 1) * blk.k
      rw [ih, Nat.succ_mul]
      omega

/-- Indexing stays in the LEFT segment when the wire fits there. -/
theorem addrOf_append_left (bs cs : List CodeBlock) (g : Nat)
    (hg : g < capacityOf bs) :
    addrOf (bs ++ cs) g = addrOf bs g := by
  induction bs generalizing g with
  | nil => simp [capacityOf] at hg
  | cons blk rest ih =>
      by_cases h : g < blk.k
      · show (if g < blk.k then LogicalAddr.mk 0 g else _)
            = (if g < blk.k then LogicalAddr.mk 0 g else _)
        rw [if_pos h, if_pos h]
      · show (if g < blk.k then LogicalAddr.mk 0 g
              else ⟨(addrOf (rest ++ cs) (g - blk.k)).block + 1,
                    (addrOf (rest ++ cs) (g - blk.k)).idx⟩)
            = (if g < blk.k then LogicalAddr.mk 0 g
              else ⟨(addrOf rest (g - blk.k)).block + 1,
                    (addrOf rest (g - blk.k)).idx⟩)
        rw [if_neg h, if_neg h, ih (g - blk.k) (by
          unfold capacityOf at hg
          omega)]

/-- Indexing passes a saturated left segment with a block-index shift. -/
theorem addrOf_append_right (bs cs : List CodeBlock) (g : Nat)
    (hg : capacityOf bs ≤ g) :
    addrOf (bs ++ cs) g
      = ⟨bs.length + (addrOf cs (g - capacityOf bs)).block,
         (addrOf cs (g - capacityOf bs)).idx⟩ := by
  induction bs generalizing g with
  | nil =>
      show addrOf cs g
          = ⟨(List.length ([] : List CodeBlock))
              + (addrOf cs (g - capacityOf [])).block,
             (addrOf cs (g - capacityOf [])).idx⟩
      rw [show capacityOf ([] : List CodeBlock) = 0 from rfl, Nat.sub_zero]
      show addrOf cs g = ⟨0 + (addrOf cs g).block, (addrOf cs g).idx⟩
      rw [Nat.zero_add]
  | cons blk rest ih =>
      have hk : ¬ g < blk.k := by
        unfold capacityOf at hg
        omega
      show (if g < blk.k then LogicalAddr.mk 0 g
            else ⟨(addrOf (rest ++ cs) (g - blk.k)).block + 1,
                  (addrOf (rest ++ cs) (g - blk.k)).idx⟩) = _
      rw [if_neg hk, ih (g - blk.k) (by
        unfold capacityOf at hg
        omega)]
      have harith : g - blk.k - capacityOf rest
          = g - capacityOf (blk :: rest) := by
        show _ = g - (blk.k + capacityOf rest)
        omega
      rw [harith]
      show LogicalAddr.mk (rest.length
          + (addrOf cs (g - capacityOf (blk :: rest))).block + 1) _ = _
      have hlen : rest.length
            + (addrOf cs (g - capacityOf (blk :: rest))).block + 1
          = (blk :: rest).length
            + (addrOf cs (g - capacityOf (blk :: rest))).block := by
        simp only [List.length_cons]
        omega
      rw [hlen]

/-- **THE FARM CLOSED FORM**: in a uniform replicated segment, the label
of wire `g` is `⟨g / k, g % k⟩` — pure arithmetic, no list walk. -/
theorem addrOf_replicate (n : Nat) (blk : CodeBlock) (g : Nat)
    (hk : 0 < blk.k) (hg : g < n * blk.k) :
    addrOf (List.replicate n blk) g = ⟨g / blk.k, g % blk.k⟩ := by
  induction n generalizing g with
  | zero => omega
  | succ n ih =>
      show addrOf (blk :: List.replicate n blk) g = _
      by_cases h : g < blk.k
      · show (if g < blk.k then LogicalAddr.mk 0 g else _) = _
        rw [if_pos h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      · have hsub : g - blk.k < n * blk.k := by
          rw [Nat.succ_mul] at hg
          omega
        show (if g < blk.k then LogicalAddr.mk 0 g
              else ⟨(addrOf (List.replicate n blk) (g - blk.k)).block + 1,
                    (addrOf (List.replicate n blk) (g - blk.k)).idx⟩) = _
        rw [if_neg h, ih (g - blk.k) hsub]
        have hle : blk.k ≤ g := Nat.le_of_not_lt h
        have hd := Nat.div_eq_sub_div hk hle
        have hm := Nat.mod_eq_sub_mod hle
        show LogicalAddr.mk ((g - blk.k) / blk.k + 1) ((g - blk.k) % blk.k)
            = ⟨g / blk.k, g % blk.k⟩
        rw [← hm]
        congr 1
        omega

end FormalRV.QEC.LogicalLayout