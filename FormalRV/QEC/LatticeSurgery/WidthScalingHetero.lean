import FormalRV.QEC.LatticeSurgery.WidthScalingStep2b
import FormalRV.QEC.LatticeSurgery.WidthScalingXMerge

/-!
# Heterogeneous catalog chain engine for scalable lattice-surgery Shor compilation

This module generalizes the *homogeneous* chain engine of `WidthScalingStep2`/
`ChainComposition` (`chainOK` for `replicate (N+1)` of ONE gadget) to a
**heterogeneous catalog**: an ARBITRARY list of gadgets drawn from a small
catalog, with `chainOK` established BY INDUCTION ON THE LIST, reusing each
gadget's OWN self-interface certs — so a real heterogeneous program (a sequence
of different kinds) composes.

The architecture (the four design pillars, all built here):

1. **Generic adjacent-pair transport.**  `weldInterfaceOK2 h g B s SB conn …`
   reads `funcCubeOK (weldK h g B conn) (stitchSurf h s SB)` only at the seam
   layers `k ∈ {h-1, h}`; at `k=h` the `weldK`/`stitchSurf` shift reads `B`/`SB`
   at layer `0`.  So the interface check depends on `(B,SB)` ONLY through their
   layer-0 (bottom) fields.  `weldInterfaceOK2_botEq` makes this precise; the
   `gseam_*` lemmas are the generic counterparts of the existing `seam_*` (which
   were specialized to `g` vs `zChain g N`).

2. **Canonical-bottom reuse.**  If a chain's head `g2` presents the SAME layer-0
   boundary as `g` (`BotEqL g2 g`), then by (1) `weldInterfaceOK2 h g B … =
   weldInterfaceOK2 h g g …`, i.e. each gadget reuses its OWN self-interface cert
   across any heterogeneous boundary — NO per-pair cross certs.
   (`chain_interface_reduce_to_self`.)

3. **Hetero `chainOK` builder.**  `catalog_chainOK` proves `chainOK` for any
   nonempty list of catalog entries by INDUCTION on the list, discharging every
   interface via (1)+(2).

4. **Idle gadget.**  `idleMerge w` is the second catalog kind (same `w × 1`
   footprint as `zMerge`): `w` data K-worldlines, NO I/J seam.  Its layer-0
   boundary equals `zMerge`'s by design, enabling (2).

Demos: the concrete heterogeneous chain `[zMerge w, idleMerge w, zMerge w]`
(measure joint Z̄ ; idle ; measure joint Z̄), and the fully generic kind-list
`kindChain` over `ks : List Bool` — `chainOK` + interior `LaSCorrect`, for ALL
widths `w`, with NO `native_decide` over `w` OR the chain length.

Axiom-clean (`{propext, Classical.choice, Quot.sound}`), zero `sorry`, zero
`native_decide`.
-/

namespace FormalRV.QEC.LaSre

variable {h : Nat} {conn : List (Nat × Nat)} {g : LaSre} {s : Surf}

/-! ## Generic seam field-equality lemmas: `weldK h g B1 = weldK h g B2` at `k ≤ h`
    given `B1`, `B2` agree at layer `0`. -/

-- The hypothesis bundle: B1 and B2 agree on every diagram field at layer 0.
structure BotEqL (B1 B2 : LaSre) : Prop where
  yc : ∀ i j, B1.YCube i j 0 = B2.YCube i j 0
  ei : ∀ i j, B1.ExistI i j 0 = B2.ExistI i j 0
  ej : ∀ i j, B1.ExistJ i j 0 = B2.ExistJ i j 0
  ek : ∀ i j, B1.ExistK i j 0 = B2.ExistK i j 0

structure BotEqS (SB1 SB2 : Surf) : Prop where
  ij : ∀ t i j, SB1.IJ t i j 0 = SB2.IJ t i j 0
  ik : ∀ t i j, SB1.IK t i j 0 = SB2.IK t i j 0
  jk : ∀ t i j, SB1.JK t i j 0 = SB2.JK t i j 0
  ji : ∀ t i j, SB1.JI t i j 0 = SB2.JI t i j 0
  ki : ∀ t i j, SB1.KI t i j 0 = SB2.KI t i j 0
  kj : ∀ t i j, SB1.KJ t i j 0 = SB2.KJ t i j 0

-- Generic seam field equalities at k ≤ h.
theorem gseam_YCube (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).YCube i j k = (weldK h g B2 conn).YCube i j k := by
  simp only [weldK]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hB.yc]

theorem gseam_ExistI (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).ExistI i j k = (weldK h g B2 conn).ExistI i j k := by
  simp only [weldK]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hB.ei]

theorem gseam_ExistJ (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).ExistJ i j k = (weldK h g B2 conn).ExistJ i j k := by
  simp only [weldK]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hB.ej]

theorem gseam_ExistK (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).ExistK i j k = (weldK h g B2 conn).ExistK i j k := by
  simp only [weldK]
  by_cases hk1 : k + 1 < h
  · rw [if_pos hk1, if_pos hk1]
  · by_cases hk2 : (k + 1 == h) = true
    · rw [if_neg hk1, if_pos hk2, if_neg hk1, if_pos hk2]
    · have hkh : k = h := by
        rcases Nat.lt_or_ge (k + 1) h with hlt | hge
        · exact absurd hlt hk1
        · have : ¬ (k + 1 = h) := by intro hc; exact hk2 (by simp [hc])
          omega
      subst hkh
      rw [if_neg hk1, if_neg hk2, if_neg hk1, if_neg hk2, Nat.sub_self, hB.ek]

/-! ## Generic stitchSurf seam equalities. -/

theorem gseam_KI (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).KI t i j k = (stitchSurf h s SB2).KI t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.ki]

theorem gseam_KJ (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).KJ t i j k = (stitchSurf h s SB2).KJ t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.kj]

theorem gseam_IJ (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).IJ t i j k = (stitchSurf h s SB2).IJ t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.ij]

theorem gseam_IK (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).IK t i j k = (stitchSurf h s SB2).IK t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.ik]

theorem gseam_JK (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).JK t i j k = (stitchSurf h s SB2).JK t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.jk]

theorem gseam_JI (hh : 2 ≤ h) {SB1 SB2 : Surf} (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (stitchSurf h s SB1).JI t i j k = (stitchSurf h s SB2).JI t i j k := by
  simp only [stitchSurf]
  by_cases hkh : k < h
  · rw [if_pos hkh, if_pos hkh]
  · have : k = h := by omega
    subst this
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self, hS.ji]

/-! ## The generic funcCubeOK seam equality — the heart of (1). -/

theorem gfuncCubeOK_seam_eq (hh : 2 ≤ h) {B1 B2 : LaSre} {SB1 SB2 : Surf}
    (hB : BotEqL B1 B2) (hS : BotEqS SB1 SB2)
    (t i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).funcCubeOK (stitchSurf h s SB1) t i j k
      = (weldK h g B2 conn).funcCubeOK (stitchSurf h s SB2) t i j k := by
  have hkm : k - 1 ≤ h := by omega
  simp only [LaSre.funcCubeOK, LaSre.degree, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    LaSre.iParity, LaSre.jParity, LaSre.kParity,
    LaSre.allOrNoneI, LaSre.allOrNoneJ, LaSre.allOrNoneK,
    gseam_YCube hh hB i j k hk,
    gseam_ExistI hh hB i j k hk, gseam_ExistI hh hB (i - 1) j k hk,
    gseam_ExistJ hh hB i j k hk, gseam_ExistJ hh hB i (j - 1) k hk,
    gseam_ExistK hh hB i j k hk, gseam_ExistK hh hB i j (k - 1) hkm,
    gseam_KI hh hS t i j k hk, gseam_KI hh hS t i j (k - 1) hkm,
    gseam_KJ hh hS t i j k hk, gseam_KJ hh hS t i j (k - 1) hkm,
    gseam_IJ hh hS t i j k hk, gseam_IJ hh hS t (i - 1) j k hk,
    gseam_IK hh hS t i j k hk, gseam_IK hh hS t (i - 1) j k hk,
    gseam_JK hh hS t i j k hk, gseam_JK hh hS t i (j - 1) k hk,
    gseam_JI hh hS t i j k hk, gseam_JI hh hS t i (j - 1) k hk]

theorem gvalidCube_seam_eq (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (i j k : Nat) (hk : k ≤ h) :
    (weldK h g B1 conn).validCube i j k = (weldK h g B2 conn).validCube i j k := by
  have hkm : k - 1 ≤ h := by omega
  simp only [LaSre.validCube, LaSre.hasI, LaSre.hasJ, LaSre.hasK,
    gseam_YCube hh hB i j k hk,
    gseam_ExistI hh hB i j k hk, gseam_ExistI hh hB (i - 1) j k hk,
    gseam_ExistJ hh hB i j k hk, gseam_ExistJ hh hB i (j - 1) k hk,
    gseam_ExistK hh hB i j k hk, gseam_ExistK hh hB i j (k - 1) hkm]

/-! ## The generic interface-check transport: weldInterfaceOK2_botEq. -/

theorem weldInterfaceOK2_botEq (hh : 2 ≤ h) {B1 B2 : LaSre} {SB1 SB2 : Surf}
    (hB : BotEqL B1 B2) (hS : BotEqS SB1 SB2) (n w wj : Nat) :
    weldInterfaceOK2 h g B1 s SB1 conn n w wj
      = weldInterfaceOK2 h g B2 s SB2 conn n w wj := by
  have hh0 : 0 < h := by omega
  simp only [weldInterfaceOK2]
  congr 1
  funext t
  congr 1
  funext i
  congr 1
  funext j
  rw [if_pos hh0, if_pos hh0]
  rw [gfuncCubeOK_seam_eq hh hB hS t i j (h - 1) (by omega),
      gfuncCubeOK_seam_eq hh hB hS t i j h (le_refl h)]

theorem weldInterfaceValidOK2_botEq (hh : 2 ≤ h) {B1 B2 : LaSre} (hB : BotEqL B1 B2)
    (w wj : Nat) :
    weldInterfaceValidOK2 h g B1 conn w wj
      = weldInterfaceValidOK2 h g B2 conn w wj := by
  have hh0 : 0 < h := by omega
  simp only [weldInterfaceValidOK2]
  congr 1
  funext i
  congr 1
  funext j
  rw [if_pos hh0, if_pos hh0]
  rw [gvalidCube_seam_eq hh hB i j (h - 1) (by omega),
      gvalidCube_seam_eq hh hB i j h (le_refl h)]

/-! ## Layer-0 agreement: a nonempty chain's bottom is its head's bottom. -/

theorem weldChain_botEqL (hh : 2 ≤ h) (g2 : LaSre) (rest : List LaSre) :
    BotEqL (weldChain h conn (g2 :: rest)) g2 := by
  cases rest with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons g3 rest' =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i j <;>
      simp only [weldChain, weldK, if_pos (show (0:Nat) < h by omega),
        if_pos (show (0:Nat) + 1 < h by omega)]

theorem weldChainSurf_botEqS (hh : 2 ≤ h) (s2 : Surf) (srest : List Surf) :
    BotEqS (weldChainSurf h (s2 :: srest)) s2 := by
  cases srest with
  | nil => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
                  fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | cons s3 srest' =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t i j <;>
      simp only [weldChainSurf, weldSurf] <;> rw [if_pos (show (0:Nat) < h by omega)]

/-! ## BotEqL / BotEqS are symmetric & transitive (combine head agreement). -/

theorem BotEqL.symm {B1 B2 : LaSre} (h : BotEqL B1 B2) : BotEqL B2 B1 :=
  ⟨fun i j => (h.yc i j).symm, fun i j => (h.ei i j).symm,
   fun i j => (h.ej i j).symm, fun i j => (h.ek i j).symm⟩

theorem BotEqL.trans {B1 B2 B3 : LaSre} (h12 : BotEqL B1 B2) (h23 : BotEqL B2 B3) :
    BotEqL B1 B3 :=
  ⟨fun i j => (h12.yc i j).trans (h23.yc i j), fun i j => (h12.ei i j).trans (h23.ei i j),
   fun i j => (h12.ej i j).trans (h23.ej i j), fun i j => (h12.ek i j).trans (h23.ek i j)⟩

theorem BotEqS.symm {S1 S2 : Surf} (h : BotEqS S1 S2) : BotEqS S2 S1 :=
  ⟨fun t i j => (h.ij t i j).symm, fun t i j => (h.ik t i j).symm,
   fun t i j => (h.jk t i j).symm, fun t i j => (h.ji t i j).symm,
   fun t i j => (h.ki t i j).symm, fun t i j => (h.kj t i j).symm⟩

theorem BotEqS.trans {S1 S2 S3 : Surf} (h12 : BotEqS S1 S2) (h23 : BotEqS S2 S3) :
    BotEqS S1 S3 :=
  ⟨fun t i j => (h12.ij t i j).trans (h23.ij t i j),
   fun t i j => (h12.ik t i j).trans (h23.ik t i j),
   fun t i j => (h12.jk t i j).trans (h23.jk t i j),
   fun t i j => (h12.ji t i j).trans (h23.ji t i j),
   fun t i j => (h12.ki t i j).trans (h23.ki t i j),
   fun t i j => (h12.kj t i j).trans (h23.kj t i j)⟩

/-! ## THE TRANSPORT-TO-SELF lemma (design (1)+(2) fused).  If the chain's head
    `g2` presents the SAME layer-0 boundary as `g` (canonical-bottom reuse), the
    chain's interface cert against `g` reduces to `g`'s own SELF-interface cert. -/

theorem chain_interface_reduce_to_self (hh : 2 ≤ h)
    (g2 : LaSre) (rest : List LaSre) (s2 : Surf) (srest : List Surf)
    (hBg : BotEqL g2 g) (hSg : BotEqS s2 s)
    (n w wj : Nat) :
    weldInterfaceOK2 h g (weldChain h conn (g2 :: rest)) s
        (weldChainSurf h (s2 :: srest)) conn n w wj
      = weldInterfaceOK2 h g g s s conn n w wj := by
  rw [weldInterfaceOK2_botEq hh
        ((weldChain_botEqL hh g2 rest).trans hBg)
        ((weldChainSurf_botEqS hh s2 srest).trans hSg)]

theorem chain_validInterface_reduce_to_self (hh : 2 ≤ h)
    (g2 : LaSre) (rest : List LaSre)
    (hBg : BotEqL g2 g) (w wj : Nat) :
    weldInterfaceValidOK2 h g (weldChain h conn (g2 :: rest)) conn w wj
      = weldInterfaceValidOK2 h g g conn w wj := by
  rw [weldInterfaceValidOK2_botEq hh ((weldChain_botEqL hh g2 rest).trans hBg)]

/-! ## §IDLE.  The idle gadget — w data worldlines, NO I/J seam. -/

def idleMerge (w : Nat) : LaSre :=
  { maxI := w, maxJ := 1, maxK := 3
    YCube  := fun _ _ _ => false
    ExistI := fun _ _ _ => false
    ExistJ := fun _ _ _ => false
    ExistK := fun i j k => decide (i < w) && j == 0 && decide (k < 2) -- all w worldlines
    ColorI := fun _ _ _ => false, ColorJ := fun _ _ _ => false }

def idleSurf (w : Nat) : Surf :=
  { IJ := fun _ _ _ _ => false
    IK := fun _ _ _ _ => false               -- NO seam piece
    JK := fun _ _ _ _ => false, JI := fun _ _ _ _ => false
    KI := fun s i j _ => s == 0 && j == 0 && decide (i < w)          -- joint Z on all data
    KJ := fun s i j _ => decide (1 ≤ s) && decide (s - 1 = i) && decide (s ≤ w) && j == 0 }

theorem idle_validCube (w i j k : Nat) : (idleMerge w).validCube i j k = true := by
  simp [LaSre.validCube, LaSre.hasI, LaSre.hasJ, idleMerge]

theorem idle_valid (w : Nat) : (idleMerge w).valid = true := by
  rw [LaSre.valid, List.all_eq_true]
  intro c _
  exact idle_validCube w c.1 c.2.1 c.2.2

-- Parity / all-or-none cancellation at the interior k=1, same per-column technique.
theorem idle_jParity_k1 (w s i : Nat) :
    jParity (idleMerge w) (idleSurf w) s i 0 1 = false := by
  simp [jParity, idleMerge, idleSurf]

theorem idle_iParity_k1 (w s i : Nat) :
    iParity (idleMerge w) (idleSurf w) s i 0 1 = false := by
  simp [iParity, idleMerge, idleSurf]

theorem idle_allOrNoneI_k1 (w s i : Nat) :
    allOrNoneI (idleMerge w) (idleSurf w) s i 0 1 = true := by
  rw [allOrNoneI]
  apply allEq_const_present (b := (idleSurf w).KJ s i 0 1)
  intro p hp hpres
  fin_cases hp <;> simp_all [idleMerge, idleSurf]

theorem idle_allOrNoneJ_k1 (w s i : Nat) :
    allOrNoneJ (idleMerge w) (idleSurf w) s i 0 1 = true := by
  rw [allOrNoneJ]
  apply allEq_const_present (b := s == 0)
  intro p hp hpres
  fin_cases hp <;> simp_all [idleMerge, idleSurf]

theorem idle_funcCubeOK_k1 (w s i : Nat) :
    funcCubeOK (idleMerge w) (idleSurf w) s i 0 1 = true := by
  unfold funcCubeOK
  rw [idle_iParity_k1, idle_jParity_k1, idle_allOrNoneI_k1, idle_allOrNoneJ_k1]
  by_cases hiw : i < w
  · have hK : (idleMerge w).hasK i 0 1 = true := by simp [LaSre.hasK, idleMerge, hiw]
    rw [hK]
    simp [idleMerge]
  · have hd : (idleMerge w).degree i 0 1 ≤ 1 := by
      simp only [LaSre.degree, idleMerge]
      simp [hiw]
    rw [if_neg (show ¬((idleMerge w).YCube i 0 1 = true) by simp [idleMerge]), if_pos hd]

theorem idle_funcCubeOK_k0 (w s i : Nat) :
    funcCubeOK (idleMerge w) (idleSurf w) s i 0 0 = true := by
  unfold funcCubeOK
  have hd : (idleMerge w).degree i 0 0 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, idleMerge, h]
  rw [if_neg (show ¬((idleMerge w).YCube i 0 0 = true) by simp [idleMerge]), if_pos hd]

theorem idle_funcCubeOK_k2 (w s i : Nat) :
    funcCubeOK (idleMerge w) (idleSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  have hd : (idleMerge w).degree i 0 2 ≤ 1 := by
    by_cases h : i < w <;> simp [LaSre.degree, idleMerge, h]
  rw [if_neg (show ¬((idleMerge w).YCube i 0 2 = true) by simp [idleMerge]), if_pos hd]

theorem idle_funcOK (w n : Nat) :
    funcOK (idleMerge w) (idleSurf w) n = true := by
  rw [LaSre.funcOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  rintro ⟨i, j, k⟩ hc
  rw [mem_gridCubes] at hc
  obtain ⟨_, hj, hk⟩ := hc
  have hj0 : j = 0 := by simp only [idleMerge] at hj; omega
  subst hj0
  simp only [idleMerge] at hk
  interval_cases k
  · exact idle_funcCubeOK_k0 w s i
  · exact idle_funcCubeOK_k1 w s i
  · exact idle_funcCubeOK_k2 w s i

/-! ## CANONICAL BOTTOM: idleMerge's layer-0 = zMerge's layer-0. -/

theorem idle_zMerge_botEqL (w : Nat) : BotEqL (idleMerge w) (zMerge w) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i j <;> simp [idleMerge, zMerge]

theorem idle_zMerge_botEqS (w : Nat) : BotEqS (idleSurf w) (zMergeSurf w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t i j <;> simp [idleSurf, zMergeSurf]

/-! ## IDLE SELF-INTERFACE CERTS (width-symbolic), mirroring WidthScalingStep2b. -/

abbrev iSeam (w : Nat) : LaSre := weldK 3 (idleMerge w) (idleMerge w) (zChainConn w)
abbrev iSeamSurf (w : Nat) : Surf := stitchSurf 3 (idleSurf w) (idleSurf w)

theorem iSeam_ExistJ (w i j k : Nat) : (iSeam w).ExistJ i j k = false := by
  simp only [iSeam, weldK, idleMerge]; split <;> rfl
theorem iSeam_ExistI (w i j k : Nat) : (iSeam w).ExistI i j k = false := by
  simp only [iSeam, weldK, idleMerge]; split <;> rfl
theorem iSeam_YCube (w i j k : Nat) : (iSeam w).YCube i j k = false := by
  simp only [iSeam, weldK, idleMerge]; split <;> rfl

theorem iSeam_validCube (w i j k : Nat) : (iSeam w).validCube i j k = true := by
  simp only [LaSre.validCube, LaSre.hasJ, iSeam_ExistJ, iSeam_YCube,
    Bool.false_or, Bool.and_false, Bool.not_false, Bool.and_true]
  simp

theorem idle_refValid_sym (w : Nat) :
    weldInterfaceValidOK2 3 (idleMerge w) (idleMerge w) (zChainConn w) w 1 = true := by
  rw [weldInterfaceValidOK2, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact iSeam_validCube w i j (3 - 1)
  · exact iSeam_validCube w i j 3

-- ExistK at seam layers (idle has the SAME worldlines as zMerge, so identical).
theorem iSeam_ExistK1 (w i : Nat) : (iSeam w).ExistK i 0 1 = decide (i < w) := by
  simp only [iSeam, weldK]; rw [if_pos (by norm_num)]; simp [idleMerge]
theorem iSeam_ExistK2 (w i : Nat) : (iSeam w).ExistK i 0 2 = decide (i < w) := by
  simp only [iSeam, weldK, zChainConn_contains]; simp [idleMerge]
theorem iSeam_ExistK3 (w i : Nat) : (iSeam w).ExistK i 0 3 = decide (i < w) := by
  simp only [iSeam, weldK]; simp [idleMerge]

-- Stitched idle surface KI/KJ are the k-independent idleSurf value.
theorem iSeamSurf_KI1 (w s i : Nat) :
    (iSeamSurf w).KI s i 0 1 = (idleSurf w).KI s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem iSeamSurf_KI2 (w s i : Nat) :
    (iSeamSurf w).KI s i 0 2 = (idleSurf w).KI s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem iSeamSurf_KI3 (w s i : Nat) :
    (iSeamSurf w).KI s i 0 3 = (idleSurf w).KI s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]
theorem iSeamSurf_KJ1 (w s i : Nat) :
    (iSeamSurf w).KJ s i 0 1 = (idleSurf w).KJ s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem iSeamSurf_KJ2 (w s i : Nat) :
    (iSeamSurf w).KJ s i 0 2 = (idleSurf w).KJ s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_pos (by norm_num)]; rfl
theorem iSeamSurf_KJ3 (w s i : Nat) :
    (iSeamSurf w).KJ s i 0 3 = (idleSurf w).KJ s i 0 0 := by
  simp only [iSeamSurf, stitchSurf]; rw [if_neg (by norm_num)]

theorem iSeam_iParity2 (w s i : Nat) :
    iParity (iSeam w) (iSeamSurf w) s i 0 2 = false := by
  rw [iParity, show (2 : Nat) - 1 = 1 from rfl,
    iSeam_ExistJ, iSeam_ExistK2, iSeam_ExistK1, iSeamSurf_KI2, iSeamSurf_KI1]
  simp
theorem iSeam_iParity3 (w s i : Nat) :
    iParity (iSeam w) (iSeamSurf w) s i 0 3 = false := by
  rw [iParity, show (3 : Nat) - 1 = 2 from rfl,
    iSeam_ExistJ, iSeam_ExistK3, iSeam_ExistK2, iSeamSurf_KI3, iSeamSurf_KI2]
  simp
theorem iSeam_jParity2 (w s i : Nat) :
    jParity (iSeam w) (iSeamSurf w) s i 0 2 = false := by
  rw [jParity, show (2 : Nat) - 1 = 1 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK2, iSeam_ExistK1, iSeamSurf_KJ2, iSeamSurf_KJ1]
  simp
theorem iSeam_jParity3 (w s i : Nat) :
    jParity (iSeam w) (iSeamSurf w) s i 0 3 = false := by
  rw [jParity, show (3 : Nat) - 1 = 2 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK3, iSeam_ExistK2, iSeamSurf_KJ3, iSeamSurf_KJ2]
  simp
theorem iSeam_allOrNoneI2 (w s i : Nat) :
    allOrNoneI (iSeam w) (iSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneI, show (2 : Nat) - 1 = 1 from rfl,
    iSeam_ExistJ, iSeam_ExistK2, iSeam_ExistK1, iSeamSurf_KJ2, iSeamSurf_KJ1]
  apply allEq_const_present (b := (idleSurf w).KJ s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all
theorem iSeam_allOrNoneI3 (w s i : Nat) :
    allOrNoneI (iSeam w) (iSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneI, show (3 : Nat) - 1 = 2 from rfl,
    iSeam_ExistJ, iSeam_ExistK3, iSeam_ExistK2, iSeamSurf_KJ3, iSeamSurf_KJ2]
  apply allEq_const_present (b := (idleSurf w).KJ s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all
theorem iSeam_allOrNoneJ2 (w s i : Nat) :
    allOrNoneJ (iSeam w) (iSeamSurf w) s i 0 2 = true := by
  rw [allOrNoneJ, show (2 : Nat) - 1 = 1 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK2, iSeam_ExistK1, iSeamSurf_KI2, iSeamSurf_KI1]
  apply allEq_const_present (b := (idleSurf w).KI s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all
theorem iSeam_allOrNoneJ3 (w s i : Nat) :
    allOrNoneJ (iSeam w) (iSeamSurf w) s i 0 3 = true := by
  rw [allOrNoneJ, show (3 : Nat) - 1 = 2 from rfl]
  simp only [iSeam_ExistI, iSeam_ExistK3, iSeam_ExistK2, iSeamSurf_KI3, iSeamSurf_KI2]
  apply allEq_const_present (b := (idleSurf w).KI s i 0 0)
  intro p hp hpres
  fin_cases hp <;> simp_all

theorem iSeam_funcCubeOK2 (w s i : Nat) :
    funcCubeOK (iSeam w) (iSeamSurf w) s i 0 2 = true := by
  unfold funcCubeOK
  rw [iSeam_iParity2, iSeam_jParity2, iSeam_allOrNoneI2, iSeam_allOrNoneJ2]
  by_cases hiw : i < w
  · rw [show (iSeam w).hasK i 0 2 = true by simp only [LaSre.hasK, iSeam_ExistK2]; simp [hiw]]
    rw [if_neg (show ¬((iSeam w).YCube i 0 2 = true) by rw [iSeam_YCube]; simp)]
    rw [if_neg (show ¬((iSeam w).degree i 0 2 ≤ 1) by
      simp only [LaSre.degree, iSeam_ExistK2, iSeam_ExistI, iSeam_ExistJ,
        show (2 : Nat) - 1 = 1 from rfl, iSeam_ExistK1]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((iSeam w).YCube i 0 2 = true) by rw [iSeam_YCube]; simp),
      if_pos (show (iSeam w).degree i 0 2 ≤ 1 by
        simp only [LaSre.degree, iSeam_ExistK2, iSeam_ExistI, iSeam_ExistJ,
          show (2 : Nat) - 1 = 1 from rfl, iSeam_ExistK1]; simp [hiw])]

theorem iSeam_funcCubeOK3 (w s i : Nat) :
    funcCubeOK (iSeam w) (iSeamSurf w) s i 0 3 = true := by
  unfold funcCubeOK
  rw [iSeam_iParity3, iSeam_jParity3, iSeam_allOrNoneI3, iSeam_allOrNoneJ3]
  by_cases hiw : i < w
  · rw [show (iSeam w).hasK i 0 3 = true by simp only [LaSre.hasK, iSeam_ExistK3]; simp [hiw]]
    rw [if_neg (show ¬((iSeam w).YCube i 0 3 = true) by rw [iSeam_YCube]; simp)]
    rw [if_neg (show ¬((iSeam w).degree i 0 3 ≤ 1) by
      simp only [LaSre.degree, iSeam_ExistK3, iSeam_ExistI, iSeam_ExistJ,
        show (3 : Nat) - 1 = 2 from rfl, iSeam_ExistK2]; simp [hiw])]
    simp
  · rw [if_neg (show ¬((iSeam w).YCube i 0 3 = true) by rw [iSeam_YCube]; simp),
      if_pos (show (iSeam w).degree i 0 3 ≤ 1 by
        simp only [LaSre.degree, iSeam_ExistK3, iSeam_ExistI, iSeam_ExistJ,
          show (3 : Nat) - 1 = 2 from rfl, iSeam_ExistK2]; simp [hiw])]

theorem idle_refFunc_sym (w : Nat) :
    weldInterfaceOK2 3 (idleMerge w) (idleMerge w) (idleSurf w) (idleSurf w)
      (zChainConn w) (w + 1) w 1 = true := by
  rw [weldInterfaceOK2, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j hj
  have hj0 : j = 0 := by have := List.mem_range.1 hj; omega
  subst hj0
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [if_pos (by norm_num)]; exact iSeam_funcCubeOK2 w s i
  · exact iSeam_funcCubeOK3 w s i

/-! ## §DEMO.  The heterogeneous chain [zMerge, idleMerge, zMerge], directly. -/

theorem zidz_chainOK (w : Nat) :
    chainOK 3 (w + 1) (zChainConn w) w 1
      [zMerge w, idleMerge w, zMerge w]
      [zMergeSurf w, idleSurf w, zMergeSurf w] = true := by
  -- second link: head = idle, neighbour = z ; tail = [z]
  have link2 : chainOK 3 (w + 1) (zChainConn w) w 1
      (idleMerge w :: [zMerge w]) (idleSurf w :: [zMergeSurf w]) = true := by
    rw [show (idleMerge w :: [zMerge w]) = (idleMerge w :: zMerge w :: []) from rfl,
        show (idleSurf w :: [zMergeSurf w]) = (idleSurf w :: [zMergeSurf w]) from rfl]
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, idle_valid w⟩, idle_funcOK w (w + 1)⟩, ?_⟩, ?_⟩,
      ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, zMerge_valid w⟩, zMerge_funcOK w (w + 1)⟩⟩
    · rw [chain_validInterface_reduce_to_self (by norm_num) (zMerge w) []
            (idle_zMerge_botEqL w).symm]
      exact idle_refValid_sym w
    · rw [chain_interface_reduce_to_self (by norm_num) (zMerge w) [] (zMergeSurf w) []
            (idle_zMerge_botEqL w).symm (idle_zMerge_botEqS w).symm]
      exact idle_refFunc_sym w
  -- first link: head = z, neighbour = idle ; tail = [idle, z]
  show chainOK 3 (w + 1) (zChainConn w) w 1
      (zMerge w :: idleMerge w :: [zMerge w])
      (zMergeSurf w :: [idleSurf w, zMergeSurf w]) = true
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, zMerge_valid w⟩, zMerge_funcOK w (w + 1)⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [chain_validInterface_reduce_to_self (by norm_num) (idleMerge w) [zMerge w]
          (idle_zMerge_botEqL w)]
    exact zMerge_refValid_sym w
  · rw [chain_interface_reduce_to_self (by norm_num) (idleMerge w) [zMerge w]
          (idleSurf w) [zMergeSurf w] (idle_zMerge_botEqL w) (idle_zMerge_botEqS w)]
    exact zMerge_refFunc_sym w
  · simpa only [chainOK, Bool.and_eq_true, beq_iff_eq] using link2

/-- **★ HETEROGENEOUS INTERIOR CORRECTNESS (∀w) ★** — the welded
[Z̄-merge ; idle ; Z̄-merge] heterogeneous program is structurally valid AND
satisfies the interior functionality across every weld seam, for ALL widths `w`,
with NO native_decide.  Obtained from `chainOK_sound` fed the hetero `chainOK`. -/
theorem zidz_LaSCorrect (w : Nat) :
    LaSCorrect
      (weldChain 3 (zChainConn w) [zMerge w, idleMerge w, zMerge w])
      (weldChainSurf 3 [zMergeSurf w, idleSurf w, zMergeSurf w]) (w + 1) = true := by
  obtain ⟨hv, hf, _, _⟩ :=
    chainOK_sound 3 (w + 1) (zChainConn w) w 1
      [zMerge w, idleMerge w, zMerge w] [zMergeSurf w, idleSurf w, zMergeSurf w]
      (zidz_chainOK w)
  rw [LaSre.LaSCorrect, hv, hf]; rfl

/-! ## §GENERIC.  The catalog kind-list builder — chainOK for ANY sequence. -/

/-- The catalog entry: pick gadget / surface / a CANONICAL-bottom witness against
the reference `g0`, plus per-gadget self-interface certs.  A `CatalogEntry w g0
s0` packages everything the generic builder needs of one catalog gadget. -/
structure CatalogEntry (w : Nat) (g0 : LaSre) (s0 : Surf) where
  g : LaSre
  sg : Surf
  hi : g.maxI = w
  hj : g.maxJ = 1
  hk : g.maxK = 3
  hv : g.valid = true
  hf : g.funcOK sg (w + 1) = true
  -- canonical bottom: this gadget agrees with the reference g0/s0 at layer 0
  hbL : BotEqL g g0
  hbS : BotEqS sg s0
  -- this gadget's OWN self-interface certs
  rfv : weldInterfaceValidOK2 3 g g (zChainConn w) w 1 = true
  rff : weldInterfaceOK2 3 g g sg sg (zChainConn w) (w + 1) w 1 = true

/-- The merge catalog kind at width `w` (reference = zMerge w / zMergeSurf w). -/
def zEntry (w : Nat) : CatalogEntry w (zMerge w) (zMergeSurf w) :=
  { g := zMerge w, sg := zMergeSurf w
    hi := rfl, hj := rfl, hk := rfl
    hv := zMerge_valid w, hf := zMerge_funcOK w (w + 1)
    hbL := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    hbS := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
            fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    rfv := zMerge_refValid_sym w, rff := zMerge_refFunc_sym w }

/-- The idle catalog kind at width `w`. -/
def iEntry (w : Nat) : CatalogEntry w (zMerge w) (zMergeSurf w) :=
  { g := idleMerge w, sg := idleSurf w
    hi := rfl, hj := rfl, hk := rfl
    hv := idle_valid w, hf := idle_funcOK w (w + 1)
    hbL := idle_zMerge_botEqL w
    hbS := idle_zMerge_botEqS w
    rfv := idle_refValid_sym w, rff := idle_refFunc_sym w }

/-- Pick the catalog entry for a kind bit (`true` = merge, `false` = idle). -/
def kindEntry (w : Nat) (b : Bool) : CatalogEntry w (zMerge w) (zMergeSurf w) :=
  if b then zEntry w else iEntry w

/-- **★ THE GENERIC CATALOG-CHAIN BUILDER ★** — for ANY nonempty list of catalog
entries (all canonical-bottom against the same reference `g0/s0`), the welded
chain passes `chainOK`, by induction on the list, each interface discharged by
the transport-to-self lemma (reducing to the head's own self-cert).  NO
native_decide, NO per-pair cross certs. -/
theorem catalog_chainOK (w : Nat) (g0 : LaSre) (s0 : Surf) :
    ∀ (es : List (CatalogEntry w g0 s0)), es ≠ [] →
      chainOK 3 (w + 1) (zChainConn w) w 1 (es.map (·.g)) (es.map (·.sg)) = true := by
  intro es
  induction es with
  | nil => intro h; exact absurd rfl h
  | cons e rest ih =>
    intro _
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil, chainOK, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨e.hi, e.hj⟩, e.hk⟩, e.hv⟩, e.hf⟩
    | cons e2 rest' =>
      simp only [List.map_cons, chainOK, Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨⟨⟨⟨e.hi, e.hj⟩, e.hk⟩, e.hv⟩, e.hf⟩, ?_⟩, ?_⟩, ?_⟩
      · -- validInterface: e vs weldChain (e2 :: rest'); reduce to e's self-cert
        rw [show (rest'.map (·.g)) = (rest'.map (·.g)) from rfl,
            chain_validInterface_reduce_to_self (by norm_num) e2.g (rest'.map (·.g))
              (e2.hbL.trans e.hbL.symm)]
        exact e.rfv
      · -- funcInterface: reduce to e's self-cert
        rw [chain_interface_reduce_to_self (by norm_num) e2.g (rest'.map (·.g))
              e2.sg (rest'.map (·.sg)) (e2.hbL.trans e.hbL.symm) (e2.hbS.trans e.hbS.symm)]
        exact e.rff
      · -- recurse on the tail
        have := ih (by simp)
        simpa only [List.map_cons, chainOK, Bool.and_eq_true, beq_iff_eq] using this

/-- **★ chainOK FOR ANY KIND-SEQUENCE ★** — for any `ks : List Bool` (true = merge,
false = idle), the welded catalog chain passes `chainOK`, for ALL widths `w`. -/
theorem kindChain_chainOK (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    chainOK 3 (w + 1) (zChainConn w) w 1
      ((ks.map (kindEntry w)).map (·.g)) ((ks.map (kindEntry w)).map (·.sg)) = true :=
  catalog_chainOK w (zMerge w) (zMergeSurf w) (ks.map (kindEntry w))
    (by simpa using hk)

/-- **★ INTERIOR CORRECTNESS FOR ANY KIND-SEQUENCE (∀w) ★** — the welded catalog
chain for any merge/idle sequence `ks` is structurally valid AND satisfies the
interior functionality across every weld seam, for ALL widths `w`.  The true
"any sequence over the catalog" theorem — NO native_decide over `w` OR the chain
length/composition. -/
theorem kindChain_LaSCorrect (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    LaSCorrect
      (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g)))
      (weldChainSurf 3 ((ks.map (kindEntry w)).map (·.sg))) (w + 1) = true := by
  obtain ⟨hv, hf, _, _⟩ :=
    chainOK_sound 3 (w + 1) (zChainConn w) w 1
      ((ks.map (kindEntry w)).map (·.g)) ((ks.map (kindEntry w)).map (·.sg))
      (kindChain_chainOK w ks hk)
  rw [LaSre.LaSCorrect, hv, hf]; rfl

end FormalRV.QEC.LaSre
