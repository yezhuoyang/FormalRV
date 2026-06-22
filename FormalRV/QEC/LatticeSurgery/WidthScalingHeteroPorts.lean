import FormalRV.QEC.LatticeSurgery.WidthScalingHetero

/-!
# Hetero ports + full `LaSCorrectFull` for ANY merge/idle sequence (∀w)

This module closes the ONLY remaining heterogeneous gap: PORTS and the full
`LaSCorrectFull` for an ARBITRARY merge/idle catalog sequence `ks : List Bool`,
at ALL widths `w`, with NO `native_decide` over `w` OR the chain length.

KEY INSIGHT.  Every catalog surface (`zMergeSurf w` AND `idleSurf w`) presents
the SAME k-INDEPENDENT canonical `KI`/`KJ` worldline (idle only zeroed the `IK`
seam piece).  So for `ss = a list of catalog surfaces`, `(weldChainSurf 3 ss).KI`
/`.KJ` at ANY layer `k` equals that canonical value — not just at the top layer.
Hence BOTH boundary reads (IN at `k=0`, OUT at `k=top`) trivially reduce to the
canonical value, and the ports proof becomes the SAME per-column X-passthrough
spec match as the single merge, at both boundaries.

Targets (∀w, ∀ ks : List Bool, NO native_decide):
  (1) Generic surface-canonicality (`KI`+`KJ`), by induction on the surface list.
  (1b) Each catalog surface is canonical (`KI`/`KJ` = `zMergeSurf`'s).
  (2)  Chain HEIGHT: `weldChain 3 _ gs |>.maxK = gs.length * 3`; `heteroTop ks`.
  (3)  `heteroStackPorts w ks` — IN ports at `k=0`, OUT ports at `k=heteroTop ks`.
  (4)  `kindChain_portsOK` — `portsOK` of the welded catalog surface at both
       boundaries vs `zMergePaulis w` (joint-Z flow 0, X passthrough flow s).
  (5)  HEADLINE `kindChain_LaSCorrectFull` — full `LaSCorrectFull` for ANY `ks`,
       ∀w, via `weldChain_LaSCorrectFull` + `kindChain_chainOK` + (4).

Axiom-clean (`{propext, Classical.choice, Quot.sound}`), zero `sorry`, zero
`native_decide`, genuinely heterogeneous (`∀ ks`, no specialization to one kind).
-/

namespace FormalRV.QEC.LaSre

/-! ## (1) Generic surface-canonicality (KI + KJ), induction on the list. -/

theorem weldChainSurf_KI_const (F : Nat → Nat → Nat → Nat → Bool)
    (hFk : ∀ t i j k, F t i j k = F t i j 0)
    (ss : List Surf) (hss : ss ≠ []) (hF : ∀ sg ∈ ss, sg.KI = F)
    (t i j k : Nat) :
    (weldChainSurf 3 ss).KI t i j k = F t i j 0 := by
  induction ss generalizing t i j k with
  | nil => exact absurd rfl hss
  | cons s rest ih =>
    cases rest with
    | nil =>
      have hs : s.KI = F := hF s (by simp)
      show s.KI t i j k = F t i j 0
      rw [hs, hFk]
    | cons s2 rest' =>
      show (weldSurf 3 s (weldChainSurf 3 (s2 :: rest')) (fun x => (x, x))).KI t i j k
        = F t i j 0
      simp only [weldSurf]
      by_cases hk : k < 3
      · rw [if_pos hk]
        have hs : s.KI = F := hF s (by simp)
        rw [hs, hFk]
      · rw [if_neg hk]
        exact ih (by simp) (fun sg hsg => hF sg (by simp [hsg])) t i j (k - 3)

theorem weldChainSurf_KJ_const (F : Nat → Nat → Nat → Nat → Bool)
    (hFk : ∀ t i j k, F t i j k = F t i j 0)
    (ss : List Surf) (hss : ss ≠ []) (hF : ∀ sg ∈ ss, sg.KJ = F)
    (t i j k : Nat) :
    (weldChainSurf 3 ss).KJ t i j k = F t i j 0 := by
  induction ss generalizing t i j k with
  | nil => exact absurd rfl hss
  | cons s rest ih =>
    cases rest with
    | nil =>
      have hs : s.KJ = F := hF s (by simp)
      show s.KJ t i j k = F t i j 0
      rw [hs, hFk]
    | cons s2 rest' =>
      show (weldSurf 3 s (weldChainSurf 3 (s2 :: rest')) (fun x => (x, x))).KJ t i j k
        = F t i j 0
      simp only [weldSurf]
      by_cases hk : k < 3
      · rw [if_pos hk]
        have hs : s.KJ = F := hF s (by simp)
        rw [hs, hFk]
      · rw [if_neg hk]
        exact ih (by simp) (fun sg hsg => hF sg (by simp [hsg])) t i j (k - 3)

/-! ## (1b) Each catalog surface is canonical (KI/KJ = zMergeSurf's). -/

theorem kindEntry_sg_KI (w : Nat) (b : Bool) :
    (kindEntry w b).sg.KI = (zMergeSurf w).KI := by cases b <;> rfl
theorem kindEntry_sg_KJ (w : Nat) (b : Bool) :
    (kindEntry w b).sg.KJ = (zMergeSurf w).KJ := by cases b <;> rfl

theorem kindChain_surfs_KI (w : Nat) (ks : List Bool) :
    ∀ sg ∈ (ks.map (kindEntry w)).map (·.sg), sg.KI = (zMergeSurf w).KI := by
  intro sg hsg
  simp only [List.mem_map] at hsg
  obtain ⟨e, he, rfl⟩ := hsg
  obtain ⟨b, _, rfl⟩ := he
  exact kindEntry_sg_KI w b

theorem kindChain_surfs_KJ (w : Nat) (ks : List Bool) :
    ∀ sg ∈ (ks.map (kindEntry w)).map (·.sg), sg.KJ = (zMergeSurf w).KJ := by
  intro sg hsg
  simp only [List.mem_map] at hsg
  obtain ⟨e, he, rfl⟩ := hsg
  obtain ⟨b, _, rfl⟩ := he
  exact kindEntry_sg_KJ w b

/-! ## (2) Chain HEIGHT lemma — weldChain maxK = len*3. -/

theorem weldChain_maxK_const (conn : List (Nat × Nat)) (gs : List LaSre)
    (hgs : gs ≠ []) (hg : ∀ g ∈ gs, g.maxK = 3) :
    (weldChain 3 conn gs).maxK = gs.length * 3 := by
  induction gs with
  | nil => exact absurd rfl hgs
  | cons g rest ih =>
    cases rest with
    | nil => show g.maxK = (1 : Nat) * 3; rw [hg g (by simp)]
    | cons g2 rest' =>
      show (weldK 3 g (weldChain 3 conn (g2 :: rest')) conn).maxK = _
      simp only [weldK]
      rw [ih (by simp) (fun gg hgg => hg gg (by simp [hgg]))]
      simp only [List.length_cons]; ring

theorem kindEntry_g_maxK (w : Nat) (b : Bool) : (kindEntry w b).g.maxK = 3 := by
  cases b <;> rfl

theorem kindChain_maxK (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g))).maxK = ks.length * 3 := by
  rw [weldChain_maxK_const]
  · simp only [List.length_map]
  · simp only [ne_eq, List.map_eq_nil_iff]; exact hk
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨e, he, rfl⟩ := hg
    obtain ⟨b, _, rfl⟩ := he
    exact kindEntry_g_maxK w b

abbrev heteroTop (ks : List Bool) : Nat := ks.length * 3 - 1

/-! ## (3) The ports. -/

def heteroStackPorts (w : Nat) (ks : List Bool) : List Port :=
  (List.range w).map (fun c => ⟨c, 0, 0, 4, 5⟩)
    ++ (List.range w).map (fun c => ⟨c, 0, heteroTop ks, 4, 5⟩)

theorem heteroStackPorts_get {w : Nat} {ks : List Bool} {p : Port} {idx : Nat}
    (h : (p, idx) ∈ (heteroStackPorts w ks).zipIdx) :
    p.pj = 0 ∧ p.blueSel = 4 ∧ p.redSel = 5 ∧ p.pi = idx % w ∧ p.pi < w
      ∧ (p.pk = 0 ∨ p.pk = heteroTop ks) := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  simp only [heteroStackPorts, List.getElem?_append, List.getElem?_map,
    List.length_map, List.length_range] at h
  by_cases hidx : idx < w
  · rw [if_pos hidx, List.getElem?_eq_getElem (by simp [hidx]), List.getElem_range,
      Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, (Nat.mod_eq_of_lt hidx).symm, hidx, Or.inl rfl⟩
  · rw [if_neg hidx] at h
    by_cases hidx2 : idx - w < w
    · rw [List.getElem?_eq_getElem (by simp [hidx2]), List.getElem_range,
        Option.map_some, Option.some.injEq] at h
      subst h
      have hmod : idx % w = idx - w := by
        conv_lhs => rw [show idx = (idx - w) + w from by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hidx2]
      exact ⟨rfl, rfl, rfl, hmod.symm, hidx2, Or.inr rfl⟩
    · exfalso
      rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)] at h
      simp at h

/-! ## (4) The ports proof. -/

theorem kindChain_portsOK (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    portsOK (weldChainSurf 3 ((ks.map (kindEntry w)).map (·.sg)))
      (heteroStackPorts w ks) (zMergePaulis w) (w + 1) = true := by
  have hne : ((ks.map (kindEntry w)).map (·.sg)) ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff]; exact hk
  have hKI : ∀ t i j k,
      (weldChainSurf 3 ((ks.map (kindEntry w)).map (·.sg))).KI t i j k
        = (zMergeSurf w).KI t i j 0 :=
    fun t i j k => weldChainSurf_KI_const (zMergeSurf w).KI (fun _ _ _ _ => rfl)
      _ hne (kindChain_surfs_KI w ks) t i j k
  have hKJ : ∀ t i j k,
      (weldChainSurf 3 ((ks.map (kindEntry w)).map (·.sg))).KJ t i j k
        = (zMergeSurf w).KJ t i j 0 :=
    fun t i j k => weldChainSurf_KJ_const (zMergeSurf w).KJ (fun _ _ _ _ => rfl)
      _ hne (kindChain_surfs_KJ w ks) t i j k
  rw [portsOK, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro pp hpp
  obtain ⟨p, idx⟩ := pp
  obtain ⟨hpj, hbl, hrd, hpi, hlt, _hpk⟩ := heteroStackPorts_get hpp
  have hw : 0 < w := by omega
  have hmw : idx % w < w := Nat.mod_lt _ hw
  simp only [Surf.sel, hbl, hrd, hpj, hpi]
  rw [hKI s (idx % w) 0 p.pk, hKJ s (idx % w) 0 p.pk]
  simp only [zMergeSurf, zMergePaulis, portBlue, portRed]
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp [hmw]
  · have hs0 : ¬ s = 0 := by omega
    by_cases hc : s - 1 = idx % w
    · have hsw : s ≤ w := by omega
      simp [hs0, hc, hmw, hsw]
      omega
    · simp [hs0, hc, hmw]

/-! ## (5) HEADLINE — full LaSCorrectFull for ANY merge/idle sequence, ∀w.
     NOTE: tactic-mode `apply` is REQUIRED; term-mode `:=` heartbeat-times-out. -/

theorem kindChain_LaSCorrectFull (w : Nat) (ks : List Bool) (hk : ks ≠ []) :
    LaSCorrectFull
      (weldChain 3 (zChainConn w) ((ks.map (kindEntry w)).map (·.g)))
      (weldChainSurf 3 ((ks.map (kindEntry w)).map (·.sg)))
      (heteroStackPorts w ks) (zMergePaulis w) (w + 1) = true := by
  apply weldChain_LaSCorrectFull 3 (w + 1) (zChainConn w) w 1
    ((ks.map (kindEntry w)).map (·.g)) ((ks.map (kindEntry w)).map (·.sg))
    (heteroStackPorts w ks) (zMergePaulis w)
  · exact kindChain_chainOK w ks hk
  · exact kindChain_portsOK w ks hk

end FormalRV.QEC.LaSre
