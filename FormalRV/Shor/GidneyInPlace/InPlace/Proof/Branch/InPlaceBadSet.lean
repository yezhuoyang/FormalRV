/-
  FormalRV.Shor.GidneyInPlace.InPlaceBadSet
  ─────────────────────────────────────────────
  The BAD SET for the two windowed product-add legs that underlie the two-register
  Gidney in-place coset multiplier (`GidneyTwoRegInPlace.gidneyTwoRegInPlaceCosetMul`),
  plus its Born-mass DOUBLING bound.  DEFINITION + mass bound ONLY (this checkpoint).

  The in-place multiply runs two windowed product-adds: forward `b += a·k`, then the
  uncompute leg `a -= b·kInv`.  Each leg's COSET-level (mod-`N`) canonical identity can
  fail on a finite "wrap" band of register branch indices — the symmetric-difference
  set `CosetFoldWindowed.cosetState_windowedMul_embed_off` isolates, where the coset
  state of the UNREDUCED windowed running sum differs from the coset state of the
  canonical residue product.  The in-place bad set is the UNION of the two legs' wrap
  bands; its Born mass is at most `2·numWin/2^cm` (the per-leg `numWin/2^cm`, doubled
  by `bornWeightOn_union_le` subadditivity).

  ════════════════════════════════════════════════════════════════════════════
  WHAT IS PROVEN HERE (kernel-clean, no `sorry`/`native_decide`/extra axioms):
   • `inplaceBadSet := Bfwd ∪ Brev` — a plain `Finset (Fin (2^bits))` over REGISTER
     branch indices (the data-factor index space `branchOfE`/`e_gate` projects onto).
   • `inplaceBadSet_mass_le` — the doubling: GIVEN each leg's wrap mass `≤ numWin/2^cm`
     on a COMMON data state `s`, the union carries `≤ 2·numWin/2^cm`.  (Conditional on
     the two per-leg hypotheses — see the fence below.)
   • `revCanonical_eq` — the reverse-leg arithmetic `(kInv·((k·x)%N))%N = x` from
     `kInv·k ≡ 1 [MOD N]` and `x < N`.
   • `inplaceBadSet_coupled_exists` — the FAITHFUL assembly: the reverse leg is chained
     at the forward output `(k·x)%N`, so its wrap band's canonical state is the INPUT
     residue's coset `cosetState x`; both legs' concrete wrap bands, their agreements,
     each leg's `≤ numWin/2^cm`, and the conditional doubling.

  ════════════════════════════════════════════════════════════════════════════
  NOT PROVEN HERE — explicit deferred obligations (do NOT read the docstrings as
  claiming these; the bad set is the COSET-level wrap band only):
   (D1) GATE DYNAMICS.  Nothing here runs `gidneyTwoRegInPlaceCosetMul` (or its
        `pass1`/`reverse pass2`) on a coset state.  The wrap bands are STATIC facts
        about `cosetState` equalities (`cosetState_windowedMul_embed_off`), not about
        `uc_eval` of the gate.  This file imports only `CosetFoldWindowed`; it never
        references the gate, `good_branch`, or `hInvSum_specialized_basis`.
   (D2) BASIS↔COSET BRIDGE.  `good_branch` (`gidneyTwoRegInPlace_coset_basis_good_branch`)
        consumes BASIS-level (`% 2^bits`) value hypotheses `hP1`/`hS2N`/`hS2nowrap`/
        `hkkinv`; the wrap band is a COSET-level (mod-`N`) `cosetState` symmetric
        difference.  Relating "off the wrap band" to "good_branch's hypotheses hold"
        is the deferred basis↔coset bridge — NOT established here.  In particular the
        table-sum/window value identity is a PRECONDITION of the per-leg lemma
        (`idealAcc_cosetWindowConst`, assumed), so a table-sum FAILURE is NOT in the
        bad set; only the wrap (the `q·N` running-sum offset) is.
   (D3) COMMON-STATE REALIZATION.  The two per-leg masses are proven on DIFFERENT
        coset states (forward on `cosetState ((k·x)%N)`, reverse on `cosetState x`).
        No single `s` is yet exhibited carrying BOTH `≤ numWin/2^cm`; the doubling is
        therefore CONDITIONAL until the dynamics (D1) transports the input coset state
        through both legs.
   (D4) FORWARD↦REVERSE SEMANTICS.  The actual uncompute leg is `Gate.reverse pass2`
        (a subtraction, pinned by `gidneyTwoReg_reverse_leg_cancel`); here the reverse
        wrap band is modelled by the FORWARD windowed multiplier at multiplier `kInv`.
        Transporting the forward embedding to the reversed product-add is deferred.
   (D5) REGISTER IDENTIFICATION.  Compatibility with the contract space
        `Fin (2^(n+anc))` (`InPlaceCosetSpec`, which itself defers the `2^bits ≅
        2^(n+anc)` iso) is structural here (a phase-free `Finset (Fin (2^bits))`), not
        a discharged isomorphism.
   (D6) RATE RECONCILIATION.  The eventual target `inplaceReducedLookupCosetMul_shift`
        is stated at the TIGHTER `numWin/2^cm`; this checkpoint's `2·numWin/2^cm`
        (the user-authorized target) leaves a factor-2 to re-absorb (cm offset, spec
        loosening, or a tighter shared-band union) downstream.

  Audit constraints MET: the bad set is over actual register branch indices (a
  `Finset (Fin (2^bits))`, NOT decoded residues), phase-independent (no control/phase
  data), and shape-compatible with the later `branchOfE`/`e_gate` data factor.  The
  "do not sum over the cosetState" and "do not prove `inplaceReducedLookupCosetMul_shift`"
  constraints are respected.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.GidneyInPlace.OutOfPlaceCoset.Proof.CosetFoldWindowed

namespace FormalRV.Shor.GidneyInPlace.InPlaceBadSet

open FormalRV.SQIRPort
open FormalRV.Shor.CosetBornWeight (bornWeightOn bornWeightOn_union_le)
open FormalRV.Shor.GidneyInPlace.ApproxOp (cosetState)
open FormalRV.Shor.GidneyInPlace.CosetMul (runningSum)
open FormalRV.Shor.GidneyInPlace.CosetTableSum (cosetWindowConst)
open FormalRV.Shor.GidneyInPlace.CosetFoldWindowed (cosetState_windowedMul_embed_off)

/-! ## §1. The bad set: union of the two legs' coset-level wrap bands. -/

/-- **The two-register in-place bad set.**  The UNION of the forward-leg wrap band
    `Bfwd` (`b += a·k`) and the reverse-leg wrap band `Brev` (`a -= b·kInv`), as a
    finite set of register branch indices.  Each `B*` is a coset-level (mod-`N`)
    symmetric-difference band (where the unreduced running-sum coset state differs
    from the canonical-residue coset state); see the file fence (D2) for what this does
    and does NOT capture relative to `good_branch`.  Phase-independent (a plain
    `Finset (Fin dim)`, no control/phase data) and shape-compatible with the
    `branchOfE`/`e_gate` data factor (`dim = 2^bits`). -/
def inplaceBadSet {dim : Nat} (Bfwd Brev : Finset (Fin dim)) : Finset (Fin dim) :=
  Bfwd ∪ Brev

/-! ## §2. The Born-mass doubling (CONDITIONAL on the two per-leg bounds — see D3). -/

/-- **Born mass of the in-place bad set ≤ 2·numWin/2^cm.**  If a data state `s`
    carries EACH leg's wrap mass ≤ numWin/2^cm, the union bad set carries
    ≤ 2·numWin/2^cm — the per-leg bound doubled, via `bornWeightOn_union_le`.

    This is CONDITIONAL: `hfwd`/`hrev` are supplied as hypotheses about a common `s`.
    The two per-leg bounds that the wrap lemma actually proves live on DIFFERENT coset
    states (D3); realizing both on one input coset state is the deferred dynamics
    (D1).  So this lemma is the doubling ENGINE, not yet an unconditional bound. -/
theorem inplaceBadSet_mass_le {dim : Nat} (s : QState dim)
    (Bfwd Brev : Finset (Fin dim)) (numWin cm : Nat)
    (hfwd : bornWeightOn s Bfwd ≤ (numWin : ℝ) / 2 ^ cm)
    (hrev : bornWeightOn s Brev ≤ (numWin : ℝ) / 2 ^ cm) :
    bornWeightOn s (inplaceBadSet Bfwd Brev) ≤ 2 * ((numWin : ℝ) / 2 ^ cm) := by
  unfold inplaceBadSet
  calc bornWeightOn s (Bfwd ∪ Brev)
      ≤ bornWeightOn s Bfwd + bornWeightOn s Brev := bornWeightOn_union_le s Bfwd Brev
    _ ≤ (numWin : ℝ) / 2 ^ cm + (numWin : ℝ) / 2 ^ cm := add_le_add hfwd hrev
    _ = 2 * ((numWin : ℝ) / 2 ^ cm) := by ring

/-! ## §3. The reverse-leg arithmetic: chained at `(k·x)%N`, it returns the input. -/

/-- **The reverse leg's canonical output is the input residue.**  With the reverse
    leg fed the forward output `(k·x)%N` and `kInv·k ≡ 1 [MOD N]`, the canonical
    residue product `(kInv·((k·x)%N))%N` equals `x` (for `x < N`).  This is what lets
    the reverse leg's wrap mass land on `cosetState x` (the input residue's coset). -/
theorem revCanonical_eq (N k kInv x : Nat) (hxN : x < N)
    (hkkinv : (kInv * k) % N = 1 % N) :
    (kInv * ((k * x) % N)) % N = x := by
  have hkk : (kInv * k) ≡ 1 [MOD N] := hkkinv
  have h1 : kInv * ((k * x) % N) ≡ kInv * (k * x) [MOD N] :=
    (Nat.mod_modEq (k * x) N).mul_left kInv
  have h4 : kInv * (k * x) ≡ x [MOD N] := by
    calc kInv * (k * x) = (kInv * k) * x := by ring
      _ ≡ 1 * x [MOD N] := hkk.mul_right x
      _ = x := one_mul x
  have hchain : (kInv * ((k * x) % N)) % N = x % N := h1.trans h4
  rw [hchain, Nat.mod_eq_of_lt hxN]

/-! ## §4. The faithful assembled bad set, with the legs CHAINED. -/

/-- **The two-register in-place bad set, assembled with the legs chained.**
    Instantiating `cosetState_windowedMul_embed_off` at the forward leg (multiplier
    `k`, input residue `x`) and the reverse leg (multiplier `kInv`, input `(k·x)%N` —
    the forward OUTPUT, the faithful chaining) yields concrete wrap bands `Bfwd`,
    `Brev : Finset (Fin (2^bits))` such that:
      • off `Bfwd`, the forward leg's running-sum coset = `cosetState ((k·x)%N)`, with
        wrap mass ≤ numWin/2^cm on `cosetState ((k·x)%N)` (the intermediate);
      • off `Brev`, the reverse leg's running-sum coset = `cosetState x` (via
        `revCanonical_eq`), with wrap mass ≤ numWin/2^cm on `cosetState x` (the INPUT
        residue's coset);
      • on ANY common state `s` carrying both per-leg bounds, the union bad set
        `inplaceBadSet Bfwd Brev` has mass ≤ 2·numWin/2^cm (the conditional doubling).

    The two leg masses sit on DIFFERENT coset states (`cosetState ((k·x)%N)` vs
    `cosetState x`); realizing both on the single input state via the gate dynamics is
    deferred (D1/D3).  `hkxFit` is the reverse leg's windowing bound on its chained
    input.  This file proves the COSET-level embedding only — NOT that off the bad set
    the gate is correct (which also needs D1/D2/D4 and `good_branch`'s `hP1`/`hS2N`). -/
theorem inplaceBadSet_coupled_exists (bits N cm k kInv w numWin x : Nat)
    (hN : 0 < N) (hxN : x < N) (hx : x < (2 ^ w) ^ numWin)
    (hkxFit : (k * x) % N < (2 ^ w) ^ numWin)
    (hkkinv : (kInv * k) % N = 1 % N) :
    ∃ Bfwd Brev : Finset (Fin (2 ^ bits)),
      -- forward leg `b += a·k`, input residue `x`
      (∀ i, i ∉ Bfwd →
        cosetState (2 ^ bits) N cm (runningSum (cosetWindowConst k N w x) numWin) i 0
          = cosetState (2 ^ bits) N cm ((k * x) % N) i 0)
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm ((k * x) % N)) Bfwd ≤ (numWin : ℝ) / 2 ^ cm
      -- reverse leg `a += b·kInv` at the chained input `(k·x)%N`; canonical out = `x`
      ∧ (∀ i, i ∉ Brev →
          cosetState (2 ^ bits) N cm
              (runningSum (cosetWindowConst kInv N w ((k * x) % N)) numWin) i 0
            = cosetState (2 ^ bits) N cm x i 0)
      ∧ bornWeightOn (cosetState (2 ^ bits) N cm x) Brev ≤ (numWin : ℝ) / 2 ^ cm
      -- the conditional doubling on any common state
      ∧ (∀ s : QState (2 ^ bits),
            bornWeightOn s Bfwd ≤ (numWin : ℝ) / 2 ^ cm →
            bornWeightOn s Brev ≤ (numWin : ℝ) / 2 ^ cm →
            bornWeightOn s (inplaceBadSet Bfwd Brev) ≤ 2 * ((numWin : ℝ) / 2 ^ cm)) := by
  obtain ⟨Bfwd, hf_agree, _hf_run, hf_out⟩ :=
    cosetState_windowedMul_embed_off (2 ^ bits) N cm k w numWin x hN hx
  obtain ⟨Brev, hr_agree, _hr_run, hr_out⟩ :=
    cosetState_windowedMul_embed_off (2 ^ bits) N cm kInv w numWin ((k * x) % N) hN hkxFit
  have hrev : (kInv * ((k * x) % N)) % N = x := revCanonical_eq N k kInv x hxN hkkinv
  refine ⟨Bfwd, Brev, hf_agree, hf_out, ?_, ?_,
          fun s hs1 hs2 => inplaceBadSet_mass_le s Bfwd Brev numWin cm hs1 hs2⟩
  · intro i hi
    have h := hr_agree i hi
    rwa [hrev] at h
  · have h := hr_out
    rwa [hrev] at h

end FormalRV.Shor.GidneyInPlace.InPlaceBadSet
