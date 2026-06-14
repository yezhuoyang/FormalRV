/-
  FormalRV.Shor.CosetEigenstate.CosetLayoutTransport — option (ii): the layout-conjugation
  transport principle (interleaved ↔ contiguous via a relabeling permutation).
  ════════════════════════════════════════════════════════════════════════════

  The cuccaro target is INTERLEAVED, so the gate is not GLOBAL `+c`.  Option (ii) is a
  LAYOUT RELABELING: a permutation `L` that gathers the interleaved target bits into a
  contiguous value register; conjugating the gate by `L` gives `+c` on the contiguous
  target, where the `GateAddConstBridge` / `cosetState` machinery applies; the result is
  then transported back through `L`.

  THE TRANSPORT PRINCIPLE (proven here, reusable):  if the literal gate action `gAct`
  applied to the L-transported coset state is the L-transported contiguous wrapping add
  `wrapShiftState c` (the `hconj` hypothesis), then on the L-transported coset state,
  `gAct` acts as the coset `addConst` shift:

      gAct (permState L (cosetState N m k)) = permState L (cosetState N m (k+c))    (off fit).

  Here `permState L (cosetState …)` is the coset state RELAID OUT into the physical
  (interleaved) layout.  So this IS the target deliverable's shape — the literal gate
  acting as `addConst` on the interleaved-target coset state — MODULO the single
  hypothesis `hconj`.

  ⚠ WHY `hconj` IS SCOPED TO THE COSET STATE (a soundness point, not laziness).  A NAÏVE
  `∀ s, gAct (permState L s) = permState L (wrapShiftState c s)` is UNSATISFIABLE for
  cuccaro: the gate acts as `+c` only on the CLEAN-ANCILLA subspace (carry/read = 0),
  never on arbitrary `s` (on a dirty-ancilla basis state it does something else).  The
  coset state lives in the clean subspace, and the transport only ever needs `hconj`
  there — so `hconj` is stated at the coset-state instance, which IS dischargeable.  A
  blanket `∀ s` form would be vacuously useless (no cuccaro proof could supply it).

  ⚠ WHAT `hconj` REQUIRES FOR CUCCARO (honest — this is the remaining substantial work).
  Discharging `hconj` for `gAct := uc_eval (toUCom cuccaro_addConstGate) · ` needs:
    (1) DEFINE `L` — the qubit/value relabeling sending the interleaved target positions
        `q_start + 2i + 1` to contiguous low bits `0 .. bits-1`, read/carry/frame to
        explicit tracked positions (a SWAP network, à la `InPlace.swapReg` /
        `reverse_register_swap`);
    (2) PROVE the conjugation `uc_eval(cuccaro) ∘ permState L = permState L ∘ wrapShiftState c`
        on the clean-ancilla subspace, from `cuccaro_addConstGate_target_decode` (target
        `+c mod 2^bits`) + `cuccaro_addConstGate_read_decode` (read restored) + the carry
        restoration + the `L`-conjugation of `gateToPerm` (via `UCEvalBridge.uc_eval_eq_permState`).
  Step (2) is a multi-hundred-line layout proof (the interleaved encoding threaded through
  the SWAP relabeling).  It is the genuine remaining circuit obligation; the transport
  PRINCIPLE below reduces the whole connection to exactly that one hypothesis.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/
import FormalRV.Shor.CosetEigenstate.ApproxOp

namespace FormalRV.Shor.CosetEigenstate.CosetLayoutTransport

open FormalRV.SQIRPort
open FormalRV.Shor.CosetEigenstate.ApproxOp
  (permState cosetState wrapShiftState wrapShiftState_cosetState)

/-- **THE LAYOUT-CONJUGATION TRANSPORT PRINCIPLE.**  If the gate action `gAct` on the
    L-transported coset state equals the L-transported contiguous wrapping add
    `wrapShiftState c` (`hconj`, scoped to the coset state — see header), then on that
    L-transported coset state (the coset state laid out in the physical/interleaved
    register), `gAct` performs the coset `addConst` shift to `k+c`, under the per-window
    fit.  This is the target gate-acts-as-addConst-on-the-interleaved-target-coset-state
    theorem, reduced to the single layout-conjugation hypothesis `hconj`. -/
theorem cosetState_layout_transport {dim : Nat} (L : Equiv.Perm (Fin dim))
    (gAct : QState dim → QState dim) (c N m k : Nat)
    (hconj : gAct (permState L (cosetState dim N m k))
      = permState L (wrapShiftState dim c (cosetState dim N m k)))
    (hN : 0 < N) (hfit : k + c + (2 ^ m - 1) * N < dim) :
    gAct (permState L (cosetState dim N m k)) = permState L (cosetState dim N m (k + c)) := by
  rw [hconj, wrapShiftState_cosetState dim N m k c hN hfit]

/-- The conjugation hypothesis is INVARIANT under the off-bad coset agreement: relaying
    out a coset agreement by `L` and applying `gAct` preserves it (`permState L` is a
    basis permutation, so it acts entrywise).  This lets the windowed-fold off-bad
    agreement (`CosetFoldWindowed`) transport through the layout unchanged. -/
theorem permState_agree_off {dim : Nat} (L : Equiv.Perm (Fin dim))
    (s₁ s₂ : QState dim) (B : Finset (Fin dim))
    (hagree : ∀ i, i ∉ B → s₁ i 0 = s₂ i 0) :
    ∀ i, i ∉ B.map L.symm.toEmbedding → permState L s₁ i 0 = permState L s₂ i 0 := by
  intro i hi
  show s₁ (L i) 0 = s₂ (L i) 0
  refine hagree (L i) ?_
  intro hmem
  exact hi (Finset.mem_map.mpr ⟨L i, hmem, by simp⟩)

end FormalRV.Shor.CosetEigenstate.CosetLayoutTransport
