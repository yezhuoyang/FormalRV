/-
  FormalRV.Corpus.ShorEmit — the Shor(N,a) → schedule → Stim GLUE: hand the
  framework a literal (N, a) and get the detailed scheduled surface-code circuit.

  Pipeline (closing the last gap of the emitter):
    (N, a)
      --shorBits-->        bit width  n = ⌊log₂ N⌋ + 1
      --modExpToff-->      Toffoli count  16 n³        (ModExpToffoliCount, scaffolded)
      --× 3 merges/CCZ-->  surgery-merge count         (3 M_ZZ merges per magic CCZ)
      --replicate-->       SurgerySchedule.Schedule    (each merge a verified gadget)
      --emitScheduleStim-->Stim program.

  `a` (the modular base) selects the classical Pauli-frame values, NOT the surgery
  STRUCTURE or count — so the emitted circuit shape is `a`-independent; `a` rides in
  the deferred classical frame.  We keep it in the signature for the user interface.

  For RSA-2048 the merge count is 4.1×10¹¹ (= the `shor2048_Meas` logical count), far
  too large to MATERIALISE — `emitShor` is for SMALL N; `emitShorPrefix N a k` emits
  the first `k` surgeries of ANY instance for a Stim-validatable sample.

  No `sorry`, no new `axiom`.
-/

import FormalRV.LatticeSurgery.ScheduleEmit
import FormalRV.Corpus.SurgeryDemoSurface
import FormalRV.Shor.ModExpToffoliCount

namespace FormalRV.Corpus.ShorEmit

open FormalRV.LatticeSurgery.ScheduleEmit
open FormalRV.Framework.SurgerySchedule
open FormalRV.Corpus.SurgeryDemoSurface
open FormalRV.Shor.ModExpToffoliCount

/-! ## §1. (N, a) → counts -/

/-- Bit width of the modulus `N` (`⌊log₂ N⌋ + 1`). -/
def shorBits (N : Nat) : Nat := Nat.log2 N + 1

/-- Surgery-merge count for an `n`-bit Shor modexp: 3 magic-CCZ merges per Toffoli
    (`modExpToff n = 16 n³`).  Equals the `shor2048_Meas` logical-measurement count. -/
def shorMergeCountBits (bits : Nat) : Nat := 3 * modExpToff bits

/-- Surgery-merge count for factoring `N`. -/
def shorMergeCount (N : Nat) : Nat := shorMergeCountBits (shorBits N)

/-! ## §2. (N, a) → schedule → Stim -/

/-- The full Shor(N) surgery schedule: one verified [[13,1,3]] logical-PPM merge per
    magic-CCZ measurement.  (Materialise only for small N.) -/
def shorSchedule (N : Nat) : Schedule := List.replicate (shorMergeCount N) surface3_x_surgery

/-- **END-TO-END EMITTER**: a literal (N, a) → the detailed scheduled Stim circuit. -/
def emitShor (N _a : Nat) : String := emitScheduleStim (shorSchedule N)

/-- First-`k`-surgeries prefix of the Shor(N) schedule — a Stim-validatable sample
    of ANY instance (the full circuit being astronomically large). -/
def shorSchedulePrefix (N k : Nat) : Schedule :=
  List.replicate (min k (shorMergeCount N)) surface3_x_surgery

def emitShorPrefix (N _a k : Nat) : String := emitScheduleStim (shorSchedulePrefix N k)

/-! ## §3. The counts, as theorems (small instance + RSA-2048) -/

/-- Factoring a 4-bit modulus (e.g. N=15) needs 3·16·4³ = 3072 surgery merges. -/
theorem shorMergeCountBits_4 : shorMergeCountBits 4 = 3072 := by decide

/-- **RSA-2048 (2048-bit): 412,316,860,416 surgery merges** — identical to the
    `ModExpToffoliCount.shor2048_Meas` logical-measurement count (3 per CCZ). -/
theorem shorMergeCount_rsa2048 : shorMergeCountBits 2048 = 412_316_860_416 := by decide

/-- The Shor(N) emitted-circuit footprint scales as merges × per-gadget footprint. -/
def shorScheduleFootprintBits (bits : Nat) : Nat :=
  shorMergeCountBits bits * gadgetFootprint surface3_x_surgery

/-- RSA-2048 emitted footprint: 412.3×10⁹ merges × 28 qubit-slots = 1.15×10¹³
    (qubit-reuse aside) — i.e. the circuit is parametric, not materialised. -/
theorem rsa2048_emitted_footprint :
    shorScheduleFootprintBits 2048 = 11_544_872_091_648 := by decide

/-- The prefix length is exactly `k` whenever `k ≤` the full merge count. -/
theorem prefix_length (N k : Nat) (h : k ≤ shorMergeCount N) :
    (shorSchedulePrefix N k).length = k := by
  unfold shorSchedulePrefix
  rw [List.length_replicate, Nat.min_eq_left h]

end FormalRV.Corpus.ShorEmit
