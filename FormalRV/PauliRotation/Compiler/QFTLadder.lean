/-
  FormalRV.PauliRotation.Compiler.QFTLadder
  ────────────────────────────────
  QFT / QPE in the rotation IR — the HONEST boundary.

  The inverse-QFT ladder rotation at distance `m = j − t` is
  `controlled_Rz j t (−π/2^m)`, whose constituent single-qubit rotations
  have full angle `π/2^(m+2)`: exactly Clifford+T iff `m ≤ 1` — the SAME
  boundary the repo's actual Clifford+T compiler proves
  (`QFT/AQFTCompile.lean: compileLadder_isCliffordT`, cutoff ≤ 2), with the
  dropped `m ≥ 2` tail carrying the DERIVED approximation budget
  (`compileLadder_error_budget`).  So what compiles EXACTLY into the
  four-angle rotation IR is the banded (cutoff-2) inverse QFT:

    • each kept ladder gate (m = 1, the controlled-S† of adjacent pairs)
      is THREE Z-type π/8 rotations — all-Z, hence ONE commuting layer;
    • the Hadamards are the dictionary's three π/4 rotations;
    • the bit-reversal SWAPs are Clifford (9 π/4 rotations each).

  QPE then assembles as: H-layer ++ oracle (any Gate-IR modexp, via
  `GateBridge.gateRots` — exact) ++ banded inverse QFT, and its rotation
  T-count is `Gate.tcount oracle + 3·(k−1)` (`qpeSchedule_gate_countPi8`).

  HONESTY: (1) rotations with `m ≥ 2` are NOT expressible at the four
  discrete angles — they require Clifford+T synthesis; this file compiles
  the SAME banded circuit the proven error budget is about, never the exact
  QFT.  (2) The correctness theorems here are the verified-optimizer leg
  (schedule = naive sequence); the dictionary leg (sequence = `uc_eval` of
  the BaseUCom circuit, up to global phase — including the CS† sign
  orientation) is the layer's known open item.
-/
import FormalRV.PauliRotation.Compiler.GateBridge

namespace FormalRV.PauliRotation

open FormalRV.PPM.Prog
open FormalRV.Framework (Gate)
open FormalRV.Resource

/-! ## §1. The kept ladder gate: controlled-S† as one commuting layer. -/

/-- The `m = 1` inverse-QFT ladder gate (controlled-S† on the adjacent pair
`(t+1, t)`) as its three Z-type π/8 rotations — pairwise commuting, hence
one parallel layer once scheduled. -/
def csDagRots (t : Nat) : List Rot :=
  [⟨true,  .piEighth, [⟨t, .z⟩]⟩,
   ⟨true,  .piEighth, [⟨t + 1, .z⟩]⟩,
   ⟨false, .piEighth, [⟨t, .z⟩, ⟨t + 1, .z⟩]⟩]

/-! ## §2. The banded (cutoff-2) inverse-QFT rotation sequence. -/

/-- Ladder for targets `t = k−1 … 0`: each keeps its adjacent CS† (control
`t+1`) and ends with `H t`. -/
def aqftLadderLow : Nat → List Rot
  | 0     => []
  | t + 1 => csDagRots t ++ (hGate t).flatten ++ aqftLadderLow t

/-- A SWAP as three CNOTs (nine π/4 rotations — Clifford). -/
def swapRots (i j : Nat) : List Rot :=
  (cnotGate i j).flatten ++ (cnotGate j i).flatten ++ (cnotGate i j).flatten

/-- The bit-reversal cascade preceding the ladder. -/
def bitRevRots (n : Nat) : List Rot :=
  (List.range (n / 2)).flatMap (fun i => swapRots i (n - 1 - i))

/-- **The banded inverse QFT, exactly in the rotation IR**: bit-reversal,
the top target's `H`, then the kept ladder.  (The dropped `m ≥ 2` rotations
carry the existing derived error budget — see header.) -/
def aqft2Rots : Nat → List Rot
  | 0     => []
  | n + 1 => bitRevRots (n + 1) ++ ((hGate n).flatten ++ aqftLadderLow n)

/-- The parallelized banded inverse QFT. -/
def aqft2Schedule (n : Nat) : RotProg := scheduleList (aqft2Rots n)

/-! ## §3. Resource counts. -/

private theorem swapRots_countPi8 (i j : Nat) :
    (swapRots i j).countP (fun r => r.angle == RAngle.piEighth) = 0 := rfl

private theorem flatMap_countPi8_zero (f : Nat → List Rot)
    (hf : ∀ i, (f i).countP (fun r => r.angle == RAngle.piEighth) = 0) :
    ∀ l : List Nat,
      (l.flatMap f).countP (fun r => r.angle == RAngle.piEighth) = 0
  | [] => rfl
  | i :: t => by
      rw [List.flatMap_cons, List.countP_append, hf i,
          flatMap_countPi8_zero f hf t]

theorem bitRevRots_countPi8 (n : Nat) :
    (bitRevRots n).countP (fun r => r.angle == RAngle.piEighth) = 0 :=
  flatMap_countPi8_zero _ (fun i => swapRots_countPi8 i (n - 1 - i)) _

theorem aqftLadderLow_countPi8 (t : Nat) :
    (aqftLadderLow t).countP (fun r => r.angle == RAngle.piEighth) = 3 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show ((csDagRots t ++ (hGate t).flatten) ++ aqftLadderLow t).countP _ = _
      rw [List.countP_append, List.countP_append, ih]
      show 3 + 0 + 3 * t = 3 * (t + 1)
      omega

/-- **The banded-IQFT T-count is `3·(k−1)`** (three T's per kept adjacent
controlled-S†) — and scheduling preserves it on the nose. -/
theorem aqft2Schedule_countPi8 (n : Nat) :
    countPi8 (aqft2Schedule (n + 1)) = 3 * n := by
  rw [aqft2Schedule, scheduleList_countPi8]
  show ((bitRevRots (n + 1)) ++ ((hGate n).flatten ++ aqftLadderLow n)).countP _ = _
  rw [List.countP_append, List.countP_append, bitRevRots_countPi8,
      aqftLadderLow_countPi8,
      show ((hGate n).flatten).countP (fun r => r.angle == RAngle.piEighth) = 0
        from rfl]
  omega

/-- The optimizer leg for the banded IQFT (side condition decidable). -/
theorem aqft2Schedule_denote (W n : Nat)
    (h : ∀ r ∈ aqft2Rots n,
          sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ W) :
    RotProg.denote W (aqft2Schedule n) = seqDenote W (aqft2Rots n) :=
  scheduleList_denote W (aqft2Rots n) h

/-! ## §4. QPE: H-layer ++ oracle ++ banded inverse QFT. -/

/-- The QPE preparation layer: `H` on each of the `k` phase qubits. -/
def hLayerRots (k : Nat) : List Rot :=
  (List.range k).flatMap (fun q => (hGate q).flatten)

/-- **QPE in the rotation IR**, with the modular-exponentiation oracle given
as ANY rotation sequence (e.g. `gateRots oracleGate` — exact, since the
Gate-IR oracle is Toffoli-class). -/
def qpeRots (k : Nat) (oracle : List Rot) : List Rot :=
  hLayerRots k ++ (oracle ++ aqft2Rots k)

/-- The parallelized QPE program. -/
def qpeSchedule (k : Nat) (oracle : List Rot) : RotProg :=
  scheduleList (qpeRots k oracle)

theorem hLayerRots_countPi8 (k : Nat) :
    (hLayerRots k).countP (fun r => r.angle == RAngle.piEighth) = 0 :=
  flatMap_countPi8_zero _ (fun _ => rfl) _

/-- **THE QPE T-COUNT**: oracle T-count plus `3·(k−1)` for the banded IQFT —
stated against the INDEPENDENT Gate-IR counter, so every existing per-gadget
`tcount` theorem instantiates it. -/
theorem qpeSchedule_gate_countPi8 (n : Nat) (g : Gate) :
    countPi8 (qpeSchedule (n + 1) (gateRots g)) = Gate.tcount g + 3 * n := by
  rw [qpeSchedule, scheduleList_countPi8, qpeRots, List.countP_append,
      List.countP_append, hLayerRots_countPi8, gateRots_countPi8]
  show 0 + (Gate.tcount g + (aqft2Rots (n + 1)).countP _) = _
  have h := aqft2Schedule_countPi8 n
  rw [aqft2Schedule, scheduleList_countPi8] at h
  rw [h]
  omega

/-- The optimizer leg for assembled QPE (side condition decidable). -/
theorem qpeSchedule_denote (W k : Nat) (oracle : List Rot)
    (h : ∀ r ∈ qpeRots k oracle,
          sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ W) :
    RotProg.denote W (qpeSchedule k oracle) = seqDenote W (qpeRots k oracle) :=
  scheduleList_denote W (qpeRots k oracle) h

/-! ## §5. Kernel-checked anchors. -/

-- 3-qubit banded IQFT: 1 swap (9) + H (3) + two CS†+H rounds (12) = 24 rotations
example : (aqft2Rots 3).length = 24 := by decide
example : countPi8 (aqft2Schedule 3) = 6 := aqft2Schedule_countPi8 2
-- the decidable side condition of the semantic theorem, at width 3:
example : ∀ r ∈ aqft2Rots 3,
    sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ 3 := by decide
example : RotProg.wf (aqft2Schedule 3) = true := by decide

-- a toy QPE: 2 phase qubits, a Toffoli oracle on qubits 2,3,4
example : countPi8 (qpeSchedule 2 (gateRots (.CCX 2 3 4))) = 10 :=
  qpeSchedule_gate_countPi8 1 (.CCX 2 3 4)
example : ∀ r ∈ qpeRots 2 (gateRots (.CCX 2 3 4)),
    sortedStrict r.axis = true ∧ PauliProduct.width r.axis ≤ 5 := by decide

end FormalRV.PauliRotation
