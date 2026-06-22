/-
  FormalRV.System.Params.RSA2048 — the canonical RSA-2048 / Gidney–Ekerå 2021
  workload constants, in ONE place.

  Before this module the same numerals were re-typed in seven `System/` files
  (and drifted between doc-comments); every System file that needs a GE2021
  number should reference these definitions instead of re-typing the literal.
  All are plain `Nat` definitions, so `decide` / `native_decide` proofs unfold
  them for free.

  Sources: Gidney–Ekerå 2021 (2.7·10⁹ Toffolis, 6200 logical patches, 20 M
  physical qubits, ~8 h) and Cain–Xu 2026 App. C (CCZ factory: 2565 qubits,
  12 000 µs window).  The magic budget 2 622 824 448 is the PAPER cost-model
  windowed CCZ count (`= WindowedCostModel.toffoliCount 2048 3072 11`).  The
  count of the *actually-composed* circuit (`WindowedComposed.modExp`) is
  2 578 993 152 (`WindowedComposedCost.rsa2048_head_to_head`); the paper figure
  is a PROVEN UPPER BOUND on it (+1.67 % runway-folding + lookup-rounding) — see
  `System.Compose.VerifiedWorkloadBridge` (`verifiedToffoli_le_magicBudget`).
  (`Shor.Resource.ModExpToffoliCount` is the *un-windowed* 16n³ schoolbook bound,
  a different, ~51× larger circuit — NOT this number.)
-/

namespace FormalRV.System.RSA2048

/-- GE2021's reported Toffoli count for RSA-2048 (2.7·10⁹). -/
abbrev toffoliReported : Nat := 2_700_000_000

/-- The paper cost-model CCZ/magic-state budget for the windowed RSA-2048 circuit
    (`= WindowedCostModel.toffoliCount 2048 3072 11`).  It is a PROVEN UPPER BOUND on the
    actually-composed circuit's count `2 578 993 152` (`= EGate.toffoli WindowedComposed.modExp`;
    see `System.Compose.VerifiedWorkloadBridge.verifiedToffoli_le_magicBudget`), so any
    provisioning sized for `magicBudget` covers the verified circuit. -/
abbrev magicBudget : Nat := 2_622_824_448

/-- Logical surface-code patches in the GE2021 layout. -/
abbrev patches : Nat := 6200

/-- Decoder latency budget, in code cycles. -/
abbrev decodeLatencyCycles : Nat := 10

/-- Decode lanes required for backlog-free decoding:
    `patches · decodeLatencyCycles` (see `Decoder/DecoderBacklogModel`). -/
abbrev decodeLanesRequired : Nat := patches * decodeLatencyCycles

/-- CCZ factory footprint, physical qubits (Cain–Xu 2026 App. C). -/
abbrev cczFactoryQubits : Nat := 2565

/-- CCZ factory production window, µs (one magic state per window). -/
abbrev cczWindowUs : Nat := 12_000

/-- CCZ factories needed to keep RSA-2048 reaction-limited
    (see `Magic/MagicScheduleComplete`, `Audit/GidneyEkera2021/SystemZones`). -/
abbrev factoriesNeeded : Nat := 1093

/-! ## GE2021 hardware constants (paper §1 headline machine) -/

/-- Surface-code distance of the computation patches. -/
abbrev distance : Nat := 27

/-- Physical qubits per logical tile: `2(d+1)²` at d = 27 (the ×2 is the
    routing share baked into the GE2021 tile accounting). -/
abbrev tileQubits : Nat := 1568

/-- The reported total physical-qubit budget (the title's 20 M). -/
abbrev physicalBudget : Nat := 20_000_000

/-- Surface-code cycle time, µs. -/
abbrev cycleUs : Nat := 1

/-- Reaction-time budget, µs (= `decodeLatencyCycles · cycleUs`). -/
abbrev reactionUs : Nat := 10

/-- Computation-zone physical qubits: every patch as a d = 27 tile. -/
abbrev computationZoneQubits : Nat := patches * tileQubits

/-- Syndrome bits one patch readout injects per round: `d² − 1` hard
    stabilizer bits at d = 27 (rotated surface code). -/
abbrev syndromeBitsPerPatchRound : Nat := distance * distance - 1

theorem decodeLanesRequired_value : decodeLanesRequired = 62_000 := by decide
theorem computationZoneQubits_value : computationZoneQubits = 9_721_600 := by
  decide
theorem syndromeBitsPerPatchRound_value :
    syndromeBitsPerPatchRound = 728 := by decide

end FormalRV.System.RSA2048
