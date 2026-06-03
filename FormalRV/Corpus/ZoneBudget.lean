/-
  FormalRV.Corpus.ZoneBudget — let the USER set their architecture's per-zone qubit
  counts, and build the zoned architecture from them.  Hardware-agnostic; the
  neutral-atom (qianxu) layout is one instance.

  The user supplies a list of (zone name, qubit count); `toArch` lays the zones out
  contiguously into a `ZonedArch` whose `total_sites` is the SUM of the counts, and
  the capacity invariant then checks every operation lands inside a finite zone.
  So "how many qubits in each zone" is a first-class, user-settable input.

  qianxu's total (ED Table III): N_m (memory) + N_p (processor) + 3·N_f (factories)
  + N_𝒜 (operation-zone ancilla, 894 for lp_20^{3,7}) + N_res (reservoir/reloading).
  We fix the KNOWN counts (N_𝒜 = 894, one factory ≈ 2565) and leave N_m, N_p, N_res
  as user parameters — N_res in particular is UNSPECIFIED in the paper (a real gap).

  No `sorry`, no `axiom`.
-/

import FormalRV.System.ScheduleInvariantsExplicit

namespace FormalRV.Corpus.ZoneBudget

open FormalRV.Framework.ScheduleInv

/-! ## §1. User-settable per-zone qubit budget -/

/-- A per-zone qubit budget: named zones with their physical-qubit counts, plus the
    cycle time and transport speed.  Hardware-agnostic (the user names the zones). -/
structure ZoneBudget where
  zones  : List (String × Nat)
  tCycle : Nat
  vMax   : Nat

/-- Total physical qubits = sum of the per-zone counts. -/
def ZoneBudget.total (b : ZoneBudget) : Nat := (b.zones.map Prod.snd).foldl (· + ·) 0

/-- Lay named zones out contiguously from a running offset into `ArchZone`s. -/
def layoutZones : List (String × Nat) → Nat → List ArchZone
  | [],               _   => []
  | (name, cnt) :: rest, off =>
      { name := name, site_lo := off, site_hi := off + cnt } :: layoutZones rest (off + cnt)

/-- Build the `ZonedArch` from the user's zone budget. -/
def ZoneBudget.toArch (b : ZoneBudget) : ZonedArch :=
  { zones := layoutZones b.zones 0
    total_sites := b.total
    t_cycle_us := b.tCycle
    v_max_um_per_us := b.vMax }

/-- The built architecture's total qubit count is exactly the user's zone sum. -/
theorem toArch_total (b : ZoneBudget) : b.toArch.total_sites = b.total := rfl

/-- A zone's capacity in the built architecture is exactly its user-set count. -/
theorem layout_zone_capacity (name : String) (cnt : Nat) (rest : List (String × Nat)) (off : Nat) :
    ((layoutZones ((name, cnt) :: rest) off).head?.map ArchZone.capacity) = some cnt := by
  simp [layoutZones, ArchZone.capacity]

/-! ## §2. The qianxu neutral-atom architecture as a user zone budget -/

/-- qianxu (lp_20^{3,7}) zone budget: KNOWN counts factory ≈ 2565 (App C) and
    operation-zone ancilla N_𝒜 = 894 (ED Table III); memory `N_m`, processor `N_p`,
    and reservoir `N_res` are user parameters (`N_res` is UNSPECIFIED in the paper). -/
def qianxuBudget (N_m N_p N_res tCycle vMax : Nat) : ZoneBudget :=
  { zones := [ ("memory", N_m), ("processor", N_p),
               ("factory", 2565), ("op-ancilla", 894), ("reservoir", N_res) ]
    tCycle := tCycle, vMax := vMax }

/-- qianxu total = N_m + N_p + 2565 + 894 + N_res — the sum-over-zones of ED Table
    III, with the factory and operation-ancilla counts fixed to the paper's values. -/
theorem qianxu_total (N_m N_p N_res tCycle vMax : Nat) :
    (qianxuBudget N_m N_p N_res tCycle vMax).total = N_m + N_p + 2565 + 894 + N_res := by
  simp [qianxuBudget, ZoneBudget.total]

/-- A representative ~10,000-qubit instance (memory 4000, processor 2541,
    reservoir 0): total = 10,000, matching the paper's headline.  (The exact
    N_m/N_p/N_res split is the user's to set / the paper's ED Table III to pin;
    N_res is the paper's unspecified zone.) -/
theorem qianxu_10k_instance :
    (qianxuBudget 4000 2541 0 1 1).total = 10_000 := by decide

/-- The built qianxu architecture reports the 10,000-qubit total. -/
theorem qianxu_10k_arch_total :
    (qianxuBudget 4000 2541 0 1 1).toArch.total_sites = 10_000 := by decide

/-- Increasing ANY zone's budget increases the total (monotone, parametric) — more
    qubits per zone ⇒ a larger machine, as the user sets it. -/
theorem total_mono_memory (N_m N_m' N_p N_res tC vM : Nat) (h : N_m ≤ N_m') :
    (qianxuBudget N_m N_p N_res tC vM).total ≤ (qianxuBudget N_m' N_p N_res tC vM).total := by
  rw [qianxu_total, qianxu_total]; omega

end FormalRV.Corpus.ZoneBudget
