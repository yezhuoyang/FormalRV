/-
  FormalRV.System.HardwareSensitivity — the resource lower bound as a function of the FULL set of
  hardware parameters, with a proven SENSITIVITY (monotonicity) theorem for EACH one, applied to
  BOTH Gidney papers.

  ## Hardware parameters (complete set)

    d        — code distance              → physical qubits per logical patch `2(d+1)²`
    tReact   — decoder reaction time      (DECODING SPEED)
    tMeas    — logical measurement time   (MEASUREMENT TIME)
    prod     — magic-state production time
    fq       — factory footprint (qubits)
    Q        — total physical qubits      (ARCHITECTURE SIZE)
    nDec     — parallel decoders          (DECODER PARALLELISM)
    maxPar   — max parallel operations    (MAX PARALLEL PHYSICAL OPERATIONS)
    routeLat — routing latency            (ROUTING LATENCY)

  ## The lower bound and its sensitivity

  The runtime lower bound is the MAX of four resource/causal floors (each a packing/critical-path
  impossibility, cf. `ScheduleLowerBound.magic_spacetime_floor` / `.causal_chain4`):

    magicFloor   = K·fq·prod / Q                (magic-state spacetime; sens. Q, fq, prod)
    decoderFloor = K·tReact / nDec              (decoder throughput;     sens. tReact, nDec)
    parFloor     = K·(tMeas+routeLat) / maxPar  (op-slot throughput;     sens. tMeas, routeLat, maxPar)
    depthFloor   = depth·(tMeas+tReact)         (causal critical path;   sens. depth, tMeas, tReact)

  EVERY hardware parameter appears, and each floor is PROVEN monotone in its parameters — increasing
  in every latency (`*_mono_*`), decreasing in every capacity (`*_anti_*`), physical qubits
  increasing in `d`.  So the bound is genuinely sensitive to all of decoding speed, architecture
  size, routing latency, measurement time, and max parallelism — none is silently dropped.
-/
import Mathlib.Tactic.GCongr
import FormalRV.System.Bounds.ScheduleLowerBound
import FormalRV.System.Params.RSA2048

namespace FormalRV.System.HardwareSensitivity

/-! ## §1. The four floors as numeric functions of the hardware parameters. -/

def magicFloorN   (K fq prod Q : Nat) : Nat := K * fq * prod / Q
def decoderFloorN (K tReact nDec : Nat) : Nat := K * tReact / nDec
def parFloorN     (K opTime maxPar : Nat) : Nat := K * opTime / maxPar
def depthFloorN   (depth tMeas tReact : Nat) : Nat := depth * (tMeas + tReact)
def physQubitsN   (L d : Nat) : Nat := L * (2 * (d + 1) ^ 2)

/-! ## §2. Sensitivity (monotonicity) — one theorem per hardware parameter. -/

/-- **DECODING SPEED (`tReact`)** — a slower decoder raises the decoder-throughput floor … -/
theorem decoderFloor_mono_tReact (K nDec : Nat) {t t' : Nat} (h : t ≤ t') :
    decoderFloorN K t nDec ≤ decoderFloorN K t' nDec := by unfold decoderFloorN; gcongr
/-- … and the causal critical-path floor. -/
theorem depthFloor_mono_tReact (depth tMeas : Nat) {t t' : Nat} (h : t ≤ t') :
    depthFloorN depth tMeas t ≤ depthFloorN depth tMeas t' := by unfold depthFloorN; gcongr

/-- **DECODER PARALLELISM (`nDec`)** — more decoders LOWER the floor (anti-monotone). -/
theorem decoderFloor_anti_nDec (K t : Nat) {n n' : Nat} (hpos : 0 < n) (h : n ≤ n') :
    decoderFloorN K t n' ≤ decoderFloorN K t n := by unfold decoderFloorN; exact Nat.div_le_div_left h hpos

/-- **ARCHITECTURE SIZE (`Q`)** — a larger device LOWERS the magic-state floor (anti-monotone:
    more space → less time). -/
theorem magicFloor_anti_Q (K fq prod : Nat) {Q Q' : Nat} (hpos : 0 < Q) (h : Q ≤ Q') :
    magicFloorN K fq prod Q' ≤ magicFloorN K fq prod Q := by
  unfold magicFloorN; exact Nat.div_le_div_left h hpos

/-- **PRODUCTION TIME (`prod`)** — slower factories raise the magic-state floor. -/
theorem magicFloor_mono_prod (K fq Q : Nat) {p p' : Nat} (h : p ≤ p') :
    magicFloorN K fq p Q ≤ magicFloorN K fq p' Q := by unfold magicFloorN; gcongr

/-- **FACTORY FOOTPRINT (`fq`)** — larger factories raise the magic-state floor. -/
theorem magicFloor_mono_fq (K prod Q : Nat) {f f' : Nat} (h : f ≤ f') :
    magicFloorN K f prod Q ≤ magicFloorN K f' prod Q := by unfold magicFloorN; gcongr

/-- **ROUTING LATENCY (`routeLat`) & MEASUREMENT TIME (`tMeas`)** — both enter `opTime`, so a slower
    operation raises the op-slot floor. -/
theorem parFloor_mono_opTime (K maxPar : Nat) {o o' : Nat} (h : o ≤ o') :
    parFloorN K o maxPar ≤ parFloorN K o' maxPar := by unfold parFloorN; gcongr

/-- **MEASUREMENT TIME (`tMeas`)** also raises the causal critical-path floor. -/
theorem depthFloor_mono_tMeas (depth tReact : Nat) {m m' : Nat} (h : m ≤ m') :
    depthFloorN depth m tReact ≤ depthFloorN depth m' tReact := by unfold depthFloorN; gcongr

/-- **MAX PARALLEL OPERATIONS (`maxPar`)** — more parallelism LOWERS the op-slot floor. -/
theorem parFloor_anti_maxPar (K o : Nat) {p p' : Nat} (hpos : 0 < p) (h : p ≤ p') :
    parFloorN K o p' ≤ parFloorN K o p := by unfold parFloorN; exact Nat.div_le_div_left h hpos

/-- **CODE DISTANCE (`d`)** — a larger distance raises the physical-qubit count `L·2(d+1)²`. -/
theorem physQubits_mono_d (L : Nat) {d d' : Nat} (h : d ≤ d') :
    physQubitsN L d ≤ physQubitsN L d' := by unfold physQubitsN; gcongr

/-! ## §3. The full hardware record, the combined bound, and BOTH Gidney papers. -/

structure HW where
  d : Nat
  tReact : Nat
  tMeas : Nat
  prod : Nat
  fq : Nat
  Q : Nat
  nDec : Nat
  maxPar : Nat
  routeLat : Nat
  deriving Repr

def HW.timeLB (h : HW) (K depth : Nat) : Nat :=
  max (max (magicFloorN K h.fq h.prod h.Q) (decoderFloorN K h.tReact h.nDec))
      (max (parFloorN K (h.tMeas + h.routeLat) h.maxPar) (depthFloorN depth h.tMeas h.tReact))

/-- GE2021 hardware (8 h / 20M qubits): d=27, 10 µs reaction, 27 µs measure, CCZ factory
    2565 qubits / 12000 µs, 20M qubits. -/
def ge2021 : HW :=
  { d := 27, tReact := 10, tMeas := 27, prod := RSA2048.cczWindowUs, fq := RSA2048.cczFactoryQubits,
    Q := 20000000, nDec := 1000, maxPar := 1000, routeLat := 27 }

/-- Gidney 2025 hardware (under a week / <1M qubits): d=25, 10 µs reaction, 25 µs measure,
    1M qubits; same CCZ factory spec as GE2021 (`Params.RSA2048`). -/
def gidney2025 : HW :=
  { d := 25, tReact := 10, tMeas := 25, prod := RSA2048.cczWindowUs, fq := RSA2048.cczFactoryQubits,
    Q := 1000000, nDec := 1000, maxPar := 1000, routeLat := 25 }

def ge2021_K : Nat := RSA2048.magicBudget
def gidney2025_K : Nat := 6500000000

/-- **★ Both papers, instantiated ★.**  The magic-state spacetime floor (qubit·hours) and the
    distance-driven data-qubit count, for GE2021 (d=27, K≈2.62×10⁹) and Gidney 2025 (d=25,
    K≈6.5×10⁹).  UNITS CAVEAT: the 4th argument of `magicFloorN` is its `Q` (architecture-size)
    slot, here REPURPOSED as `3 600 000 000` µs-per-hour — so `K·fq·prod / 3.6×10⁹` is the floor
    `K·fq·prod` (qubit·µs) converted to qubit·HOURS, not a runtime on a 3.6×10⁹-qubit device.
    Floors: 22.4M and 55.6M qubit-hours; the reported spacetimes (160M and 168M qubit-hours) sit
    ~7× and ~3× above their OWN floors — the framework works for both, and each is near its
    hardware-determined limit. -/
theorem both_papers :
    magicFloorN ge2021_K ge2021.fq ge2021.prod 3600000000 = 22425149
    ∧ magicFloorN gidney2025_K gidney2025.fq gidney2025.prod 3600000000 = 55575000
    ∧ physQubitsN 6189 ge2021.d = 9704352
    ∧ physQubitsN 6189 gidney2025.d = 8367528 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- **Cross-reference (dedup):** the magic-state floor computed here for GE2021 is the SAME number
    as `ScheduleLowerBound.rsa2048_floor_qubit_hours` — the two "22 425 149 qubit-hours" literals are
    proven equal rather than independently asserted. -/
theorem magicFloor_matches_rsa2048 :
    magicFloorN ge2021_K ge2021.fq ge2021.prod 3600000000
      = ScheduleLowerBound.rsa2048_floor_qubit_hours := by native_decide

/-! ### Sensitivity coverage (documentation).

    Every listed hardware parameter has a proven sensitivity theorem in §2: decoding speed
    (`decoderFloor_mono_tReact`, `depthFloor_mono_tReact`), architecture size (`magicFloor_anti_Q`),
    routing latency + measurement time (`parFloor_mono_opTime`, `depthFloor_mono_tMeas`), max
    parallelism (`parFloor_anti_maxPar`), decoder parallelism (`decoderFloor_anti_nDec`), code
    distance (`physQubits_mono_d`), and factory cost (`magicFloor_mono_prod`,
    `magicFloor_mono_fq`).  None is dropped from the bound.  (This coverage claim is carried by the
    named theorems themselves; a former `sensitivity_complete` theorem stated only `0 ≤ timeLB` —
    vacuous — and was removed.) -/

end FormalRV.System.HardwareSensitivity
