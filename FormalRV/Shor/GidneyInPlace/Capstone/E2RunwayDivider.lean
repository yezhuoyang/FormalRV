/-
  FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider — Stage A divider, ATTEMPT A.
  ════════════════════════════════════════════════════════════════════════════

  GOAL.  A verified reversible DIVMOD-by-N gate (Stage A of the runway-shift gate).
  STRATEGY (attempt A): IN-PLACE subtract shifted `N·2^k` over `cm` steps; the
  quotient bits accumulate in a dedicated `cm`-wire QUOTIENT band.

  LAYOUT (interleaved Cuccaro; chosen so NO swap adapter is needed for the divider).
    With `q_start := 0`, `bits` data wires:
      • DATA band (Cuccaro TARGET register): wire `2i+1`, i ∈ [0,bits), weight 2^i.
        Read by `cuccaro_target_val bits 0`.  This is the running value / output remainder.
      • carry-in wire `0`: transient, clean in/out.
      • READ band (Cuccaro read/addend register): wire `2i+2`, i ∈ [0,bits): transient
        workspace (used by compare/subtract to stage the two's-complement constant);
        clean in/out.
      • FLAG wire `flagPos := 2*bits+1`: transient; clean in/out (cleaned by the
        quotient-bit copy: see `divStep`).
      • QUOTIENT band: wires `qBase + k`, k ∈ [0,cm): persistent output, quotient bit k.
        We take `qBase := 2*bits+2`.
    Total dim `dimDiv bits cm = 2*bits + 2 + cm`.

  THE DIVSTEP (one quotient bit, fully verified here).  On a window of width `w`
  starting at `q_start` holding running value `r < 2^w` with `r < 2N`:
      `divStep` = compareConst[N] (flag ^= [N≤r]) ; condSub[N] (r -= flag·N)
                ; CX flag→qbit (qbit ^= flag) ; CX qbit→flag (flag ^= qbit).
    Effect on a clean-flag, clean-read, clean-qbit, clear-carry state with target r:
      target  ↦ r % N        (= r − [N≤r]·N, since r < 2N)
      qbit    ↦ [N≤r]         (= r / N, since r < 2N)         ← PERSISTS
      flag    ↦ false         (cleaned: flag == qbit after the two CXs)
      read/carry ↦ unchanged (clean), everything else framed.

  FULL DIVIDER (general cm) — CLOSED.  Long division processing k = cm−1 … 0 with
  the divstep instantiated on the window `[q_start + 2k, …)` of width `bits − k`, so
  it effectively subtracts `N·2^k` when the running top exceeds it.  The full cm-step
  induction is PROVED (`divModN_decode_gen`), with the partial-quotient/partial-
  remainder invariant carried in `DivState`; the headline support-form contract is
  `divModN_decode`.

  HEADLINE (`divModN_decode`, fully verified, kernel-clean).  On the support
  `v = z + j·N` (`z < N`, `j < 2^cm`, budget `2^cm·N ≤ 2^bits`), running
  `divModN bits cm N` on the clean input `encDiv bits v`:
    • DATA band (Cuccaro target reg, `q_start = 0`) decodes to `z = v % N`;
    • QUOTIENT band wire `qBase bits + k` holds bit `k` of `j = v / N`;
    • TRANSIENT workspace (carry / read band / flag) returns clean;
    • the gate is `WellTyped (dimDiv bits cm)`.
  (`Gate.reverse (divModN bits cm N)` then composes for Stage C; Stage B is the
  verified residue multiply `residueMul_decode` from E2RunwayResidueMul.)

  Kernel-clean: no `sorry`, no `native_decide`; axioms ⊆ {propext, Classical.choice,
  Quot.sound} (verified via `#print axioms divModN_decode`).
-/

-- Re-export shim: split into E2RunwayDivider/ submodules (same namespace); importers unchanged.
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.Setup
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.Divider
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.DecodeBase
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.DecodeInduction
import FormalRV.Shor.GidneyInPlace.Capstone.E2RunwayDivider.DecodeHeadline
