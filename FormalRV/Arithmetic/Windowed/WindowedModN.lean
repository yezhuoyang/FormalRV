/-
  FormalRV.Shor.WindowedCircuit.WindowedModN — the PER-WINDOW mod-N windowed
  multiplier.

  The existing windowed multiplier (`WindowedCircuitCorrect.lean`) is a
  PRODUCT adder: each window does `acc ← (acc + T_j[v]) mod 2^bits`, and the
  final value is `(a·y) mod 2^bits`.  Gidney's windowed multiplication
  (arXiv:1905.07682) instead reduces mod N after EVERY window:
  `acc ← (acc + T_j[v]) mod N` with table entries `T_j[v] = a·(2^w)^j·v mod N`,
  so the multiplier computes `(a·y) mod N` directly.  This file closes that
  gap at the Cuccaro layout.

  HEADLINE (`windowedModNMulCircuit_correct`): on the SAME clean input family
  `mulInputOf cuccaroAdder w bits numWin y` as the product-adder theorem, the
  per-window mod-N circuit leaves

      (a · y) mod N

  in the accumulator, provided `0 < w`, `0 < N`, `2·N ≤ 2^bits` and
  `y < 2^(w·numWin)`.

  Per-window structure (`modNLookupAddStep`): the Cuccaro comparator borrows
  the addend (read) register for its two's-complement constant, so the QROM
  word must be cleared before the constant-compare stage and re-supplied for
  the flag-uncompute stage:

      read(T) ; add ; unread(T)                -- acc ← acc + t   (t = T_j[v] < N)
      ; compareConst(N) → flag                 -- flag ^= [N ≤ acc]
      ; conditionalSub(N)                      -- acc ← acc mod N
      ; read(T) ; regCompareXor ; unread(T)    -- flag ^= [acc < t] = flag  (flag → 0)

  The flag-uncompute works because `acc_out = (s+t) mod N < t  ⟺  N ≤ s+t`
  when `s, t < N` — the standard modular-adder uncompute comparison, here
  realized as a REGISTER-register comparator (`regCompareXor`, new in this
  file: X-conjugated MAJ chain, top carry of `¬acc + t` = `[acc < t]`).

  New general-state (any `f : Nat → Bool`) reduction-stage lemmas, re-derived
  from the per-position Cuccaro primitives (the Tick-59/60 stage lemmas are
  tied to the `cuccaro_input_F` input family and do not apply inside the
  windowed frame):
  * `compareConstXor_state_general`  — the SQIR-style constant comparator;
  * `condSub_state_general`          — the flag-conditional subtract;
  * `regCompareXor_state_general`    — the register-register comparator.

  Follow-up (NOT in this pass): factor the reduction pipeline into a
  `ModAdder` interface so the Gidney `ModularAdder` pipeline (which has the
  same compare/conditional-subtract/uncompute shape) instantiates it too —
  this file is deliberately Cuccaro-specific.

  Kernel-clean: no `sorry`, no `native_decide`, no axioms beyond the prelude.
-/

-- Re-export shim: this file was split into WindowedModN/ submodules (same namespace).
-- Importers are unchanged.  See each submodule for its section.
import FormalRV.Arithmetic.Windowed.WindowedModN.Helpers
import FormalRV.Arithmetic.Windowed.WindowedModN.Comparators
import FormalRV.Arithmetic.Windowed.WindowedModN.CondSub
import FormalRV.Arithmetic.Windowed.WindowedModN.Reduction
import FormalRV.Arithmetic.Windowed.WindowedModN.Step
import FormalRV.Arithmetic.Windowed.WindowedModN.StepInvariant
import FormalRV.Arithmetic.Windowed.WindowedModN.Fold
import FormalRV.Arithmetic.Windowed.WindowedModN.Counts
