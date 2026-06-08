# Autoresearch RULES — FormalRV gap closure (READ EVERY ITERATION)

## Mission
Close every audit gap in the locked remediation plan (M1→M7) by **proving** the
missing bridges. Where a full proof is genuinely out of reach this cycle, make
**honest progress** (smaller proven lemma + a precise recorded residual) — never fake.
Code-distance (C1) is OUT OF SCOPE. See PROGRESS.md for the milestone state.

## HARD INVARIANTS — never violate, no exceptions
1. **No `sorry`, no `admit`**, no placeholder tactic that abandons a goal. Ever.
2. **No new `axiom`.** Allowed axioms are exactly Lean's `propext, Classical.choice, Quot.sound`.
3. **No `native_decide`** in anything presented as verified. Use `decide` (small/finite) or a
   structured proof. If neither is feasible, **relabel honestly** as a distinct
   "native-evaluated" tier in docstrings/README — never ✅ "kernel-clean" nor ➗ "decide".
4. Every NEW headline theorem must satisfy `#print axioms <thm>` ⊆
   `{propext, Classical.choice, Quot.sound}` AND be gated by `#verify_clean` in a `Verifier.lean`.
5. **Never weaken, delete, comment-out, generalize-to-trivial, or restate** an EXISTING theorem
   to make something pass. Closing a gap ≠ deleting the gap. A statement may only be
   strengthened or left alone.
6. **Don't regress the crown jewels.** After any edit, re-confirm `#print axioms` is still clean for:
   `FormalRV.SQIRPort.Shor_correct_var` and `FormalRV.BQAlgo.Shor_correct_verified_no_modmult_axioms`.
7. **Touch only files relevant to the CURRENT milestone.** No cosmetic/sweeping refactors, no
   drby-by edits to unrelated subsystems, no renaming for taste.
8. No `set_option maxHeartbeats`/`maxRecDepth` inflation to *hide* a stuck proof as if solved. If a
   proof is legitimately heavy, that's fine, but record it; do not use options to mask non-termination.
9. **Do not edit the audit findings or this plan to move goalposts.** A gap is "closed" only when its
   written acceptance criterion is literally met and re-checkable.
10. Prefer reusing existing infra (lemmas, families) over re-proving. Cite what you reused.

## Operating mode: CONTINUOUS / event-driven (10 min is an UPPER BOUND, not a cadence)
- **Do not idle waiting for the clock.** The moment a chunk finishes, start the next one immediately.
- Run heavy `lake build`s in the BACKGROUND (`run_in_background: true`). Build completion re-invokes
  you instantly — that is the primary "fire when done" signal. Chain: edit → background build →
  (woken on completion) → check result + next chunk → background build → … with no artificial gaps.
- Within a turn, do as many iterations back-to-back as fit before a genuine wait point.
- The recurring 10-min cron (job 4b79c4e5) is ONLY a safety net: it restarts the loop if you ever
  fully stall/yield with no pending background task. Normal continuation is immediate, not on the tick.
- If you yield with no background build pending, you may ScheduleWakeup a short fallback; otherwise the
  cron covers the ≤10-min upper bound.

## Per-iteration protocol
1. Read RULES.md + PROGRESS.md (and LESSONS at its top). Pick the current milestone and the
   **smallest next provable step**.
2. Do ONE bounded chunk. Keep edits minimal and local.
3. `lake build` the touched module(s). On green, run `#print axioms` on the new theorem(s).
4. **Append a timestamped PROGRESS.md entry** with these fields:
   `ITER <n> @ <UTC>` · `MILESTONE` · `ATTEMPTED` · `RESULT (green/red)` ·
   `ERROR+ROOT-CAUSE` (if red) · `REFLECTION` (what I learned / would do differently) · `NEXT`.
5. At a green milestone boundary, make a checkpoint commit on the current branch
   (`feat/ldpc-ppm-correctness`) with a clear message; never push unless asked.
6. If stuck on the SAME step for 3 iterations: record the blocker, try a different
   decomposition/tactic, and add a LESSONS entry. If still blocked, mark the step
   `NEEDS-HUMAN` with a precise question and move to the next independent step.

## Milestone acceptance criteria (definition of done)
- **M1 (WS1a):** `FormalRV/Arithmetic/SQIRModMult/ModExpWelded.lean` proves `shor_modexp_welded`
  (ModMulImpl + uc_well_typed + Toffoli-count + magic-count, all on ONE `verifiedFamily` term)
  and `shor_resource_welded` (chains into `Shor_correct_var`). Both kernel-clean + `#verify_clean`'d.
- **M2 (WS2'):** Steane [[7,1,3]] and/or the [[18,2,d]] BB code have `css_condition = true` PROVEN
  (not native) and `derivedK = k` kernel-clean; `derivedK`/headline require the CSS hypothesis.
- **M3 (WS3):** stabilizer-tableau faithfulness theorem for `apply_PPM_pos`; CX-macro→real-CNOT
  Gottesman bridge; CCX/magic via one explicit gadget-channel obligation (proven for the gadget).
- **M4 (WS7):** `VerifiedShorOnCode` inhabited for the small code, `#verify_clean` passing;
  CainXu `Certificate` inhabited with a real code-tied `encodeState`.
- **M5 (WS5):** a non-trivial parallel schedule (books factory footprint, real deps) proven
  `scheduleValid`; add `factoryThroughputRespected`; instantiate `magic_spacetime_floor` against it;
  RSA floor numbers kernel-clean or honestly relabelled; gate the Example demo.
- **M6 (WS4/WS6):** internalize Stim `has_flow` as a Lean merge-correctness theorem; production
  emit scripts use the faithfulness-proven `Codegen.GateQasm`; `emitShor` depends on `a` and links
  to the proven circuit; neutral-atom verifier reads the Lean-emitted QASM; broken emit cmds fixed.
- **M7 (WS1b/WS8):** optimized windowed weld (paper-matched count) OR honest relabel; GE2021 ceiling
  reads the constructed `surfaceCodeD 27` (kill 1405-vs-1568); README honesty pass + CI smoke gate.

## Reflection discipline
Every iteration names the error CLASS when something fails (api-misuse / wrong-lemma /
missing-hypothesis / scope-creep / build-env / proof-too-slow / spec-mismatch). Recurring
mistakes get promoted to the LESSONS block at the top of PROGRESS.md so they are not repeated.
