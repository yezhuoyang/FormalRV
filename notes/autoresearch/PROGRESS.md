# Autoresearch PROGRESS LOG — FormalRV gap closure

> Living log. Newest entries appended at the BOTTOM of the LOG section.
> Read RULES.md first every iteration. Current milestone is tracked in STATE.

## LESSONS (recurring mistakes to avoid — promote here when a mistake repeats)
- **NEVER `git commit` with a bare/`-a` invocation on a shared tree.** Commit explicit paths only
  (`git commit -- <my files>`). On 2026-06-07 a bare commit swept in ANOTHER agent's 48 staged
  refactor renames; undone via `git reset --soft` (recoverable in reflog as 616fe52).
- **Do NOT run the autonomous cron loop while another agent is editing the same working tree/branch.**
  Two concurrent writers + a 150-file in-flight refactor = collisions. Loop is PAUSED until the tree
  is clean / coordination is decided.

## STATE
- **LOOP STATUS: PAUSED (2026-06-07)** — another agent is mid-refactor (Shor/ → Arithmetic/, 48 renames,
  237 changes). My cron (4b79c4e5) DELETED. M1 work (ModExpWelded.lean) preserved as untracked, builds
  green + kernel-clean in the current (refactored) worktree. Resume only after coordination decided.
- Current milestone: **M1 (WS1a — welded textbook modexp theorem) — CORE DONE, awaiting safe integration**
- Branch: `feat/ldpc-ppm-correctness`
- Crown-jewel axiom check (must stay clean): `Shor_correct_var`,
  `Shor_correct_verified_no_modmult_axioms` = `[propext, Classical.choice, Quot.sound]` ✓ (baseline)
- Locked scope decisions: welded textbook-first; PPM stabilizer-faithful; capstone small-code-first;
  native_decide → structured-proof-or-honest-relabel. (See memory: formalrv-audit-and-remediation.)

## MILESTONE BOARD
- [~] M1 WS1a  welded textbook modexp (semantics+count, one family)   ← CORE DONE (green); remaining: shor_resource_welded + wire to root
- [ ] M2 WS2'  Steane/[[18,2,d]] proven CSS + kernel-clean k
- [ ] M3 WS3   stabilizer-faithful PPM + magic-injection gadget
- [ ] M4 WS7   inhabit VerifiedShorOnCode (small code) + Certificate
- [ ] M5 WS5   parallel schedule + factory throughput + floor instantiation + gate Example
- [ ] M6 WS4/WS6  internalize has_flow; verified emitter on production path; real Stim Shor; fix cmds
- [ ] M7 WS1b/WS8  optimized weld; GE2021 weld to real code; README honesty + CI gate

## OPEN QUESTIONS / NEEDS-HUMAN
- (none yet)

## LOG
<!-- append ITER entries below -->

### ITER 1 @ 2026-06-07 (kickoff, recon only — no code changes)
- MILESTONE: M1 (WS1a welded textbook modexp)
- ATTEMPTED: Map the exact `verifiedFamily ↔ count-chain` seam so the welded count theorem can
  reuse existing infra rather than re-prove anything.
- RESULT: green (recon; no build needed). Seam fully identified:
  * Verified family = `FormalRV.BQAlgo.our_modmult_family bits N a ainv multBits : Nat → BaseUCom`
    (MCPBridge.lean:788). Iterate `i` = `Gate.toUCom (modMultInPlaceShor bits N (a^(2^i)%N) (ainv^(2^i)%N) multBits)`
    — CORRECT per-iterate a^(2^i) structure (not the fixed-a scaffold).
  * Semantics ALREADY proven on this family: `f_modmult_circuit_verified_bits_MMI`
    (SQIRModMultAccumulatorRange.lean:1348) ⇒ ModMulImpl; `our_modmult_family_uc_well_typed`
    (MCPBridge.lean:796) ⇒ uc_well_typed. So conjuncts (i)+(ii) of `shor_modexp_welded` are reuse, not new proof.
  * Per-gate Toffoli/T count ALREADY proven and CONSTANT-INDEPENDENT:
    `tcount_sqir_modmult_MCP_gate_eq = 112*bits^2` (ToffoliCount.lean:247), side-conditions only.
    ⇒ total over m iterates = `m * 112 * bits^2`, identical for the varying-a family.
  * Existing scaffold `tcount_shorModExpMCPChain` (ModExpCount.lean:92) already does the induction-over-m
    — but on a FIXED-a chain of `sqir_modmult_MCP_gate`. The weld = redo that sum on `our_modmult_family`
    (the object semantics is proven for), reusing the constant-independent per-gate count.
- ERROR+ROOT-CAUSE: none.
- REFLECTION: The textbook weld is lower-risk than estimated — both halves (semantics, count) already
  exist; M1 is really "state one theorem bundling them on ONE term + sum the per-iterate count." The
  only genuinely-new lemma is the inductive total-count on `our_modmult_family`.
- NEXT (iter 2): Confirm `tcount (modMultInPlaceShor ...)` relates to `sqir_modmult_MCP_gate`'s
  `112*bits^2` (find/prove a direct per-iterate count lemma on the family's gate). Decide: count the
  UNCONTROLLED family total first (cleanest weld for H5/H6), add controlled-power/QPE-control overhead
  as a refinement. Then create `FormalRV/Arithmetic/SQIRModMult/ModExpWelded.lean` with
  `shorModExpFamilyToffoli` + the inductive `= m*112*bits^2` lemma; build green; #print axioms.

### ITER 2 @ 2026-06-07 — M1 CORE LANDED (green, kernel-clean, gated)
- MILESTONE: M1 (WS1a)
- ATTEMPTED: Create `FormalRV/Arithmetic/SQIRModMult/ModExpWelded.lean` with the welded theorem:
  semantics + well-typedness + total T-count on the SAME family `f_modmult_circuit_verified_bits`.
- RESULT: **green**. `lake build FormalRV.Arithmetic.SQIRModMult.ModExpWelded` OK (first try after recon).
  Added: `family_iterate_gate` (rfl: family iterate i = toUCom of the counted gate — weld on the SAME term);
  `tcount_verified_family_iterate` (=112*bits^2 per iterate, reusing tcount_sqir_modmult_MCP_gate_shor +
  coprime_pow / ZMod.coprime_mod_iff_coprime / coprime_pow_mod_pos); `tcount_verified_modexp_chain`
  (Sum_{i<m} = m*112*bits^2 via Finset.sum_const); `shor_modexp_welded` (semantics + welltyped + count).
  #print axioms shor_modexp_welded = [propext, Classical.choice, Quot.sound]; crown jewels still clean;
  #verify_clean ACCEPTS both new headline theorems at build time.
- ERROR+ROOT-CAUSE: none — iter-1 recon paid off; reused lemmas resolved first build.
- REFLECTION: constant-independence of the per-gate T-count made the sum trivial (Finset.sum_const).
- NEXT (iter 3): add `shor_resource_welded` chaining shor_modexp_welded semantics into Shor_correct_var
  (BasicSettingRelaxed) so ONE theorem carries success-bound AND count; wire ModExpWelded into the
  Arithmetic umbrella so the gate runs in the full build; then flip M1 to [x] and start M2.
