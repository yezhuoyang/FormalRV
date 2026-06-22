/-
  scripts/CheckErrorCorpus.lean — the Lean half of the differential error
  corpus: parse every (backend, program) pair from disk, run the
  per-conjunct diagnostic, and assert the EXPECTED failing conjuncts.

  The expectations encode the capture matrix:
    * AGREE rows — the VM error kind has a Lean conjunct that fires;
    * Lean-stronger rows (e13–e16) — Lean fails, the VM passes;
    * VM-stronger row (e17) — the VM fails (token ttl), Lean passes;
    * parse rows (e09 on the VM side, e18 on both) — rejected before
      checking.

  Run (after EmitErrorCorpus):
      lake env lean --run scripts/CheckErrorCorpus.lean
-/
import FormalRV.Codegen.DeviceProgramParse

open FormalRV.Codegen.DeviceProgramParse

/-- (example, backend tag, expected outcome) — outcomes are the CANONICAL
    CONTRACT CODES, the SAME strings the FTQ-VM reports
    (`tests/test_error_corpus.py` asserts the VM side; rows agree
    literally except the documented model-gap rows e13–e17).
    `.inl codes` = expected violated codes (`[]` = PASS);
    `.inr ()` = the Lean PARSER itself must reject (the SYNTAX code). -/
def expectations : List (String × String × (List String ⊕ Unit)) :=
  [ ("e01_clean",             "std",        .inl [])
  , ("e02_qubit_conflict",    "dualrail",   .inl ["QUBIT_EXCLUSIVITY"])
  , ("e03_cnot_cap",          "std",        .inl ["GATE_PARALLELISM"])
  , ("e04_cap_reconfigured",  "dualrail",   .inl [])
  , ("e05_slow_decode",       "std",        .inl ["DECODER_REACTION"])
  , ("e06_pfu_before_decode", "std",        .inl ["FEEDFORWARD_CAUSALITY"])
  , ("e07_reuse_after_measure", "std",      .inl ["QUBIT_LIFECYCLE"])
  , ("e08_use_before_request", "std",       .inl ["QUBIT_LIFECYCLE"])
  , ("e09_unknown_site",      "std",        .inl ["ARCH_BOUNDS"])
  , ("e10_unsupported_gate",  "std",        .inl ["GATE_UNSUPPORTED"])
  , ("e11_wrong_duration",    "std",        .inl ["GATE_DURATION"])
  , ("e12_decoder_burst",     "tinyqueue",  .inl ["DECODER_OVERLOAD"])
  , ("e13_dangling_live",     "std",        .inl ["QUBIT_LIFECYCLE"])     -- VM: pass (model gap)
  , ("e14_double_request",    "std",        .inl ["QUBIT_LIFECYCLE"])     -- VM: pass (model gap)
  , ("e15_magic_window",      "magicstock", .inl ["MAGIC_DEMAND_WINDOW"]) -- VM: pass (model gap)
  , ("e16_slow_feedforward",  "std",        .inl ["FEEDFORWARD_LATENCY"]) -- VM: pass (model gap)
  , ("e17_stale_feedforward", "staledecode", .inl [])                     -- VM: FEEDFORWARD_FRESHNESS (Lean gap)
  , ("e18_empty_interval",    "std",        .inr ())
  , ("e19_syndrome_flood",    "surfacestream", .inl ["SYNDROME_BANDWIDTH"])
  , ("e20_syndrome_paced",    "surfacestream", .inl [])
  , ("e21_decoder_paced",     "strictdecode", .inl [])
  , ("e22_decoder_oversubscribed", "strictdecode", .inl ["DECODER_OVERLOAD"])
  , ("e23_decoder_premature_reuse", "strictdecode", .inl ["DECODER_OVERLOAD"])
  , ("e24_decode_before_measure", "std",        .inl ["SYNDROME_CAUSALITY"])
  , ("e25_magic_unprepared",  "magicscarce",   .inl ["MAGIC_SUPPLY"]) ]

def main : IO UInt32 := do
  let dir := "ftq_vm/backend/examples/corpus"
  let mut failures := 0
  IO.println "example                      backend     Lean diagnosis"
  IO.println (String.replicate 78 '-')
  for (name, tag, expected) in expectations do
    let backendText ← IO.FS.readFile s!"{dir}/backend_{tag}.json"
    let programText ← IO.FS.readFile s!"{dir}/{name}.dp"
    match diagnoseDeviceProgram backendText programText, expected with
    | .error e, .inr () =>
        IO.println s!"{name.leftpad 28 ' '} {tag.leftpad 11 ' '} PARSE-REJECT ✓ ({e})"
    | .error e, .inl _ =>
        IO.println s!"{name.leftpad 28 ' '} {tag.leftpad 11 ' '} UNEXPECTED PARSE ERROR: {e}"
        failures := failures + 1
    | .ok diag, .inl want =>
        let verdict := if diag.isEmpty then "PASS" else s!"FAIL {diag}"
        if diag = want then
          IO.println s!"{name.leftpad 28 ' '} {tag.leftpad 11 ' '} {verdict} ✓"
        else
          IO.println s!"{name.leftpad 28 ' '} {tag.leftpad 11 ' '} {verdict} ✗ expected {want}"
          failures := failures + 1
    | .ok diag, .inr () =>
        IO.println s!"{name.leftpad 28 ' '} {tag.leftpad 11 ' '} expected parse reject, got {diag}"
        failures := failures + 1
  if failures == 0 then
    IO.println "ALL LEAN CORPUS EXPECTATIONS MET"
    return 0
  else
    IO.println s!"{failures} EXPECTATION FAILURE(S)"
    return 1
