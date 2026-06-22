#!/usr/bin/env python3
"""Delete dead `:= True` placeholder defs (with their docstrings) by line range.
Ranges are 1-indexed inclusive; processed descending so earlier ranges stay valid."""
import sys, io

EDITS = {
    r"FormalRV/Shor/MainAlgorithm/ContinuedFractionBridge/ConvergentBridgeFinal.lean":
        [(71, 90), (92, 107)],
    r"FormalRV/Shor/MainAlgorithm/ContinuedFractionBridge/OFPostStepValues.lean":
        [(87, 95)],
    r"FormalRV/Shor/MainAlgorithm/QuantumAndContinuedFractions/ContinuedFractionInvariants.lean":
        [(198, 222)],
}

for path, ranges in EDITS.items():
    with io.open(path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    # sanity-check: the last line of each range must be the placeholder def
    for s, e in ranges:
        assert lines[e-1].lstrip().startswith("def ") and ":= True" in lines[e-1], \
            f"{path}:{e} is not a ':= True' def: {lines[e-1]!r}"
        print(f"{path}: deleting lines {s}-{e}")
    for s, e in sorted(ranges, reverse=True):
        del lines[s-1:e]
    with io.open(path, "w", encoding="utf-8", newline="") as f:
        f.writelines(lines)
    print(f"  -> wrote {path} ({len(lines)} lines)")
