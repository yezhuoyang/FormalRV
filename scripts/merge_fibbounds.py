#!/usr/bin/env python3
"""Merge EuclideanIterationFibBounds.lean INTO EuclideanIterationBoundsAndGcd.lean.

BoundsAndGcd depends on FibBounds (uses cf_aux_full_q_inv, eucl_iter_fib_bound),
so FibBounds' bodies are prepended. The merged file imports what FibBounds
imported (OFPostStepNatEqualities); both share `namespace FormalRV.SQIRPort`.
Then FibBounds is deleted and dropped from the subfolder umbrella.
"""
import io, os

BASE = "FormalRV/Shor/MainAlgorithm/PostProcessingAndMeasurement"
FIB = f"{BASE}/EuclideanIterationFibBounds.lean"
GCD = f"{BASE}/EuclideanIterationBoundsAndGcd.lean"
UMB = "FormalRV/Shor/MainAlgorithm/PostProcessingAndMeasurement.lean"

NS_OPEN = "namespace FormalRV.SQIRPort"
NS_END = "end FormalRV.SQIRPort"
NEW_IMPORT = "import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.OFPostStepNatEqualities"


def read(p):
    with io.open(p, "r", encoding="utf-8") as f:
        return f.read()


def body_between_namespace(text):
    """Return the content strictly between the first `namespace` line and the
    last `end` line (exclusive), stripped of surrounding blank lines."""
    i = text.index(NS_OPEN) + len(NS_OPEN)
    j = text.rindex(NS_END)
    return text[i:j].strip("\n")


fib = read(FIB)
gcd = read(GCD)

fib_body = body_between_namespace(fib)
gcd_body = body_between_namespace(gcd)

assert "cf_aux_full_q_inv" in fib_body and "eucl_iter_fib_bound" in fib_body, "FibBounds bodies missing"
assert "eucl_iter_le_two_m_plus_one" in gcd_body, "GCD bodies missing"

merged = (
    NEW_IMPORT + "\n\n" +
    NS_OPEN + "\n\n" +
    fib_body + "\n\n" +
    gcd_body + "\n\n" +
    NS_END + "\n"
)

with io.open(GCD, "w", encoding="utf-8", newline="") as f:
    f.write(merged)
print(f"Wrote merged {GCD} ({merged.count(chr(10))} lines)")

os.remove(FIB)
print(f"Removed {FIB}")

# Drop FibBounds from the subfolder umbrella.
umb = read(UMB)
drop = "import FormalRV.Shor.MainAlgorithm.PostProcessingAndMeasurement.EuclideanIterationFibBounds\n"
assert drop in umb, "umbrella import of FibBounds not found"
umb = umb.replace(drop, "")
with io.open(UMB, "w", encoding="utf-8", newline="") as f:
    f.write(umb)
print(f"Dropped FibBounds import from {UMB}")
