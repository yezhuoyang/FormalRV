"""
Cross-validate our ZX-as-IR / PPM framework against Tan-Niu-Gidney's LaSsynth
source (the 'stimzx' library = Gidney's ZX->stabilizer-flow tool) AND Stim.

Thesis under test (our Lean ZXStabilizer.lean + SurgeryReduction.lean):
  a lattice surgery, expressed as a ZX diagram, GOES THROUGH PPM, and the PPM
  realization has the SAME stabilizer flows as the ZX diagram.

We test it on the canonical CNOT-via-lattice-surgery:
  (A) ZX side  - stimzx computes the external stabilizers (flows) of the CNOT
                 ZX diagram (the gold standard).
  (B) PPM side - our framework realizes the SAME surgery as a PPM sequence
                 (init ancilla |0>, M_XX(A,T), M_ZZ(A,C), M_X(A)); Stim confirms
                 it has the same flows (modulo measurement-record byproducts -
                 the 'off-chip Pauli corrections' of Tan Fig.4c).
Both must agree.
"""
import os, sys
# Point LASSYNTH_DIR at the Tan-Niu-Gidney isca24_SAT_scalpel source (contains stimzx/).
SCALPEL = os.environ.get("LASSYNTH_DIR",
    r"C:/Users/yezhu/Documents/resourceFormal/scalpel_x/isca24_SAT_scalpel")
sys.path.insert(0, SCALPEL)
try:
    import stimzx
except ImportError:
    sys.exit(f"stimzx not found - set LASSYNTH_DIR to the isca24_SAT_scalpel source (tried {SCALPEL})")
import stim

# (A) ZX side: gold-standard CNOT flows from the ZX diagram.
g = stimzx.text_diagram_to_zx_graph(r'''
in----Z------out
      |
in----X------out
''')
zx = {(str(e.input), str(e.output)) for e in stimzx.zx_graph_to_external_stabilizers(g)}
print("(A) stimzx ZX-diagram CNOT flows (input -> output):")
for i, o in sorted(zx): print(f"     {i} -> {o}")
assert zx == {("+X_","+XX"), ("+Z_","+Z_"), ("+_X","+_X"), ("+_Z","+ZZ")}, zx
print("    -> matches the 4 defining CNOT flows.")

# (B) PPM side: the lattice-surgery merge sequence (our IR). C=0, T=1, A=2.
c = stim.Circuit("R 2\nMPP X2*X1\nMPP Z2*Z0\nMX 2")
ppm_checks = [
    ("X_ -> XX (control X spreads to target)", "X0 -> X0*X1 xor rec[0] xor rec[2]"),
    ("Z_ -> Z_ (control Z preserved)",          "Z0 -> Z0"),
    ("_X -> _X (target X preserved)",           "X1 -> X1"),
    ("_Z -> ZZ (target Z spreads to control)",  "Z1 -> Z0*Z1 xor rec[1]"),
]
print("\n(B) our PPM realization (Stim) - same CNOT flows (mod byproduct records):")
ok = True
for desc, fl in ppm_checks:
    r = c.has_flow(stim.Flow(fl))
    ok = ok and r
    print(f"     [{'PASS' if r else 'FAIL'}] {desc}: {fl}")

print("\nZX (stimzx)  ==  PPM (Stim)  for the CNOT-via-lattice-surgery."
      if ok else "\nMISMATCH"); sys.exit(0 if ok else 1)
