"""
Render GENUINE, circuit-derived spacetime diagrams of the Lean-emitted lattice-surgery
circuits, using Stim's native diagram tool (not hand-drawn). Each diagram is produced
directly from a `.stim` file the FormalRV emitters wrote, so it faithfully shows the
actual qubits / operations of the verified surgery — no manual positioning.

`timeline-svg`  = the circuit as a left-to-right timeline (the real RX/CX/MX schedule).
`timeslice-svg` = the qubit layout / operations per time-slice.
SVG → PNG via cairosvg.

Run:  python PyCircuits/draw_stim_spacetime.py     Out: docs/diagrams/stim_*.png
"""
import os
import stim
import cairosvg

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)


def render(stim_rel, name, dtype="timeline-svg", width=1700):
    path = os.path.join(ROOT, stim_rel)
    if not os.path.exists(path):
        print(f"  SKIP {name}: {stim_rel} not found")
        return
    c = stim.Circuit.from_file(path)
    svg = str(c.diagram(dtype))
    cairosvg.svg2png(bytestring=svg.encode("utf-8"),
                     write_to=os.path.join(OUT, name + ".png"), output_width=width)
    print(f"  drew {name}.png  ({dtype} of {stim_rel}: {c.num_qubits} qubits, {c.num_measurements} meas)")


print("Stim-rendered spacetime diagrams (from the Lean-emitted .stim circuits):")
# the verified surface3 logical-X̄ surgery (StimEmit.surgeryToStim surface3_x_surgery)
render("PyCircuits/surface3_surgery.stim", "stim_surface3_surgery", "timeline-svg", width=1700)
render("PyCircuits/surface3_surgery.stim", "stim_surface3_timeslice", "timeslice-svg", width=900)
# the distance-5 full-Shor lattice-surgery prefix (emitShorPrefixAtDistance 15 2 5 3)
render("PyCircuits/shor_distance5_demo.stim", "stim_shor_d5_prefix", "timeline-svg", width=1700)
print("\nStim spacetime diagrams written to docs/diagrams/")
