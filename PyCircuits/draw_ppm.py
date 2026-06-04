"""
Render FormalRV's compiled PPM programs in the Litinski "Game of Surface Codes"
Pauli-product-measurement style: logical qubits as horizontal wires, each
multi-qubit Pauli measurement drawn as a vertical column of colour-coded Pauli
boxes (X orange, Y yellow, Z green) joined by a bar, magic-T injections in
purple, and deferred Pauli-frame updates as dashed boxes.

The programs below are the VERBATIM output of `compileArithmeticGateToPPM`
(FormalRV/PPM/CircuitToPPMInterface/Part2.lean:159):
  X q     -> [frame X on q]
  CX c t  -> [measure ZZ on {c,t},  frame X on t]
  CCX a b t -> [useMagicT t,  measure ZZZ on {a,b,t},  frame X on t]
  seq     -> concatenation.

Run:  python PyCircuits/draw_ppm.py     Out: docs/diagrams/ppm_*.png
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)

PCOL = {"X": "#ED8936", "Y": "#ECC94B", "Z": "#48BB78"}   # Pauli palette
MAGIC = "#9F7AEA"                                          # magic-T injection


def draw_ppm(program, nq, title, outfile, qlabels=None):
    """program: list of columns. Each column is a dict:
       {'op':'measure','pauli':'Z','qubits':[...]}        joint Pauli measurement
       {'op':'frame','pauli':'X','qubits':[q]}            deferred Pauli-frame update
       {'op':'magicT','qubits':[q]}                       consume one |T> token
    """
    ncol = len(program)
    fig, ax = plt.subplots(figsize=(1.7 + 1.25 * ncol, 0.7 + 0.85 * nq))
    ax.set_xlim(-0.2, ncol + 1.2); ax.set_ylim(-0.7, nq - 0.3); ax.axis("off")
    ypos = lambda q: nq - 1 - q                      # q0 on top
    # qubit wires + labels
    for q in range(nq):
        ax.plot([0.1, ncol + 0.9], [ypos(q), ypos(q)], color="#999", lw=1.2, zorder=1)
        lab = qlabels[q] if qlabels else f"q{q}"
        ax.text(-0.05, ypos(q), f"$|{lab}\\rangle$", ha="right", va="center", fontsize=12)
    bw, bh = 0.62, 0.62
    for i, col in enumerate(program):
        x = i + 0.8
        qs = col["qubits"]
        # connecting bar for multi-qubit measurements
        if col["op"] == "measure" and len(qs) > 1:
            ax.plot([x, x], [ypos(max(qs)), ypos(min(qs))], color="#2f855a", lw=2.4, zorder=2)
        for q in qs:
            y = ypos(q)
            if col["op"] == "measure":
                p = col["pauli"]; fc = PCOL[p]
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=fc, ec="#1a4731", lw=1.6, zorder=3))
                ax.text(x, y, p, ha="center", va="center", fontsize=12.5, fontweight="bold", color="white", zorder=4)
            elif col["op"] == "frame":
                p = col["pauli"]
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=PCOL[p] + "55", ec=PCOL[p],
                             lw=1.6, ls="--", zorder=3))
                ax.text(x, y, p, ha="center", va="center", fontsize=11.5, fontweight="bold", color="#9c4221", zorder=4)
            elif col["op"] == "magicT":
                ax.add_patch(FancyBboxPatch((x - bw / 2, y - bh / 2), bw, bh,
                             boxstyle="round,pad=0.02", fc=MAGIC, ec="#44337a", lw=1.6, zorder=3))
                ax.text(x, y, "T", ha="center", va="center", fontsize=12.5, fontweight="bold", color="white", zorder=4)
        # column caption
        cap = {"measure": "$M_{" + col.get("pauli", "") * len(qs) + "}$",
               "frame": "frame", "magicT": "$|T\\rangle$"}[col["op"]]
        ax.text(x, -0.55, cap, ha="center", va="center", fontsize=9, color="#444")
    ax.set_title(title, fontsize=11.5, fontweight="bold")
    # legend
    handles = [plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["Z"], mec="#1a4731", label="Z measure"),
               plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=PCOL["X"] + "55", mec=PCOL["X"], label="X frame (deferred)"),
               plt.Line2D([0], [0], marker="s", ls="", ms=11, mfc=MAGIC, mec="#44337a", label="magic-T inject")]
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.5, -0.02),
              ncol=3, frameon=False, fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, outfile), dpi=140, bbox_inches="tight")
    plt.close(fig)
    print(f"  drew {outfile}  ({ncol} PPM columns, {nq} qubits)")


print("FormalRV compiled PPM programs (Litinski PPM style):")

# compileArithmeticGateToPPM (CX 0 1)
draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]},
          {"op": "frame", "pauli": "X", "qubits": [1]}],
         2, "compileArithmeticGateToPPM (CX 0 1)  —  CNOT as a joint ZZ measurement + X-frame",
         "ppm_cx.png")

# compileArithmeticGateToPPM (CCX 0 1 2)
draw_ppm([{"op": "magicT", "qubits": [2]},
          {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (CCX 0 1 2)  —  Toffoli = magic-T inject + joint ZZZ + X-frame",
         "ppm_ccx.png")

# a small composite: seq (CX 0 1) (CCX 0 1 2)  (concatenation of programs)
draw_ppm([{"op": "measure", "pauli": "Z", "qubits": [0, 1]},
          {"op": "frame", "pauli": "X", "qubits": [1]},
          {"op": "magicT", "qubits": [2]},
          {"op": "measure", "pauli": "Z", "qubits": [0, 1, 2]},
          {"op": "frame", "pauli": "X", "qubits": [2]}],
         3, "compileArithmeticGateToPPM (seq (CX 0 1) (CCX 0 1 2))  —  programs concatenate",
         "ppm_seq.png")

print("\nPPM diagrams written to docs/diagrams/")
