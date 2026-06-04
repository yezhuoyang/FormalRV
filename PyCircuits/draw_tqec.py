"""
TQEC-style 3D spacetime diagrams of the lattice-surgery computations FormalRV
verifies.  Time runs UP (z).  A logical surface-code patch is a box whose
vertical faces carry the boundary type (X = red / rough, Z = blue / smooth); a
lattice-surgery MERGE is a connecting tube coloured by the measured Pauli type
(X-merge bright red, Z-merge bright blue).

Schematic note: FormalRV verifies the abstract `SurgeryGadget` (merged parity
rows + Pauli frame, by `decide`); these diagrams are its spacetime view.  The
three X̄-measurement gadgets (surface / Steane / bivariate-bicycle) are VERIFIED;
the CNOT panel is the standard construction shown for orientation (no verified
CNOT object exists yet — see honest scope in the README).

Run:  python PyCircuits/draw_tqec.py     Out: docs/diagrams/tqec_*.png
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
XR, ZB = "#e53e3e", "#3182ce"            # saturated X / Z (merges)
XRL, ZBL, TM = "#fc8181", "#90cdf4", "#e2e8f0"   # light X / Z boundaries, time faces


def box(ax, o, s, fx, fz, ft, alpha=0.9, ec="#2d3748", lw=0.6):
    x, y, z = o; dx, dy, dz = s
    v = [(x, y, z), (x+dx, y, z), (x+dx, y+dy, z), (x, y+dy, z),
         (x, y, z+dz), (x+dx, y, z+dz), (x+dx, y+dy, z+dz), (x, y+dy, z+dz)]
    for poly, fc in [([v[0], v[3], v[7], v[4]], fx), ([v[1], v[2], v[6], v[5]], fx),
                     ([v[0], v[1], v[5], v[4]], fz), ([v[3], v[2], v[6], v[7]], fz),
                     ([v[0], v[1], v[2], v[3]], ft), ([v[4], v[5], v[6], v[7]], ft)]:
        ax.add_collection3d(Poly3DCollection([poly], facecolor=fc, edgecolor=ec, linewidths=lw, alpha=alpha))


def patch(ax, x, y, z0, z1, w=1.2):
    box(ax, (x, y, z0), (w, w, z1 - z0), XRL, ZBL, TM, alpha=0.55)


def merge_x(ax, x0, x1, y, z0, z1, kind, w=1.0):
    c = XR if kind == "X" else ZB
    box(ax, (x0, y + (1.2 - w) / 2, z0), (x1 - x0, w, z1 - z0), c, c, c, alpha=0.96)


def newfig(title, sz=(7.6, 6.6), elev=18, azim=-60):
    fig = plt.figure(figsize=sz); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=elev, azim=azim); ax.set_axis_off()
    ax.text2D(0.5, 0.97, title, transform=ax.transAxes, ha="center", va="top", fontsize=11, fontweight="bold")
    return fig, ax


def finish(ax, fig, name, lim, legend=True):
    ax.set_xlim(0, lim[0]); ax.set_ylim(0, lim[1]); ax.set_zlim(0, lim[2])
    ax.set_box_aspect(lim)
    if legend:
        ax.legend(handles=[Patch(fc=XR, label="X-merge / X boundary"),
                           Patch(fc=ZB, label="Z-merge / Z boundary"),
                           Patch(fc=TM, label="time slice (init/measure)")],
                  loc="lower left", fontsize=8, framealpha=0.9)
    fig.savefig(os.path.join(OUT, name), dpi=140, bbox_inches="tight"); plt.close(fig)
    print(f"  drew {name}")


def xbar_panel(ax, codelabel, tau_s):
    """A logical-X̄ measurement: data patch + ancilla, joined by an X-merge tube of
    height ~ tau_s, then the ancilla is measured."""
    H = 2 + tau_s + 2
    patch(ax, 0, 0, 0, H)                         # data patch, full time
    zmid = 2
    patch(ax, 2.6, 0, zmid - 0.4, zmid + tau_s + 0.4)   # ancilla patch
    merge_x(ax, 1.2, 2.6, 0, zmid, zmid + tau_s, "X")   # X-merge tube
    ax.text(0.6, 0.6, H + 0.3, codelabel, fontsize=9, ha="center")
    ax.text(3.2, 0.6, zmid + tau_s + 0.7, "ancilla", fontsize=8, ha="center")
    return H


# ---- 1. surface3 X̄ measurement (verified) ----
fig, ax = newfig("Lattice-surgery logical-X̄ measurement, surface [[13,1,3]]\n"
                 "surface3_x_surgery — verify_surgery_gadget = true (decide)")
H = xbar_panel(ax, "data [[13,1,3]]", 2)
ax.text(1.9, 1.7, 3.0, "X̄ merge\n(X-type, τ_s=2)", fontsize=8, ha="center", color="#9b2c2c")
finish(ax, fig, "tqec_xbar.png", (4, 2, H + 1))

# ---- 2. the three VERIFIED code families side by side ----
fig = plt.figure(figsize=(13.5, 5.2))
fig.suptitle("The same verified logical-X̄ surgery, across code families  "
             "(verify_surgery_gadget = true, decide)", fontsize=12, fontweight="bold")
for i, (lab, tau, thm) in enumerate([("surface [[13,1,3]]", 2, "surface3_x_surgery_verifies"),
                                     ("Steane [[7,1,3]]", 2, "steane_x_surgery_verifies"),
                                     ("biv.-bicycle [[18,2,6]]", 4, "bb_x_surgery_verifies")]):
    ax = fig.add_subplot(1, 3, i + 1, projection="3d")
    ax.view_init(elev=18, azim=-60); ax.set_axis_off()
    H = xbar_panel(ax, lab, tau)
    ax.text2D(0.5, 0.05, thm, transform=ax.transAxes, ha="center", fontsize=8, color="#2f855a")
    ax.set_xlim(0, 4); ax.set_ylim(0, 2); ax.set_zlim(0, H + 1); ax.set_box_aspect((4, 2, H + 1))
fig.savefig(os.path.join(OUT, "tqec_codes.png"), dpi=140, bbox_inches="tight"); plt.close(fig)
print("  drew tqec_codes.png")

# ---- 3. CCZ magic-injection schedule: 3 surgery merges (cczInjectionSchedule) ----
fig, ax = newfig("CCZ magic-injection schedule — 3 surgery merges\n"
                 "cczInjectionSchedule = [mA, mB, mC]  (each a verified SurgeryGadget)")
patch(ax, 0, 0, 0, 8)                                          # data block, full time
for k, z0 in enumerate([1, 3.4, 5.8]):                         # three sequential merges
    patch(ax, 2.6, 0, z0 - 0.3, z0 + 1.6)                      # magic-state ancilla patch
    merge_x(ax, 1.2, 2.6, 0, z0, z0 + 1.3, "X")
    ax.text(3.25, 0.6, z0 + 1.7, f"m{chr(65+k)}", fontsize=8, ha="center")
ax.text(0.6, 0.6, 8.3, "data block", fontsize=9, ha="center")
finish(ax, fig, "tqec_ccz.png", (4, 2, 9))

# ---- 4. lattice-surgery CNOT (ILLUSTRATIVE — standard construction) ----
fig, ax = newfig("Lattice-surgery CNOT (standard construction — illustrative)\n"
                 "ZZ-merge then XX-merge then measure ancilla; FormalRV verifies each merge as a gadget",
                 sz=(8.2, 6.6))
patch(ax, 0, 0, 0, 6)            # control
patch(ax, 2.6, 0, 0, 6)         # ancilla (|+>), measured at top
patch(ax, 5.2, 0, 0, 6)         # target
merge_x(ax, 1.2, 2.6, 0, 1.2, 2.4, "Z")     # ZZ merge control-ancilla (blue)
merge_x(ax, 3.8, 5.2, 0, 3.4, 4.6, "X")     # XX merge ancilla-target (red)
ax.text(0.6, 0.6, 6.3, "control", fontsize=9, ha="center")
ax.text(3.2, 0.6, 6.3, "ancilla |+⟩", fontsize=9, ha="center")
ax.text(5.8, 0.6, 6.3, "target", fontsize=9, ha="center")
ax.text(1.9, 1.7, 1.8, "ZZ\n(Z-merge)", fontsize=8, ha="center", color="#2a4365")
ax.text(4.5, 1.7, 4.0, "XX\n(X-merge)", fontsize=8, ha="center", color="#9b2c2c")
finish(ax, fig, "tqec_cnot.png", (7, 2, 7))

print("\nTQEC diagrams written to docs/diagrams/")
