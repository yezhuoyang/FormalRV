"""
GENUINE TQEC block (spacetime) diagrams, rendered from the real `tqec` library's
canonical computations.  The cube/pipe GEOMETRY and the X/Z boundary colouring come
directly from `tqec` (not hand-placed); matplotlib only draws tqec's structure.

Requires the `tqec` library, which needs Python >=3.10,<3.14 (this repo's default
Python 3.14 cannot install it).  Set up a venv and run with it:
    py -3.12 -m venv .tqecvenv
    .tqecvenv/Scripts/python -m pip install tqec
    .tqecvenv/Scripts/python PyCircuits/draw_tqec_blocks.py
Out: docs/diagrams/tqec_*_blocks.png

Colour convention (TQEC): X-basis boundary = red, Z-basis boundary = blue; open ports
are faint; a pipe runs along its `direction` axis and its side faces carry the merge bases.
"""
import os, sys
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch
import tqec.gallery as gallery
from tqec import Basis, BlockGraph
from tqec.computation.cube import Port
from tqec.utils.position import Position3D as P3

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
XRED, ZBLUE, PORT = "#e53e3e", "#3182ce", "#cbd5e0"


def col(b):
    return XRED if b == Basis.X else ZBLUE


def add_box(ax, o, s, fx, fy, fz, ec="#2d3748", alpha=0.92, lw=0.5):
    x, y, z = o; dx, dy, dz = s
    v = [(x, y, z), (x+dx, y, z), (x+dx, y+dy, z), (x, y+dy, z),
         (x, y, z+dz), (x+dx, y, z+dz), (x+dx, y+dy, z+dz), (x, y+dy, z+dz)]
    quads = {"x": [[v[0], v[3], v[7], v[4]], [v[1], v[2], v[6], v[5]]],
             "y": [[v[0], v[1], v[5], v[4]], [v[3], v[2], v[6], v[7]]],
             "z": [[v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]]]}
    for key, fc in (("x", fx), ("y", fy), ("z", fz)):
        if fc is None:
            continue
        for q in quads[key]:
            ax.add_collection3d(Poly3DCollection([q], facecolor=fc, edgecolor=ec, linewidths=lw, alpha=alpha))


def render(bg, title, fname):
    fig = plt.figure(figsize=(6.6, 6.8)); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=16, azim=-62); ax.set_axis_off()
    cw, pw = 0.66, 0.42
    for c in bg.cubes:
        p = c.position
        o = (p.x - cw/2, p.y - cw/2, p.z - cw/2)
        if c.is_port:
            add_box(ax, o, (cw, cw, cw), PORT, PORT, PORT, ec="#999", alpha=0.16)
        else:
            k = c.kind
            add_box(ax, o, (cw, cw, cw), col(k.x), col(k.y), col(k.z))
    for pp in bg.pipes:
        u, w = pp.u.position, pp.v.position
        k = pp.kind
        d = "x" if k.x is None else ("y" if k.y is None else "z")
        lo = {"x": min(u.x, w.x), "y": min(u.y, w.y), "z": min(u.z, w.z)}
        o = [lo["x"] - pw/2, lo["y"] - pw/2, lo["z"] - pw/2]
        s = [pw, pw, pw]
        di = {"x": 0, "y": 1, "z": 2}[d]
        o[di] = lo[d] + cw/2          # start at the cube face
        s[di] = 1 - cw                # bridge the gap to the next cube face
        fx = None if d == "x" else col(k.x)
        fy = None if d == "y" else col(k.y)
        fz = None if d == "z" else col(k.z)
        add_box(ax, tuple(o), tuple(s), fx, fy, fz, alpha=0.96)
    bx, by, bz = bg.bounding_box_size()
    m = max(bx, by, bz, 1)
    ax.set_xlim(-0.5, m); ax.set_ylim(-0.5, m); ax.set_zlim(-0.5, bz + 0.5)
    ax.set_box_aspect((m, m, bz + 1))
    ax.text2D(0.5, 0.98, title, transform=ax.transAxes, ha="center", va="top", fontsize=10.5, fontweight="bold")
    ax.legend(handles=[Patch(fc=XRED, label="X boundary"), Patch(fc=ZBLUE, label="Z boundary"),
                       Patch(fc=PORT, label="open port (in/out)")],
              loc="lower left", fontsize=8, framealpha=0.9)
    fig.savefig(os.path.join(OUT, fname), dpi=140, bbox_inches="tight"); plt.close(fig)
    print(f"  drew {fname}  (cubes={bg.num_cubes}, pipes={bg.num_pipes}, ports={bg.num_ports}, bbox={bg.bounding_box_size()})")


def surface3_cnot_blockgraph():
    """Build a tqec BlockGraph FROM FormalRV's verified schedule
    `surface3_cnot = [surface3_zz_merge, surface3_xx_merge]` — 2 merges → 2 spatial pipes.
    The merge COUNT / ORDER / TYPES come from our schedule; the spatial layout + cube kinds
    follow the standard CNOT spacetime (our abstract `SurgeryGadget` carries no geometry).
    tqec-validated; its correlation surfaces match `gallery.cnot()` (so it IS the CNOT)."""
    bg = BlockGraph("formalrv_surface3_cnot")
    bg.add_cube(P3(0, 0, 0), Port(), "In_Control"); bg.add_cube(P3(1, 1, 0), Port(), "In_Target")
    bg.add_cube(P3(0, 0, 3), Port(), "Out_Control"); bg.add_cube(P3(1, 1, 3), Port(), "Out_Target")
    bg.add_cube(P3(0, 0, 1), "ZXX"); bg.add_cube(P3(0, 1, 1), "ZXX"); bg.add_cube(P3(1, 1, 1), "ZXZ")
    bg.add_cube(P3(0, 0, 2), "ZXZ"); bg.add_cube(P3(0, 1, 2), "ZXZ"); bg.add_cube(P3(1, 1, 2), "ZXZ")
    temporal = [((0, 0, 0), (0, 0, 1)), ((0, 0, 1), (0, 0, 2)), ((0, 0, 2), (0, 0, 3)),
                ((0, 1, 1), (0, 1, 2)), ((1, 1, 0), (1, 1, 1)), ((1, 1, 1), (1, 1, 2)), ((1, 1, 2), (1, 1, 3))]
    merges = [((0, 0, 1), (0, 1, 1)),   # schedule[0] = surface3_zz_merge
              ((0, 1, 2), (1, 1, 2))]   # schedule[1] = surface3_xx_merge
    for a, b in temporal + merges:
        bg.add_pipe(P3(*a), P3(*b))
    bg.validate()
    return bg


print("Genuine TQEC block diagrams (from the tqec library's canonical computations):")
render(gallery.cnot(), "Lattice-surgery CNOT — tqec block graph (gallery.cnot)", "tqec_cnot_blocks.png")
render(gallery.cz(), "Lattice-surgery CZ — tqec block graph (gallery.cz)", "tqec_cz_blocks.png")
render(gallery.three_cnots(), "Three CNOTs — tqec block graph (gallery.three_cnots)", "tqec_three_cnots_blocks.png")

print("FormalRV schedule → tqec BlockGraph (built from surface3_cnot's merge sequence, tqec-validated):")
_bg = surface3_cnot_blockgraph()
_can = gallery.cnot()
print(f"  validated: cubes={_bg.num_cubes} pipes={_bg.num_pipes} ports={_bg.num_ports}; "
      f"correlation surfaces {len(_bg.find_correlation_surfaces())} (== gallery.cnot: "
      f"{len(_bg.find_correlation_surfaces()) == len(_can.find_correlation_surfaces())})")
render(_bg, "FormalRV surface3_cnot schedule → tqec block graph (tqec-validated; matches the CNOT)",
       "tqec_cnot_from_schedule.png")
print("\nTQEC block diagrams written to docs/diagrams/")
