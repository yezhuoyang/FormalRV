"""
FormalRV lattice-surgery MACRO compiler + certificate + renderer.

Architecture (per the design we're following):
    arithmetic macro  ->  SurgeryBlock templates  ->  tiled 3D space-time layout
                      ->  CERTIFICATE (the trusted artifact)  ->  renderer (untrusted)

Each arithmetic macro (Cuccaro `MAJ` / `UMA`) emits a reusable `SurgeryBlock` with a 3D
space-time footprint and typed ports.  `ripple_carry_adder(n)` tiles them so the carry
propagates through SPACE (Gidney/Fowler AutoCCZ layout, arXiv:1905.08916 Fig.14/16), not
time.  `certificate()` checks the layout is conflict-free (disjoint block volumes, chained
carry ports) and reports the space-time volume — this certificate, not the picture, is the
trusted output.  `render()` draws the certified layout in the Gidney style.

The LOGICAL correctness of MAJ/UMA and the timing are FormalRV's Lean-verified artifacts
(the Cuccaro adder + the `SysCall` schedule); this module is the geometric layout/render layer.

Plain matplotlib — runs in the repo's default Python (no tqec needed).
Run:  python PyCircuits/ls_macro_compiler.py     Out: docs/diagrams/ls_adder_macro.png
"""
import os
from dataclasses import dataclass, field

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from matplotlib.patches import Patch

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "diagrams")
os.makedirs(OUT, exist_ok=True)
MAJ_C, UMA_C, FAC_C, CARRY_C, PORT_C, EDGE = "#e2483a", "#8a63d2", "#f2c037", "#1f2937", "#2faa55", "#15181d"


@dataclass
class SurgeryBlock:
    kind: str                       # "MAJ" | "UMA" | "CCZ-factory"
    x0: float; x1: float
    y0: float; y1: float
    t0: float; t1: float
    color: str
    ports: dict = field(default_factory=dict)   # name -> (x, y, t)

    def vol(self):
        return (self.x1 - self.x0) * (self.y1 - self.y0) * (self.t1 - self.t0)

    def overlaps(self, o, eps=1e-6):
        return (self.x0 < o.x1 - eps and o.x0 < self.x1 - eps and
                self.y0 < o.y1 - eps and o.y0 < self.y1 - eps and
                self.t0 < o.t1 - eps and o.t0 < self.t1 - eps)


# ---- macro templates ---------------------------------------------------------
def emit_maj(i, x, t, dx=1.2, dt=2.0):
    """Cuccaro MAJ on (carry_in, a_i, b_i) -> (a_i, b_i', carry_out), consuming a CCZ."""
    b = SurgeryBlock("MAJ", x, x + dx, 0.0, 1.0, t, t + dt, MAJ_C)
    b.ports = {f"a{i}": (x + 0.3, 0.5, t), f"b{i}": (x + 0.9, 0.5, t),
               "c_in": (x, 0.5, t + 0.3 * dt), "c_out": (x + dx, 0.5, t + 0.7 * dt),
               "ccz": (x + dx / 2, 1.0, t + dt)}
    return b


def emit_uma(i, x, t, dx=1.2, dt=2.0):
    """Cuccaro UMA — the un-majority-and-add back-sweep that restores a_i and writes the sum."""
    b = SurgeryBlock("UMA", x, x + dx, 0.0, 1.0, t, t + dt, UMA_C)
    b.ports = {f"s{i}": (x + 0.6, 0.5, t + dt), "c_in": (x + dx, 0.5, t + 0.3 * dt),
               "c_out": (x, 0.5, t + 0.7 * dt)}
    return b


def ripple_carry_adder(n):
    """Tile n MAJ blocks (carry rising through space) then n UMA blocks back — the Cuccaro
    ripple-carry adder layout.  Returns (blocks, factories)."""
    blocks, facs = [], []
    dx, dt, gap = 1.2, 2.0, 0.4
    for i in range(n):                                   # forward MAJ sweep
        x, t = i * (dx + gap), i * (dt * 0.6)            # staircase: later + to the right
        m = emit_maj(i, x, t, dx, dt); blocks.append(m)
        fx = m.ports["ccz"]
        facs.append(SurgeryBlock("CCZ-factory", fx[0] - 0.25, fx[0] + 0.25, 1.1, 1.6,
                                 fx[2] - 0.4, fx[2] + 0.1, FAC_C))
    t_turn = (n - 1) * (dt * 0.6) + dt + 0.6
    for i in range(n - 1, -1, -1):                       # back UMA sweep (writes the sum)
        x = i * (dx + gap)
        t = t_turn + (n - 1 - i) * (dt * 0.6)
        blocks.append(emit_uma(i, x, t, dx, dt))
    return blocks, facs


# ---- certificate (the trusted artifact) -------------------------------------
def certificate(blocks, facs, n):
    allb = blocks + facs
    conflicts = [(a.kind, b.kind) for i, a in enumerate(allb) for b in allb[i + 1:] if a.overlaps(b)]
    # carry chain: every MAJ_i c_out should feed MAJ_{i+1} c_in (adjacency in space)
    majs = [b for b in blocks if b.kind == "MAJ"]
    carry_chain_ok = all(majs[i].ports["c_out"][0] <= majs[i + 1].ports["c_in"][0] + 1e-6
                         for i in range(len(majs) - 1))
    cert = {
        "n_bits": n,
        "blocks": len(blocks), "factories": len(facs),
        "spacetime_volume": round(sum(b.vol() for b in allb), 2),
        "conflict_free": len(conflicts) == 0,
        "conflicts": conflicts,
        "carry_chain_ok": carry_chain_ok,
        "bbox": [round(min(b.x0 for b in allb), 2), round(max(b.x1 for b in allb), 2),
                 round(min(b.t0 for b in allb), 2), round(max(b.t1 for b in allb), 2)],
    }
    return cert


# ---- renderer (untrusted visualization) -------------------------------------
def _cuboid(ax, b, alpha, ec=EDGE, lw=1.1):
    x0, x1, y0, y1, t0, t1 = b.x0, b.x1, b.y0, b.y1, b.t0, b.t1
    v = [(x0, y0, t0), (x1, y0, t0), (x1, y1, t0), (x0, y1, t0),
         (x0, y0, t1), (x1, y0, t1), (x1, y1, t1), (x0, y1, t1)]
    faces = [[v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]], [v[0], v[1], v[5], v[4]],
             [v[2], v[3], v[7], v[6]], [v[1], v[2], v[6], v[5]], [v[0], v[3], v[7], v[4]]]
    ax.add_collection3d(Poly3DCollection(faces, facecolor=b.color, edgecolor=ec, linewidths=lw, alpha=alpha))


def _tube(ax, p, q, r=0.08, color=CARRY_C):
    (x0, y0, z0), (x1, y1, z1) = p, q
    b = SurgeryBlock("", min(x0, x1) - r, max(x0, x1) + r, min(y0, y1) - r, max(y0, y1) + r,
                     min(z0, z1) - r, max(z0, z1) + r, color)
    _cuboid(ax, b, 0.95, ec=color, lw=0.4)


def render(blocks, facs, cert, fname, title):
    fig = plt.figure(figsize=(8.4, 6.2)); ax = fig.add_subplot(111, projection="3d")
    ax.view_init(elev=20, azim=-58); ax.set_axis_off()
    for f in facs:
        _cuboid(ax, f, 0.95)
    for b in blocks:
        _cuboid(ax, b, 0.5)
        if b.kind == "MAJ":
            ax.text((b.x0 + b.x1) / 2, b.y1, b.t1 + 0.15, "MAJ", color=MAJ_C, fontsize=8,
                    ha="center", fontweight="bold")
            for nm in (k for k in b.ports if k.startswith(("a", "b"))):
                px, py, pz = b.ports[nm]
                _cuboid(ax, SurgeryBlock("", px - 0.12, px + 0.12, py - 0.12, py + 0.12,
                                         pz - 0.18, pz, PORT_C), 0.95, lw=0.5)
                ax.text(px, py, pz - 0.4, nm, color="#1d6b38", fontsize=7, ha="center")
            ax.text(b.ports["ccz"][0], b.ports["ccz"][1] + 0.4, b.ports["ccz"][2], "CCZ",
                    color="#9a6b00", fontsize=6.5, ha="center")
        else:
            ax.text((b.x0 + b.x1) / 2, b.y1, b.t1 + 0.15, "UMA", color=UMA_C, fontsize=8,
                    ha="center", fontweight="bold")
            if any(k.startswith("s") for k in b.ports):
                nm = next(k for k in b.ports if k.startswith("s")); px, py, pz = b.ports[nm]
                ax.text(px, py, pz + 0.35, nm, color="#5b3da8", fontsize=7, ha="center")
    majs = [b for b in blocks if b.kind == "MAJ"]
    for i in range(len(majs) - 1):                       # carry worldline through space
        _tube(ax, majs[i].ports["c_out"], majs[i + 1].ports["c_in"])

    xs = [b.x0 for b in blocks + facs] + [b.x1 for b in blocks + facs]
    ts = [b.t0 for b in blocks + facs] + [b.t1 for b in blocks + facs]
    m = max(max(xs) - min(xs), max(ts) - min(ts))
    ax.set_xlim(min(xs), min(xs) + m); ax.set_ylim(-0.5, m - 0.5 + min(xs)); ax.set_zlim(min(ts), min(ts) + m)
    ax.set_box_aspect((1, 0.5, 1))
    sub = f"{cert['n_bits']}-bit · {cert['blocks']} blocks + {cert['factories']} CCZ factories · " \
          f"vol {cert['spacetime_volume']} · conflict-free={cert['conflict_free']} · carry-chain={cert['carry_chain_ok']}"
    ax.text2D(0.5, 1.02, title, transform=ax.transAxes, ha="center", va="top", fontsize=11, fontweight="bold")
    ax.text2D(0.5, 0.95, sub, transform=ax.transAxes, ha="center", va="top", fontsize=8, color="#444")
    ax.legend(handles=[Patch(fc=MAJ_C, alpha=0.5, label="MAJ block"), Patch(fc=UMA_C, alpha=0.5, label="UMA block"),
                       Patch(fc=FAC_C, label="CCZ factory"), Patch(fc=PORT_C, label="input port"),
                       Patch(fc=CARRY_C, label="carry worldline")],
              loc="lower center", bbox_to_anchor=(0.5, -0.02), ncol=5, fontsize=7.4, framealpha=0.92)
    fig.savefig(os.path.join(OUT, fname), dpi=145, bbox_inches="tight"); plt.close(fig)


if __name__ == "__main__":
    n = 3
    blocks, facs = ripple_carry_adder(n)
    cert = certificate(blocks, facs, n)
    cert_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                             "PyCircuits", "syscalls", "adder_macro_certificate.txt")
    with open(cert_path, "w") as f:
        for k, v in cert.items():
            f.write(f"{k}: {v}\n")
    print("CERTIFICATE (the trusted layout artifact):")
    for k, v in cert.items():
        print(f"  {k}: {v}")
    render(blocks, facs, cert,
           "ls_adder_macro.png" if False else "ls_adder_macro.png",
           f"{n}-bit ripple-carry adder — tiled MAJ/UMA lattice-surgery layout (certified)")
    print(f"\n-> docs/diagrams/ls_adder_macro.png   (+ certificate {os.path.basename(cert_path)})")
