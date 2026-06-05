#!/usr/bin/env python3
"""
Compile the FormalRV distance-3 two-patch surface-code XX-merge onto a neutral-atom zoned
architecture with ZAC (UCLA-VAST, HPCA'25), and render a GIF of the atom movement that
implements the lattice surgery.

  python run_zac_surgery.py            # full merge
  python run_zac_surgery.py <N>        # only the first N CZ-gate worth of QASM (smaller GIF)

Pipeline:  surface3_xx_merge.qasm  --ZAC-->  ZAIR atom-movement schedule  -->  GIF (PillowWriter).
The animation shows AOD pickups, big moves storage<->entanglement zone, and Rydberg CZ flashes
(the merge's syndrome-extraction two-qubit gates) — the neutral-atom realization of the surgery.
"""
import json
import os
import sys

ZAC_PATH = r"C:/Users/yezhu/Documents/VerifyShor/ZAC"
sys.path.insert(0, ZAC_PATH)

from zac.ds.architecture import Architecture
from zac.zac import ZAC
from zac.animator import animator as animator_module
from matplotlib.animation import PillowWriter, FuncAnimation
import matplotlib
matplotlib.use("Agg")
import matplotlib.patches  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ARCH = os.path.join(HERE, "surface3_surgery_arch.json")
QASM = os.path.join(HERE, "surface3_xx_merge.qasm")
GIF = os.path.join(HERE, "surface3_xx_merge_neutral_atom.gif")
OUT_DIR = os.path.join(HERE, "zac_result")

_orig_update_init = animator_module.Animator.update_init
ZONE_LABELS = [
    {"name": "MEMORY / STORAGE ZONE\n53 atoms = 27 data+surgery-ancilla + 26 syndrome ancillas",
     "color": "#1f77b4", "xy": (-2, -3), "wh": (34, 23)},
    {"name": "ENTANGLEMENT ZONE  (pairwise Rydberg CZ = the merge's syndrome gates)",
     "color": "#2ca02c", "xy": (-2, 26), "wh": (124, 60)},
]


def patched_update_init(self):
    res = _orig_update_init(self)
    for z in ZONE_LABELS:
        self.ax.add_patch(matplotlib.patches.Rectangle(
            z["xy"], z["wh"][0], z["wh"][1], linewidth=2, edgecolor=z["color"],
            facecolor=z["color"], alpha=0.07, zorder=-10))
        self.ax.text(z["xy"][0] + z["wh"][0] / 2, z["xy"][1] + z["wh"][1] / 2, z["name"],
                     color=z["color"], fontsize=10, fontweight="bold", ha="center", va="center",
                     alpha=0.6, zorder=-9)
    return res


animator_module.Animator.update_init = patched_update_init


def patched_animate(self, code, output, scaling_factor=4, font=8, ffmpeg="ffmpeg"):
    matplotlib.rcParams.update({"font.size": font})
    self.code = code
    self.fig, self.ax = self.setup_canvas(scaling_factor)
    self.title = self.ax.set_title("")
    self.inst_str = ""
    num_frame = self.create_schedule()
    print(f"    animation frames: {self.INIT_FRM + num_frame}")
    anim = FuncAnimation(self.fig, self.update, init_func=self.update_init,
                         frames=self.INIT_FRM + num_frame)
    anim.save(output, writer=PillowWriter(fps=self.FPS))


animator_module.Animator.animate = patched_animate


def maybe_prefix_qasm(max_cz):
    """Write a prefix QASM with at most max_cz cx gates, for a shorter GIF; return its path."""
    if not max_cz:
        return QASM
    out = os.path.join(HERE, f"surface3_xx_merge_prefix{max_cz}.qasm")
    head, body, ncx = [], [], 0
    for ln in open(QASM):
        s = ln.strip()
        if s.startswith(("OPENQASM", "include", "qreg", "creg")):
            head.append(s)
        elif s.startswith("cx"):
            if ncx < max_cz:
                body.append(s); ncx += 1
        elif s:
            body.append(s)
    open(out, "w").write("\n".join(head + body) + "\n")
    print(f"prefix QASM: {out} ({ncx} cx)")
    return out


def main():
    # arg: "all" = compile the FULL merge + report resources (no GIF); <N> = first N CZ + GIF;
    # default = an 8-CZ prefix (~2 syndrome-check merge steps) + GIF.
    arg = sys.argv[1] if len(sys.argv) > 1 else "8"
    do_gif = (arg != "all")
    max_cz = 0 if arg == "all" else int(arg)
    qasm = maybe_prefix_qasm(max_cz)
    for d in (OUT_DIR, os.path.join(OUT_DIR, "code"), os.path.join(OUT_DIR, "time")):
        os.makedirs(d, exist_ok=True)
    spec = json.load(open(ARCH)); arch = Architecture(spec); arch.preprocessing()
    setting = {"name": "surface3_xx_merge", "arch_spec": ARCH, "dependency": True,
               "dir": OUT_DIR + "/", "routing_strategy": "maximalis_sort",
               "trivial_placement": True, "dynamic_placement": False, "use_window": True,
               "window_size": 1000, "reuse": True, "use_verifier": True}
    z = ZAC()
    z.parse_setting(setting)
    z.set_architecture_spec_path(ARCH)
    z.set_architecture(arch)
    z.set_program(qasm)
    code = z.solve(save_file=True)
    res = json.load(open(z.code_filename))
    print(f"ZAC compiled: {len(res.get('instructions', []))} ZAIR instructions, "
          f"runtime {res.get('runtime', 0):.2f} us, verifier ok")
    if do_gif:
        z.animate(code, output=GIF)
        print(f"GIF -> {GIF} ({os.path.getsize(GIF)} bytes)")


if __name__ == "__main__":
    main()
