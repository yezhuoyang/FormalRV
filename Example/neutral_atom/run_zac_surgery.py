#!/usr/bin/env python3
"""
Compile the FormalRV 2-bit Cuccaro adder's distance-3 SURFACE-CODE LATTICE SURGERY, FULL MERGE
(surface3_adder2_d3_full.qasm: 5 [[13,1,3]] patches; each of the 12 joint-Z measurements is the
COMPLETE merged-code syndrome, surface3_zz_merge 88 CX / surface3_zzz_merge 131 CX; + 4 magic) onto
a neutral-atom zoned architecture with ZAC (UCLA-VAST, HPCA'25), and render a GIF of the atom
movement, annotated with Qian Xu's zones and the FormalRV SysCall each ZAC op realizes.

  python run_zac_surgery.py            # default: first 12 CZ + GIF
  python run_zac_surgery.py <N>        # first N CZ + GIF
  python run_zac_surgery.py all        # compile the FULL adder surgery + report resources (no GIF)

Atoms are placed by ROLE (surface3_adder2_d3_full.roles.json) into Qian Xu's zones: MEMORY (the 5
d=3 patches), OPERATION-ANCILLA (the 39 reused surgery+syndrome ancillae), FACTORY (the 4 |CCZ>
magic atoms, used), RESERVOIR.  The ENTANGLING zone (Rydberg CZ) is where the merges + magic fire.
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
import json as _json
ARCH = os.path.join(HERE, "surface3_surgery_arch.json")
QASM = os.path.join(HERE, "surface3_adder2_d3_full.qasm")     # FULL merged-code syndrome per merge
GIF = os.path.join(HERE, "surface3_adder2_d3_neutral_atom.gif")
ROLES = os.path.join(HERE, "surface3_adder2_d3_full.roles.json")
OUT_DIR = os.path.join(HERE, "zac_result")

# Zone TAXONOMY of Qian Xu's factoring architecture (memory / operation-ancilla / factory /
# reservoir + entangling zone), as separated regions of the one storage array (gaps between them).
# (name, color, x0, y0, x1, y1, label_xy)
ZONE_REGIONS = [
    ("MEMORY (5 d=3 patches)", "#1f77b4", -1.5, -1.5, 37.5, 13.5, (18, 16)),
    ("ANCILLA (N_A)", "#b7791f", 46.5, -1.5, 70.5, 13.5, (58.5, 16)),
    ("FACTORY", "#805ad5", 76.5, -1.5, 82.5, 13.5, (79.5, 16)),
    ("RES", "#718096", 85.5, -1.5, 94.5, 13.5, (90, 16)),
]
ENT_REGION = ("ENTANGLING ZONE (processor) - Rydberg CZ = the full merges + magic injection",
              "#2ca02c", -1.5, 39, 98, 91, (48, 60))

# ZAC instruction type -> the FormalRV SysCall it realizes (shown per frame).
SYSCALL_OF = {
    "init": "SysCall: FRESHANC (place patches)",
    "rearrangeJob": "SysCall: routing (AOD transport)",
    "rydberg": "SysCall: GATE2Q = MERGE (Rydberg CZ)",
    "1qGate": "SysCall: basis rotation",
}


def build_zone_mapping():
    """Place each atom into its Qian-Xu zone by ROLE (from surface3_adder2_d3.roles.json):
    data -> MEMORY (5 patch-rows, cols 0-12); merge ancilla -> OPERATION-ANCILLA (cols 16-18);
    magic atom -> FACTORY (cols 22-23).  All in storage SLM 0.  Returns (slm_id, row, col)."""
    roles = _json.load(open(ROLES))["roles"]
    m, mi, ki = [], 0, 0
    for i, role in enumerate(roles):
        if role == "data":                         # MEMORY: 5 patches as rows of 13 (cols 0-12)
            m.append((0, i // 13, i % 13))
        elif role == "merge":                      # OPERATION-ANCILLA pool: cols 16-23
            m.append((0, mi // 8, 16 + mi % 8)); mi += 1
        else:                                      # magic -> FACTORY: cols 26-27
            m.append((0, ki // 2, 26 + ki % 2)); ki += 1
    return m


_orig_update_init = animator_module.Animator.update_init
_orig_update = animator_module.Animator.update


def patched_update_init(self):
    res = _orig_update_init(self)
    # separate zone regions (rectangles) + labels in the clear gap between storage and computation
    for name, color, x0, y0, x1, y1, (lx, ly) in ZONE_REGIONS:
        self.ax.add_patch(matplotlib.patches.Rectangle(
            (x0, y0), x1 - x0, y1 - y0, linewidth=2.5, edgecolor=color,
            facecolor=color, alpha=0.13, zorder=-10))
        self.ax.text(lx, ly, name, color=color, fontsize=9, fontweight="bold",
                     ha="center", va="bottom", zorder=-9)
    nm, color, x0, y0, x1, y1, (lx, ly) = ENT_REGION
    self.ax.add_patch(matplotlib.patches.Rectangle(
        (x0, y0), x1 - x0, y1 - y0, linewidth=1.6, edgecolor=color,
        facecolor=color, alpha=0.05, zorder=-10))
    self.ax.text(lx, ly, nm, color=color, fontsize=9, fontweight="bold",
                 ha="center", va="bottom", zorder=-9)
    # per-frame SysCall banner — below the plot (clear of all zones)
    self._sc_text = self.ax.text(
        0.5, -0.09, "", transform=self.ax.transAxes, fontsize=9.5, fontweight="bold",
        color="#c026d3", ha="center", va="top", zorder=20,
        bbox=dict(boxstyle="round", fc="#faf0ff", ec="#c026d3", alpha=0.95))
    return res


def patched_update(self, f):
    res = _orig_update(self, f)
    s = self.inst_str
    kind = next((k for k in ("rydberg", "rearrangeJob", "1qGate", "init") if k in s), None)
    if hasattr(self, "_sc_text"):
        self._sc_text.set_text("FormalRV " + SYSCALL_OF.get(kind, "SysCall: (idle)"))
    return res


animator_module.Animator.update_init = patched_update_init
animator_module.Animator.update = patched_update


def patched_animate(self, code, output, scaling_factor=6, font=9, ffmpeg="ffmpeg"):
    matplotlib.rcParams.update({"font.size": font})
    self.code = code
    self.fig, self.ax = self.setup_canvas(scaling_factor)   # 2x larger figure (was 3.5)
    self.title = self.ax.set_title("")
    self.inst_str = ""
    num_frame = self.create_schedule()
    total = self.INIT_FRM + num_frame
    step = 9                                                 # subsample frames to keep the GIF small
    frames = list(range(0, total, step))
    print(f"    animation frames: {len(frames)} of {total} (every {step})")
    anim = FuncAnimation(self.fig, self.update, init_func=self.update_init, frames=frames)
    anim.save(output, writer=PillowWriter(fps=max(3, self.FPS // step)))


animator_module.Animator.animate = patched_animate


def maybe_prefix_qasm(max_cz):
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
    return out


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else "12"
    do_gif = (arg != "all")
    max_cz = 0 if arg == "all" else int(arg)
    qasm = maybe_prefix_qasm(max_cz)
    for d in (OUT_DIR, os.path.join(OUT_DIR, "code"), os.path.join(OUT_DIR, "time")):
        os.makedirs(d, exist_ok=True)
    spec = json.load(open(ARCH)); arch = Architecture(spec); arch.preprocessing()
    setting = {"name": "surface3_xx_merge", "arch_spec": ARCH, "dependency": True,
               "dir": OUT_DIR + "/", "routing_strategy": "maximalis_sort",
               "trivial_placement": False, "dynamic_placement": False, "use_window": True,
               "window_size": 1000, "reuse": True, "use_verifier": True}
    z = ZAC()
    z.parse_setting(setting)
    z.set_architecture_spec_path(ARCH)
    z.set_architecture(arch)
    z.set_program(qasm)
    z.set_initial_mapping(build_zone_mapping())
    code = z.solve(save_file=True)
    res = json.load(open(z.code_filename))
    print(f"ZAC compiled: {len(res.get('instructions', []))} ZAIR instructions, "
          f"runtime {res.get('runtime', 0):.2f} us, verifier ok")
    if do_gif:
        z.animate(code, output=GIF)
        print(f"GIF -> {GIF} ({os.path.getsize(GIF)} bytes)")


if __name__ == "__main__":
    main()
