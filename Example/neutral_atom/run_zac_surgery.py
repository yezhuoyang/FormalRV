#!/usr/bin/env python3
"""
Compile the FormalRV distance-3 two-patch surface-code XX-merge onto a neutral-atom zoned
architecture with ZAC (UCLA-VAST, HPCA'25) and render a GIF of the atom movement that implements
the lattice surgery — with the architecture made CONSISTENT with FormalRV's system-spec zones and
each frame annotated with the FormalRV SysCall it realizes.

  python run_zac_surgery.py            # default: first 4 CZ (one syndrome-check step) + GIF
  python run_zac_surgery.py <N>        # first N CZ + GIF
  python run_zac_surgery.py all        # compile the FULL merge + print resources (no GIF)

Atoms are placed into the SAME zones as FormalRV's `myArch` (Adder2EndToEnd.lean): Data (the 27
data + surgery-ancilla atoms), Ancilla (the 26 syndrome ancillas), Factory (reserved for |CCZ>
magic — empty here, the merge is Clifford), Routing.  The entanglement zone (Rydberg CZ) is the
neutral-atom-specific physical realization of FormalRV's logical Gate2q merge.
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

N_DATA = 27   # qubits 0..26  = 26 data + 1 surgery ancilla  -> Data zone
N_ANC = 26    # qubits 27..52 = 26 syndrome ancillas          -> Ancilla zone

# Storage row bands (3 rows x 3um each) = the FormalRV zones, mirrored on the atoms.
ZONE_BANDS = [  # (name, color, y_lo, y_hi)
    ("DATA (data+surgery anc)", "#1f77b4", -1, 7),
    ("ANCILLA (syndrome anc)", "#b7791f", 8, 16),
    ("FACTORY (|CCZ>, reserved)", "#805ad5", 17, 25),
    ("ROUTING (bus)", "#718096", 26, 34),
]
ENT_BAND = ("ENTANGLEMENT - Rydberg CZ = the merge", "#2ca02c", 46, 108)

# ZAC instruction type -> the FormalRV SysCall it realizes (shown per frame).
SYSCALL_OF = {
    "init": "SysCall: FRESHANC (place patches)",
    "rearrangeJob": "SysCall: routing (AOD transport)",
    "rydberg": "SysCall: GATE2Q = MERGE (Rydberg CZ)",
    "1qGate": "SysCall: basis rotation",
}


def build_zone_mapping():
    """Place atoms into the FormalRV zones: data (0..26) -> Data band (rows 0-2),
    syndrome ancillas (27..52) -> Ancilla band (rows 3-5).  Returns (slm_id, row, col) per atom."""
    m = []
    for q in range(N_DATA):
        m.append((0, q // 10, q % 10))            # Data: rows 0-2
    for j in range(N_ANC):
        m.append((0, 3 + j // 10, j % 10))        # Ancilla: rows 3-5
    return m


_orig_update_init = animator_module.Animator.update_init
_orig_update = animator_module.Animator.update


def patched_update_init(self):
    res = _orig_update_init(self)
    # zone outlines + LEFT-MARGIN labels (no overlap with atoms)
    for name, color, y0, y1 in ZONE_BANDS:
        self.ax.add_patch(matplotlib.patches.Rectangle(
            (-0.5, y0), 30, y1 - y0, linewidth=1.2, edgecolor=color,
            facecolor=color, alpha=0.05, zorder=-10))
        # labels placed in the CLEAR area right of the storage (x>=32, below the entanglement zone)
        self.ax.text(33, (y0 + y1) / 2, name, color=color, fontsize=8.5, fontweight="bold",
                     ha="left", va="center", zorder=-9)
    nm, color, y0, y1 = ENT_BAND
    self.ax.add_patch(matplotlib.patches.Rectangle(
        (-0.5, y0), 122, y1 - y0, linewidth=1.5, edgecolor=color,
        facecolor=color, alpha=0.05, zorder=-10))
    self.ax.text(33, y0 + 2, nm, color=color, fontsize=9, fontweight="bold",
                 ha="left", va="bottom", zorder=-9)
    # per-frame SysCall banner — top interior of the plot (clear band above the entanglement zone)
    self._sc_text = self.ax.text(
        2, 114, "", fontsize=9, fontweight="bold",
        color="#c026d3", ha="left", va="top", zorder=20,
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


def patched_animate(self, code, output, scaling_factor=3.5, font=8, ffmpeg="ffmpeg"):
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
    arg = sys.argv[1] if len(sys.argv) > 1 else "4"
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
