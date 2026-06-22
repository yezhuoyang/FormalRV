#!/usr/bin/env python3
"""Build a clean reorg commit from HEAD via a temp index, ignoring all
working-tree co-edits by other agents.

It applies ONLY our deterministic transformation:
  * file renames (move loose Shor root files into subfolders; StandardShor under Shor/)
  * exact-line `import <old>` -> `import <new>` rewrites in every HEAD consumer
The working tree is never touched, so other agents' uncommitted WIP is preserved.
Run from the repo root.
"""
import os, subprocess, sys

# module old -> new
G_RES, G_PPM, G_OF = "FormalRV.Shor.Resource", "FormalRV.Shor.PPM", "FormalRV.Shor.OrderFinding"
MAP = {
    "FormalRV.StandardShor": "FormalRV.Shor.StandardShor",
    "FormalRV.Shor.ControlledModExpCount": f"{G_RES}.ControlledModExpCount",
    "FormalRV.Shor.ModExpToffoliCount": f"{G_RES}.ModExpToffoliCount",
    "FormalRV.Shor.CliffordTControlledModExp": f"{G_RES}.CliffordTControlledModExp",
    "FormalRV.Shor.ShorCriticalPathFloor": f"{G_RES}.ShorCriticalPathFloor",
    "FormalRV.Shor.ShorFullMachineRequirement": f"{G_RES}.ShorFullMachineRequirement",
    "FormalRV.Shor.PPMShorMaster": f"{G_PPM}.PPMShorMaster",
    "FormalRV.Shor.ShorPPMEndToEnd": f"{G_PPM}.ShorPPMEndToEnd",
    "FormalRV.Shor.ShorPPMUnitaryReduction": f"{G_PPM}.ShorPPMUnitaryReduction",
    "FormalRV.Shor.ShorModMulPPMFactoryE2E": f"{G_PPM}.ShorModMulPPMFactoryE2E",
    "FormalRV.Shor.TeleportCCXGrounded": f"{G_PPM}.TeleportCCXGrounded",
    "FormalRV.Shor.ShorEmit": f"{G_PPM}.ShorEmit",
    "FormalRV.Shor.ShorEmitDistance": f"{G_PPM}.ShorEmitDistance",
    "FormalRV.Shor.Eigenstate": f"{G_OF}.Eigenstate",
    "FormalRV.Shor.TotientLowerBound": f"{G_OF}.TotientLowerBound",
    "FormalRV.Shor.EncodingAgnostic": f"{G_OF}.EncodingAgnostic",
    "FormalRV.Shor.ProbabilityTransfer": f"{G_OF}.ProbabilityTransfer",
    "FormalRV.Shor.SuccessSensitivity": f"{G_OF}.SuccessSensitivity",
}

def mod_to_path(m):
    return m.replace(".", "/") + ".lean"

# fs path renames derived from MAP, plus the README (no imports).
FILE_RENAMES = {mod_to_path(o): mod_to_path(n) for o, n in MAP.items()}
FILE_RENAMES["FormalRV/StandardShor/README.md"] = "FormalRV/Shor/StandardShor/README.md"

IDX = os.path.abspath(".git/reorg_tmp.index")
ENV = dict(os.environ, GIT_INDEX_FILE=IDX)

def git(args, env=None, inp=None, check=True):
    r = subprocess.run(["git", *args], env=env, input=inp,
                       capture_output=True)
    if check and r.returncode != 0:
        sys.exit(f"git {args} failed:\n{r.stderr.decode(errors='replace')}")
    return r.stdout

def head_bytes(path):
    return git(["show", f"HEAD:{path}"])

def rewrite(content):
    try:
        text = content.decode("utf-8")
    except UnicodeDecodeError:
        return content  # binary (none expected) -> leave as-is
    out = []
    for ln in text.splitlines(keepends=True):
        stripped = ln.rstrip("\r\n")
        for old, new in MAP.items():
            if stripped == f"import {old}":
                ending = ln[len(stripped):]
                ln = f"import {new}{ending}"
                break
        out.append(ln)
    return "".join(out).encode("utf-8")

def stage_blob(path, content):
    h = git(["hash-object", "-w", "--stdin"], inp=content).decode().strip()
    git(["update-index", "--add", "--cacheinfo", f"100644,{h},{path}"], env=ENV)

def remove_path(path):
    git(["update-index", "--force-remove", path], env=ENV)

# seed temp index from HEAD
git(["read-tree", "HEAD"], env=ENV)

# 1. renames (rewrite .lean intra-moved imports; README copied verbatim)
for old, new in FILE_RENAMES.items():
    content = head_bytes(old)
    if new.endswith(".lean"):
        content = rewrite(content)
    stage_blob(new, content)
    remove_path(old)
    print(f"  R {old} -> {new}")

# 2. consumers: every HEAD .lean importing any old module (minus the moved files)
consumers = set()
for old in MAP:
    out = git(["grep", "-l", "-F", f"import {old}", "HEAD", "--", "*.lean"], check=False)
    for line in out.decode().splitlines():
        consumers.add(line.split(":", 1)[1])
consumers -= set(FILE_RENAMES.keys())
for path in sorted(consumers):
    new_content = rewrite(head_bytes(path))
    if new_content != head_bytes(path):
        stage_blob(path, new_content)
        print(f"  M {path}")

# 3. commit from temp index onto current branch
tree = git(["write-tree"], env=ENV).decode().strip()
parent = git(["rev-parse", "HEAD"]).decode().strip()
msg = """refactor(Shor): group loose root files into subfolders; move StandardShor under Shor/

Declutters the Shor/ root (was 33 loose .lean files) into functional
subfolders, and brings the textbook entry point under Shor/:

- Shor/OrderFinding/  : Eigenstate, TotientLowerBound, EncodingAgnostic,
                        ProbabilityTransfer, SuccessSensitivity
- Shor/Resource/      : ControlledModExpCount, ModExpToffoliCount,
                        CliffordTControlledModExp, ShorCriticalPathFloor,
                        ShorFullMachineRequirement
- Shor/PPM/           : PPMShorMaster, ShorPPMEndToEnd, ShorPPMUnitaryReduction,
                        ShorModMulPPMFactoryE2E, TeleportCCXGrounded,
                        ShorEmit, ShorEmitDistance
- Shor/StandardShor.lean (+ StandardShor/README.md) moved from the top level
  (namespace FormalRV.StandardShor kept, so #check sites stay valid).

Pure move + import-path rewrite; no declarations changed. Existing subfolders
(MainAlgorithm/, PostQFT/, VerifiedShor/, Approx/) are untouched, as is the
Gidney/windowed group (deferred to avoid colliding with the live windowed-move
agent). Verified green for all Shor targets in the full-library pass before an
unrelated concurrent Arithmetic WIP breakage.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>
Co-Authored-By: John Ye <yezhuoyang@cs.ucla.edu>
"""
commit = git(["commit-tree", tree, "-p", parent, "-m", msg]).decode().strip()
print(f"\nNew commit: {commit}")
print("Run:  git reset --mixed", commit, " (resync main index; working tree preserved)")
