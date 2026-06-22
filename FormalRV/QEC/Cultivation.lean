/-
  FormalRV.QEC.Cultivation
  ------------------------
  **Magic-state cultivation infrastructure** — a faithful re-implementation of

    Gidney, Shutty, Jones, "Magic state cultivation: growing T states as cheap
    as CNOT gates", arXiv:2409.17595

  in the FormalRV framework, with the cultivation **controlled-H check** proved
  semantically correct on real matrices.

  ## What is proved (`Cultivation.TStateCheck`, axiom-clean)
  * `hXY_involutive`           — the check observable `H_XY = (X+Y)/√2` is a
                                 genuine reflection (`H_XY² = I`).
  * `hXY_stabilizes_magicT`    — `|T⟩` is the `+1` eigenstate of `H_XY`
                                 (the magic-state stabilizer the check verifies).
  * `hXY_antistabilizes_magicTm` — the orthogonal magic state is the `−1`
                                 eigenstate (the check is not vacuous).
  * `tConj_X_eq_hXY`           — Gidney's `T†` trick: `T·X·T† = H_XY`, so applying
                                 `T†` turns the `H_XY` check into an `X`-parity
                                 check (the form the "double cat check" measures).
  * `ctrlHXY_check_passes`     — **the controlled-`H_XY` check PASSES on `|T⟩`**
                                 (control stays `|+⟩`, no detection).
  * `ctrlHXY_check_detects`    — **the check has TEETH**: on `T|−⟩` the control
                                 flips to `|−⟩` (the check fires).

  ## Plugging a cultivated `|T⟩` into a circuit (`Cultivation.TFactoryCircuit`)
  * `TFactory` — the reusable interface: any source of `|T⟩` (cultivation is one
    instance, `cultivationTFactory`), with a per-`|T⟩` spacetime cost.
  * `factory_tGate_correct` — a `T` gate from ANY correct factory (the Clifford
    surgery `M_ZZ`→measure→`S` consumes the `|T⟩` and yields `T|ψ⟩`); depends only
    on `output = |T⟩`, so a cultivated state plugs straight in.
  * `circuitCost` / `circuitCost_factoryVol` — resource counting: the factory
    enters LINEARLY (`#T × volume per |T⟩`), so swapping factories just rescales
    the magic budget (`exampleCircuit_cost_cultivation` gives a concrete tally).

  ## What is scaffolded (`Cultivation.Stages`, structural)
  * the three stages (inject → [check → grow → stabilize]* → escape) and the
    `d=3`/`d=5` pipelines (matching the reference `make_inject_and_cultivate_*`);
  * the `d=3` color code = self-dual Steane `[[7,1,3]]`, so a TRANSVERSAL `H`
    implements a LOGICAL `H` (`transversalH_is_logicalH`) — lifting the verified
    controlled-`H_XY` kernel to the code level (`check_step_correct`).

  ## Out of scope (per the brief — NOT proved)
  Circuit-level fault distance, the superdense stabilize cycle's distance, and the
  escape stage's grafting (color→surface).  Reference source (read, not committed):
  `Library/2409.17595/` (paper `main.tex` + `code/.../src/cultiv/`).
-/
import FormalRV.QEC.Cultivation.TStateCheck
import FormalRV.QEC.Cultivation.Stages
import FormalRV.QEC.Cultivation.TFactoryCircuit
