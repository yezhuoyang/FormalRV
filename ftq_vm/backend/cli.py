"""Command-line interface.

    python -m ftq_vm run examples/backend_simple.yaml examples/program_buggy.yaml --out out/
    python -m ftq_vm tui examples/backend_simple.yaml examples/program_fixed.yaml
    python -m ftq_vm check-cert out/certificate.json
    python -m ftq_vm examples

``run`` writes ``trace.json``, ``stats.json`` and ``certificate.json`` to the
output directory and prints a colorful Rich summary.  Exit codes: 0 = pass,
1 = constraint violations found, 2 = could not load the inputs.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from rich.console import Console

from .loader import LoadError, load_backend, load_program
from .models import RunConfig
from .report import render_report
from .simulator import RunResult, run_simulation

EXAMPLES_DIR = Path(__file__).parent / "examples"
DEFAULT_ERROR_PRINT_LIMIT = 8


def _write_outputs(result: RunResult, out_dir: Path) -> dict[str, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = {
        "trace": out_dir / "trace.json",
        "stats": out_dir / "stats.json",
        "certificate": out_dir / "certificate.json",
    }
    paths["trace"].write_text(
        json.dumps(result.trace_dict(), indent=2), encoding="utf-8")
    paths["stats"].write_text(
        json.dumps(result.stats.model_dump(mode="json"), indent=2), encoding="utf-8")
    paths["certificate"].write_text(
        json.dumps(result.certificate, indent=2), encoding="utf-8")
    return paths


def _load(args: argparse.Namespace):
    backend_path = args.backend_flag or args.backend
    program_path = args.program_flag or args.program
    if not backend_path or not program_path:
        raise LoadError("both a backend and a program file are required, e.g.\n"
                        "  python -m ftq_vm run examples/backend_simple.yaml "
                        "examples/program_fixed.yaml")
    backend = load_backend(backend_path)
    program = load_program(program_path, backend)
    return backend, program


def cmd_run(args: argparse.Namespace) -> int:
    console = Console()
    try:
        backend, program = _load(args)
    except LoadError as exc:
        console.print(f"[bold red]error:[/bold red] {exc}")
        return 2
    cfg = RunConfig(seed=args.seed, factory_mode=args.factory_mode)
    result = run_simulation(backend, program, cfg)
    paths = _write_outputs(result, Path(args.out))
    render_report(result, console, max_errors=args.max_errors)
    console.print(f"[dim]Stats written to {paths['stats']}.[/dim]")
    console.print(f"[dim]Trace written to {paths['trace']}.[/dim]")
    console.print(f"[dim]Certificate written to {paths['certificate']}.[/dim]")
    return 0 if result.ok else 1


def cmd_tui(args: argparse.Namespace) -> int:
    console = Console()
    try:
        backend, program = _load(args)
    except LoadError as exc:
        console.print(f"[bold red]error:[/bold red] {exc}")
        return 2
    cfg = RunConfig(seed=args.seed, factory_mode=args.factory_mode)
    result = run_simulation(backend, program, cfg)
    from .tui import FTQVMApp  # textual import is slow; keep it lazy
    FTQVMApp(result).run()
    return 0 if result.ok else 1


def cmd_check_cert(args: argparse.Namespace) -> int:
    from .check_certificate import main as check_main
    return check_main(args.certificate)


def cmd_examples(_args: argparse.Namespace) -> int:
    for path in sorted(EXAMPLES_DIR.glob("*.yaml")):
        print(path)
    return 0


def _add_run_args(p: argparse.ArgumentParser) -> None:
    p.add_argument("backend", nargs="?", help="backend YAML/JSON file")
    p.add_argument("program", nargs="?", help="program YAML/JSON file")
    p.add_argument("--backend", dest="backend_flag", help=argparse.SUPPRESS)
    p.add_argument("--program", dest="program_flag", help=argparse.SUPPRESS)
    p.add_argument("--seed", type=int, default=0,
                   help="PRNG seed for stochastic factories (default 0)")
    p.add_argument("--factory-mode", choices=["stochastic", "conservative"],
                   default="stochastic",
                   help="stochastic: seeded random factory outcomes; "
                        "conservative: every ceil(1/p)-th attempt succeeds")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m ftq_vm",
        description="FTQ-VM: discrete-event checker for fault-tolerant "
                    "quantum resource contracts. All times are integer "
                    "microseconds (_us).")
    sub = parser.add_subparsers(dest="command", required=True)

    run_p = sub.add_parser("run", help="check a program against a backend")
    _add_run_args(run_p)
    run_p.add_argument("--out", default="out", help="output directory (default: out/)")
    run_p.add_argument("--max-errors", type=int, default=DEFAULT_ERROR_PRINT_LIMIT,
                       help="max errors to print on the console")
    run_p.set_defaults(func=cmd_run)

    tui_p = sub.add_parser("tui", help="interactive terminal UI for a run")
    _add_run_args(tui_p)
    tui_p.set_defaults(func=cmd_tui)

    cert_p = sub.add_parser("check-cert",
                            help="independently re-verify a certificate.json")
    cert_p.add_argument("certificate", help="path to certificate.json")
    cert_p.set_defaults(func=cmd_check_cert)

    ex_p = sub.add_parser("examples", help="list bundled example files")
    ex_p.set_defaults(func=cmd_examples)
    return parser


def _force_utf8_output() -> None:
    """Block characters / box drawing must survive legacy Windows codepages
    (e.g. GBK): re-encode stdout/stderr as UTF-8, replacing on failure."""
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass


def main(argv: list[str] | None = None) -> int:
    _force_utf8_output()
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)
