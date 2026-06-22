"""Optional FastAPI HTTP interface (programmatic access; the primary UI is
the terminal: ``python -m ftq_vm run`` / ``python -m ftq_vm tui``).

    uvicorn ftq_vm.backend.main:app --reload

Endpoints:
  GET  /health            -- liveness
  GET  /examples          -- bundled example files (name + content)
  POST /run               -- run a simulation; body carries backend + program
                             as parsed objects or as YAML/JSON text
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, Literal, Optional

from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

from .loader import LoadError, backend_from_obj, parse_text, program_from_obj
from .models import RunConfig
from .simulator import run_simulation

EXAMPLES_DIR = Path(__file__).parent / "examples"

app = FastAPI(
    title="FTQ-VM",
    description="Discrete-event checker for finite-service resource contracts "
                "in fault-tolerant quantum computation. All times are integer "
                "microseconds.",
    version="0.2.0",
)
app.add_middleware(
    CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"],
)


class RunRequest(BaseModel):
    """Backend/program may be given as parsed objects or as YAML/JSON text."""

    backend: Optional[Any] = None
    program: Optional[Any] = None
    backend_text: Optional[str] = None
    program_text: Optional[str] = None
    seed: int = 0
    factory_mode: Literal["stochastic", "conservative"] = "stochastic"


@app.get("/health")
def health() -> dict[str, str]:
    return {"status": "ok"}


@app.get("/examples")
def examples() -> list[dict[str, str]]:
    return [
        {"name": p.name, "content": p.read_text(encoding="utf-8")}
        for p in sorted(EXAMPLES_DIR.glob("*.yaml"))
    ]


@app.post("/run")
def run(req: RunRequest) -> dict[str, Any]:
    try:
        backend_obj = req.backend if req.backend is not None else parse_text(req.backend_text or "")
        program_obj = req.program if req.program is not None else parse_text(req.program_text or "")
        backend = backend_from_obj(backend_obj)
        program = program_from_obj(program_obj, backend)
    except LoadError as exc:
        raise HTTPException(status_code=422, detail=str(exc)) from exc
    cfg = RunConfig(seed=req.seed, factory_mode=req.factory_mode)
    result = run_simulation(backend, program, cfg)
    return result.model_dump(mode="json")
