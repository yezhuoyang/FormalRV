"""Colorful terminal report for one run (Rich).

This is the non-interactive face of the FTQ-VM: ``ftqvm run`` prints this
summary; the interactive Textual TUI (``ftqvm tui``) is in ``tui.py``.
"""

from __future__ import annotations

from rich.console import Console, Group
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

from .simulator import RunResult

#: error kinds -> panel border colors
_KIND_COLORS = {
    "TokenUnavailable": "yellow",
    "TokenFreshnessViolation": "yellow",
    "TokenBufferOverflow": "blue",
    "ServiceQueueOverflow": "magenta",
    "ServiceCapacityExceeded": "magenta",
    "DeadlineMiss": "red",
    "CapacityExceeded": "red",
    "ResourceConflict": "red",
}


def bar(fraction: float, width: int = 24) -> Text:
    """A block bar colored by load: green < 60% <= yellow < 90% <= red."""
    fraction = max(0.0, fraction)
    filled = min(width, round(fraction * width))
    color = "green" if fraction < 0.6 else ("yellow" if fraction < 0.9 else "red")
    text = Text()
    text.append("█" * filled, style=color)
    text.append("░" * (width - filled), style="grey35")
    text.append(f" {fraction:6.1%}", style=color)
    return text


def _summary_panel(result: RunResult) -> Panel:
    stats = result.stats
    status = Text("PASSED", style="bold white on green") if result.ok else \
        Text("FAILED", style="bold white on red")
    lines = Table.grid(padding=(0, 2))
    lines.add_column(justify="right", style="bold cyan")
    lines.add_column()
    lines.add_row("Status", status)
    lines.add_row("Backend / Program",
                  f"{result.backend_name}  /  {result.program_name}")
    lines.add_row("Runtime", f"{stats.total_runtime_us:,} us")
    lines.add_row("Ops", f"{stats.num_ops:,} (incl. factory runs)")
    lines.add_row("Errors", Text(f"{stats.error_count:,}",
                                 style="red bold" if stats.error_count else "green"))
    if stats.errors_by_kind:
        lines.add_row("By kind", ", ".join(
            f"{k}={v}" for k, v in sorted(stats.errors_by_kind.items())))
    t_produced = sum(f.tokens_produced for f in stats.factories)
    t_failed = sum(f.failures for f in stats.factories)
    if stats.factories:
        lines.add_row("Factory output",
                      f"{t_produced} tokens produced, {t_failed} failed attempts "
                      f"({result.factory_mode}, seed {result.seed})")
    if stats.bottlenecks:
        top = stats.bottlenecks[0]
        lines.add_row("Bottleneck", Text(f"{top.id} ({top.type}, "
                                         f"{top.utilization:.1%} utilized)",
                                         style="bold yellow"))
    return Panel(lines, title="[bold]FTQ-VM Run Summary[/bold]", border_style="cyan")


def _resource_table(result: RunResult, limit: int = 12) -> Table:
    """Resources and zone rollups (zone qubits collapse to one row per zone)."""
    table = Table(title="Resources & Zones", title_style="bold",
                  border_style="grey50", header_style="bold cyan")
    table.add_column("resource")
    table.add_column("kind", style="dim")
    table.add_column("peak / capacity", justify="right")
    table.add_column("utilization")
    zone_ids = {z.id for z in result.stats.zones}
    rows: list[tuple[str, str, str, int, int, float]] = [
        (z.id, f"zone of {z.count} x {z.kind}", "", z.peak_busy, z.count,
         z.utilization)
        for z in result.stats.zones
    ]
    for r in result.stats.resources:
        if "[" in r.id and r.id.split("[", 1)[0] in zone_ids:
            continue  # rolled up into its zone's row
        rows.append((r.id, r.kind, "", r.peak_usage, r.capacity, r.utilization))
    rows.sort(key=lambda row: -row[5])
    for rid, kind, _, peak, cap, util in rows[:limit]:
        peak_style = "red bold" if peak > cap else ""
        table.add_row(rid, kind,
                      Text(f"{peak:,} / {cap:,}", style=peak_style),
                      bar(util))
    if len(rows) > limit:
        table.add_row(f"... {len(rows) - limit} more", "", "", Text(""))
    return table


def _service_table(result: RunResult) -> Table:
    table = Table(title="Services", title_style="bold", border_style="grey50",
                  header_style="bold magenta")
    table.add_column("service")
    table.add_column("jobs", justify="right")
    table.add_column("max queue / cap", justify="right")
    table.add_column("deadline misses", justify="right")
    table.add_column("workers busy (peak)", justify="right")
    table.add_column("utilization")
    for s in result.stats.services:
        q_style = "red bold" if s.max_queue_length > s.queue_capacity else ""
        m_style = "red bold" if s.deadline_misses else "green"
        table.add_row(
            s.id, f"{s.total_jobs:,}",
            Text(f"{s.max_queue_length:,} / {s.queue_capacity:,}", style=q_style),
            Text(f"{s.deadline_misses:,}", style=m_style),
            f"{s.peak_busy_workers}/{s.workers}",
            bar(s.utilization))
    return table


def _token_table(result: RunResult) -> Table:
    table = Table(title="Tokens", title_style="bold", border_style="grey50",
                  header_style="bold blue")
    table.add_column("kind")
    table.add_column("initial", justify="right")
    table.add_column("produced", justify="right")
    table.add_column("consumed", justify="right")
    table.add_column("peak buffer / cap", justify="right")
    for t in result.stats.tokens:
        cap = f" / {t.buffer_capacity:,}" if t.buffer_capacity is not None else ""
        over = t.buffer_capacity is not None and t.peak_buffer > t.buffer_capacity
        table.add_row(t.kind, f"{t.initial_inventory:,}", f"{t.produced:,}",
                      f"{t.consumed:,}",
                      Text(f"{t.peak_buffer:,}{cap}",
                           style="red bold" if over else ""))
    return table


def _factory_table(result: RunResult) -> Table:
    table = Table(title="Factories", title_style="bold", border_style="grey50",
                  header_style="bold green")
    table.add_column("factory")
    table.add_column("produces", style="dim")
    table.add_column("attempts", justify="right")
    table.add_column("ok / fail", justify="right")
    table.add_column("success rate", justify="right")
    table.add_column("retries", justify="right")
    table.add_column("utilization")
    for f in result.stats.factories:
        table.add_row(
            f.id, f.produces, f"{f.attempts:,}",
            Text.assemble((f"{f.successes:,}", "green"), " / ",
                          (f"{f.failures:,}", "red" if f.failures else "green")),
            f"{f.empirical_success_rate:.1%}",
            f"{f.retries:,}",
            bar(f.utilization))
    return table


def error_panel(err) -> Panel:
    """One colored panel for a VMError (shared with the TUI)."""
    color = _KIND_COLORS.get(err.kind.value, "red")
    body = Text()
    body.append(err.message + "\n")
    if err.op_ids:
        body.append("ops: ", style="bold cyan")
        body.append(", ".join(err.op_ids) + "\n", style="cyan")
    if err.suggestion:
        body.append("fix: ", style="bold green")
        body.append(err.suggestion, style="green")
    title = f"[bold {color}]{err.kind.value}[/] [dim]t={err.time_us}us[/]"
    if err.interval is not None:
        title += f" [dim]\\[{err.interval.start_us}, {err.interval.end_us})us[/]"
    return Panel(body, title=title, border_style=color, padding=(0, 1))


def _error_panels(result: RunResult, limit: int) -> list[Panel]:
    panels = [error_panel(err) for err in result.errors[:limit]]
    if len(result.errors) > limit:
        panels.append(Panel(
            Text(f"... and {len(result.errors) - limit} more errors "
                 f"(see trace.json or run the TUI)", style="dim"),
            border_style="grey50"))
    return panels


def render_report(result: RunResult, console: Console, max_errors: int = 8) -> None:
    console.print(_summary_panel(result))
    if result.stats.factories:
        console.print(_factory_table(result))
    if result.stats.tokens:
        console.print(_token_table(result))
    console.print(_resource_table(result))
    if result.stats.services:
        console.print(_service_table(result))
    if result.errors:
        console.print(Panel(Group(*_error_panels(result, max_errors)),
                            title="[bold red]Errors[/bold red]", border_style="red"))
