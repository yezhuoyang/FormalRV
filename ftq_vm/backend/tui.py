"""Interactive terminal UI (Textual).

    python -m ftq_vm tui <backend.yaml> <program.yaml> [--seed N]

Tabs: Dashboard / Timeline / Trace / Resources / Tokens / Services /
Factories / Errors.  Keyboard: arrow keys pan the timeline, +/- zoom,
``e`` toggles errors-only in the trace, ``q`` quits.
"""

from __future__ import annotations

import bisect
import json
from typing import Optional

from rich.console import Group
from rich.panel import Panel
from rich.table import Table
from rich.text import Text
from textual.app import App, ComposeResult
from textual.binding import Binding
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.widgets import (
    DataTable,
    Footer,
    Header,
    Input,
    OptionList,
    Static,
    TabbedContent,
    TabPane,
)
from textual.widgets.option_list import Option

from .models import Event, VMError
from .report import (
    _factory_table,
    _resource_table,
    _service_table,
    _summary_panel,
    _token_table,
    error_panel,
)
from .simulator import RunResult

SPARK = " ▁▂▃▄▅▆▇█"


# --------------------------------------------------------------------------
# step-series sampling + sparklines
# --------------------------------------------------------------------------


def sample_step(series: list[tuple[int, int]], t0: int, t1: int,
                buckets: int) -> list[int]:
    """Max of a step series over each of ``buckets`` sub-intervals of [t0, t1)."""
    if not series or t1 <= t0:
        return [0] * buckets
    times = [t for t, _ in series]

    def value_at(x: int) -> int:
        i = bisect.bisect_right(times, x) - 1
        return series[i][1] if i >= 0 else 0

    out = []
    span = t1 - t0
    for b in range(buckets):
        a = t0 + span * b // buckets
        c = t0 + span * (b + 1) // buckets
        m = value_at(a)
        i = bisect.bisect_right(times, a)
        while i < len(series) and series[i][0] < c:
            m = max(m, series[i][1])
            i += 1
        out.append(m)
    return out


def sparkline(values: list[int], cap: Optional[int]) -> Text:
    """Colored sparkline; red where a capacity is exceeded."""
    scale = max(max(values, default=0), cap or 0, 1)
    text = Text()
    for v in values:
        ch = SPARK[min(8, round(v / scale * 8))]
        if cap is not None and v > cap:
            style = "bold red"
        elif cap is not None and v >= 0.9 * cap:
            style = "yellow"
        else:
            style = "green" if v else "grey35"
        text.append(ch if v or ch != " " else "·", style=style)
    return text


def _fmt_details(details: dict) -> str:
    return json.dumps(details, default=str) if details else ""


# --------------------------------------------------------------------------
# the app
# --------------------------------------------------------------------------


class FTQVMApp(App):
    """Inspect one FTQ-VM run interactively."""

    TITLE = "FTQ-VM"
    CSS = """
    #timeline, #res_detail, #tok_body, #svc_body, #trace_detail, #op_detail {
        background: $surface;
        padding: 0 1;
    }
    #trace_filter, #op_filter { dock: top; }
    DataTable { height: 1fr; }
    OptionList { width: 34; }
    .detail { height: auto; max-height: 14; border-top: solid $primary; }
    """

    BINDINGS = [
        Binding("q", "quit", "quit"),
        Binding("e", "toggle_errors", "errors only (trace)"),
        Binding("plus,=", "zoom_in", "zoom in"),
        Binding("minus", "zoom_out", "zoom out"),
        Binding("left", "pan(-1)", "pan left"),
        Binding("right", "pan(1)", "pan right"),
    ]

    def __init__(self, result: RunResult):
        super().__init__()
        self.result = result
        self.runtime = max(result.stats.total_runtime_us, 1)
        self.view0 = 0
        self.view1 = self.runtime
        self.errors_only = False
        self._trace_rows: list[Event] = []
        self.sub_title = (f"{result.backend_name} / {result.program_name} -- "
                          + ("PASSED" if result.ok else
                             f"FAILED ({result.stats.error_count} errors)"))

    # ---- layout -------------------------------------------------------------

    def compose(self) -> ComposeResult:
        yield Header(show_clock=False)
        with TabbedContent():
            with TabPane("Dashboard", id="tab_dash"):
                yield VerticalScroll(Static(id="dash"))
            with TabPane("Timeline", id="tab_timeline"):
                with Vertical():
                    yield VerticalScroll(Static(id="timeline"))
                    yield DataTable(id="op_table")
                    yield Static(id="op_detail", classes="detail")
            with TabPane("Trace", id="tab_trace"):
                with Vertical():
                    yield Input(placeholder="filter events (substring over kind/op/"
                                            "component/message)... press e for errors only",
                                id="trace_filter")
                    yield DataTable(id="trace_table")
                    yield Static(id="trace_detail", classes="detail")
            with TabPane("Resources", id="tab_resources"):
                with Horizontal():
                    yield OptionList(id="res_list")
                    yield VerticalScroll(Static(id="res_detail"))
            with TabPane("Tokens", id="tab_tokens"):
                yield VerticalScroll(Static(id="tok_body"))
            with TabPane("Services", id="tab_services"):
                yield VerticalScroll(Static(id="svc_body"))
            with TabPane("Factories", id="tab_factories"):
                with Vertical():
                    yield VerticalScroll(Static(id="fact_summary"))
                    yield DataTable(id="fact_table")
            with TabPane("Errors", id="tab_errors"):
                yield VerticalScroll(Static(id="err_body"))
        yield Footer()

    def on_mount(self) -> None:
        self._render_dashboard()
        self._render_timeline()
        self._fill_op_table()
        self._fill_trace_table()
        self._fill_resources()
        self._render_tokens()
        self._render_services()
        self._fill_factories()
        self._render_errors()

    # ---- dashboard ----------------------------------------------------------

    def _render_dashboard(self) -> None:
        parts = [_summary_panel(self.result)]
        if self.result.stats.factories:
            parts.append(_factory_table(self.result))
        if self.result.stats.tokens:
            parts.append(_token_table(self.result))
        parts.append(_resource_table(self.result))
        if self.result.stats.services:
            parts.append(_service_table(self.result))
        self.query_one("#dash", Static).update(Group(*parts))

    # ---- timeline -----------------------------------------------------------

    @staticmethod
    def _sum_step_series(series_list: list[list[tuple[int, int]]]
                         ) -> list[tuple[int, int]]:
        """Pointwise sum of step series (e.g. busy qubits across a zone)."""
        deltas: list[tuple[int, int]] = []
        for s in series_list:
            prev = 0
            for t, v in s:
                if v != prev:
                    deltas.append((t, v - prev))
                    prev = v
        deltas.sort()
        out, level = [(0, 0)], 0
        for t, d in deltas:
            level += d
            if out[-1][0] == t:
                out[-1] = (t, level)
            else:
                out.append((t, level))
        return out

    def _lanes(self) -> list[tuple[str, list[tuple[int, int]], Optional[int]]]:
        r = self.result
        lanes: list[tuple[str, list[tuple[int, int]], Optional[int]]] = []
        # one lane per op kind: number of active ops over time
        kinds: dict[str, list[tuple[int, int]]] = {}
        for op in r.op_intervals:
            kinds.setdefault(f"ops:{op['kind']}", []).append(
                (op["start_us"], op["end_us"]))
        for label in sorted(kinds):
            deltas: list[tuple[int, int]] = []
            for s, e in kinds[label]:
                deltas.append((s, +1))
                deltas.append((e, -1))
            deltas.sort()
            series, level = [(0, 0)], 0
            for t, d in deltas:
                level += d
                if series[-1][0] == t:
                    series[-1] = (t, level)
                else:
                    series.append((t, level))
            lanes.append((label, series, None))
        # zone qubits aggregate into one busy-count lane per zone
        zones = {z["id"]: z["count"]
                 for z in r.certificate.get("zones", [])}
        zone_series: dict[str, list[list[tuple[int, int]]]] = {z: [] for z in zones}
        caps = r.resource_capacities
        for rid, series in sorted(r.resource_usage_series.items()):
            zone = rid.split("[", 1)[0] if "[" in rid else None
            if zone in zone_series:
                zone_series[zone].append(series)
            else:
                lanes.append((rid, series, caps.get(rid)))
        for zid in sorted(zone_series):
            lanes.append((f"zone:{zid}",
                          self._sum_step_series(zone_series[zid]), zones[zid]))
        for sid, series in sorted(r.service_queue_series.items()):
            lanes.append((f"{sid} queue", series, None))
        for kind, series in sorted(r.token_occupancy_series.items()):
            lanes.append((f"{kind} buffer", series, None))
        return lanes

    def _render_timeline(self) -> None:
        width = 90
        t0, t1 = self.view0, self.view1
        body = Text()
        body.append(f"[{t0} .. {t1}] us   (arrows pan, +/- zoom)\n\n", style="dim")
        label_w = 26
        error_cols: dict[int, int] = {}
        for err in self.result.errors:
            if t0 <= err.time_us < t1:
                col = (err.time_us - t0) * width // (t1 - t0)
                error_cols[col] = error_cols.get(col, 0) + 1
        for label, series, cap in self._lanes():
            values = sample_step(series, t0, t1, width)
            body.append(label[:label_w].ljust(label_w), style="bold cyan")
            body.append(sparkline(values, cap))
            peak = max(values, default=0)
            cap_str = f"/{cap}" if cap is not None else ""
            body.append(f"  peak {peak}{cap_str}\n", style="dim")
        # error marker row
        body.append("errors".ljust(label_w), style="bold red")
        marks = Text()
        for col in range(width):
            if col in error_cols:
                marks.append("✖", style="bold red")
            else:
                marks.append("·", style="grey23")
        body.append(marks)
        body.append(f"  {sum(error_cols.values())} in view\n", style="dim")
        # axis
        body.append(" " * label_w, style="")
        axis = Text()
        for col in range(0, width, 15):
            t = t0 + (t1 - t0) * col // width
            axis.append(f"|{t}".ljust(15), style="dim")
        body.append(axis)
        self.query_one("#timeline", Static).update(body)

    def action_zoom_in(self) -> None:
        span = max((self.view1 - self.view0) // 2, 10)
        center = (self.view0 + self.view1) // 2
        self.view0 = max(0, center - span // 2)
        self.view1 = self.view0 + span
        self._render_timeline()

    def action_zoom_out(self) -> None:
        span = min((self.view1 - self.view0) * 2, self.runtime)
        center = (self.view0 + self.view1) // 2
        self.view0 = max(0, center - span // 2)
        self.view1 = min(self.runtime, self.view0 + span)
        if self.view1 - self.view0 < span:
            self.view0 = max(0, self.view1 - span)
        self._render_timeline()

    def action_pan(self, direction: int) -> None:
        span = self.view1 - self.view0
        shift = max(span // 4, 1) * direction
        self.view0 = max(0, min(self.view0 + shift, self.runtime - span))
        self.view1 = self.view0 + span
        self._render_timeline()

    # ---- ops table (timeline tab) -------------------------------------------

    def _fill_op_table(self) -> None:
        table = self.query_one("#op_table", DataTable)
        table.cursor_type = "row"
        table.add_columns("op", "kind", "start_us", "end_us", "uses", "tokens")
        for i, op in enumerate(self.result.op_intervals):
            tokens = ""
            if op["consumes"]:
                tokens += "-" + ",".join(op["consumes"])
            if op["produces"]:
                tokens += "+" + ",".join(op["produces"])
            table.add_row(op["id"], op["kind"], str(op["start_us"]),
                          str(op["end_us"]),
                          ",".join([*op["resources"], *op["services"]])[:40],
                          tokens, key=str(i))

    def on_data_table_row_selected(self, event: DataTable.RowSelected) -> None:
        if event.data_table.id == "op_table":
            op = self.result.op_intervals[int(event.row_key.value)]
            detail = Text()
            detail.append(f"{op['id']}  ", style="bold cyan")
            detail.append(f"({op['kind']})  [{op['start_us']}, {op['end_us']})us  "
                          f"deps: {', '.join(op['deps']) or '-'}\n")
            if op["metadata"]:
                detail.append(f"metadata: {_fmt_details(op['metadata'])}\n", style="dim")
            related = [e for e in self.result.errors if op["id"] in e.op_ids]
            for err in related[:4]:
                detail.append(f"✖ {err.headline()}\n", style="red")
            self.query_one("#op_detail", Static).update(detail)
        elif event.data_table.id == "trace_table":
            ev = self._trace_rows[int(event.row_key.value)]
            detail = Text()
            detail.append(f"t={ev.time_us}us  {ev.kind.value}  ", style="bold")
            detail.append(f"severity={ev.severity}\n",
                          style="red" if ev.severity == "error" else "dim")
            detail.append(ev.message + "\n")
            if ev.details:
                detail.append(_fmt_details(ev.details) + "\n", style="dim")
            self.query_one("#trace_detail", Static).update(detail)

    # ---- trace ---------------------------------------------------------------

    def _fill_trace_table(self, needle: str = "") -> None:
        table = self.query_one("#trace_table", DataTable)
        table.clear(columns=True)
        table.cursor_type = "row"
        table.add_columns("t_us", "event", "sev", "op", "component", "message")
        needle = needle.lower()
        self._trace_rows = []
        shown = 0
        for ev in self.result.events:
            if self.errors_only and ev.severity != "error":
                continue
            hay = f"{ev.kind.value} {ev.op_id or ''} {ev.component} {ev.message}".lower()
            if needle and needle not in hay:
                continue
            sev_style = {"error": "bold red", "warning": "yellow"}.get(ev.severity, "dim")
            table.add_row(
                str(ev.time_us), ev.kind.value,
                Text(ev.severity, style=sev_style),
                ev.op_id or "", ev.component,
                ev.message[:80], key=str(len(self._trace_rows)))
            self._trace_rows.append(ev)
            shown += 1
            if shown >= 3000:
                table.add_row("...", "truncated", "", "", "",
                              "refine the filter to see more", key="trunc")
                self._trace_rows.append(Event(time_us=0, kind=ev.kind,
                                              message="truncated"))
                break

    def on_input_changed(self, event: Input.Changed) -> None:
        if event.input.id == "trace_filter":
            self._fill_trace_table(event.value)

    def action_toggle_errors(self) -> None:
        self.errors_only = not self.errors_only
        self._fill_trace_table(self.query_one("#trace_filter", Input).value)

    # ---- resources -----------------------------------------------------------

    def _fill_resources(self) -> None:
        olist = self.query_one("#res_list", OptionList)
        for r in sorted(self.result.stats.resources, key=lambda r: -r.utilization):
            mark = "▲" if r.peak_usage > r.capacity else " "
            olist.add_option(Option(f"{mark} {r.id}  ({r.utilization:.0%})", id=r.id))
        if self.result.stats.resources:
            self._show_resource(self.result.stats.resources[0].id)

    def on_option_list_option_selected(self, event: OptionList.OptionSelected) -> None:
        self._show_resource(event.option.id)

    def _show_resource(self, rid: str) -> None:
        r = next((x for x in self.result.stats.resources if x.id == rid), None)
        if r is None:
            return
        series = self.result.resource_usage_series.get(rid, [(0, 0)])
        values = sample_step(series, 0, self.runtime, 80)
        body = Text()
        body.append(f"{r.id}  ", style="bold cyan")
        body.append(f"kind={r.kind}  capacity={r.capacity:,}  "
                    f"peak={r.peak_usage:,}  utilization={r.utilization:.1%}\n\n")
        body.append("usage ")
        body.append(sparkline(values, r.capacity))
        body.append(f" 0..{self.runtime}us\n", style="dim")
        over = [(t, v) for t, v in series if v > r.capacity]
        if over:
            body.append(f"\nOVER CAPACITY at {len(over)} point(s), e.g. t={over[0][0]}us "
                        f"usage {over[0][1]} > {r.capacity}\n", style="bold red")
        related = [e for e in self.result.errors if e.resource == rid]
        panels = [error_panel(e) for e in related[:6]]
        self.query_one("#res_detail", Static).update(Group(body, *panels))

    # ---- tokens / services / factories / errors -------------------------------

    def _render_tokens(self) -> None:
        parts = []
        for t in self.result.stats.tokens:
            series = self.result.token_occupancy_series.get(t.kind, [(0, 0)])
            values = sample_step(series, 0, self.runtime, 80)
            body = Text()
            body.append("buffer ")
            body.append(sparkline(values, t.buffer_capacity))
            cap = f" / cap {t.buffer_capacity}" if t.buffer_capacity is not None else ""
            body.append(f"\npeak {t.peak_buffer}{cap}   produced {t.produced} "
                        f"(initial {t.initial_inventory})   consumed {t.consumed}   "
                        f"leftover {t.leftover}\n", style="dim")
            related = [e for e in self.result.errors if e.token == t.kind]
            parts.append(Panel(Group(body, *(error_panel(e) for e in related[:6])),
                               title=f"[bold blue]{t.kind}[/]", border_style="blue"))
        self.query_one("#tok_body", Static).update(
            Group(*parts) if parts else Text("no tokens in this run", style="dim"))

    def _render_services(self) -> None:
        parts = []
        for s in self.result.stats.services:
            q = sample_step(self.result.service_queue_series.get(s.id, [(0, 0)]),
                            0, self.runtime, 80)
            b = sample_step(self.result.service_busy_series.get(s.id, [(0, 0)]),
                            0, self.runtime, 80)
            body = Text()
            body.append("queue  ")
            body.append(sparkline(q, s.queue_capacity))
            body.append(f"  max {s.max_queue_length:,}/{s.queue_capacity:,}\n")
            body.append("busy   ")
            body.append(sparkline(b, s.workers))
            body.append(f"  peak {s.peak_busy_workers}/{s.workers} workers, "
                        f"utilization {s.utilization:.1%}\n")
            body.append(f"{s.total_jobs:,} jobs, {s.deadline_misses:,} deadline miss(es)\n",
                        style="red bold" if s.deadline_misses else "dim")
            related = [e for e in self.result.errors if e.service == s.id]
            parts.append(Panel(Group(body, *(error_panel(e) for e in related[:6])),
                               title=f"[bold magenta]{s.id}[/]", border_style="magenta"))
        self.query_one("#svc_body", Static).update(
            Group(*parts) if parts else Text("no services in this run", style="dim"))

    def _fill_factories(self) -> None:
        summary = self.query_one("#fact_summary", Static)
        if not self.result.stats.factories:
            summary.update(Text("no factories in this run", style="dim"))
            return
        strips = []
        for f in self.result.stats.factories:
            runs = self.result.factory_runs.get(f.id, [])
            strip = Text()
            strip.append(f"{f.id:<10}", style="bold green")
            for run in runs:
                strip.append("■" if run["success"] else "✖",
                             style="green" if run["success"] else "bold red")
            strip.append(f"   {f.successes}/{f.attempts} ok, {f.retries} retries, "
                         f"{f.empirical_success_rate:.0%} (p_spec inc. mode)",
                         style="dim")
            strips.append(strip)
        summary.update(Group(_factory_table(self.result), *strips))
        table = self.query_one("#fact_table", DataTable)
        table.cursor_type = "row"
        table.add_columns("factory", "run", "attempt", "start_us", "end_us",
                          "outcome", "scheduled by")
        for fid, runs in sorted(self.result.factory_runs.items()):
            for run in runs:
                table.add_row(
                    fid, run["run_id"], str(run["attempt"]),
                    str(run["start_us"]), str(run["end_us"]),
                    Text("success", style="green") if run["success"]
                    else Text("FAIL", style="bold red"),
                    run["scheduled_by"])

    def _render_errors(self) -> None:
        errs = self.result.errors
        if not errs:
            self.query_one("#err_body", Static).update(
                Panel(Text("No violations: the schedule satisfies every "
                           "finite-service constraint.", style="bold green"),
                      border_style="green"))
            return
        self.query_one("#err_body", Static).update(
            Group(*(error_panel(e) for e in errs[:300])))
