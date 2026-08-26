"""
pytest-rich-summary  —  Rich output plugin for CW6 verification.
Displays a summary table at the end of the test run.
"""
import pytest
from rich.console import Console
from rich.table import Table
from rich.panel import Panel


class RichSummary:
    """Collect results and display a summary table at the end."""

    def __init__(self):
        self.results = []

    @pytest.hookimpl(tryfirst=True)
    def pytest_runtest_logreport(self, report):
        if report.when == "call":
            self.results.append({
                "nodeid": report.nodeid,
                "outcome": report.outcome,
                "duration": report.duration,
            })

    @pytest.hookimpl(hookimpl=True)
    def pytest_terminal_summary(self, terminalreporter):
        if not self.results:
            return

        console = Console()
        table = Table(title="CW6 Backing — Test Summary", show_lines=False)
        table.add_column("Test", style="cyan", no_wrap=True)
        table.add_column("Status", justify="center")
        table.add_column("Time", justify="right")

        passed = failed = 0
        for r in self.results:
            if r["outcome"] == "passed":
                table.add_row(r["nodeid"], "[green]✓ OK[/]", f"{r['duration']:.3f}s")
                passed += 1
            elif r["outcome"] == "failed":
                table.add_row(r["nodeid"], "[red]✗ FAIL[/]", f"{r['duration']:.3f}s")
                failed += 1
            else:
                table.add_row(r["nodeid"], "[yellow]— SKIP[/]", f"{r['duration']:.3f}s")

        console.print()
        console.print(table)
        console.print()

        total = passed + failed
        color = "green" if failed == 0 else "red"
        console.print(Panel(
            f"[{color}]{passed}/{total}[/{color}] tests passed"
            + (f"  [red]({failed} FAILED)[/red]" if failed else "  [green]ALL OK[/green]"),
            title="CW6 Verification",
            border_style=color,
        ))
