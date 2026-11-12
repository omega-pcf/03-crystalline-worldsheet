#!/usr/bin/env python3
"""
Entry point for figure generation for the CW3 paper.

Delegates to the single-file generator
``scripts/figures/CW3_all_figures.py`` (six figures:
``fig1_alphas_uniqueness``, ``fig2_ER_bridge_identity``,
``fig3_N_modes``, ``fig4_top_down``, ``fig5_three_panel``,
``fig6_cylinder_torus``).  Each generator writes its PNG into the
current working directory, so the figures end up inside ``images/``
when this script is invoked from that directory.

Usage:
    python scripts/figures/main.py                 # generate all
    python scripts/figures/main.py --list          # list generators
    python scripts/figures/main.py --output-dir ../images
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

# Deterministic, text-extractable PDFs (see docs/figures.md): matplotlib
# writes the wall clock into /CreationDate unless SOURCE_DATE_EPOCH is set,
# and Type 3 fonts on matplotlib 3.10 carry no /ToUnicode, so pdftotext
# loses the math glyphs.  Pinned to the timestamp of the figure round that
# produced images/ (2026-11-09 19:31:03 -06:00); an explicitly exported
# SOURCE_DATE_EPOCH still wins.  Set before matplotlib is imported.
os.environ.setdefault("SOURCE_DATE_EPOCH", "1794274263")

import matplotlib  # noqa: E402
import CW3_all_figures  # noqa: E402
import CW3_gue_figures  # noqa: E402


def apply_rc() -> None:
    """Re-pin the rcParams that decide what the PDF bytes look like.

    ``CW3_all_figures`` sets its own ``RC`` at import time; this runs again
    before every generator so nothing can reset the font embedding.
    """
    matplotlib.rcParams.update({
        "pdf.fonttype": 42,          # CID TrueType carries /ToUnicode
        "pdf.use14corefonts": False,
    })

GENERATORS = [
    ("fig1_alphas_uniqueness", CW3_all_figures.make_fig1),
    ("fig2_ER_bridge_identity", CW3_all_figures.make_fig2),
    ("fig3_N_modes", CW3_all_figures.make_fig3),
    ("fig4_top_down", CW3_all_figures.make_fig4),
    ("fig5_three_panel", CW3_all_figures.make_fig5),
    ("fig6_cylinder_torus", CW3_all_figures.make_fig6),
    ("fig7_spacing_histogram", CW3_gue_figures.make_fig7),
    ("fig8_sine_kernel", CW3_gue_figures.make_fig8),
]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list",
        "-l",
        action="store_true",
        help="List available figure generators and exit.",
    )
    parser.add_argument(
        "--output-dir",
        "-o",
        type=Path,
        default=HERE.parents[1] / "images",
        help="Directory to save the PNGs (default: project_root/images).",
    )
    args = parser.parse_args(argv)

    if args.list:
        print("Available figures:")
        for name, _ in GENERATORS:
            print(f"  - {name}")
        return 0

    args.output_dir.mkdir(parents=True, exist_ok=True)
    start_cwd = os.getcwd()
    os.chdir(args.output_dir)
    try:
        for name, fn in GENERATORS:
            print(f"  -> {name}")
            apply_rc()  # font embedding stays deterministic across generators
            fn()  # each generator writes to CWD (the images/ dir)
    finally:
        os.chdir(start_cwd)
    print(f"\nAll figures saved to: {args.output_dir.resolve()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
