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

import CW3_all_figures  # noqa: E402

GENERATORS = [
    ("fig1_alphas_uniqueness", CW3_all_figures.make_fig1),
    ("fig2_ER_bridge_identity", CW3_all_figures.make_fig2),
    ("fig3_N_modes", CW3_all_figures.make_fig3),
    ("fig4_top_down", CW3_all_figures.make_fig4),
    ("fig5_three_panel", CW3_all_figures.make_fig5),
    ("fig6_cylinder_torus", CW3_all_figures.make_fig6),
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
            fn()  # each generator writes to CWD (the images/ dir)
    finally:
        os.chdir(start_cwd)
    print(f"\nAll figures saved to: {args.output_dir.resolve()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
