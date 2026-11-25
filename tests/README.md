# Test suite — 03-crystalline-worldsheet

The numerical companion of the manuscript (`02-methods`, "The numerical
companion is the pytest suite in `tests/`). <!-- counts:begin id="suite-total" -->571<!-- counts:end id="suite-total" --> tests, ~25 s.

## How to run it

```bash
uv run python -m pytest tests/ -q          # full suite (the only entrypoint that works)
pnpm test                                  # same, through the package script
# counts:begin id="verify-py"
pnpm run verify:py                         # same, minus the `slow`-marked tests (543)
# counts:end id="verify-py"
uv run python -m pytest tests/ -q -m 'not slow'   # ditto, without pnpm
uv run python -m pytest tests/test_kk.py -q       # one module
```

`uv run pytest …` (no `python -m`) fails with `Failed to spawn: pytest` in this
project: `pytest` lives in the optional `test` extra, so uv does not install the
console script into the environment it spawns. Always go through
`uv run python -m pytest`. Configuration is in `pyproject.toml`
(`[tool.pytest.ini_options]`: `testpaths`, `pythonpath = ["tests/src"]`,
`markers`, `addopts`).

Markers: `slow` (deselect with `-m "not slow"`), `symbolic`, `numerical`,
`gauge`, `gravity`, `places`. The `--repulsion-full` option raises the
level-repulsion run to 25 digits / 238 zeros (~8 min).

## Layout

```
tests/
├── conftest.py            fixtures (precision tiers, tolerances, seeded RNGs)
│                          and the --repulsion-full option
├── rich_summary.py        optional rich terminal summary (plugin)
├── src/cw6/               ← the single numerical origin of the suite
│   ├── constants.py       every constant with its ORIGIN tag (DERIVED /
│   │                      CODATA / AD_HOC) and a label of the manuscript;
│   │                      also the mpmath views (PHI_MP, EPS_0_MP, …) and the
│   │                      sympy views (PHI_SYM, …) of the same formulas
│   └── helpers.py         shared computations: chi5, fib, the prime sieve,
│                          Euler/Dedekind products, Gell-Mann matrices, zeta
│                          zeros, random null vectors, …
├── test_witness_census.py every \tier[…]{N} / \witness{N}{…} key of the
│                          manuscript is a real \label and is named by a test
└── test_*.py              one module per section of the paper
```

**Rule: nothing re-derives a constant or a helper.** If a test needs φ, ε₀,
M_PCF, a character, a sieve or an Euler product, it imports it from
`cw6.constants` / `cw6.helpers`. The precision views exist so that a module
working at 40 mpmath digits does not rebuild the constants at its own precision.

## Conventions

* **Docstrings name the manuscript tag** they back — `certainty_product`,
  `prop:pcf-norms`, `basel_zeta_two` — so a witness key can be grepped from
  `tests/` and a test can be found from a tag. `test_witness_census.py` enforces
  this for every numerical witness.
* **Assertions cite figures the manuscript prints.** A number that is not in
  `src/chapters/*.tex` is either derived here or marked `AD_HOC` in
  `constants.py` with a note on why the value does not affect the conclusion.
* **No assertion may be true by construction of its own parametrisation**: if a
  test would pass whatever the code under test does, it must be rewritten
  against the manuscript or against an independently computed route (that is
  what `TestMuDiagram`, `TestL1ThreeRoutes` and the Regge-residue tests do).
* **Parametrised ids must stay citable** (`test_individual[6-56]`,
  `test_lucas[3]`, `test_logarithmic_derivative[0.0]`): the manuscript and the
  witness decisions quote them by name.
* Deterministic RNGs only (seeds in `conftest.py`); no network, no writes.
