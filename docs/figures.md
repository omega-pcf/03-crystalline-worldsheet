# Figure pipeline: deterministic, text-extractable PDFs

`pnpm run generate:figures` runs `scripts/figures/main.py`, which delegates to
`scripts/figures/CW3_all_figures.py` and `scripts/figures/CW3_gue_figures.py`
(eight figures, written into `images/`).

The chain table (generator → `images/` → verification) is
[`architecture.md` §Sources of truth](architecture.md#sources-of-truth).

## What it guarantees

1. **The text in the PDFs is extractable.** Every generated PDF carries a
   `/ToUnicode` CMap, so `pdftotext` reads `σ`, `α`, `φ` back instead of
   junk.
2. **Two consecutive runs are byte-identical.** `SOURCE_DATE_EPOCH` is pinned,
   so the PDF `/CreationDate` no longer follows the wall clock and
   `git status --porcelain images/` does not change between runs.
3. **No host font is a prerequisite.** The typography is pinned in
   `CW3_all_figures.py` (`RC`: DejaVu Serif + STIX, both bundled with
   matplotlib).

## Settings (in `scripts/figures/main.py`)

| Setting | Value | Reason |
| --- | --- | --- |
| `pdf.fonttype` | `42` | Guarantees `/ToUnicode` regardless of the locked matplotlib version (Type 3 carries it only from matplotlib 3.11 on). Applied by `apply_rc()` before every generator, so a generator resetting the rcParams cannot lose it. |
| `SOURCE_DATE_EPOCH` | `1794274263` | The timestamp of the figure round that produced `images/` (2026-11-09 19:31:03 -06:00). Honoured by the pdf, ps and svg backends; an explicitly exported value still wins. |

## Verifying

```bash
pnpm run generate:figures          # run once
sha256sum images/* > /tmp/a
pnpm run generate:figures          # run twice
sha256sum images/* > /tmp/b && diff /tmp/a /tmp/b   # must be silent

pdffonts images/fig1_alphas_uniqueness.pdf    # emb sub uni: yes yes yes
pdftotext images/fig1_alphas_uniqueness.pdf - # reads σ, α …
```

Docker (`kjarosh/latex`) is not involved in figure generation: it is only the
LaTeX engine of `pnpm run build`.
