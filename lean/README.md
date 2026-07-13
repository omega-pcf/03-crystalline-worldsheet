# CW3 — Lean 4 / Mathlib Backing

Lean 4 formal backing for `CW3_paper_integrado_nuevo_s4.tex`.

The single Lean library `CW3_Backing` (defined by `lakefile.toml`) compiles
the file `CW3_Backing.lean`, which backs every `\Lean{...}` tag cited in the
manuscript (113 tags, namespace-marked for collision safety).

## Build

```bash
lake build
```

This pulls the Mathlib dependency pinned in `lake-manifest.json` and then
compiles `CW3_Backing.lean`.
