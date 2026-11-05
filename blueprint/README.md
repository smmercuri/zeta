# Blueprint

Human-readable blueprint for the `zeta` formalization, linked to the Lean code
via `\lean{}` / `\leanok` / `\uses{}` annotations.

## Building locally

Requires Python + a TeX distribution (full TeX Live recommended for the PDF):

```bash
pip install leanblueprint        # provides plasTeX + the blueprint LaTeX package
cd <repo root>
leanblueprint web                # HTML + dependency graph -> blueprint/web/
leanblueprint pdf                # PDF (xelatex + unicode-math) -> blueprint/print/
leanblueprint checkdecls         # verify every \lean{...} names a real declaration
```

- The **web** build (plasTeX → MathJax) handles the raw unicode math in the
  chapters directly.
- The **PDF** build uses `xelatex` + `unicode-math` (see `src/print.tex`). A few
  chapters use raw `²` / `₀` super/subscripts; if xelatex's math font lacks them,
  either rely on the web build or rewrite those as `^{2}` / `_{0}`.
- `checkdecls` needs the Lean project to be built first (`lake build`).

## Layout

- `src/content.tex`: inputs the 21 chapters in reading order.
- `src/web.tex`, `src/print.tex`: web and PDF roots.
- `src/preamble/`: shared macros (`common`) and per-target theorem setup.
- `src/plastex.cfg`: plasTeX/web configuration.
- `src/references.bib`: bibliography.

Only sources are tracked. The build output (`web/`, `print/`, `lean_decls`, and
the stray `src/*.aux` / `*.log` / `*.pdf` latexmk files) is ignored via
`blueprint/.gitignore`; rebuild it locally with the commands above.
