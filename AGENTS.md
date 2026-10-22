# AGENTS.md — catalan-sun-lean

Lean 4 / Mathlib slice of structural lemmas from Sun's Catalan preprint (arXiv:2609.04176v1), including Theorem 5.1 and Lemma 5.5.

**This project does not claim Theorem 1.1 (G irrational).**

## Commands

```powershell
python scripts/gates/check.py
lake build
python ..\lean-proof-forge\scripts\verify_lean_project.py --project .
```

Toolchain: Lean **4.32.2** / Mathlib **v4.32.2** (same pin as `aria-moebius`).

## Work rules

- Gate a scaffolded statement numerically (`scripts/gates/check.py`) before proving it.
- Do not pursue Props 6.3/7.4 as formalization targets; Theorem 9.1 fails the paper's own numeric test (`docs/FORMALIZATION-NOTES.md`).
- The Lean claims no part of §9.

## Pointers

- `README.md` — what is proved, DOI map
- `docs/FORMALIZATION-NOTES.md` — scalar verdict on Theorem 9.1
- `docs/con-leche.md` — external kernel check
- `CITATION.cff` / `ZENODO.md` — cite / DOI map
