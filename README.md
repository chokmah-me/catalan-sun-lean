# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1.** It locks arithmetic facts that the
paper's proof depends on, starting with:

| ID | Content | File | Forge status |
|----|---------|------|--------------|
| P4 | `4ρ−2ρ² = 39/200`, `Δ_{>B} = 83/2400` at `ρ=1/20` | `CatalanSun/Ledger.lean` | proved |
| P1 | Lemma 5.4 positive-part + 2-integrality toolkit | `CatalanSun/TwoAdic.lean` | proved (partial) |
| P2 | Cauchy `n≤2` + odd-denom applicability | `CatalanSun/Cauchy.lean` | proved |
| P3 | Thm 2.1 polynomial / constant-denom fragment | `CatalanSun/FunctionalEq.lean` | proved (partial) |

`lean-proof-forge` verify: **pass** (0 sorry, axioms ⊆ classical three). See `results/lean_verify_brief.md`.

Deferred: full RatFunc pole-chain; general-`n` Cauchy; Props 6.3/7.4; Mertens/PNT; Thm 1.1.

## Build

```text
lake build
```

Or via lean-proof-forge:

```text
python ../lean-proof-forge/scripts/verify_lean_project.py --project .
```

Toolchain: Lean 4.32.2 / Mathlib v4.32.2 (same pin as `aria-moebius`).

## Incoming (not on the default target)

`incoming/TailRecurrence.lean` defines the Catalan tail `T_m` / weighted tail `u_m` and sketches Sun eq. 1.4. It extends this slice but is **not kernel-green** (two `sorry`s: summability, positivity). lean-proof-forge forbids `sorry`, so it stays out of `CatalanSun.lean` until those are discharged.

Paper notes: `docs/catalan-constant-irrational.md`, `docs/robustness-check-catalan.md`.

Repo: https://github.com/chokmah-me/catalan-sun-lean (private).
