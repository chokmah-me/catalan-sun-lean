# Handoff: catalan-sun-lean, next session

**Written 2026-09-17 at commit `e58dfb8`; updated the same day after Stage D
closed.** For an agent picking this up cold.
Read this file, then `docs/FORMALIZATION-NOTES.md`. Everything below was
verified in-session; where something is inferred rather than checked, it says so.

---

## 1. What this repo is, and the one rule that matters

Lean 4 / Mathlib formalization of structural lemmas from Zhi-Wei Sun,
*Catalan's constant is irrational* (arXiv:2609.04176v1, math.GM, unrefereed).

**It does not claim Theorem 1.1, and must not start.** The repo's credibility
rests on being scrupulous about the boundary between what is proved in Lean and
what is assumed, cited, or externally computed. Several files carry explicit
"what this does NOT establish" docstrings. Preserve that discipline; it is the
product, not a formality.

**The standing rule, which has now paid off four times (and cost nothing the
fifth time, when it confirmed a widened bound in seconds):** before proving a
scaffolded statement, (a) check it against the paper, and (b) gate it
numerically in Python, keeping the scripts. Sessions have been lost to skipping
this. Details and the four instances: `docs/FORMALIZATION-NOTES.md`.

## 2. Current state (verified, not asserted)

- `lake build` clean: **2957 jobs**, exit 0.
- **0** `sorry` / `admit` / `native_decide`. (A `grep` for `sorry` hits one
  comment in `Thm21.lean:7` — the phrase "are sorry-free", not a hole.)
- **150** `#print axioms` lines, all within `[propext, Classical.choice,
  Quot.sound]`.
- `lean-proof-forge` **is installed** (synced skill; path in
  `results/lean_verify_brief.md`). Its verifier reports CAPABILITY_LIMITED:
  every check passes, and the axiom audit is UNKNOWN only for 38 `private` or
  primed helper names its resolver cannot address; those are covered
  transitively by the 150 curated `#print axioms` lines in `CatalanSun.lean`.
  Run it with `_tmp/` (gitignored vendored tooling) moved aside, or it flags a
  `sorryAx` string inside lean4export's tests.
- Toolchain: Lean 4.32.2 / Mathlib v4.32.2.

Proved through §5: Thm 2.1, Cor 2.1, Prop 3.1, Cauchy–Binet, PC0–PC3, det-level
Lemma 5.4, **Thm 5.1**, **Lemma 5.5 (both (5.2) and (5.3))**, **Corollary
5.2's positive-part collapse**, **(5.3) over the full index set**
(`Cor52.ledgerFull_little_o`), and **the model comparison**
`Cor52.posPartLedger_sub_little_o`: the exact and `(0)` ledgers of (5.24)
agree to `o(B²)`. §5 is now self-contained at the ledger level.

## 3. The index-set gap — closed (do not reopen)

`Cor52.posPartLedger` indexes over `layerIndexFull B S`, cutoff
`layerBound B S = 6B + 2S + 5`, while `Lemma55.lemma_5_5_ledger_little_o_holds`
((5.3)) is over `layerIndex B`, cutoff `5B`. This was the one gap the previous
session left. **Both tasks it set are done**, in `Cor52.lean` Stage F and the
closing Stage D, with `Lemma55.lean` untouched:

- `ledgerFull_little_o` — (5.3) verbatim over `layerIndexFull B (B/20)`. The
  `5B` only ever entered as a numeric cap; every cap is now `12B`
  (`layerBound B (B/20) ≤ 12B` for `B ≥ 1`), giving
  `SUM ≤ 111·B·log(12B)·(13 + log 12B)`. Gate: `scripts/gates/gate_full53.py`.
- `posPartLedger_sub_little_o` — `|posPartLedger − posPartLedger0| ≤ εB²`
  eventually, for every `f`. Via `Finset.abs_sum_le_sum_abs`, the termwise
  `abs_layer_diff_le`, and one `abs_sub_comm` applied at the `ℤ` level before
  casting (the predicted sign trap; doing it after the cast lets `rw` grab the
  wrong `|·−·|`).

Why it was mechanical: `layer_int_bound` (the (5.2) input) has no upper cutoff
on `Q`. Nothing here needed new mathematics. Everything built on the first
try.

## 4. The `5B` question — reopened, and now the most important thing here

An earlier version of this section said the `[5B, 6.1B]` band was "covered by
§8" because `Δ_{>B}` is a closed form in `ρ`. **That was inferred, not read,
and it is wrong.** §8 states `ℰ_ρ(t)` for `1 < t < 2+ρ` and integrates
`∫_1^{2+ρ}` (eq. 8.2): an explicit cutoff at `p = (2+ρ)B = 2.05B`.

The exact ledger (`scripts/gates/gate_ledger_vs_paper.py analyze
scripts/gates/data/ledger_S_B20_B200-1200.csv`) then shows three things,
recorded in full at `docs/FORMALIZATION-NOTES.md#tail-band`:

- Where the paper integrates, `mAQ/B` **is** the paper's density: `Λ_mid`
  matched to 1.2% and rising, (8.2) matched to 0.1%, (8.1)'s branches
  visible per prime. The §5 transcription is faithful.
- Above `(2+ρ)B`, `m^A_{p,B} = −2S` exactly for every prime up to `4B`
  (the `−2·1_{Q ≤ 2i+1}` term of (5.7)). That `m`-mass is `2ρ(2−ρ)B² =
  (39/200)B²`, **numerically identical to the raw quadratic (9.4)** and 20×
  `δ₀`. The `a` part of the tail cancels exactly via (3.5)/(3.7), so the old
  "65× δ₀" figure was the wrong quantity.
- Whether that `0.195·B²` is already inside `39/200` or is missing cannot be
  decided from §§5–9. By (3.5)/(3.7) the whole `B²` claim reduces to
  `log|Ξ_I| − ∑_p m_p log p ≤ −δ₀B² + o(B²)`, with `Ξ_I` the (4.5) closed
  form that `PascalCauchy.Xi_closed_form` already states.

**This has now been done — and it did not need `Ξ_I` at all.** Full note:
`docs/FORMALIZATION-NOTES.md#scalar-verdict`. Summary below in §4a.

## 4a. The verdict: the `B²` claim fails by `≈ 1.87` as the paper reduces it

`scripts/gates/gate_scalar.py`. Rather than the (4.5) closed form, use the
paper's own reduction. From (3.5), (5.13) summed over odd `p`, and (5.24),
everything cancels except three computable terms:

```
log H_B^min + log|q̂_B|  ≤  log|det R[A,J]| + v₂(F_B) log 2 − ∑_{odd Q} m_Q log p
```

Theorem 9.1 asserts this is `≤ −δ₀B² + o(B²)`, `δ₀ > 0.0097`. Measured:

| `B` | 200 | 400 | 800 | 1000 |
|---|---|---|---|---|
| `SCALAR/B²` | +1.826146 | +1.845926 | +1.851237 | **+1.854020** |

Converging upward to `≈ +1.86`, not drifting logarithmically (increments fall
~4× per doubling). **`B = 1000` was run as a blind prediction test**: the
earlier three points predicted `+1.854003`, measured `+1.854020`. **The dominant term is `v₂(F_B) log 2 → 2 log 2 = 1.386`.**
`F_B` is in the numerator of (3.5) and `v₂(F_B) ~ 2B²`; (5.24) sums over odd
`p` only, so that mass is never removed. **Remark 9.3 names this exact term**
("the residual real power of 2 from `F_D` ... included in ... (6.21)") and
assigns it to `c_odd = 0.00628` — which is **221× too small**. Remark 6.2's
`(19/200)log 2 = 0.0658` is still 21× too small. Lemma 5.4 concerns
`H_B^min`'s 2-part, not the real place.

Validated three ways (algebraic, direct-from-(3.5), and the (5.13) identity
to `1.6e-16`); `det R` checked against brute-force `polygamma` at
`B = 20,40,60`, against an exact-integer evaluation at `B = 200,400`, and
across four row sets `A`.

**This does not impugn the Lean**, which claims nothing in §9 and is
unaffected. If you want to continue on the paper: find where `2 log 2 · B²`
is cancelled, or treat Theorem 9.1 as unsupported. If you want to continue on
the formalization, §5 below is unchanged and still the real work.

## 5. The bigger missing piece — start here (scope before starting)

Nothing in §5 currently constrains a *height*. `aQB` / `mAQ` are pure ℕ/ℤ
floor-and-collision combinatorics: `grep -c padicVal` returns **0** for both
`Thm51.lean` and `Lemma55.lean`. The only valuation↔determinant bridge in the
repo is `lemma_5_4_det`, and it is `p = 2` only.

So the paper's actual Cor 5.2 — `log H_B^min ≤ ∑_Q [a−m]₊ log p` — is **not**
formalized, and `Cor52.lean` says so in its header. The prerequisite is the
§4→§5 odd-`p` valuation lemma (`v_p(Ξ_I) ≥ ℓ^A_Q(I) − …`), which is unstarted
and probably larger than Lemma 5.5 was. `PascalCauchy.Xi_closed_form` is the
natural input but is ℝ-valued with no arithmetic attached.

**Do not name anything `logHmin` until that lands.** If you want a staged step,
state the valuation input as an explicit hypothesis (`LayerValuationInput`) and
prove Cor 5.2's *deductive* step against it, leaving the input visibly open —
the pattern `thm_5_1_statement` followed for several sessions.

## 6. Tooling notes that will save you time

- **The numeric gates are committed at `scripts/gates/`** — see its README.
  `gate_ledger_vs_paper.py` plus `data/ledger_S_B20_B200-1200.csv` hold the
  exact per-layer `(a, m)` values at `S = B/20` up to `B = 1200`; recomputing
  them costs about a minute at `B = 1200` and scales badly past that.
  **Run `python scripts/gates/check.py` first** (exit 0 = the Python mirror
  still agrees with the Lean definitions), and re-run it after any change to a
  layer definition in `Thm51.lean` or `Lemma55.lean`.
  - `layers.py` — verbatim brute-force mirror of the Lean defs; dies past B≈80
    because `mAQ` enumerates `C(2B+S+3, S)` subsets.
  - `fast2.py` — O(1) `NKQ` via modular inverse (`h ≡ 2⁻¹(−2i−1) mod Q`) plus an
    **exact** DP minimizer for `mAQ` over residue classes. Validated against
    `layers.py` on 189 layers, **0 mismatches**; reaches B=1200 in ~70s.
  - `check.py` also asserts `thm_5_1` (`aQB ≥ mAQ`) numerically — a free check
    of the mirror against proved Lean. **If it fails, the mirror drifted, not
    the Lean.**
- **Known Lean traps** (all in `FORMALIZATION-NOTES.md`): `push_cast` destroys
  `((B/Q : ℕ) : ℝ)` — use `rw [Int.cast_mul, Int.cast_add, Int.cast_one,
  Int.cast_natCast]` then `norm_num`. `abs_add` is now `abs_add_le`;
  `Nat.pos_pow_of_pos` is now `Nat.pow_pos`. `abs_max_sub_max_le_max` at
  `b = d = 0` gives positive-part 1-Lipschitzness (already done,
  `Cor52.abs_posPart_sub_le`).
- `lake build` is ~2957 jobs, mostly cached Mathlib; budget minutes and
  background it.
- Editing these UTF-8 files from Python on Windows needs explicit
  `encoding='utf-8'`.

## 7. Suggested order

0. ~~The (4.5) mirror and the `−δ₀B²` check.~~ **Done — see §4a.** The
   paper's ledger does not close as reduced: `+1.86` against a needed
   `−0.0097`. Decide whether to keep formalizing §5 in light of that; the
   Lean itself is unaffected and makes no §9 claim.
1. Scope the §4→§5 odd-`p` valuation lemma (§5) before committing to it. If
   staged, land `LayerValuationInput` as an explicit hypothesis and Cor 5.2's
   deductive step against it; keep `logHmin` out of the namespace until the
   input is proved.
2. Optionally settle §4's residual uncertainty by reading §8 directly.
3. Props 6.3/7.4 remain **certified-numerics** work (Arb / interval arithmetic),
   not Lean work. `mpmath` and `sympy` are installed; `python-flint` is not.
