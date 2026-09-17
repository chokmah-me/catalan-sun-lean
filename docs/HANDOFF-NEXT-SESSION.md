# Handoff: catalan-sun-lean, next session

**Written 2026-09-17, at commit `e58dfb8`.** For an agent picking this up cold.
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

**The standing rule, which has now paid off four times:** before proving a
scaffolded statement, (a) check it against the paper, and (b) gate it
numerically in Python, keeping the scripts. Sessions have been lost to skipping
this. Details and the four instances: `docs/FORMALIZATION-NOTES.md`.

## 2. Current state (verified, not asserted)

- `lake build` clean: **2957 jobs**, exit 0.
- **0** `sorry` / `admit` / `native_decide`. (A `grep` for `sorry` hits one
  comment in `Thm21.lean:7` — the phrase "are sorry-free", not a hole.)
- **140** `#print axioms` lines, all within `[propext, Classical.choice,
  Quot.sound]`.
- `lean-proof-forge` is **not installed on this machine**. Its checks were run
  manually; `results/lean_verify_brief.md` says so. Do not claim a forge pass
  without the forge.
- Toolchain: Lean 4.32.2 / Mathlib v4.32.2.

Proved through §5: Thm 2.1, Cor 2.1, Prop 3.1, Cauchy–Binet, PC0–PC3, det-level
Lemma 5.4, **Thm 5.1**, **Lemma 5.5 (both (5.2) and (5.3))**, and now
**Corollary 5.2's positive-part collapse** (`CatalanSun/Cor52.lean`).

## 3. The one open gap I created — start here

`Cor52.posPartLedger` indexes over `layerIndexFull B S`, cutoff
`layerBound B S = 6B + 2S + 5`. But `Lemma55.lemma_5_5_ledger_little_o_holds`
((5.3)) is proved over `layerIndex B`, cutoff `5B`. **The two index sets differ,
so (5.3) cannot currently be consumed by Cor 5.2.** Stage D is therefore a
deliberate stub: I proved the index-set-independent termwise piece
(`abs_layer_diff_le`) and the containment
(`layerIndex_subset_layerIndexFull`), and did **not** claim the summed `o(B²)`
comparison.

**Task 1 (highest value): re-prove (5.3) over `layerIndexFull`.**

Why the cutoff had to widen: `[aQB − mAQ]₊` is *nonzero* for odd prime powers
`Q ≥ 5B`. Exact support is `Q ≤ 2(N−1)+2B+1 = 6B+2S+5` (`N = Ndim B S`),
because `aQB` counts solutions of `Q ∣ 2i+2h+1` over `i < N`, `1 ≤ h ≤ B`, and
that is the largest value the modulus argument attains. Above it `NKQ`, `aQB`
and `mAQ` all vanish. The truncated band carries `≈ 0.627·B²` — `Θ(B²)`, not
`o(B²)`.

**This is mechanical, not research.** `5*B` enters (5.3)'s proof only as a
numeric bound — never structurally. The four places to change:

| lemma | line | change |
|---|---|---|
| `card_layerIndex_le` | `Lemma55.lean:1428` | `≤ 5*B` → `≤ layerBound B S` |
| `sum_inv_layer_le` | `Lemma55.lean:1497` | `harmonic (5*B)` → `harmonic (layerBound B S)` |
| `layer_term_le` | `Lemma55.lean:1451` | `log (5*B)` bound → `log (layerBound B S)` |
| `eventually_log_sq_le` | `Lemma55.lean:1534` | same substitution; still `log²x/x → 0` |

`layer_pow_injOn` (unique factorization) is cutoff-independent and needs nothing.

**Checked numerically before writing this:** the crude bound
`111·B·log(L)·(6+log L)` at `L = 6B+2S+5` versus `L = 5B` gives `RHS/B²` of
88.5 vs 84.3 (B=10²), 2.08 vs 2.02 (10⁴), 0.286 vs 0.279 (10⁵), 0.0048 vs
0.0047 (10⁷). **~2% degradation; `o(B²)` survives comfortably.** Consider
proving it directly over `layerIndexFull` rather than generalizing `layerIndex`,
to avoid disturbing the existing green (5.3).

**Task 2: close Stage D.** With Task 1 done:
`Finset.abs_sum_le_sum_abs` → termwise `abs_layer_diff_le` →
`mul_le_mul_of_nonneg_right` → re-proved (5.3). **Sign trap:** (5.3)'s summand
is written `|((a0−m0) − (a−m))|` — the opposite order from what you will have.
One `abs_sub_comm`; it presents as a failed `exact`.

## 4. The `5B` question — settled, do not redo it

I spent real effort on this; the answer is recorded so you do not repeat it.

**The `5B` is the paper's own number**, not a scaffold invention. Three
confirmations: `da77779`'s docstring transcribes it "(per the proof)"; an
earlier session fetched the arXiv v1 §5.1 HTML and found "the separate
`p^ν < 5B` restriction used later in (5.3)'s summation range"; and
`docs/robustness-check-catalan.md` independently attributes it to the paper.

**But the band `[5B, 6.1B]` is already covered by §8, so `δ₀` is safe.**
Partitioning the ledger by the paper's own three ranges puts the band wholly
inside *Large primes (`p > B`)*, which is unbounded above. Measured mass split:

| B | small `Q≤S` | mid `S<p<B` | large `p>B, Q<5B` | large `p>B, Q≥5B` |
|---|---|---|---|---|
| 200 | 12.2% | 40.3% | 43.9% | 3.6% |
| 400 | 19.0% | 35.8% | 42.1% | 3.2% |
| 800 | 23.1% | 34.5% | 39.4% | 3.0% |

Decisive: `Δ_{>B} = (2/3)ρ + (1/2)ρ²` (eq. 8.4) is a **closed form in `ρ` alone
with no cutoff parameter** — the integral over the whole `p>B` tail.

So: a **bookkeeping inconsistency between §5.1 and §8 inside the paper**, not a
missing contribution. Note the band is `≈65×δ₀` in raw magnitude, so it would
have been fatal had it genuinely been dropped. It is not dropped.

**Residual uncertainty, stated honestly:** this partition used the plain-language
range description in `docs/catalan-constant-irrational.md`, **not** §§6–9 of the
paper directly. The `Δ_{>B}` closed form is strong evidence the tail is
unbounded, but if you want it airtight, read §8's derivation for an explicit
upper cutoff. That is the one loose end here.

## 5. The bigger missing piece (scope before starting)

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

- **The numeric gate lives in `.scratchpad/cor52/`** (gitignored, local only):
  - `layers.py` — verbatim brute-force Python mirror of the Lean defs.
  - `fast2.py` — O(1) `NKQ` via modular inverse (`h ≡ 2⁻¹(−2i−1) mod Q`) plus an
    **exact** DP minimizer for `mAQ` over residue classes. Cross-validated
    against `layers.py` on 189 layers, **0 mismatches**. Brute force is
    `C(2B+S+3, S)` and dies past B≈80; the DP reaches B=1200 in ~70s.
  - `FINDINGS.md`, `gate_support.py`, `gate_threshold.py`, `gate_mass.py`.
  - **Free consistency check:** 0 violations of `thm_5_1` (`aQB ≥ mAQ`) across
    every layer tested — the Python mirror agrees with proved Lean. Re-run this
    first if you modify any layer definition.
  - Consider promoting these to a committed regression check; they are the most
    reusable asset here and are one `rm -rf` from gone.
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

1. Re-prove (5.3) over `layerIndexFull` (§3, Task 1) — mechanical, unblocks all.
2. Close Stage D (§3, Task 2) — then §5 is genuinely self-contained.
3. Optionally settle §4's residual uncertainty by reading §8 directly.
4. Scope the §4→§5 valuation lemma (§5) before committing to it.
5. Props 6.3/7.4 remain **certified-numerics** work (Arb / interval arithmetic),
   not Lean work. `mpmath` and `sympy` are installed; `python-flint` is not.
