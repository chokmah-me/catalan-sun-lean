**Update (this session, 2026-09-15, working Lean/lake toolchain available):** the
statement-hypothesis fix below is landed (`thm_5_1_statement` now takes
`S * 20 ≤ B` and `Injective f`, `lake build`-verified). `sum_NKQ_tail_ge` (KI)
is **not yet proved**, but the "concrete blocker" this note originally
flagged — the `NKQ`/`sumT` convolution identity — **is now solved exactly**
and landed (`lake build`-verified, zero `sorry`): see "Exact `sumT` formula
(landed)" below, which replaces the open-ended trapezoid sketch with a closed
form. What remains for (KI) is now a much narrower, precisely-stated gap: see
"What's left for (KI)" at the end of this file.

# Theorem 5.1: reduction to one remaining inequality

**Status:** analysis only, not a proof. Written in a session with **no Lean
toolchain reachable** (sandbox network policy blocks `release.lean-lang.org`,
so `elan`/`lake`/`mathlib` could not be installed and nothing below was
type-checked). Treat every Lean snippet here as a sketch for a human/agent
with a working `lake build` to verify, adjust, and land — not as
landable code.

## What this note establishes

Given the lemmas already proved and `lake build`-verified in
`CatalanSun/Thm51.lean` (`mAQ_le_ellAQ_consecutive`,
`aQB_sub_ellAQ_consecutive` (5.16), `second_line_nonneg`,
`phiQ_add_CAQ_le_phiQ_N` (5.17)), assembling `thm_5_1` requires **exactly one**
further fact — call it (KI), for "key inequality." Everything else is
`linarith`-level bookkeeping over already-proved results. This narrows
"finish Theorem 5.1" from an open-ended task to a single, precisely-stated
combinatorial inequality about `NKQ` and `phiQ`.

It also flags a **hypothesis gap**: the current scaffold

```lean
def thm_5_1_statement : Prop :=
  ∀ (B : ℕ), 20 ≤ B →
    ∀ (Q : ℕ), OddPrimePower Q →
      ∀ (S : ℕ), 0 < S → S < B →
        ∀ (f : Fin S → Fin (S + 3)),
          aQB B S Q ≥ mAQ B S Q f
```

is missing hypotheses the derivation actually needs: `Injective f` (used by
(5.17)) and the paper's ratio bound `S * 20 ≤ B` (used by (KI) below — see
"Why (KI) needs the ratio bound"). The corrected target should be:

```lean
def thm_5_1_statement : Prop :=
  ∀ (B : ℕ), 20 ≤ B →
    ∀ (Q : ℕ), OddPrimePower Q →
      ∀ (S : ℕ), 0 < S → S * 20 ≤ B →
        ∀ (f : Fin S → Fin (S + 3)), Function.Injective f →
          aQB B S Q ≥ mAQ B S Q f
```

(`S * 20 ≤ B` already implies `S < B` via `S_lt_B_of_ratio`, so the old
`S < B` hypothesis can be dropped or kept redundantly.)

## The reduction

Fix `B S Q` with `hQ : 0 < Q`, `hSN : S ≤ Ndim B S` (`S_le_Ndim`), and
`f : Fin S → Fin (S+3)` with `hf : Injective f`. Write `J` for
`consecutiveInitial (Ndim B S) S hSN` and `ℓ_J` for `ellAQ B S Q f J _`.

1. **`mAQ_le_ellAQ_consecutive`**: `mAQ B S Q f ≤ ℓ_J`.
2. **`aQB_sub_ellAQ_consecutive` (5.16)**:
   `aQB B S Q - ℓ_J = 2*sumT - phiQ Q (2*B) - CAQ B S Q f - 2*phiQ Q S + sum2`
   where `sumT = ∑ i ∈ tailFin B S hSN, (NKQ B Q i.val : ℤ)` and `sum2` is the
   nonnegative correction sum.
3. **`second_line_nonneg`**: `sum2 ≥ 0`.
4. **`phiQ_add_CAQ_le_phiQ_N` (5.17)** (needs `hf : Injective f`):
   `phiQ Q (2*B) + CAQ B S Q f ≤ phiQ Q (Ndim B S)`.

Chain them:

```text
aQB B S Q = ℓ_J + 2*sumT - phiQ Q (2*B) - CAQ B S Q f - 2*phiQ Q S + sum2
          ≥ ℓ_J + 2*sumT - phiQ Q (2*B) - CAQ B S Q f - 2*phiQ Q S      [sum2 ≥ 0]
          ≥ ℓ_J + 2*sumT - phiQ Q (Ndim B S) - 2*phiQ Q S              [(5.17)]
          ≥ ℓ_J                                                        [if (KI) holds]
          ≥ mAQ B S Q f                                                [step 1]
```

The last step needs exactly:

**(KI)** `phiQ Q (Ndim B S) + 2 * phiQ Q S ≤ 2 * sumT`, i.e.

```lean
theorem sum_NKQ_tail_ge {B S Q : ℕ} (hQ : 0 < Q) (hB : 20 ≤ B) (hS0 : 0 < S)
    (hSB : S * 20 ≤ B) (hS : S ≤ Ndim B S) :
    (phiQ Q (Ndim B S) : ℤ) + 2 * (phiQ Q S : ℤ) ≤
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ)
```

Given `sum_NKQ_tail_ge`, the assembly is a `linarith` call:

```lean
theorem thm_5_1 {B Q S : ℕ} (hB : 20 ≤ B) (hOPP : OddPrimePower Q)
    (hS0 : 0 < S) (hSB : S * 20 ≤ B)
    (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    aQB B S Q ≥ mAQ B S Q f := by
  have hQ : 0 < Q := hOPP.pos
  have hSN : S ≤ Ndim B S := S_le_Ndim B S
  have h16 := aQB_sub_ellAQ_consecutive (B := B) (S := S) (Q := Q) hQ hSN f
  have h17 := phiQ_add_CAQ_le_phiQ_N (B := B) (S := S) (Q := Q) f hf
  have h2 := second_line_nonneg (B := B) (S := S) (Q := Q) (hS := hSN) (Q := Q)
  have hKI := sum_NKQ_tail_ge (B := B) (S := S) (Q := Q) hQ hB hS0 hSB hSN
  have hle := mAQ_le_ellAQ_consecutive (B := B) (S := S) (Q := Q) f hSN
  linarith
```

(Argument names/order above are a sketch — the actual `second_line_nonneg`
signature takes `Q` implicitly from context via the goal, and exact
`(B :=) (S :=) (Q :=)` named-argument syntax will need adjusting to whatever
`lake build` accepts. The mathematical content — which five facts combine and
how — is the part this note is confident about.)

## Why (KI) is the hard part, and why it needs the ratio bound

`sum_NKQ_tail_ge` is **not** a loose bound — a back-of-envelope order-of-magnitude
check shows it is tight and genuinely needs `S * 20 ≤ B`:

- `NKQ B Q i` counts `h ∈ [1,B]` with `Q ∣ 2i+2h+1`. Since `Q` is odd, `2` is
  invertible mod `Q`, so this is "how many integers in an interval of length
  `B` hit a fixed residue class mod `Q`" — roughly `B/Q`, periodic in `i` with
  period `Q` (see `NKQ`'s definition; note `2i+2h+1 ≡ 0 (mod Q)` iff
  `i + h ≡ (Q-1)/2 (mod Q)` after multiplying by the inverse of 2).
- `tailFin` has `Ndim B S - S = 2B + 3` elements, so
  `sumT = ∑_{i=S}^{N-1} NKQ(B,Q,i) ≈ (2B+3) · (B/Q)`, i.e. `2*sumT ≈ 4B²/Q`
  to leading order (roughly independent of `S`, since `NKQ` is periodic in `i`
  and the count of terms barely depends on `S`).
- `phiQ Q (Ndim B S) ≈ (2B+S)²/(2Q) = 2B²/Q + 2BS/Q + S²/(2Q)` and
  `2 * phiQ Q S ≈ S²/Q`, so the right side of (KI) needs to beat
  `2B²/Q + 2BS/Q + O(S²/Q)`.
- Leading `B²/Q` terms roughly cancel (`4B²/Q` vs `2B²/Q`, with room to
  spare), but the **cross term `2BS/Q`** on the RHS-to-beat is linear in `B`
  times `S`, not quadratic in `B` alone — it only stays dominated by the
  `O(B²/Q)` slack once `S = O(B)` with a small enough constant. This is
  exactly the role of `S * 20 ≤ B` (i.e. `S ≤ B/20`): it caps the cross term
  at `2B·(B/20)/Q = B²/(10Q)`, small relative to the `~2B²/Q` slack. Drop the
  ratio bound (e.g. try `S` close to `B`) and the crude estimate above
  suggests (KI) can fail — consistent with the paper stating Theorem 5.1's
  proof for `B ≥ 20` alongside the fixed ratio `S/B = 1/20` used throughout
  the paper (see `docs/robustness-check-catalan.md`, row 1).
- Because the margin is only a **constant-factor** slack (not an asymptotic
  landslide), (KI) almost certainly needs **exact** floor-function bookkeeping
  — an analogue of `phiQ_formula`/`phiQ_sub_quadratic_eq` for the *shifted,
  truncated* sum `sumT`, not the asymptotic quadratic bounds
  (`phiQ_sub_quadratic_nonneg`/`_le`) already in the file. Those quadratic
  bounds carry `±Q/8` slop, which is too coarse once the cross term `2BS/Q`
  is a fixed fraction of the leading term.

**Suggested proof strategy for (KI)** (untested): double-count
`∑_{i=S}^{N-1} NKQ(B,Q,i) = ∑_{i=S}^{N-1} #{h ∈ [1,B] : Q ∣ 2(i+h)+1}` by
swapping the order of summation over `j = i+h` (a convolution of two integer
intervals, lengths `N-S = 2B+3` and `B`), which gives an exact
piecewise-linear ("trapezoidal") count of multiples of `Q` weighted by
`min(B,j) - max(1, j-(N-S)+1) + 1`. This is the same style of exact identity
`phiQ_formula` already proves for the un-convolved case; extending it to a
convolution is genuinely more work (case splits on where the trapezoid's
ramps fall relative to `Q`-periodicity) and is the actual "residue engine"
the paper's (5.18)-(5.21) presumably carry out. This is the concrete blocker.

## What was and wasn't verified this session

- **Verified by inspection against the tracked, `lake build`-passing source**:
  the five lemma names/shapes cited above, `Ndim`, `Dref`, `OddPrimePower`,
  `tailFin`, `S_le_Ndim`, `consecutiveInitial`, `injective_f_add`.
- **Not verified (no compiler available)**: any Lean snippet in this note,
  including `thm_5_1`'s assembly proof and the statement of `sum_NKQ_tail_ge`.
- **Paper cross-reference**: attempts to fetch the exact text of paper
  equations (5.15)-(5.21) via `arxiv.org/pdf/2609.04176` through this
  session's web-fetch tool gave inconsistent/unreliable equation numbering
  across repeated attempts (it correctly reproduced (5.1)'s floor-function
  definition verbatim on a calibration check, but disagreed with itself about
  whether (5.15)-(5.21) exist as numbered display equations). The reduction
  above does **not** depend on that extraction being right — it only uses the
  already-`lake build`-verified Lean lemmas in this repo plus elementary
  arithmetic. The one place paper cross-reference mattered (confirming that
  Theorem 5.1 does carry a ratio hypothesis like `S ≤ B/20`, not just
  `S < B`) was corroborated independently by (a) the pre-existing
  `docs/WORKPLAN-CONTINUATION.md` note "assemble `thm_5_1` under `S*20 ≤ B`
  and `Injective f`" (written by a prior session with real paper + lake
  access) and (b) the leading-order estimate above, which shows the
  unconditional (`S < B` only) statement is not plausible from the already-
  proved building blocks alone.

## Exact `sumT` formula (landed)

All landed, `lake build`-verified, zero `sorry`, in `CatalanSun/Thm51.lean`
under `## PROOF-D`:

- `r0Q Q := (Q - 1) / 2`, with `two_mul_r0Q : Odd Q → 2 * r0Q Q + 1 = Q`.
- `dvd_two_add_one_iff : Q ∣ 2*j+1 ↔ j % Q = r0Q Q` (for `Q` odd): since `Q`
  is odd, `2` is invertible mod `Q`, and this pins the unique residue.
- `PsiQ Q n := #{j < n : j % Q = r0Q Q}`, with the closed form
  `PsiQ_eq : PsiQ Q n = (n + r0Q Q) / Q` (a single floor division — no sum).
- `NKQ_eq_PsiQ_sub : NKQ K Q i = PsiQ Q (i+K+1) - PsiQ Q (i+1)`: `NKQ` is a
  window-difference of `PsiQ`, because `Q | 2i+2h+1 ↔ Q | 2(i+h)+1` and `h`
  ranges over `[1,K]` iff `j := i+h` ranges over `[i+1, i+K]`.
- `sum_NKQ_tail_eq`: summing `NKQ_eq_PsiQ_sub` over `tailFin` and reindexing
  each `PsiQ`-sum via `phiQ_sub_eq_sum_Ico` (already in the file) gives, for
  `hQ : 0 < Q`, `hodd : Odd Q`, `hS : S ≤ Ndim B S`:

  ```text
  sumT = phiQ Q (N + (B+1) + r0Q Q) - phiQ Q (S + (B+1) + r0Q Q)
       - phiQ Q (N + 1 + r0Q Q)     + phiQ Q (S + 1 + r0Q Q)
  ```

  where `N = Ndim B S = 2B+S+3`, all cast to `ℤ`. This is an **exact identity**
  (not a bound), built entirely from `phiQ` at four shifted arguments — no
  convolution/trapezoid case-split was needed in the end. It supersedes the
  "Suggested proof strategy for (KI)" section above (the double-counting
  sketch), which is no longer the right approach: `PsiQ`'s single-floor
  closed form made the case-split unnecessary.

## What's left for (KI)

`sum_NKQ_tail_ge` (i.e. `phiQ Q (Ndim B S) + 2*phiQ Q S ≤ 2*sumT`) now reduces,
via `sum_NKQ_tail_eq`, to a **pure inequality among six `phiQ` evaluations**
(the four inside `sumT`, plus `phiQ Q (Ndim B S)` and `phiQ Q S` themselves) —
no more combinatorics, only real analysis of `phiQ`'s remainder.

Using the file's existing `phiQ_sub_quadratic_eq` (exact: `phiQ Q n =
n²/(2Q) - n/2 + Corr(n)` where `Corr(n) = r(Q-r)/(2Q)`, `r = n % Q`), expand
all six terms. The pure-quadratic parts cancel almost completely (worked out
by hand this session): with `N = 2B+S+3`, the quadratic part of
`2*sumT - phiQ(N) - 2*phiQ(S)` equals `(4B² - 4B - 4BS - S² - 6S - 9)/(2Q) +
B + 1.5S + 1.5` — positive and `Ω(B)` for `B ≥ 20`, `S*20 ≤ B` (the bracket is
`≥ 3.8B² - 4.3B - 9 > 0` in that regime). **The obstruction is the six
`Corr(·)` remainder terms.**

The existing bound `Corr(n) ≤ Q/8` (`phiQ_sub_quadratic_le`) is **too coarse
alone**: it was calibrated for a single `phiQ` evaluation, but naively
applied to all six terms it can dominate the `O(B)` quadratic-part slack
once `Q` is large (worst case `Q → ∞`, sanity-checked by hand this session:
with e.g. `B=20, S=1, Q` huge, all four `sumT`-side arguments land near
`Q/2` — because of the `+ r0Q Q ≈ Q/2` shift — so their individual `Corr`
values are each `≈ Q/8`, not small). What actually happens in that regime
(verified by hand) is that the four `sumT`-side `Corr` terms **nearly cancel
against each other** (they enter with net coefficient `2-2-2+2 = 0` and are
all evaluated near the same point `≈ N+r0Q Q`, so their pairwise differences
are `O(B²/Q) → 0`), while `Corr(N)` and `Corr(S)` (the two "tail" terms, `O(B)`
sized independent of `Q`) are what must be controlled against the
quadratic-part slack. A **naive per-term `Q/8` bound loses this
cancellation** and is not sufficient by itself.

**What a proof needs:** either (a) a Lipschitz/second-difference bound on
`Corr` — e.g. `|Corr(a+d) - Corr(a) - Corr(b+d) + Corr(b)|` small when `a,b`
are close (to control the four-term cancellation exactly, not just bound each
term separately), or (b) a case split on `Q` relative to `B` (e.g. `Q ≤ cB`
vs `Q > cB` for a suitable constant `c`), using `Corr(n) ≤ Q/8` in the first
regime and `Corr(n) ≤ n/2` (trivial: `r ≤ n`, `Corr(n) = r(Q-r)/(2Q) ≤ r/2`)
in the second. Route (b) is more mechanical and is the recommended next step:
`phiQ_sub_quadratic_le` already gives the `Q/8` half; the `n/2` half is a
two-line `nlinarith`/`positivity` fact not yet in the file. The six
arguments are all within `O(B)` of either `N + r0Q Q`, `S + r0Q Q`, `N`, or
`S`, so the threshold analysis only needs to track `B`, `S`, `Q`, `r0Q Q`
(no new combinatorics — this really is now a `nlinarith`-with-the-right-case-
split problem, not an open combinatorial identity).

## Two concrete regimes landed (this session, continued)

Pushed further on the `Corr` bound and landed two more `lake build`-verified,
zero-`sorry` **partial** results in `CatalanSun/Thm51.lean` under
`## PROOF-E` (neither is `sum_NKQ_tail_ge` itself — both are named
sub-lemmas with an explicit extra hypothesis on `Q`):

- **`sum_NKQ_tail_ge_of_Q_large`**: for `Q ≥ 2 * Ndim B S + 2 * B`, both
  sides of (KI) are exactly `0` (`NKQ` vanishes pointwise since
  `2i+2h+1 < Q` always, and `phiQ_of_lt` kills the two `phiQ` terms).
  Trivial once you see it; the real content is establishing the right
  threshold value.
- **`sum_NKQ_tail_ge_of_Q_small`**: for `Q ≤ B` (a *conservative* sub-case
  of the paper's actual small-`Q` range, chosen because it lets the crude
  `Corr(n) ≤ Q/8` bound go through cleanly). Landed by clearing the `Q`
  denominator from `phiQ_sub_quadratic_le`/`_nonneg` first (new helper
  lemmas `phiQ_poly_le`/`phiQ_poly_ge`: `8Q·φ(n) ≤ 4n²-4nQ+Q²` and the
  reverse), which avoids `nlinarith` ever touching a division by a variable
  — that was the single biggest source of tactic timeouts this session.
  The final polynomial step needed `set_option maxHeartbeats 4000000` (the
  un-normalized six-term expression is large) plus manual `ring_nf`+`linarith`
  staging instead of one big `nlinarith` call, since `nlinarith`'s product
  search kept timing out on an expression this size even though the needed
  combination is a simple fixed linear one once expanded.

**What this confirms about the hard part.** While deriving the `Q ≤ B`
threshold by hand, the naive worst-case combination (bound every `Corr`
term separately by `Q/8`, drop the positive ones to `0`) does **not**
actually work as originally guessed in the first version of this note —
working it out symbolically (`ring_nf` on the residual) showed real
`B·r0Q`/`S·r0Q` cross terms that a crude per-term bound cannot absorb; a
sharper decomposition (splitting the slack into `7·(B² − Q²) ≥ 0` plus a
`(16B+24S+24)·r0Q ≥ 0` term plus a `B,S`-only remainder bounded via
`B² ≥ 20BS` and `B² ≥ 400S²`, both themselves products of the ratio
hypothesis with itself) was needed even for this conservative threshold.

**Remaining gap.** `B < Q < 2·Ndim(B,S) + 2·B` (roughly `B` to `~6B`) is
**not covered by either regime** and is still open. Closing it likely means
either (a) redoing the `sum_NKQ_tail_ge_of_Q_small` derivation with the
tighter threshold `Q² ≤ 4B² − S² − 4BS − 6S − 9` (attempted this session,
`ring_nf`-verified to reduce to a residual `D(r) = -28r² + (16B+24S-4)r +
(16B²-16BS-12S²+8B-12S-31)` in `r = r0Q Q`, which **is** numerically
nonneg on the valid range but needs a genuine concavity/two-endpoint
argument, not a one-shot `nlinarith` — the naive version of this attempt
timed out and was abandoned in favor of the conservative `Q ≤ B` version
above), or (b) merging the two regimes' thresholds so `sum_NKQ_tail_ge_of_Q_large`'s
bound reaches down further (e.g. show `NKQ` is *small* rather than *zero*
for a wider `Q` range, using the periodicity fact `NKQ B Q (i+Q) = NKQ B Q i`
— not yet attempted).

A later session extended coverage to `sum_NKQ_tail_ge_of_Q_le_2B` (`Q ≤ 2·B`,
landed, `lake build`-verified) using the same crude `Corr(n) ≤ Q/8` technique
but with a concave-quadratic-in-`Q` endpoint argument (`g(0) ≥ 0` and
`g(2B) ≥ 0`, `g` concave since its `Q²` coefficient is `−7`, so nonneg on
`[0,2B]` follows from the two endpoints via `2B·g(Q) = (2B−Q)·g(0) + Q·g(2B) +
14BQ(2B−Q)`). So the true open gap as of that session was narrower:
`2·B < Q < 2·Ndim(B,S) + 2·B`.

## Session 2026-09-16: numeric structure of the remaining `2B < Q < 2N+2B` gap

**Toolchain note:** this session had a genuinely working `lake build` (elan +
Lean 4.32.2 + Mathlib cache installed fresh on a machine that had none; unlike
the session that wrote the note above, `release.lean-lang.org` was reachable).
`lake build` on the tracked source passes clean: 0 `sorry`, axioms restricted
to `[propext, Classical.choice, Quot.sound]`. No new Lean was landed this
session — the time went into **numerically characterizing** the open gap
before committing to a proof strategy, since the previous session's `g(Q)`
concavity trick (the same one used for `_le_2B`) provably fails past
`Q ≈ 2.5B`: a direct check (`B=20,S=1`) shows `g` (the polynomial from the
`_le_2B` proof) goes negative at `Q=50`, well inside the open gap
(`2B=40` to `2N+2B=128` for these params) — so extending `_le_2B`'s
technique to a larger threshold is **not possible**; the crude per-term
`Corr(n) ≤ Q/8` bound is fundamentally too lossy once `Q` gets much past `2B`.

**What direct numeric evaluation of the true (KI) inequality shows** (Python,
exact integer arithmetic, `phiQ`/`NKQ` computed directly from their
definitions — not the `Corr` bound): for `B=20, S=1` (`N=44`, gap
`Q ∈ (40, 128)`, `Q` odd), the slack `2·sumT − φ_Q(N) − 2·φ_Q(S)` as a
function of `Q` is:

- **Flat-ish plateau** for `Q ∈ [2B, 2N] = [40, 88]`: slack stays close to
  `2B = 40` (observed range `39`–`41` at these params; `2B` was confirmed as
  the right order of magnitude, not exact, across other `(B,S)` samples too —
  e.g. `B=60,S=3` gives plateau values `117`–`120` against `2B=120`).
- **Linear decrease** for `Q ∈ [2N, 2N+2B] = [88, 128]`: slack decreases by
  exactly `2` per step of `2` in `Q` (i.e. slope `−1` in `Q`), from `40` down
  to a minimum of exactly `2` at `Q = 2N+2B−1 = 127` (the largest odd `Q`
  below the `_large` regime's threshold, where the true slack must jump to
  `0`/undefined-comparison since both sides become `0` by `phiQ_of_lt`).
- This pattern (flat plateau ≈ `2B`, then linear decay to a **tight** minimum
  of `2` right at the `_large` boundary) was confirmed at `B ∈ {20,40,60,80,100}`
  with `S = B/20`: in every case the minimum slack over the whole gap is
  exactly `2`, always at `Q = 2N+2B−1`. So (KI) is **tight by design** near
  the top of the range — there is no room for a lossy bound there, matching
  why the `_large` lemma's threshold looks exact rather than conservative.

**A candidate exact mechanism for the linear-decay region**, derived but not
yet Lean-verified: writing `Corr(n) = r(Q−r)/(2Q)` with `r = n mod Q`
(`phiQ_sub_quadratic_eq`'s remainder term), the four `sumT`-side arguments
pair up as `A1 = A3 + B` and `A2 = A4 + B` (`A1,A3` from the `N`-branch,
`A2,A4` from the `S`-branch, all sharing the same `+ r0Q Q` shift). When
there is **no mod-`Q` wraparound** in forming `A1` from `A3` (i.e.
`A3 % Q + B < Q`), there is an exact identity (checked numerically,
20000 random trials, zero violations):

```text
Corr(n + B) − Corr(n) = B * (Q − 2*(n % Q) − B) / (2*Q)      [when n%Q + B < Q]
```

Applying this to both pairs, the `(Q−B)`-type terms cancel between the two
pairs, collapsing the Corr-part of (KI)'s slack to something proportional to
`B * (r4 − r3) / Q` where `r3 = A3 % Q`, `r4 = A4 % Q`, minus the two
"tail" terms `Corr(N) + 2·Corr(S)`. Since `A3 − A4 = N − S = 2B+3` is a fixed
constant (independent of `Q`), `r3` and `r4` are tightly linked mod `Q`. This
looks like the right mechanism for the linear-decay region, but formalizing
it requires splitting on **which** of the (at least) four wraparound
conditions hold (`A3`↦`A1`, `A4`↦`A2`, and the relation between `r3`,`r4`
via the fixed offset `2B+3`) — genuinely more case-split work, not yet
attempted in Lean. The plateau region (`Q ∈ [2B, 2N]`) is comfortably
positive numerically but was **not** found to be covered by any simple
extension of the existing `Corr(n) ≤ Q/8` technique either (that bound is
already too lossy by `Q ≈ 2.5B`, well before the plateau's right edge at
`2N ≈ 4.4B` for `B=20`), so it likely needs the same exact-Corr-difference
mechanism, or a separate argument.

**Recommended next step for a future session:** attempt the no-wraparound
`Corr` difference identity above as a Lean lemma first (it is a clean,
numerically-verified, unconditional fact about `Corr`/`%`, useful
independent of the wraparound case-split), then build the wraparound
case-split around it referencing the fixed offset `A3 − A4 = 2B+3` and
`A1 − A2 = 2B+3` (same offset) to bound how many of the four points can
simultaneously wrap.

## Session 2026-09-16 (continued): gap closed via floor-division, not `Corr`

Landed, `lake build`-verified, zero-`sorry`, in `CatalanSun/Thm51.lean`:
`Corr` (def), `phiQ_eq_quadratic_add_Corr`, `Corr_add_sub_Corr_of_no_wrap`
(the exact identity sketched above, formalized directly), and — the piece
that actually closes almost all of the gap —
`phiQ_add_eq_phiQ_add_of_no_wrap` (`phiQ Q (n+B) = phiQ Q n + B * (n/Q)`
under the same no-wrap hypothesis `n%Q+B<Q`), `phiQ_add_le_add_of_le` (the
`B`-step forward difference of `phiQ` is monotone in the base point — proved
via `phiQ_sum_Ico` and a `Finset.map` shift, no `Corr` needed), and
**`sum_NKQ_tail_ge_of_gap`**, which closes (KI) under `2B < Q < 2N+2B` plus
one extra hypothesis (see below).

**Why floor-division beat the `Corr`-difference route in practice.** The
`Corr` identity above is mathematically equivalent to
`phiQ_add_eq_phiQ_add_of_no_wrap` (checked symbolically:
`q(n+B)-q(n) + Corr_diff = B*(n/Q)` where `q` is the quadratic part), but
working directly with `phiQ` and `Nat.div`/`Nat.mod` avoided a lot of `ℚ`
cast/field-arithmetic bookkeeping that made the `Corr`-based attempt at the
four-term combination unwieldy. Concretely: writing `A3 = N+1+r0Q Q`,
`A4 = S+1+r0Q Q` (`N = Ndim B S`), one has `A4 < Q` throughout the whole
open gap (`S` is too small relative to `B` to reach `Q > 2B` — this needs
only the ratio hypothesis) and `Q ≤ A3` once `Q < 2N+2B` — i.e. `⌊A4/Q⌋=0`,
`⌊A3/Q⌋=1` — **except** `⌊A3/Q⌋` can jump to `2` for a narrow band of `Q`
just above `2B` (`hA1lt` below is exactly the condition that rules this
out). Given `⌊A4/Q⌋=0` and `⌊A3/Q⌋=1`,
`phiQ_add_eq_phiQ_add_of_no_wrap` applied at `A4` and at `A3` gives
`phiQ(A2) = phiQ(A4)` and `phiQ(A1) = phiQ(A3)+B` exactly (no approximation),
collapsing sumT's four-term combination to `phiQ(A3) - phiQ(A4) + B`, and
(KI) reduces to the *same* `phiQ N + 2·phiQ S ≤ 2B` quadratic-positivity
fact that the `_le_2B`/`_of_Q_small` lemmas' pure-polynomial steps already
established (reused here via `phiQ_poly_le` unconditionally — no
`Corr(n) ≤ Q/8` bound needed at all for this piece, since it's now an exact
identity rather than a bound).

**The `d=0` sub-case** (`Q > N`, i.e. `A3 < Q` too) is handled separately:
both `phiQ N` and `phiQ S` vanish (`phiQ_of_lt`), and the goal reduces to
`phiQ(A2)+phiQ(A3) ≤ phiQ(A1)+phiQ(A4)`, which is exactly
`phiQ_add_le_add_of_le` applied to `S+1+r0Q Q ≤ N+1+r0Q Q` (monotonicity of
`phiQ`'s `B`-step difference in the base point — a clean, `Corr`-free,
unconditional fact, no case-split on `Q` needed).

**`sum_NKQ_tail_ge_of_gap`'s exact signature:**

```lean
theorem sum_NKQ_tail_ge_of_gap {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q)
    (hB : 20 ≤ B) (hSB : S * 20 ≤ B) (hS : S ≤ Ndim B S)
    (hQlo : 2 * B < Q) (hQhi : Q < 2 * Ndim B S + 2 * B)
    (hA1lt : Ndim B S + 2 * B + 1 + r0Q Q < 2 * Q) :
    (phiQ Q (Ndim B S) : ℤ) + 2 * (phiQ Q S : ℤ) ≤
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ)
```

**Remaining gap after this session.** `hA1lt` is *not* implied by
`hQlo`/`hQhi` alone — it fails on a narrow band of `Q` just above `2B`
(verified numerically: `Q ∈ {2B+1, 2B+3}` for `B=20`, i.e. exactly 2-3 odd
`Q` values before `hA1lt` starts holding, growing very slowly with `B`; see
the `A1 ≥ 2Q` check in this session's Python scratch work). Root cause: in
that band, forming `A1 = A3+B` wraps around `Q` a *second* time (`⌊A3/Q⌋=1`
but `⌊A1/Q⌋=2`), so `phiQ_add_eq_phiQ_add_of_no_wrap`'s hypothesis
genuinely fails there — it is not a proof-engineering gap, the mechanism
itself doesn't apply. Two ways to close this residual sliver, neither
attempted yet:
(a) extend `sum_NKQ_tail_ge_of_Q_le_2B`'s technique (crude `Corr(n) ≤ Q/8`
bound, concave-quadratic-in-`Q` endpoint argument) a small fixed amount past
`2B` — it was already shown sufficient up to exactly `2B`, and the residual
band is only ~2-4 values wide, so pushing the threshold by a small additive
constant (not a new asymptotic regime) is plausible; or (b) prove a direct
"at most double wrap" version of `phiQ_add_eq_phiQ_add_of_no_wrap` handling
`⌊(n+B)/Q⌋ = ⌊n/Q⌋+1` (one extra wrap) with an explicit correction term,
then a 3-way case split (`0`, `1`, or `2` wraps for `A3→A1`) instead of the
current 2-way (`d=0` vs `d=1`) split.

**Assembling `thm_5_1` still needs:** combining `sum_NKQ_tail_ge_of_Q_large`,
`sum_NKQ_tail_ge_of_Q_le_2B`, and `sum_NKQ_tail_ge_of_gap` (which together
cover all `Q` except the narrow `hA1lt`-failing sliver above) into the
single `sum_NKQ_tail_ge` statement via a `Q`-range case split, once that
sliver is closed. Not yet attempted this session — `sum_NKQ_tail_ge_of_gap`
was landed as a standalone lemma with its own explicit hypotheses, not yet
wired into a case-split dispatcher.

## Session 2026-09-16 (continued further): residual sliver closed, `thm_5_1` proved

Landed, `lake build`-verified, zero-`sorry`: `sum_NKQ_tail_ge_of_gap2`, the
unconditional `sum_NKQ_tail_ge` (dispatching over `Q ≤ 2B`, `Q ≥ 2·Ndim B S +
2·B`, and `_gap`/`_gap2` for the two halves of the middle range), and
`thm_5_1` itself (the `linarith` assembly sketched earlier in this file).
**Theorem 5.1 is now fully proved**, `#print axioms` restricted to
`[propext, Classical.choice, Quot.sound]`.

**Correction to the earlier "~2-4 values" estimate.** The previous session's
claim that `hA1lt`'s failure band was only ~2-4 odd `Q` values just above `2B`
was checked only at `B=20`; a wider scan showed the true residual (negation
of `sum_NKQ_tail_ge_of_gap`'s literal hypothesis `Ndim B S + 2*B + 1 + r0Q Q <
2*Q`) grows *linearly* with `B` (e.g. ~35 values at `B=2000`), and moreover is
not uniformly pinned to a single `(⌊A1/Q⌋,⌊A2/Q⌋)` quotient pair — a first
attempt assuming a single closed form `(2,1)` for the whole residual failed
numerically once `S` was allowed to range over its full `1..B/20` domain (not
just `S = B/20`), which had masked a further sub-case. The residual actually
splits into three quotient regimes, all reachable depending on `B,S,Q`:
`(⌊A1/Q⌋,⌊A2/Q⌋) ∈ {(1,0), (1,1), (2,1)}` (the fourth combinatorial
possibility, `(2,0)`, never occurs — `A1 − A2 = Ndim B S − S` is a fixed
constant and `Q > 2B` bounds how far apart their quotients can be).

**How it was closed.** `sum_NKQ_tail_ge_of_gap2` handles the full residual
(negation of `_gap`'s hypothesis) via `phiQ_formula` applied directly at each
of the four shifted points with `omega`-derived, explicit integer quotients —
not the `no_wrap` additive identity (`phiQ_add_eq_phiQ_add_of_no_wrap`), which
only covers single-wrap steps and cannot express a second wraparound. Internal
structure: outer `by_cases` on `A2 < Q` (`(1,0)` vs `A2 ≥ Q`), then inner
`by_cases` on `A1 < 2*Q` within the `A2 ≥ Q` branch (`(1,1)` vs `(2,1)`). Each
branch collapses `2*sumT` to its own closed form (`2*B`, `2*Q−2*S−2*r0Q Q−2`,
or `2*B+2*N−2*Q−2*S` respectively) and closes via the same
`phiQ_poly_le`-based quadratic-positivity technique as `_le_2B`/`_gap`, using
the branch's own tight linear hypothesis (not `hQhi`) as the `nlinarith` hint
— the `(2,1)` branch's polynomial fact is false against the full `hQhi` upper
bound but true against the tighter `A1 ≥ 2*Q` bound, which was the fix needed
after an initial `nlinarith` failure with the looser hint.

**`sum_NKQ_tail_ge`** dispatches `Q ≤ 2*B` / `Q ≥ 2*Ndim B S + 2*B` / (within
the remaining gap) `_gap`'s `hA1lt` / its negation, calling the four regime
lemmas. **`thm_5_1`** is exactly the `linarith` assembly this file sketched
under "The reduction" above, now with all five inputs proved unconditionally.

## Environment note for next session

This session could not install Lean/elan: `elan toolchain install` failed
with `CONNECT tunnel failed, response 403` against
`release.lean-lang.org`, and the sandbox's outbound proxy status
(`GET $HTTPS_PROXY/__agentproxy/status`) confirms that host is policy-denied
(`connect_rejected`), unlike `pypi.org`/`registry.npmjs.org`/etc. which are
allowlisted. `arxiv.org` is denied the same way for direct `curl`. Next
session needs either a machine with unrestricted network (as prior sessions
evidently had — see the Windows paths in `results/lean_verify_*`) or a
sandbox with `release.lean-lang.org` and a Mathlib cache host allowlisted.
