# Workplan: continuing past Theorem 5.1 toward Lemma 5.5

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## Next session pointer

**2026-09-16 (newest): re-verification REFUTES the "minimizer-free" numeric
claim recorded below (the "even later" entry) — that claim does NOT hold
either; the recommended Step-1 proof route based on it is a dead end.**
Re-derived `ellAQN`/`ell0AQ` from scratch (independent Python script, bit-for-
bit against the current `Thm51.lean`/`Lemma55.lean` source, dropping only the
shared `CAQ` constant as before) and validated the hill-climbing minimizer
search against **exact brute force** on two small cases (including one with
`Q` large relative to `N`, the regime where growth appears) — brute force and
hill-climb agreed exactly both times, so the search itself is not at fault.

Sweeping `ell0AQ(consecutive) - min_{I'} ellAQN(Ndim0, I')` over arbitrary
card-`S` subsets `I'` (same-residue-class, top-block, mid-block, random, plus
hill-climbed near-minimizers — not just adversarial near-minimizers) gives
`ratio/S` (ratio = gap / (1+B/Q)) that **grows with `Q`, not saturating**:

```
S=10,  B=200:  ratio/S = 2.19 at Q=243
S=40,  B=800:  ratio/S = 1.87 at Q=1331
S=160, B=3200: ratio/S = 1.22 at Q=2187, still rising
```

This is the same unbounded-growth shape as the original counterexample to
`lemma_5_5_row_stability` itself (see "latest" entry immediately below),
**not** the "ratio/S stays under ~1.8, bounded" pattern the prior session
reported for the same claim. The prior session's scratch scripts were never
committed, so the exact source of the discrepancy between the two numeric
runs is unknown — but this re-derivation was checked directly against the
current Lean definitions and validated against brute force, so it is taken
as the more trustworthy result going forward.

Also fetched the paper's actual §5.1 HTML text directly (arXiv:2609.04176v1)
to double check for a missed constraint: confirmed there is **no stated
relation between `Q` and `B`/`S`** anywhere in Lemma 5.5's statement or proof
sketch, beyond "odd prime power `Q`" and the separate `p^ν < 5B` restriction
used later in (5.3)'s summation range. The proof text gives no mechanism
explaining why the bound wouldn't blow up as `Q` grows relative to `S`/`B`.

**Conclusion:** both the literal `lemma_5_5_row_stability` statement AND the
stronger minimizer-free strengthening of it appear to be genuinely false /
unprovable as stated, for the same underlying reason. This now looks like a
real gap in the paper's Lemma 5.5 argument (option (b) from the original
halt note below), not a transcription bug in this repo's Lean scaffold, and
not fixable via the minimizer-free shortcut previously proposed. **Do not
pursue the 3-step proof route in the "even later" entry below — its Step 1
premise does not hold.**

**Recommended next steps:**
1. Consider whether a *weaker, differently-scoped* restatement of Lemma 5.5
   might still be true and still sufficient for (5.3) — e.g. bounding
   `|m^A - m^{(0)}|` by `C(1+B/Q)` only for `Q ≤ c·√B` or some other relation
   tying `Q`'s growth to `B`/`S`, then handling large `Q` separately (if the
   large-`Q` contribution to the (5.3) sum is negligible for a different
   reason — e.g. there may be few odd prime powers in that range, or the
   `log p` weighting may suppress it). This has NOT been checked numerically
   yet.
2. Alternatively, treat this as a genuine gap in the arXiv v1 preprint worth
   flagging explicitly (in the spirit of the existing "Aside — the paper's
   'Lemma 5.3'" note), and consider whether (5.3)'s `o(B²)` conclusion can be
   reached by a different route that doesn't require the per-`Q` bound to be
   uniform in `Q` at all — only that the SUM over `layerIndex B` (`p^ν < 5B`)
   is `o(B²)`, which is a weaker requirement than a uniform per-layer bound.
3. Before any further Lean work, re-verify numerically whichever restatement
   is chosen, keeping the verification script this time
   (`.scratchpad/lemma55-reverify/` — not committed to the repo per existing
   convention, but worth keeping locally across sessions this time, since the
   loss of the previous session's script is why this discrepancy took an
   extra session to catch).

**2026-09-16 (latest): numerical counterexample found to
`lemma_5_5_row_stability` as literally stated; Step 1 work HALTED pending
review.** Working in worktree `lemma55-step1` (branch
`worktree-lemma55-step1`). Before writing any Lean, re-verified the
"load-bearing claim" identified in the scoping pass below (see the "even
later" entry immediately following this one) more thoroughly: fixed `S=10,
B=200`, scanning `Q` from 3 up to 361, all odd prime powers, all `< 5B =
1000` so within the paper's own claimed regime for the eventual `o(B^2)`
sum:

```
Q=    3 consec=  -51 min0=   -54 gap=     3 budget= 67.67 ratio=   0.04
Q=    5 consec=  -36 min0=   -40 gap=     4 budget= 41.00 ratio=   0.10
Q=    7 consec=  -27 min0=   -34 gap=     7 budget= 29.57 ratio=   0.24
Q=    9 consec=  -23 min0=   -31 gap=     8 budget= 23.22 ratio=   0.34
Q=   11 consec=  -18 min0=   -31 gap=    13 budget= 19.18 ratio=   0.68
Q=   25 consec=   -8 min0=   -28 gap=    20 budget=  9.00 ratio=   2.22
Q=   27 consec=    4 min0=   -22 gap=    26 budget=  8.41 ratio=   3.09
Q=   49 consec=    0 min0=   -24 gap=    24 budget=  5.08 ratio=   4.72
Q=   81 consec=   11 min0=   -22 gap=    33 budget=  3.47 ratio=   9.51
Q=  121 consec=   10 min0=   -20 gap=    30 budget=  2.65 ratio=  11.31
Q=  169 consec=    0 min0=   -20 gap=    20 budget=  2.18 ratio=   9.16
Q=  243 consec=   10 min0=   -30 gap=    40 budget=  1.82 ratio=  21.94
Q=  289 consec=   10 min0=   -20 gap=    30 budget=  1.69 ratio=  17.73
Q=  361 consec=   10 min0=   -20 gap=    30 budget=  1.55 ratio=  19.30
```

`gap = ell0AQ(consecutive)_noC − (local-search min of ellAQN over the
Ndim0 model)_noC` (dropping the shared `CAQ` constant, which cancels
identically since it doesn't depend on the row set), `budget = 1 + B/Q`,
`ratio = gap/budget`. **The ratio grows with `Q`, with no sign of
saturating at a fixed value** — this is the wrong shape for an *absolute*
constant `C` bound (`lemma_5_5_row_stability` requires `ratio ≤ C`
uniformly over **all** odd prime powers `Q`, and the paper's own proof
sketch gives no upper cutoff on `Q` either). This reproduces and sharpens
the earlier spot-check below (which found ratio ≈ 18-22 at `Q=243` alone
but hadn't yet swept across `Q` to see the growth trend).

Verification steps taken to rule out a transcription/search bug before
accepting this as a real problem:
- Re-derived `NKQ`/`FNQ`/`indicatorQle`/`CAQ`/`ellAQN` bit-for-bit from
  `Thm51.lean` lines 42-93 in a **standalone Lean `#eval` script**
  (`lean --run`, no Mathlib import, just core + `List`), confirming Lean
  brute force over all card-3 subsets of a small `Fin(126)` space (i.e.
  `S=3, B=60, Q=9`) agrees exactly with the Python local-search result on
  the same parameters (both give `mAQ_noC = -9`, `ell0AQ_noC(consecutive)
  = 1`, `min-over-Ndim0-model_noC = -8`; ratio there ≈ 1.3, fine).
- Verified the Python local-search hill-climbing algorithm reproduces the
  *exact* Lean brute-force optimum at that small scale (not just close),
  giving confidence it also finds true optima (or very near them) at
  larger scales where brute force is infeasible.
- The growth trend (ratio increasing with `Q`, not bounded) is consistent
  across two independently-written Python scripts in this session and the
  earlier single-point spot-check.

**What this means:** either (a) `lemma_5_5_row_stability`'s Lean statement
in `Lemma55.lean` has a transcription bug relative to the paper (e.g. a
missing side constraint on `Q`, such as `Q ≤ c·B` for some constant tying
it to `B`, that the paper's proof implicitly assumes even though its
statement as quoted says "for every odd prime power `Q`"), (b) the paper's
Lemma 5.5 proof sketch is itself incomplete/wrong at large `Q` relative to
`S`/`B` (plausible — this is a terse, unrefereed Sept-2026 math.GM
preprint; the proof text is "the two row sets have symmetric difference at
most six... at most three replacements are needed, proving (5.2)" with no
actual derivation of why 3 replacements suffice or how the bound behaves
as `Q → ∞` relative to `S`), or (c) there's a numerical bug still
unaccounted for despite the cross-checks above. **Did not proceed to write
any Lean lemmas this session** given this open question. Scratch scripts
(not committed to the repo, session scratchpad only): a `Q`-sweep script
computing `ellAQN` minus the shared `CAQ` term via local-search
hill-climbing with random restarts, plus the Lean `#eval` cross-check
(`LemmaCheck.lean`, standalone re-derivation of `Thm51.lean`'s defs) — both
worth recreating to re-verify if picking this up again.

**Recommended next steps for whoever continues this:**
1. Re-examine whether `Q` should be bounded (e.g. `Q ≤ c·B`) somewhere in
   Lemma 5.5's actual hypotheses — check whether Corollary 5.2's use of
   Lemma 5.5 only ever invokes it for `Q < 5B` (the `layerIndex`
   restriction already present in `lemma_5_5_ledger_little_o`) and whether
   the `∀ Q` in `lemma_5_5_row_stability` should instead read `∀ Q, Q < 5*B
   → ...` or similar — note this does NOT obviously fix it, since
   `Q=243 < 5B=1000` was already in the tested range above and still shows
   ratio ≈ 22.
2. Consider whether `S` needs to scale with `Q` in some way not captured
   by the fixed `S*20 ≤ B` hypothesis alone, or whether an additional
   relation between `Q` and `S` is implicit in the paper's argument (e.g.
   the "every residue class contains at most `1+U/Q` admissible indices"
   remark suggests the argument may implicitly assume `Q` is not too large
   relative to `S`, since with `Q > S` every index sits in its own
   residue class and the "occupancy" argument the paper leans on has no
   force).
3. If the discrepancy persists after investigating 1-2, this may be worth
   flagging as a genuine gap in the paper itself (in the spirit of the
   existing "Aside — the paper's 'Lemma 5.3'" numbering-gap note found
   during the Thm 5.1 push) rather than treated as a scaffolding bug in
   this repo — but that conclusion should not be reached without first
   ruling out 1-2 above.

**2026-09-16 (even later): scoped the hard direction of (5.2); numerically
confirmed the load-bearing claim; NOT started in Lean.** Read the actual
paper text for §5.1 (arXiv:2609.04176v1, HTML at
https://arxiv.org/html/2609.04176v1#S5.E8) via the user. Key findings:

- `m^{(0)}_{Q,B}` is confirmed to be `ell0AQ` at the FIXED consecutive set
  (not a min over subsets) — matches this repo's existing `m0AQ` def, no
  bug there.
- The paper's own proof of the hard direction is genuinely informal/
  hand-wavy: "The two row sets have symmetric difference at most six... If
  a minimizing set uses any of [the 3 extra top indices], replace each by
  an unused index in the common range... At most three replacements are
  needed." It does NOT explain why the resulting swapped set `I'` (a
  card-`S` subset of the common range `{0,...,U₀}`, not necessarily the
  consecutive block) has `ellAQN(Ndim0, I') ≥ ell0AQ(consecutive) - O(1+B/Q)`.
  This second half is the real missing lemma, not addressed by the paper's
  text at all.
- Investigated whether the per-index additive term `g(i) := 2*NKQ(B,Q,i) -
  NKQ(S,Q,i) - 2*indicatorQle(Q,i) - FNQ(N,Q,i)` is monotone in `i` (which
  would let the consecutive block win the additive part by a greedy/
  exchange argument). **It is NOT monotone** — numerically checked (Python,
  thousands of trials): ~22% of adjacent pairs violate `g(i) ≤ g(i+1)`,
  with violation magnitudes comparable to the O(1+B/Q) budget itself. `g`
  is essentially periodic with period ≈ `Q` (driven by `NKQ(B,Q,i)`'s
  sawtooth), so the S indices with globally smallest `g` are scattered
  across the whole range, not `{0,...,S-1}`. **This kills the cheap
  "greedy prefix is optimal" shortcut** — any correct argument must jointly
  bound the additive-term slack and the collision-sum term together (the
  paper's "double-Vandermonde occupancy... O(1+B/Q)" claim), not treat them
  separately.
- **Numerically verified the actual load-bearing claim** (Python, see
  below): for arbitrary card-`S` subsets `I'` of `{0,...,Ndim0-1}`
  (including adversarial choices: all-one-residue-class, top block, middle
  block, random), `ell0AQ(consecutive) - ellAQN(Ndim0, I')` stays bounded
  by roughly `2*(1+B/Q)` — critically, the ratio **does not grow with S**
  (checked S up to 160, B up to 3200, Q up to 2187 ≈ B): ratio/S stays
  under ~1.8 throughout, not blowing up. This is strong evidence
  `ell0AQ(consecutive) ≤ ellAQN(Ndim0, I') + C*(1+B/Q)` holds for an
  absolute `C`, for EVERY card-`S` subset `I'` of the common range (not
  just near-minimizers) — i.e. a genuinely stronger and cleaner lemma than
  the paper's own argument requires, and one that sidesteps needing to
  characterize the minimizer's structure at all.
- **Recommended proof route for next session** (combines two prior
  planning passes + this numeric check):
  1. Prove the strengthened, minimizer-free claim: `∀ I' : Finset (Fin
     (Ndim0 B S))` with `I'.card = S`,
     `ell0AQ B S Q f hS0 ≤ ellAQN B S Q f (Ndim0 B S) I' hI' + C*(1+B/Q)`
     for an absolute `C` — this is self-contained, doesn't need the
     exact-model `U`/swap argument at all, and is the actual hard content.
     Likely needs: (a) a joint bound combining the collision-sum term
     (reuse `collisionSum_eq_phiQ_of_balanced`/`collisionSum_ge_phiQ` from
     Thm51.lean — consecutive's residue occupancy is exactly balanced,
     hence minimizes the collision term outright) with (b) a bound on how
     much the additive `g`-term sum can differ between `I'` and
     consecutive, using `phiQ`-type summation bounds (NOT monotonicity of
     `g` itself, which is false) — likely via comparing `∑_{i∈I'} g(i)`
     against `∑_{i<S} g(i)` through the same `Φ_Q` machinery already used
     for `phiQ_sub_quadratic_le`/`phiQ_superadditive` in Thm51.lean, since
     `NKQ(B,Q,i)` itself is expressible via `PsiQ`/`phiQ`-style counting
     (see `NKQ_eq_PsiQ_sub`).
  2. Given step 1, chain it with the existing swap-mechanics
     (`abs_FNQ_shift_le`-style bound for the exact-model's 3 extra top
     indices, i.e. build `I'` from the true minimizer `I` by ≤3 swaps into
     the common range, each costing `O(1+B/Q)` — reuse/adapt
     `collisionSum_move` for the occupancy-side swap cost) to get
     `ellAQN(Ndim0, I') ≥ ellAQ(I) - 3*O(1+B/Q) = mAQ - O(1+B/Q)`.
  3. Combine 1+2: `m0AQ = ell0AQ(consecutive) ≤ ellAQN(Ndim0,I') + O(1+B/Q)
     ≤ mAQ + O(1+B/Q)`, closing (5.2)'s hard direction.
  - Estimated ~15-25 new Lean lemmas total (index-swap mechanics + the
    step-1 joint additive/collision bound). Multi-session effort; not
    attempted in Lean yet (`Lemma55.lean` unchanged since the easy
    direction landed).
  - Scratch numerical-check scripts (not committed, session scratchpad):
    swept `g(i)` monotonicity and the `ell0AQ(consecutive) vs ellAQN(I')`
    gap across S∈{1..160}, B up to 3200, Q up to 2187, various adversarial
    `I'` (same-residue-class, top-block, mid-block, random). Worth
    re-deriving/keeping a copy in `.scratchpad/` if picking this up again,
    to re-verify before investing further Lean effort.

**2026-09-16 (later): (5.2)'s easy direction proved; found and fixed a real
scaffold bug.** `CatalanSun/Lemma55.lean` now has `mAQ_le_m0AQ_add`
(sorry-free): `mAQ B S Q f ≤ m0AQ B S Q f hS0 + S * (3/Q + 1)` — i.e. one
direction of (5.2) with an explicit constant, unconditional.

**Bug found and fixed:** the original scaffold's `ell0AQ` called `ellAQ`
verbatim, but `ellAQ`'s `FNQ` term hardcoded `N = Ndim B S` internally — so
`ell0AQ` never actually used the `U₀ = 2B+S-1` cutoff; it was a no-op
relabeling of the same value at full dimension. Fixed by generalizing
`Thm51.lean`'s `ellAQ` into a new `ellAQN` (explicit `N` parameter, used
only in the `FNQ` term), with `ellAQ B S Q f I hI := ellAQN B S Q f
(Ndim B S) I hI` preserving every existing call site/proof in `Thm51.lean`
unchanged (full project still builds clean, 0 sorry, axioms ⊆ classical
three). `Lemma55.lean`'s `ell0AQ` now correctly calls `ellAQN B S Q f
(Ndim0 B S) ...`.

Chain of new lemmas proved (all sorry-free) toward `mAQ_le_m0AQ_add`:
- `div_add_le_div_add` / `div_le_div_add` / `abs_div_shift_le`: the atomic
  fact `|⌊(x+d)/Q⌋ - ⌊x/Q⌋| ≤ d/Q + 1`.
- `abs_FNQ_shift_le`: specializes the div-shift bound to `FNQ (Ndim B S)`
  vs `FNQ (Ndim0 B S)` (they differ by the constant `3`), at any
  `i < S ≤ Ndim0 B S`.
- `nQr_consecutiveInitial_castLE`, `ellAQN_castLE_sub_eq`,
  `consecutiveInitial_castLE_eq`: show `ellAQ`'s only `N`-dependent term is
  `FNQ` (the `CAQ`/collision-sum/`NKQ`/`indicatorQle` terms depend only on
  `i.val`, not `N`), so `ellAQ B S Q f (consecutive @ Ndim) - ell0AQ B S Q f
  hS0` collapses to `∑_{i<S} (FNQ(Ndim0) - FNQ(Ndim))`.
- `abs_ellAQ_consecutive_sub_ell0AQ_le`: sums the per-index `FNQ` bound to
  get `|ellAQ(consecutive) - ell0AQ| ≤ S * (3/Q + 1)`.
- `mAQ_le_m0AQ_add`: combines the above with the existing
  `mAQ_le_ellAQ_consecutive` (from `Thm51.lean`) via `linarith`.

**What's left for (5.2) — the hard direction:** `m0AQ ≤ mAQ + C(1+B/Q)`.
`mAQ` is `min` over *all* card-`S` subsets `I` of `Fin (Ndim B S)`, not just
the consecutive one, so this direction needs the paper's genuine
"row-swap replacement" argument (not just the `FNQ`-shift trick above,
which only handles the `U → U₀` swap at a *fixed* row set): for whichever
`I` achieves `mAQ`'s minimum, show it differs from the consecutive set by
symmetric difference ≤ 6, that each one-element swap changes `ellAQ` by at
most `O(1+B/Q)` (via `nQr`/`collisionSum` occupancy bounds, similar in
spirit to `Thm51.lean`'s COMB machinery but genuinely new — nothing in
`Thm51.lean` bounds the effect of swapping one row index for another), and
that at most 3 such swaps suffice. This is materially new combinatorial
work, not yet started. Once landed, `lemma_5_5_row_stability` follows by
combining both directions and taking `C = max(3, sup over the two
constants)` — or just restating with `C` large enough to dominate both
`3/Q+1` (as `1+B/Q` since `Q ≤ 5B` on the relevant range) and the
replacement-argument constant.

Then **(5.3)** (`lemma_5_5_ledger_little_o`) still needs the separate
prime-power-counting sum, as described below — untouched this session.

**2026-09-16: Theorem 5.1 is now fully proved and unconditional** (see
README and `docs/THM51-REDUCTION-NOTES.md` for the closed derivation
history — `sum_NKQ_tail_ge` was finished via a 3-way quotient case split,
`thm_5_1` assembled from PROOF-A–E via `linarith`, `lake build` clean: 0
sorry, axioms ⊆ classical three). The material below this point in the file
predates that and is kept only as history; do not restart Theorem 5.1 work.

**Next target: Lemma 5.5** (paper p.12, "Corrected full-row stability").
Content: there's an absolute constant `C` such that for every odd prime
power `Q`, `|m^A_{Q,B} - m^{(0)}_{Q,B}| ≤ C(1 + B/Q)` (eq. 5.2), where
`m^{(0)}` is the analogue of `m^A` using the *consecutive* row set
`{0,...,S-1}` and cutoff `U_0 := 2B+S-1` instead of the exact selected-row
model's `U = N-1 = 2B+S+2`. Consequently the denominator-layer ledger
difference summed over odd prime powers is `o(B^2)` (eq. 5.3). The paper's
proof is qualitative/asymptotic, not an exact identity: the two row sets
have symmetric difference at most six; each row's contribution changes by
`O(1+B/Q)` under the swap (every residue class mod `Q` contains at most
`1+U/Q` admissible indices); at most three replacements are needed; nonzero
layers satisfy `p^ν < 5B`, and summing `O(1+B/Q)` over `O(√B log B)` prime
powers below `5B` gives `O(B log B) = o(B²)`.

This is a materially different kind of target than anything landed so far
in `Thm51.lean` — those are exact algebraic/combinatorial identities;
Lemma 5.5 is a genuine big-O asymptotic bound requiring prime-power
counting (`p^ν < 5B`) and a nontrivial "at most 3 replacements suffice"
combinatorial argument, likely needs Mathlib's prime-counting /
`Nat.factorization` machinery or a from-scratch bound. Expect this to need
its own scaffold file (e.g. `CatalanSun/Lemma55.lean`) rather than an
extension of `Thm51.lean`.

**Aside — the paper's "Lemma 5.3":** Corollary 5.2's proof (p.12) invokes
"Lemma 5.3" but no such lemma is displayed anywhere in the arXiv v1 PDF
between Theorem 5.1's proof and Corollary 5.2 — apparently a numbering/
typesetting gap in this (Sept 2026, math.GM, lightly-reviewed) preprint.
From the citation's usage (`[x]_+ = x` given `x ≥ 0`), it is almost
certainly the trivial positive-part identity and not separate mathematical
content; no Lean work is needed for it beyond a one-line `max_eq_left` /
`sup_eq_left`-style fact if it's ever needed as a named lemma.

**2026-09-16: scaffolding landed** in `CatalanSun/Lemma55.lean` (defs only,
0 sorry, `lake build` clean): `Ndim0`/`Ndim0_le_Ndim` (the `U₀ = 2B+S-1`
cutoff, tracked as `Ndim0 B S = 2B+S = U₀+1` so it plugs into `ellAQ`'s
existing `N` parameter), `ell0AQ`/`m0AQ` (the consecutive-row-set analogues
of `ellAQ`/`mAQ`, reusing `ellAQ`'s formula at dimension `Ndim0` via
`Fin.castLE` into `Ndim`), `a0QB` (the `aQB` analogue at `Ndim0`), and two
target `Prop`s: `lemma_5_5_row_stability` ((5.2), `∃` absolute `C : ℚ`) and
`lemma_5_5_ledger_little_o` ((5.3), unwound to an `ε`-`B₀` statement over
`layerIndex B` — odd prime powers `p^ν < 5B` — fixing `S = B/20`). Neither
target is proved yet.

Start here next:

1. Read `docs/THM51-REDUCTION-NOTES.md` for Theorem 5.1's now-closed
   derivation history (context only, nothing left to do there).
2. Prove `lemma_5_5_row_stability` (5.2) in `Lemma55.lean`: the paper's
   argument is "symmetric difference of row sets ≤ 6, each swap costs
   `O(1+B/Q)`, at most 3 replacements needed." This likely needs a new
   combinatorial lemma bounding how many indices' `⌊(U-i)/Q⌋` value changes
   when `U` shifts by a bounded amount, plus the existing collision/occupancy
   machinery from `Thm51.lean` (`collisionSum`, `nQr`) applied to the
   perturbed vs. unperturbed row sets.
3. Prove `lemma_5_5_ledger_little_o` (5.3) from (5.2): sum the per-layer
   bound over `layerIndex B`, using `Nat.card` bounds on prime powers
   `< 5B` (Mathlib's prime-counting API, e.g. around `Nat.primeCounting` or
   a cruder `Finset.filter Nat.Prime (range (5*B))` cardinality bound) to
   get `O(√B log B)` layers, hence `O(B log B) log(5B) = o(B²)`. May need to
   sharpen `layerIndex`'s bound or add a lemma relating its cardinality to
   `Nat.sqrt B`.
4. Still not Theorem 1.1; Props 6.3/7.4 and Mertens/PNT remain further out.
4. Evidence from the Theorem 5.1 push (context, not directly reusable):
   `.scratchpad/geneval-thm51-proof/`, `.scratchpad/geneval-thm51-comb/`,
   `.scratchpad/geneval-abs45-thm51-scaffold/`,
   `.scratchpad/geneval-psia-integrality/`,
   `.scratchpad/geneval-pascal-cauchy-pc3/`

## What landed

Sorry-free prefix toward Theorem 2.1 (adversarial verifier PASS; lake build green;
axioms ⊆ classical three):

- **M0** (`CatalanSun/Rank.lean`): `rank_eq_card_iff_mulVec_injective`,
  `exists_nontrivial_column_dependence_of_rank_lt`
- **M1–M2** (`CatalanSun/NewtonDiff.lean`): paper alternating binomial sum
  vanishes for `natDegree p < n`; `paperFwdDiff`; Pochhammer/choose helpers
- **M3** (`CatalanSun/Thm21.lean`): column dependence ⇒
  `paperFwdDiff fSeq n = 0` for all `2B ≤ n ≤ 2B+S+2`
- **M4** (`CatalanSun/Structure.lean` + `Thm21` / `Tail`):
  `Dlam`/`Plam`, deg bounds, and
  `fSeq_eq_neg_tail_succ_mul_Dlam_add_Plam`:
  `f_i = −T_{i+1} D_λ(i) + P_λ(i)`.
  **Paper correction:** written `T_i` form is impossible for polynomial `P`
  under `Π_i = ∏_{h=1}^B` (k=0 needs `(2i+1)²`); Lean uses `T_{i+1}`
  (aligns with ClearedEq23 / `(2X+3)²`).
- **M5** (`NewtonDiff` + `Thm21`): Newton interpolant deg ≤ 2B−1;
  `ASeq = Plam.eval − fSeq = T_{i+1} D` (sign chosen for ClearedEq23)
- **M6** (`Structure` + `Thm21`): `G0`, `Kpoly`,
  `Kpoly_eq_zero_of_column_dep` (ℕ zeros + `G0 ∣ K` + `K(−3/2)=0`)
- **M7** (`CatalanSun/FunctionalEq.lean`): `ClearedEq23`,
  `clearedEq23_to_clearedEq`, `no_clearedEq23_solution_*`

Still present: `RmatrixFin`, rank→minor bridge, conditional `cor_2_1_of_thm_2_1`.

**Landed (M8):** Theorem 2.1 (`thm_2_1_full_column_rank`) and absolute
Corollary 2.1 (`cor_2_1`) are proved in `Thm21.lean`.

## Prior session context

`CatalanSun/FunctionalEq.lean`: the full "no rational solution" theorem —

```lean
theorem no_rational_solution (P Q : ℚ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q
```

i.e. no nonzero rational function `P/Q` satisfies the cleared form of Sun's
functional equation. This is the obstruction Theorem 2.1 will use (now also via
`no_clearedEq23_solution_real` for the paper's `(2X+3)²` form).

## What's already in the repo

- `CatalanSun/Ledger.lean` — P4, exact rational ledger identities. Done.
- `CatalanSun/TwoAdic.lean` — P1, 2-adic toolkit. Done (toolkit only).
- `CatalanSun/Cauchy.lean` — P2, general-`n` Cauchy determinant
  (`det_cauchyMatrix` / Remark 4.1). Done.
- `CatalanSun/CauchyBinet.lean` — Cauchy–Binet `det_mul_eq_sum_minors`. Done.
- `CatalanSun/FunctionalEq.lean` — P3, full `no_rational_solution` + M7 ClearedEq23. Done.
- `CatalanSun/Tail.lean` — Sun eq. 1.4. Done, sorry-free.
- `CatalanSun/Residual.lean` — residual entries `R_{α,j}` (eq. 2.1); **entry-level**
  Lemma 5.4 + `RmatrixRatFin`. Done.
- `CatalanSun/Lemma54.lean` — **det-level Lemma 5.4** (`lemma_5_4_det`). Done.
- `CatalanSun/PascalCauchy.lean` — **PC0–PC3 complete** Pascal×Diag×Cauchy +
  `∑ Ξ_I` + Lemma 4.2 + Lemma 4.1 via `paperP`/`PsiA : ℤ`
  (`det_polyEval_dvd_vandermonde`) + signed `Xi_closed_form` (Lean (4.5) without
  `q`). Done.
- `CatalanSun/Thm51.lean` — §5 layer defs + combinatorial core (COMB-A/B/C) +
  `thm_5_1_statement` (unproved). Done (scaffold + COMB; Thm 5.1 not proved).
- `CatalanSun/Rank.lean` — `RmatrixFin`; rank→minor bridge; conditional Cor 2.1; M0. Done.
- `CatalanSun/NewtonDiff.lean` — M1–M2 finite-diff / Newton helpers. Done.
- `CatalanSun/Structure.lean` — M4 `Dlam`/`Plam` + degree bounds. Done.
- `CatalanSun/Thm21.lean` — M3–M8: structure, Newton deg, `K≡0`,
  `Dlam ≠ 0`, `thm_2_1_full_column_rank`, absolute `cor_2_1`. Done.

## M8 status: Theorem 2.1 assembled

Proved for integers `B > S > 0`:
`(RmatrixFin B S).rank = Fintype.card (Fin S)`, and absolute Cor 2.1 via
`cor_2_1_of_thm_2_1`.

Scratchpad: `.scratchpad/geneval-m8/`.

## Known gap after Theorem 2.1

**Prop 3.1 proved** in `CatalanSun/NewtonCompletion.lean`:
`prop_3_1_det_Atilde` — `det Atilde = ± F_B · det (RmatrixFin.submatrix selectedRows id)`,
via `M = DiffMat * Atilde`, column facts, reindex to nested `fromBlocks`,
`det_fromBlocks_zero₂₁` / `det_fromBlocks_zero₁₂`, then `det_mul` back to `Atilde`.
**`qhat_ne_zero` proved** in `CatalanSun/Qhat.lean`: some injective omitted-row
map `o` has `(Ahat B S o).det ≠ 0`.

**General-`n` Cauchy proved** in `CatalanSun/Cauchy.lean`: `det_cauchyMatrix`
(Remark 4.1 product form).

**Cauchy–Binet proved** in `CatalanSun/CauchyBinet.lean`: `det_mul_eq_sum_minors`
(plus `m=0`/`m=1`/`square` specializations and `m > n ⇒ det = 0`).

**Det-level Lemma 5.4 landed** (no Pascal–Cauchy required for the positive-part
vanishing: entry 2-integrality ⇒ det 2-integrality ⇒ `R₂ ≥ 0`, and
`v₂(F_B) > 0` for `B ≥ 2`).

**PC0–PC3 complete** in `CatalanSun/PascalCauchy.lean`: residual minor =
Pascal × DiagCauchy, then Cauchy–Binet → `∑ Ξ_I` (paper (4.1) without `q^S`);
Lemma 4.2 odd-Cauchy closed form; Lemma 4.1 with integer `PsiA : ℤ`
via `paperPPoly` / `paperPMatrixZ` / `det_polyEval_dvd_vandermonde`
(column ops + constructive `/ₘ` + induction + Laplace).
**Signed (4.5) packaging landed:** `det_rowsSubmatrix_diagCauchy` (ABS-A) and
`Xi_closed_form` (ABS-B; two copies of `V(I)`, no `q`/`|·|`).
**Thm 5.1 scaffolding landed** in `Thm51.lean` (defs + statement Prop).
**Thm 5.1 combinatorial core landed** in `Thm51.lean` (COMB-A/B/C:
`phiQ_sub_quadratic_nonneg`/`_le`, `sum_choose_nQr_consecutive`,
`collisionSum_eq_phiQ_of_balanced`/`collisionSum_ge_phiQ`).
**PROOF-A/B/C landed** in `Thm51.lean`: `mAQ_le_ellAQ`,
`aQB_sub_ellAQ_consecutive` (5.16), `phiQ_add_CAQ_le_phiQ_N` (5.17),
`phiQ_superadditive`. **Next:** residue engine (5.18)–(5.21) + assemble
`thm_5_1` under `S*20 ≤ B` and `Injective f`; then Lemma 5.3. Still not
Theorem 1.1. See `docs/THM51-REDUCTION-NOTES.md` for a (2026-09-16,
type-check-unverified) reduction of this to one named target lemma,
`sum_NKQ_tail_ge`, plus a ready `linarith` assembly.

## Process notes

- Plan-agent Mathlib pass before implementer; isolated worktree; adversarial
  verifier before merge.
- `lake build` is slow (~2890 jobs, mostly cached Mathlib) — budget several
  minutes, run in background.
- Zero tolerance for `sorry`/`admit`.
