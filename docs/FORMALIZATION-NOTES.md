# Formalization notes: divergences from the paper, and traps

Where this Lean development **deliberately differs** from Zhi-Wei Sun,
*Catalan's constant is irrational* (arXiv:2609.04176v1), and the non-obvious
traps hit while proving it. Split out of `README.md`, which now carries only
the status table and pointers.

Read this before touching `CatalanSun/Lemma55.lean` or `Thm51.lean`: several
entries below record statements that are **false as first scaffolded**, and two
of them cost multiple sessions each.

Companion documents:

- [`WORKPLAN-CONTINUATION.md`](WORKPLAN-CONTINUATION.md) — session-by-session
  history and the next-session pointer.
- [`THM51-REDUCTION-NOTES.md`](THM51-REDUCTION-NOTES.md) — Theorem 5.1's
  (now closed) derivation history.
- [`con-leche.md`](con-leche.md) — the external kernel check.

## Contents

- [Paper's `T_i` vs Lean's `T_{i+1}`](#the-t_i-form) — a genuine impossibility
  in the paper's written form.
- [Lemma 5.5: `m0AQ` is a minimum, not a fixed set](#lemma-55-m0aq) — the
  scaffold bug that made (5.2) false.
- [Lemma 5.5: the easy-direction constant](#lemma-55-easy-direction-constant) —
  why the first proved bound was too weak.
- [Lemma 5.5: the hard direction](#lemma-55-hard-direction) — why any free
  index works.
- [Lemma 5.5: a sign trap](#lemma-55-sign-trap) — the `FNQ` shift runs opposite
  ways in the two directions.
- [Lemma 5.5: (5.3)'s layer index](#lemma-55-53-layer-index) — the second
  transcription bug.
- [Lemma 5.5: (5.3)'s proof route](#lemma-55-53-proof-route) — why Chebyshev
  was not needed.
- [Cor 5.2: `layerIndex`'s `5B` cutoff is too small](#cor-52-cutoff) — the
  third transcription-class finding; a `Θ(B²)` truncation.
- [The tail band above `(2+ρ)B`](#tail-band) — §8 integrates only to
  `2+ρ`; the exact `m`-layers carry `(39/200)·B²` beyond it; decisive next
  computation named.
- [**The reduced `B²` claim, measured**](#scalar-verdict) — that computation,
  run. Theorem 9.1 needs `≤ −0.0097`; it measures **`+1.85`**, converging to
  `≈ +1.86`. Dominant term: `v₂(F_B) log 2 → 2 log 2`.

---

<a id="the-t_i-form"></a>
**Note:** paper’s written `f_i = T_i D + P` cannot yield a polynomial `P` under `Π_i = ∏_{h=1}^B`; Lean uses the `T_{i+1}` form. M5/M6 take `A = P − f = T_{i+1} D` so ClearedEq23 matches with positive sign. PC0 uses the matching `T_{i+1}` leading sign `(-1)^{j-1}`.

<a id="lemma-55-m0aq"></a>
**Note (Lemma 5.5, `m0AQ`):** the paper's `m^{(0)}_{Q,B}` is formalized as a
**minimum** over card-`S` subsets at dimension `Ndim0 B S`, mirroring `mAQ`,
not as the value at the fixed consecutive row set alone (an earlier scaffold
used the fixed-set reading; it makes (5.2) demonstrably false — the fixed set
is far from optimal once `Q` is large relative to `S`, so the gap grows like
`S` rather than `1+B/Q`; see `docs/WORKPLAN-CONTINUATION.md` for the
numerics). `docs/catalan-constant-irrational.md`'s reading of the paper
independently supports the minimized version. Separately, the paper's claim
of `O(√B log B)` odd prime powers below `5B` undercounts — it omits the
primes themselves (`~5B/log 5B` of them); the `o(B²)` conclusion of (5.3)
still appears to survive via Chebyshev (`∑ log p ≈ 5B`), but Lean should
derive it that way rather than reproduce the paper's count. **Re-verified
2026-09-17:** re-ran the (5.3) ledger sum with `m0` minimized on both sides
(the prior numerics used the since-refuted fixed-set `m0`) and `SUM/B²`
decays monotonically (0.32 → 0.06 for `B` from 100 to 800), consistent with
`o(B²)`.

<a id="lemma-55-easy-direction-constant"></a>
**Note (Lemma 5.5, easy-direction constant):** the first easy-direction proof
landed (`mAQ_le_m0AQ_add`, `S*(3/Q+1)`) was too weak to establish (5.2) as
stated — for `Q > 3` its constant is `S ≈ B/20`, not `O(1+B/Q)`. The
per-index `FNQ` shift between `Ndim` and `Ndim0` is actually always `0` or
`1` (never the `2` that bound allowed) and nonzero on only 3 residue classes
mod `Q`, giving a genuine `O(1+B/Q)` bound (`mAQ_le_m0AQ_add_sharp`,
`sum_FNQ_shift_le`) — see `docs/WORKPLAN-CONTINUATION.md` for the full
derivation and a list of `ℕ`-division arithmetic pitfalls hit while proving
it (`Nat.div_lt_iff_lt_mul`'s argument order, `omega`'s inability to unify
differently-ordered products, etc.), worth reading before further div-heavy
Lean work in this file.

<a id="lemma-55-hard-direction"></a>
**Note (Lemma 5.5, hard direction):** `m0AQ ≤ mAQ + 105(1+B/Q)` is proved by
swapping the `≤ 3` indices of `mAQ`'s minimizer that lie in `topBlock` — the
indices of `Fin (Ndim B S)` with no counterpart in `Fin (Ndim0 B S)` — for
free indices of the common range. **Any** free index works: no greedy choice,
occupancy pigeonhole, or minimizer characterization is needed, because each
swap's cost is bounded *termwise* (`nQr_le`/`FNQ_le`/`NKQ_le` for the additive
part, `abs_collTerm_swap_le` for the collision part). This was checked
numerically before any Lean was written — the *adversarially worst*
replacement still saturates at `≈ 10(1+B/Q)` across `B ≤ 6000`, and the
end-to-end gap at `≈ 0.5(1+B/Q)` — and it collapsed what earlier scoping had
budgeted as the main combinatorial stage. Note `Thm51.lean`'s
`collisionSum_move` is *not* usable here: its hypothesis `c b + 2 ≤ c a` only
covers balance-improving moves, whereas an arbitrary swap can go either way;
`abs_collTerm_swap_le` proves the two-sided bound by direct `Finset` splitting
instead.

<a id="lemma-55-sign-trap"></a>
**Note (Lemma 5.5, a sign trap):** the `FNQ` shift sum runs *opposite* ways in
(5.2)'s two directions. The easy direction gets it free from
`FNQ_shift_nonneg`; in the hard direction that same lemma yields the bound in
the useless direction, and the genuine counting bound `sum_FNQ_shift_le` is
required. Worth knowing before touching either direction.

<a id="lemma-55-53-layer-index"></a>
**Note (Lemma 5.5, (5.3) layer index — scaffold bug fixed):** the (5.3)
statement previously passed `pv.1` (the *prime* `p`) as the layer argument to
`a0QB`/`m0AQ`/`aQB`/`mAQ`, rather than `pv.1 ^ pv.2` (the prime power
`Q = p^ν`). The paper sums `a_{p^ν,B}`/`m^A_{p^ν,B}`, and
`thm_5_1_statement` quantifies its layer argument as `OddPrimePower Q`, so
`Q = p^ν` is correct; the two readings agree only when `ν = 1`. The `log p`
weight correctly stays `Real.log pv.1`. The as-written version happened to be
`o(B²)` as well, so this was a fidelity fix rather than the repair of a false
statement — but it is the same class of transcription bug as the earlier
`m0AQ` fixed-set error, and worth the same scrutiny on any new statement.

<a id="lemma-55-53-proof-route"></a>
**Note (Lemma 5.5, (5.3) proof route):** (5.3) needs **no prime number
theory**. Summing the proved (5.2) bound over `layerIndex B` needs only that
`(p,ν) ↦ p^ν` is injective with values in `[1,5B)` — giving `≤ 5B` layers and
`∑ 1/Q ≤ harmonic(5B) ≤ 1+log(5B)` — and `log p ≤ log(5B)`. That yields
`Θ(B log²B)`, hence `o(B²)`, with about a factor-10 margin over the true sum.
The crude bound was checked numerically at every inequality before any Lean was
written (`.scratchpad/lemma55/l53crudest.py`, `l53final.py`); `RHS/B²` decays
`~½` per doubling. The one analytic step is `log²x/x → 0`
(`Real.tendsto_pow_log_div_mul_add_atTop`).

<a id="cor-52-cutoff"></a>
**Note (Cor 5.2, the layer cutoff — found 2026-09-17, before any Lean was
written):** `Lemma55.layerIndex B` filters odd prime powers by `p^ν < 5*B`.
That cutoff is **too small for Corollary 5.2's (5.24)**: `[a_{Q,B} −
m^A_{Q,B}]₊` is *not* zero for `Q ≥ 5B`.

The exact support is `Q ≤ 2(N−1) + 2B + 1 = 6B + 2S + 5`, where
`N = Ndim B S = 2B+S+3`. The reason is structural: `aQB` counts solutions of
`Q ∣ 2i+2h+1` over `i < N` and `1 ≤ h ≤ B`, and `2(N−1)+2B+1` is the largest
value that modulus argument can take, so `NKQ` — and with it both `aQB` and
`mAQ` — vanishes identically above it. Verified: every odd prime power in
`[5B, 6B+2S+5]` gives a nonzero layer, and every one above gives `aQB = 0`
*and* `mAQ = 0`.

At `ρ = 1/20` the threshold is `≈ 6.1·B`, so `[5B, 6.1B]` is a
constant-fraction band that always contains nonzero layers. The truncated
mass is **`Θ(B²)`, not `o(B²)`** — measured `drop/B²` = 0.599, 0.663, 0.632,
0.628, 0.627 at `B` = 100, 200, 400, 800, 1200 (`S = B/20`), i.e. stable
rather than decaying, and roughly **65× the proof's `δ₀ ≈ 0.00966` margin**.

Consequence: `Cor52` must **not** index over `layerIndex B`. The clean route
is to sum over all odd prime powers and prove the vanishing above
`6B + 2S + 5`, since that vanishing is structural rather than asymptotic.

This does **not** invalidate `lemma_5_5_ledger_little_o_holds`, which is a true
statement about the sum over `layerIndex B` as defined — but it does mean that
theorem cannot be consumed directly for a ledger indexed over the larger set.
**Provenance, and why this is NOT a fourth paper error (resolved
2026-09-17).** The `5B` is the *paper's* number, not a scaffold invention:
`da77779`'s docstring transcribes it as "restricted (per the proof) to
`p^ν < 5·B`"; an earlier session fetched the arXiv v1 §5.1 HTML directly and
recorded "the separate `p^ν < 5B` restriction used later in (5.3)'s summation
range"; and `robustness-check-catalan.md` independently attributes to the
paper "prime powers below `5B`".

But partitioning the ledger by the paper's own three ranges shows the band is
**already accounted for**. §§6–9 evaluate *Small* (`Q ≤ S`), *Middle*
(`S < p < B`) and *Large* (`p > B`) — and `[5B, 6B+2S+5]` lies wholly inside
*Large*, which is bounded below by `B` and **unbounded above**. Measured split
of the ledger mass:

| B | small `Q≤S` | mid `S<p<B` | large `p>B`, `Q<5B` | large `p>B`, `Q≥5B` |
|---|---|---|---|---|
| 200 | 12.2% | 40.3% | 43.9% | 3.6% |
| 400 | 19.0% | 35.8% | 42.1% | 3.2% |
| 800 | 23.1% | 34.5% | 39.4% | 3.0% |

The band is 7.0% of the large-prime range, not a fourth uncovered range.
Decisively, `Δ_{>B} = (2/3)ρ + (1/2)ρ²` (eq. 8.4) is a **closed form in `ρ`
alone with no cutoff parameter** — an integral over the whole `p > B` tail,
which by construction runs past `5B`. So the paper's §8 does cover it.
**[Withdrawn the same day: this was inferred, not read. §8 integrates
`∫_1^{2+ρ}` with an explicit cutoff; see `#tail-band` below.]**

**What this means.** The `5B` cutoff is a real inconsistency *within the paper*
— (5.3)'s summation range truncates at `5B` while §8's `Δ_{>B}` integrates the
full tail — but it is a **bookkeeping mismatch between two sections, not a
missing contribution**, and `δ₀` is not under threat from it. The band is
`≈ 65×δ₀` in raw magnitude, so had it genuinely been dropped the proof would
fail; it is not dropped. For *this repo* the consequence is unchanged and
purely technical: `layerIndex`'s cutoff is wrong for (5.24)'s ledger, so
`Cor52` must index over `layerIndexFull`, and (5.3) needs re-proving there.

**Closed 2026-09-17.** (5.3) is re-proved over `layerIndexFull B (B/20)` as
`Cor52.ledgerFull_little_o`, by the same crude route with every cap widened
from `5B` to `12B` (`layerBound B (B/20) = 6B + 2(B/20) + 5 ≤ 12B`): at most
`12B` layers, `∑ 1/Q ≤ harmonic(layerBound) ≤ 1 + log 12B`, `log p ≤ log 12B`,
giving `SUM ≤ 111·B·log(12B)·(13 + log 12B)`. The `5B` never entered the
original proof structurally, which is why this was mechanical: the (5.2)
input `layer_int_bound` carries no upper cutoff on `Q`. `Lemma55.lean` is
untouched; `lemma_5_5_ledger_little_o_holds` stands as the paper-literal
statement. Gated first in `scripts/gates/gate_full53.py` (the widened bound is
at most 1.9× the old one and still decays to `0`). With it,
`Cor52.posPartLedger_sub_little_o` closes the model comparison: the two (5.24)
ledgers agree to `o(B²)`. Sign trap confirmed exactly as predicted — (5.3)'s
summand is `|(a0−m0) − (a−m)|`, the termwise Lipschitz bound comes out as
`|(a−m) − (a0−m0)|`, and one `abs_sub_comm` at the `ℤ` level (before the cast,
so `rw` cannot grab the wrong `|·−·|`) bridges them.

<a id="tail-band"></a>
**Note (the tail band above `(2+ρ)B` — found 2026-09-17, reading §8 directly
and running the exact ledger against it). This reopens the paragraph above.**
The "§8 covers it" conclusion was inferred from `Δ_{>B}` being a closed form
in `ρ`. Reading §8 itself: the large-prime density `ℰ_ρ(t)` (8.1) is stated
"for `1 < t < 2+ρ`", its last branch is `−2ρ` on `2+2ρ/3 < t < 2+ρ`, and
(8.2) integrates `∫_1^{2+ρ} ℰ_ρ(t) dt = −(4/3)ρ − (5/4)ρ²`. **The large-prime
range is integrated with an explicit upper cutoff `t = 2+ρ`, i.e. `p <
2.05B`.** Not the full tail, and not `5B` either. So §5.1's `5B`, §8's
`(2+ρ)B`, and (5.24)'s "all odd `p`" are three different ranges.

What the exact layers do there (`scripts/gates/gate_ledger_vs_paper.py`,
data in `scripts/gates/data/`, `B = 200…1200`, `S = B/20`):

| `B` | `∫_ρ^1 m/B` vs `Λ_mid = 0.17636` | `∫_1^{2+ρ} m/B` vs (8.2) `= −0.06979` | `∫_{2+ρ}^{thr} m/B` |
|---|---|---|---|
| 200 | 0.16420 | −0.06640 | −0.19875 |
| 400 | 0.16478 | −0.06765 | −0.20182 |
| 800 | 0.17245 | −0.06936 | −0.19889 |
| 1200 | 0.17427 | −0.06986 | −0.20000 |

(Trapezoid in `t = p/B` over primes, which removes prime-discreteness noise;
the plain `∑ log p`-weighted sums agree to within a few percent.) Two
conclusions and one open question:

1. **Where the paper integrates, the repo's `mAQ` reproduces the paper's
   densities.** `∫_1^{2+ρ} m/B` matches (8.2) to 0.1% at `B = 1200`, and the
   (8.1) branch values (`−2ρ` on `(1+ρ, 4/3)`, `−ρ` on `(4/3+…, 2)`, `−2ρ`
   near `2+ρ`) are visible prime by prime. `∫_ρ^1 m/B` is 1.2% under `Λ_mid`
   and rising with `B`. So `ℰ_ρ` **is** the min-layer density `m^A_{p,B}/B`,
   and the (5.7)/(5.8) transcription is faithful at the level §§7–8 use.
2. **Above `(2+ρ)B` the exact layers are not zero.** For every prime in
   `((2+ρ)B, 4B)`, `m^A_{p,B} = −2S` exactly and `a_{p,B} = 2B` exactly (at
   `B = 1200`: 282 primes, all `(2400, −120)`). The mechanism is the term
   `−2·1_{Q ≤ 2i+1}` of (5.7): for `p < 2N ≈ 4.1B` it fires on the top rows,
   and the minimiser takes `S` of them. So `−∑_{p > (2+ρ)B} m_p log p =
   2ρ(2−ρ)·B² + o(B²) = (39/200)·B²` — **numerically identical to the raw
   quadratic (9.4), `4ρ − 2ρ² = 2ρ(2−ρ)`**. The earlier `[5B, 6.1B]` band
   (`≈ 0.627·B²` of raw `(a−m) log p` mass) is a sub-band of this; its `a`
   part cancels exactly against `log ∏Π_i − log F_B` by (3.5)/(3.7), and its
   `m` part is `0` there (the indicator stops firing at `4B`), so the earlier
   "65× δ₀" figure was the wrong quantity to worry about. The right one is
   the `m`-mass on `((2+ρ)B, 4B)`, which is `0.195·B²`, about **20× δ₀**.
3. **Open: is that `0.195·B²` inside the raw quadratic or missing?** The
   identity `2ρ(2−ρ) = 39/200` is exact and suggests the paper's "raw
   Cauchy–tail contribution" *is* this tail mass under different bookkeeping.
   But the paper's own text assigns `39/200` to Stirling on (4.5) and then
   subtracts a separate baseline `−2ρ − (7/4)ρ²` (8.3) on `(1, 2+ρ)` to get
   `Δ_{>B}`, which is not obviously consistent with `39/200` also being the
   `(2+ρ, 4)` tail. **This cannot be settled from §§5–9 alone.** It needs the
   fixed scalar: by (3.5) and (3.7), everything except `m` and `det R[A,J]`
   cancels exactly, so the paper's whole `B²` claim reduces to
   `log|Ξ_I| − ∑_p m_p log p ≤ −δ₀ B² + o(B²)` with `Ξ_I` the (4.5) closed
   form. `PascalCauchy.Xi_closed_form` states (4.5) in Lean, ℝ-valued. **The
   decisive next computation is to mirror it in Python (log-gamma plus
   `mpmath` for the weighted tails) and evaluate `log|Ξ_I| − ∑ m log p` at
   `B = 200…1200` against `−δ₀B²`.** That is a direct numerical verdict on
   §9 and needs no new Lean.

Corrections this forces elsewhere: the "settled" §4 of the handoff brief
and the "not a fourth paper error" verdict above are withdrawn as stated;
what survives is that the `[5B, 6.1B]` band's *raw* mass is dominated by
the `a` part, which does cancel.

Third finding of the same class as the `m0AQ` and `p`-vs-`p^ν` bugs, and again
caught by gating numerically before writing Lean. Scripts and the full tables:
**`scripts/gates/`** (committed; `layers.py` brute-force mirror, `fast2.py`
accelerated and cross-validated, `check.py` regression runner). A free consistency check fell out of the
sweep: **0 violations of `thm_5_1` (`aQB ≥ mAQ`)** across every layer tested.

---

<a id="scalar-verdict"></a>
**Note (the reduced `B²` claim, measured directly — 2026-09-17, later).**
The computation the tail-band note called decisive has now been run.
**Result: the quantity the paper needs to be `≤ −δ₀ = −0.0097` measures
`+1.85` and is converging upward to roughly `+1.86`.** Gate:
`scripts/gates/gate_scalar.py`.

*What was computed, and why it is the right quantity.* Combining the paper's
own equations, with no appeal to `Ξ_I` or to any choice of `I`:

- (3.5) `q̂_B = ± F_B · det R[A,J] / ∏_i Π_i`
- (5.13) summed over odd `p`: `∑_{odd Q} a_Q log p = log ∏Π_i − log F_B +
  v₂(F_B) log 2` (the `v₂` term appears because `Π_i` is odd, so only the odd
  part of `F_B` is counted on the left)
- (5.24) `log H_B^min ≤ ∑_{odd Q} (a_Q − m_Q) log p`

Adding the first two to the third, everything except three terms cancels:

```
log H_B^min + log|q̂_B|  ≤  log|det R[A,J]| + v₂(F_B) log 2 − ∑_{odd Q} m_Q log p
```

up to the `O(B)` from `q^S`. Call the right side `SCALAR(B)`. Theorem 9.1
asserts exactly `SCALAR(B) ≤ −δ₀B² + o(B²)`. Every term is directly
computable: `m_Q` from the committed `fast2` mirror over **all** odd prime
powers (not only the `a > m` rows the ledger CSV keeps), `v₂(F_B)` by
Legendre, and `det R[A,J]` from (2.1).

| `B` | `log\|det R\|/B²` | `v₂(F_B)log2/B²` | `−∑m log p/B²` | **`SCALAR/B²`** |
|---|---|---|---|---|
| 200 | +0.475164 | +1.353994 | −0.003012 | **+1.826146** |
| 400 | +0.544358 | +1.368411 | −0.066843 | **+1.845926** |
| 800 | +0.613610 | +1.376486 | −0.138860 | **+1.851237** |

The paper needs `≤ −0.009662`. The increments fall by ~4× per doubling and an
`a·log B` fit collapses (`a = 0.0285 → 0.0077` across the three pairs), so
this converges to a finite positive constant near `+1.86`; it is not
logarithmic drift that `o(B²)` could absorb.

*Where it comes from.* The dominant term is `v₂(F_B) log 2 → 2 log 2 =
1.3863`. `F_B = ∏_{r<2B} r!` sits in the **numerator** of (3.5), and
`v₂(F_B) ~ 2B²`. That 2-adic mass is real-place mass in `log|q̂_B|` that the
odd-prime ledger (5.24) never removes, because (5.24) sums over odd `p` only.
The paper does address this, and the numbers do not work. **Remark 9.3**
states that "the residual real power of 2 from `F_D`, the Cauchy factor
`2^{S(S-1)}`, and the missing 2-power in the odd von Mangoldt sum are
included in the derivation of the odd-prime small-scale expression (6.21)",
concluding that the applicable cost is therefore `c_odd`. But
`c_odd = 0.00628`, and the residual real power of 2 alone is
`v₂(F_B) log 2 / B² → 2 log 2 = 1.386` — **221× larger**. Remark 6.2's
alternative `(19/200) log 2 = 0.0658` is still 21× too small. Lemma 5.4 is
about `H_B^min`'s 2-part (`[A_{2,B} − R_{2,B}]₊ = 0`) and does not bear on
the real place. So the term is named but absorbed into a constant two orders
of magnitude too small to hold it. The
remaining `+0.47…+0.61` is `log|det R|/B²`, which is still rising.

*How far this was checked.* Three independent routes agree:

1. The algebraic route above.
2. A direct route computing `log|q̂_B|` from (3.5) and the (5.24) bound
   separately, never using the combined identity: `+1.826146` and
   `+1.845926` at `B = 200, 400` — identical to the table.
3. The summed (5.13) identity verified numerically at each `B` (relative
   difference `≤ 1.6e-16`).

`det R` itself was validated against a brute-force `polygamma` computation of
(2.1) at `B = 20, 40, 60` (agreement `~1e-13`), the tail `T_m` against two
independent formulas and against the paper's identity (1.4), and the
fixed-point evaluation against an exact-integer one at `B = 200, 400` (every
printed digit). `log|det R|` is insensitive to the row set `A`: four choices
at `B = 200` agree to `1e-4` in the `B²` coefficient. Both precisions in
every run agree, with the alternating sum's cancellation (`~6000` bits at
`B = 800`) far below the working precision.

*What this does and does not establish.* It does **not** exhibit an error in
a specific line of the paper; §9's proof sketch is compressed, and the
grouping of factors there is not reproduced here term by term. What it
establishes is that **the inequality Theorem 9.1 states, in the form its own
§§3 and 5 reduce it to, fails numerically by about `1.87` in the `B²`
coefficient, with the prime 2's contribution to `F_B` the largest identified
component — a term Remark 9.3 names and assigns to `c_odd`, which is 221×
too small to carry it.** Anyone continuing should either show that the
grouping in §9 cancels `2 log 2 · B²` some other way, or treat Theorem 9.1
as unsupported at this level of bookkeeping.

**This supersedes the tail-band note's open question.** The `(39/200)B²`
coincidence noted there is not the binding issue; `SCALAR` is computed
without reference to that band at all.
