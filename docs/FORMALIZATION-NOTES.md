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

**What this means.** The `5B` cutoff is a real inconsistency *within the paper*
— (5.3)'s summation range truncates at `5B` while §8's `Δ_{>B}` integrates the
full tail — but it is a **bookkeeping mismatch between two sections, not a
missing contribution**, and `δ₀` is not under threat from it. The band is
`≈ 65×δ₀` in raw magnitude, so had it genuinely been dropped the proof would
fail; it is not dropped. For *this repo* the consequence is unchanged and
purely technical: `layerIndex`'s cutoff is wrong for (5.24)'s ledger, so
`Cor52` must index over `layerIndexFull`, and (5.3) needs re-proving there.

Third finding of the same class as the `m0AQ` and `p`-vs-`p^ν` bugs, and again
caught by gating numerically before writing Lean. Scripts and the full tables:
`.scratchpad/cor52/` (`layers.py` brute-force mirror, `fast2.py` accelerated
and cross-validated, `FINDINGS.md`). A free consistency check fell out of the
sweep: **0 violations of `thm_5_1` (`aQB ≥ mAQ`)** across every layer tested.
