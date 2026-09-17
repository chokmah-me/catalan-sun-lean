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
