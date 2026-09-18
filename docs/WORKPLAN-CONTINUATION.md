# Workplan: §§2–5 formalized; the paper's §9 claim measured and failing

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
**Divergences from the paper and known traps:**
[`FORMALIZATION-NOTES.md`](FORMALIZATION-NOTES.md) (split out of the README).
**How the §9 verdict was interrogated:**
[`REVIEW-DIALOGUE-2026-09-17.md`](REVIEW-DIALOGUE-2026-09-17.md).
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

> **Status, 2026-09-17.** The §§2–5 formalization target is met: Thm 2.1,
> Prop 3.1, Cauchy–Binet, Thm 5.1, Lemma 5.5, and Cor 5.2's §5 content are
> proved, `lake build` clean, 0 `sorry`, axioms ⊆ the classical three.
> **Separately, the paper's own Theorem 9.1 has been measured numerically and
> fails**: the quantity it needs `≤ −0.0097` measures `≈ +1.85`, dominated by
> a `2 log 2 · B²` real-place term that Remark 9.3 assigns to a constant 221×
> too small. See [`FORMALIZATION-NOTES.md#scalar-verdict`](FORMALIZATION-NOTES.md#scalar-verdict).
> **Consequence for planning:** further formalization of §§6–9 toward Theorem
> 1.1 is not worth starting. The §4→§5 valuation lemma below remains the only
> mathematically interesting open item, and it is now optional rather than
> on a path to Theorem 1.1.

## Next session pointer

**→ Start with [`HANDOFF-NEXT-SESSION.md`](HANDOFF-NEXT-SESSION.md)**, which
condenses everything below into an actionable brief for a cold start.

**2026-09-17 (newest of all): THE PAPER'S §9 CLAIM MEASURED — AND IT FAILS.**

The tail-band note named mirroring the (4.5) closed form as the decisive next
computation. It turned out `Ξ_I` was not needed: the paper's own (3.5),
(5.13)-summed-over-odd-`p`, and (5.24) collapse Theorem 9.1's left side to

```
log H_B^min + log|q̂_B|  ≤  log|det R[A,J]| + v₂(F_B) log 2 − ∑_{odd Q} m_Q log p
```

with every term directly computable. Theorem 9.1 asserts this is
`≤ −δ₀B² + o(B²)`, `δ₀ > 0.0097`. Measured (`scripts/gates/gate_scalar.py`):

| `B` | 200 | 400 | 800 | 1000 | 1200 |
|---|---|---|---|---|---|
| `SCALAR/B²` | +1.826146 | +1.845926 | +1.851237 | +1.854020 | **+1.854615** |

Converging upward to `≈ +1.86`. The dominant term is
`v₂(F_B) log 2 → 2 log 2 = 1.386`: `F_B` is in the numerator of (3.5) with
`v₂(F_B) ~ 2B²`, and (5.24) sums over odd `p` only. **Remark 9.3 names this
exact term** and folds it into `c_odd = 0.00628` — 221× too small.

**The failure has two independent components, not one**
([`#two-components`](FORMALIZATION-NOTES.md#two-components)): subtracting
`2 log 2` leaves `+0.479`, still ~50× `δ₀` and the wrong sign, sitting in
Prop 9.5's incomplete cancellation (`log|det R|/B² − ∑m log p/B²` is flat at
`+0.475` across `B = 200…1000`). A repair must close both.

A structural check that raises confidence: `log|det R|/B²` rises by `+0.069`
per doubling while `−∑m log p/B²` falls by `−0.068`. They cancel to ~5%,
which is exactly the `B² log B` cancellation Prop 9.5 asserts. **The paper's
own mechanism is working in the data; what survives it is `+1.86`.**

Validated three independent ways plus `det R` against brute force. Full note
and all caveats: `FORMALIZATION-NOTES.md#scalar-verdict`. **No `.lean` file
changed; the formalization claims no part of §9 and is unaffected.**

---

**2026-09-17 (earlier): STAGE D CLOSED — (5.3) re-proved over
`layerIndexFull`, and the two (5.24) ledgers agree to `o(B²)`. `lake build`
clean (2957 jobs), 0 sorry, 150 audited declarations, axioms ⊆ classical
three.**

Both tasks the handoff brief set out are done, in `Cor52.lean`, with
`Lemma55.lean` untouched:

- **Stage F** — `layerFull_pow_injOn`, `card_layerIndexFull_le`,
  `layerBound_le_twelve` (`6B + 2(B/20) + 5 ≤ 12B`), `sum_inv_layerFull_le`,
  `layerFull_term_le`, `eventually_log_sq_le_twelve`, `ledgerFull_sum_le`,
  and **`ledgerFull_little_o`** — (5.3) verbatim with `layerIndex B` replaced
  by `layerIndexFull B (B/20)`. Mechanical, as predicted: `5B` was only ever a
  numeric cap, and `layer_int_bound` has no upper cutoff on `Q`. Bound:
  `111·B·log(12B)·(13 + log 12B)`. Gated first: `scripts/gates/gate_full53.py`
  (≤ 1.9× the old bound, decays to 0).
- **Stage D closed** — `abs_posPartLedger_sub_le`
  (`Finset.abs_sum_le_sum_abs` + `abs_layer_diff_le`, sign flipped by one
  `abs_sub_comm` *at the `ℤ` level before casting*, so `rw` cannot pick the
  wrong `|·−·|`) and **`posPartLedger_sub_little_o`**:
  `|posPartLedger − posPartLedger0| ≤ ε B²` eventually, for every `f`.
- Everything built first try; the only fixes were three style-linter
  warnings. Ten new `#print axioms` lines in `CatalanSun.lean` (140 → 150).

**Later the same day — the tail band, and a withdrawn conclusion.** Read
§8 directly: `ℰ_ρ` is stated for `1 < t < 2+ρ` and (8.2) integrates
`∫_1^{2+ρ}`; the earlier "§8 covers the `[5B, 6.1B]` band" verdict was
inferred from the closed form and is withdrawn. Ran the exact ledger at
`S = B/20`, `B = 200…1200` (`scripts/gates/gate_ledger_vs_paper.py`, data
committed): where the paper integrates, `mAQ/B` reproduces `Λ_mid` (1.2%)
and (8.2) (0.1%); above `(2+ρ)B` every prime up to `4B` has `m = −2S`
exactly, a mass of `2ρ(2−ρ)B² = (39/200)B²`, identical to the raw quadratic
(9.4) and 20× `δ₀`. Whether that is bookkeeping or an omission reduces, via
(3.5)/(3.7), to `log|Ξ_I| − ∑ m log p ≤ −δ₀B²` with `Ξ_I` = (4.5) =
`PascalCauchy.Xi_closed_form`. Full note: `FORMALIZATION-NOTES.md#tail-band`.
**The (4.5) mirror is now the top priority**, ahead of the valuation lemma.
Also: `lean-proof-forge` is installed after all; its verifier passes every
check and reports the axiom audit UNKNOWN only for private/primed helpers.

**Next after that (unchanged from the brief, §5):** the §4→§5 odd-`p` valuation lemma
`v_p(Ξ_I) ≥ ℓ^A_Q(I) − …` is the real missing piece before anything about
`H_B^min` can be stated. Scope it before committing; if staged, state it as an
explicit `LayerValuationInput` hypothesis and prove Cor 5.2's deductive step
against it. Do not name anything `logHmin` until it lands.

---

**2026-09-17 (superseded above): COROLLARY 5.2 PARTLY LANDED — and the numeric
gate found a third transcription-class bug, this time in the layer cutoff.
`lake build` clean (2957 jobs), 0 sorry, axioms ⊆ classical three.**

**The finding, and it is load-bearing.** `Lemma55.layerIndex B` filters odd
prime powers by `p^ν < 5*B`. That is **too small for Cor 5.2's (5.24)**:
`[a_{Q,B} − m^A_{Q,B}]₊` is *nonzero* for `Q ≥ 5B`. The exact support is
`Q ≤ 2(N−1)+2B+1 = 6B+2S+5` (`N = Ndim B S`), because `aQB` counts solutions
of `Q ∣ 2i+2h+1` over `i < N`, `1 ≤ h ≤ B`, and that is the largest value the
modulus argument attains — above it `NKQ`, `aQB` and `mAQ` all vanish. Every
odd prime power in `[5B, 6B+2S+5]` gives a nonzero layer; every one above
gives exactly zero.

The truncated band is **`Θ(B²)`, not `o(B²)`**: measured `drop/B²` = 0.599,
0.663, 0.632, 0.628, **0.627** at `B` = 100, 200, 400, 800, 1200 with
`S = B/20` — stable, not decaying, and about **65× the paper's `δ₀ ≈ 0.00966`
margin**. So this is not a cosmetic index quibble.

**Provenance resolved: the `5B` is the PAPER's, and the band IS covered by
§8.** `da77779`'s docstring transcribes it "(per the proof)"; an earlier
session fetched the arXiv §5.1 HTML and found "the separate `p^ν < 5B`
restriction used later in (5.3)'s summation range"; the robustness check
independently attributes it to the paper. **But** partitioning the ledger by
the paper's own three ranges (Small `Q≤S` / Middle `S<p<B` / Large `p>B`)
puts `[5B, 6B+2S+5]` wholly inside *Large*, which is unbounded above — and
`Δ_{>B} = (2/3)ρ + (1/2)ρ²` (eq. 8.4) is a closed form in `ρ` with no cutoff,
i.e. the integral over the entire `p>B` tail. Measured, the band is 7.0% of
the large-prime range and ~3% of the ledger. So this is a **bookkeeping
inconsistency between §5.1 and §8 within the paper, not a missing
contribution**, and `δ₀ ≈ 0.00966` is **not** threatened — though the band is
`≈65×δ₀` raw, so it would have been fatal had it actually been dropped.

**Consequence: Lemma 5.5's (5.3) cannot be consumed as-is by Cor 5.2.**
`lemma_5_5_ledger_little_o_holds` remains true — it is a correct statement
about its own index set — but it is indexed over `layerIndex B`, whereas
(5.24) needs `layerIndexFull B S`. `Cor52.layerIndex_subset_layerIndexFull`
records the containment; the gap is the `[5B, 6B+2S+5]` band.

**What landed** (`CatalanSun/Cor52.lean`, all unconditional):
- Stage A: `posPart_eq_self_of_nonneg` (the paper's phantom "Lemma 5.3"),
  `posPart_nonneg`, `abs_posPart_sub_le` (1-Lipschitz, via Mathlib's
  `abs_max_sub_max_le_max` at `b = d = 0`).
- Stage B: `layerBound`/`layerBound_eq`/`five_mul_lt_layerBound`,
  `layerIndexFull`/`layerFull_mem_iff`/`layerFull_oddPrimePower`,
  `layerLogTerm`, `posPartLedger`, and their nonnegativity.
- Stage C (the heart): `posPart_layer_eq` — Thm 5.1 ⇒ `[a−m]₊ = a−m` — and
  `posPartLedger_eq_raw`. Genuinely easy, as predicted; the four hypothesis
  discharges are copied from `lemma_5_5_ledger_little_o_holds`.
- Stage D (honest partial): `posPartLedger0`, `layerIndex_subset_layerIndexFull`,
  `abs_layer_diff_le` (the termwise comparison, which *is* index-set
  independent). The summed `o(B²)` comparison is **not** claimed.
- Stage E: `two_not_mem_layerIndexFull`, recording the `p = 2` omission that
  `lemma_5_4_det` justifies.

**Not claimed, and stated so in the file header, README, and brief:** anything
about `H_B^min`, integerizers, or `q̂_B`. That bridge needs the §4→§5 odd-`p`
valuation lemma `v_p(Ξ_I) ≥ ℓ^A_Q(I) − …`, which does not exist — there is no
`padicVal` anywhere in `Thm51.lean` or `Lemma55.lean`, and the only
valuation↔determinant bridge in the repo (`lemma_5_4_det`) is `p = 2` only.
Nothing is named `logHmin`.

**Start here next, in priority order:**
1. **Re-prove (5.3) over `layerIndexFull`.** The existing proof's shape should
   survive: `card_layerIndex_le` becomes `≤ 6B+2S+5`-many layers,
   `sum_inv_layer_le` becomes `harmonic(6B+2S+5)`, and the `log²x/x → 0` step
   is unchanged. This is the single highest-value next step — it makes Stage D
   closeable and repairs the one real gap this session opened.
2. Then close Stage D (`posPartLedger` vs `posPartLedger0` to `o(B²)`) via
   `Finset.abs_sum_le_sum_abs` + `abs_layer_diff_le` + the re-proved (5.3).
   Watch the sign order: (5.3)'s summand is `|((a0−m0) − (a−m))|`, needing one
   `abs_sub_comm`.
3. Only then consider the conditional bridge (`LayerValuationInput` +
   `cor_5_2_conditional`), or leave it as a `def … : Prop`.
4. Props 6.3/7.4 remain certified-numerics work, not Lean work.

**Numeric gate scripts kept** (`.scratchpad/cor52/`, gitignored):
`layers.py` (verbatim brute-force mirror of the Lean defs), `fast2.py`
(O(1) `NKQ` via modular inverse + an exact DP minimizer over residue classes,
cross-validated against `layers.py` on 189 layers, 0 mismatches),
`gate_support.py`, `gate_threshold.py`, `gate_mass.py`, `FINDINGS.md`.
A free consistency check fell out: **0 violations of `thm_5_1` (`aQB ≥ mAQ`)**
across every layer tested — the Python mirror agrees with proved Lean.

---

**2026-09-17 (newest of all): LEMMA 5.5 IS COMPLETE. (5.3)
(`lemma_5_5_ledger_little_o_holds`) is proved, unconditional, `lake build`
clean, 0 sorry, axioms ⊆ classical three. Next target: Props 6.3/7.4.**

**The headline: Chebyshev was not needed.** Every prior entry in this file
assumed (5.3) required `∑_{p<5B} log p ≈ 5B` and flagged the ε-B₀ limit as "a
different flavor from everything landed so far." Running the numeric gate first
(this file's own standing rule) showed the **crudest possible bound — no prime
number theory at all — is already `o(B²)` with ~10× margin**:

* `(p,ν) ↦ p^ν` is injective on `layerIndex B` (unique factorization) with
  values in `[1,5B)`. So `≤ 5B` layers, and `∑_{layers} 1/Q ≤ harmonic(5B)`.
* `log p ≤ log Q ≤ log(5B)`.

giving `SUM ≤ 111·B·log(5B)·(6+log 5B) = Θ(B log²B)`. The whole thing reduces
to `log²x/x → 0` (`Real.tendsto_pow_log_div_mul_add_atTop`). Measured
`RHS/B²`: 84.3 → 2.02 → 0.279 → 0.0047 for `B` = 10², 10⁴, 10⁵, 10⁷ — decaying
`~½` per doubling. Scripts kept: `.scratchpad/lemma55/l53crudest.py`,
`l53final.py`, `l53inj.py`, `l53shape.py`, `l53crude.py`.

**A statement bug found and fixed — same class as the `m0AQ` one.** (5.3)'s
`def` passed `pv.1` (the *prime* `p`) as the layer argument to
`a0QB`/`m0AQ`/`aQB`/`mAQ`, not `pv.1 ^ pv.2`. The paper sums over `Q = p^ν`,
and `thm_5_1_statement` quantifies its layer argument as `OddPrimePower Q`, so
`p^ν` is correct — the two agree only at `ν = 1`. The `log p` weight correctly
stays `log pv.1`. The as-written form was also `o(B²)`, so this was a fidelity
fix, not the repair of a false claim. **Lesson repeated from the `m0AQ`
episode: check each scaffolded statement against the paper before proving it,
not after.**

**`Mathlib.NumberTheory.Chebyshev` EXISTS at this pin** (Lean 4.32.2) and is
rich — `theta_le_log4_mul_x` (θ(x) ≤ x log 4), `pi_le_log4_mul_div` (explicit
π(x) upper bound), `psi_le_const_mul_self`, `pi_ge`, `theta_ge`,
`Chebyshev.sum_PrimePow_eq_sum_sum`, plus `primorial_le_four_pow` and the
`vonMangoldt` API. Not needed for (5.3), but this is exactly the machinery
Props 6.3/7.4 and Mertens/PNT will want — **do not re-derive it from scratch.**

**What landed** (`Lemma55.lean`, Stage G–I, all unconditional):
- Stage G (pure ℕ): `layer_mem_iff`, `layer_oddPrimePower`, `layer_pow_injOn`,
  `card_layerIndex_le` (`≤ 5B` — replaces the paper's undercounted
  `O(√B log B)` layer count, which this proof never needs).
- Stage H (ℝ): `layer_int_bound` (the two (5.2) halves combined, `≤ 111(B/Q+1)`),
  `layer_term_le`, `sum_inv_layer_le` (the harmonic step), `ledger_sum_le`.
- Stage I: `eventually_log_sq_le`, `lemma_5_5_ledger_little_o_holds`.

**Lean pitfalls hit (all casts again, none combinatorial):**
- The documented `push_cast`-vs-ℕ-division trap bit again, exactly as recorded
  below: `push_cast` turned `((B/Q : ℕ) : ℝ)` into `↑B/↑Q` and broke the match.
  The fix that worked is the one already in `lemma_5_5_row_stability_holds`:
  `rw [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast]` then
  `norm_num`, converting to real division exactly once via `Nat.cast_div_le`.
- `abs_add` is now **`abs_add_le`**; `Nat.pos_pow_of_pos` is now
  **`Nat.pow_pos`**; `Int.cast_le`'s type argument is `R`, not `α`.
- `Nat.pow_right_injective` leaves a beta-redex goal — close with an explicit
  `show x.1 ^ x.2 = x.1 ^ y.2` before `rw`.
- Writing `(1:ℝ)/(n:ℝ)` inside a `Finset.image` sum elaborates `n` as a ℕ-power
  and fails instance synthesis; annotate `((n : ℕ) : ℝ)`.
- Editing these UTF-8 files from Python on Windows needs explicit
  `encoding='utf-8'` — the cp1252 default raises `UnicodeDecodeError` mid-edit.

**Not attempted:** Props 6.3/7.4, Mertens/PNT, Theorem 1.1, Corollary 5.2
(whose "Lemma 5.3" is the cited-but-undisplayed trivial `[x]_+ = x` fact).

---

**2026-09-17 (newest of all): (5.2) IS FULLY PROVED — both directions,
unconditional, absolute constant `C = 210`. `lemma_5_5_row_stability_holds`
is in `Lemma55.lean`; `lake build` clean, 0 sorry, axioms ⊆ classical three.
Lemma 5.5's only remaining open piece is (5.3).**

**The numeric gate, run first (and it passed).** Per this file's own standing
recommendation — two prior sessions were lost to skipping it — no Lean was
written until the claim was checked. Two independent measurements:

| check | measured | shape |
|---|---|---|
| end-to-end `(m0AQ−mAQ)/(1+B/Q)`, both sides minimized, `B ≤ 800`, `Q ≤ 2187` | worst **0.523** | saturates |
| adversarially-worst 3-swap repair cost / `(1+B/Q)`, `B ≤ 6000`, `Q ≤ 2B` | worst **10.16** | saturates |
| `nQr Q r I ≤ (N−1)/Q + 1` | 0 violations, tight at `r=0` | — |

Saturating, not growing — the opposite of the shape that (correctly) refuted
the earlier fixed-set formulations. Scripts kept this time:
`.scratchpad/lemma55/l55gate_hard.py`, `l55gate_swap.py` (gitignored, local).

**The insight that collapsed the work.** Every prior sketch in this file
assumed the replacement index had to be chosen well (greedy / min-occupancy),
implying minimizer extraction, an occupancy pigeonhole, and an exchange
argument. It does not: **any** free index works, because every per-swap cost
is bounded *termwise*. The adversarial gate above is what establishes this.
The entire feared "genuinely new combinatorics" stage reduced to one direct
`Finset`-splitting lemma plus a ≤3-step induction. Landed in 16 declarations
across six stages, all first- or second-try.

**What landed** (`Lemma55.lean`, all unconditional):
- Stage A: `nQr_le` (was missing; via the already-public
  `card_range_filter_mod_eq`), `FNQ_le`, `indicatorQle_le_one`.
- Stage B: `gTerm`, `three_mul_div_le` (extraction of code previously inlined
  in `sum_FNQ_shift_le`), `abs_gTerm_le` (`≤ 7*(B/Q)+9`).
- Stage C: `collTerm`, `nQr_insert`, `collTerm_insert`, `collTerm_erase`,
  `abs_collTerm_swap_le` — the only genuinely new combinatorics, and routine.
- Stage D: `card_insert_erase_eq`, `ellAQN_eq_collTerm_add`,
  `abs_ellAQN_swap_le` (`≤ 30*(B/Q)+30` per swap).
- Stage E: `mAQ_eq_ellAQ_min` (the mechanical mirror this file flagged as
  missing), `topBlock`/`card_topBlock`, `exists_free_common`,
  `card_inter_topBlock_swap`, `swap_descent_aux`,
  `exists_preimage_of_disjoint_topBlock`.
- Stage F: `m0AQ_le_mAQ_add`, `abs_mAQ_sub_m0AQ_le`,
  `lemma_5_5_row_stability_holds`.

**Corrections #1 and #2 in the 2026-09-17 entry below were both right and
both load-bearing.** `collisionSum_move` really is unusable for an arbitrary
swap (its `c b + 2 ≤ c a` hypothesis only covers balance-improving moves), and
`mAQ_eq_ellAQ_min` really did need adding. Correction #3's "termwise
`O(1+B/Q)`" observation is exactly what made the whole thing cheap.

**One sign trap worth recording.** In the hard direction the `FNQ` shift sum
runs the *opposite* way from the easy direction. In the easy direction
`FNQ_shift_nonneg` makes it automatically `≤ 0`; here that same lemma gives
the bound in the **wrong** direction (it yields `ellAQN(Ndim0,J) ≥
ellAQN(Ndim,J.map e)`, which is useless), and the genuine counting bound
`sum_FNQ_shift_le` is required. This is precisely why the 2026-09-17 entry
kept `sum_FNQ_shift_le` as a standalone lemma — that call was correct.

**Lean pitfalls hit (all casts, none combinatorial).** `push_cast` rewrites
`((B / Q : ℕ) : ℤ)` — ℕ-division — into `↑B / ↑Q`, silently destroying the
match against every lemma stated with the ℕ-division cast. It does this even
inside a `have` whose statement is written the other way. Cost several
`linarith` failures whose context *looked* correct. Fix: never `push_cast` a
goal containing a ℕ-division cast; use `Int.cast_mul`/`Int.cast_natCast`
explicitly, or `set` the atom first. Also: `omega` treats `(0-1)/Q` as opaque,
so pin `(0 - 1) / Q = 0` with a `have` in the `N = 0` edge case. Also:
`Finset.card_insert_of_not_mem` is now `card_insert_of_notMem`; `attachFin`
takes a `Finset ℕ`, not a `Finset (Fin n)` — use `I.attach.image` instead.

**Next target: (5.3)** — **DONE 2026-09-17; route below is SUPERSEDED.** The
Chebyshev summation prescribed here was never needed: layer injectivity gives
`≤ 5B` layers and `∑ 1/Q ≤ harmonic(5B)`, which already yields `Θ(B log²B)`.
See the top-of-file entry. Kept only as history. Now unblocked — it can
consume the proved `lemma_5_5_row_stability_holds` plus the already-proved
`abs_a0QB_sub_aQB_le` directly. Route: sum the per-layer `O(1+B/Q)` bound over
`layerIndex B` via Chebyshev (`∑_{p<5B} log p ≈ 5B`, giving `Θ(B log² B)`),
**not** via the paper's `O(√B log B)` layer count, which undercounts (it omits
the primes themselves). Numerics already favorable: `SUM/B²` decays
monotonically 0.32 → 0.06 for `B` from 100 to 800 (`.scratchpad/lemma55/l53min.py`).
Note the ε-B₀ form of the statement will need a real-analysis limit argument,
a different flavor from everything landed so far.

---

**2026-09-17 (newest of all): sharpened (5.2)'s easy direction from an
`O(S)` constant to a genuine `O(1+B/Q)` constant — the previously-committed
`mAQ_le_m0AQ_add` could never establish `lemma_5_5_row_stability` as stated.
Also re-ran the (5.3) ledger sum against the corrected minimized `m0AQ`:
`SUM/B²` now decays monotonically, resolving the open worry from the prior
entry.**

**The bug found this session:** `mAQ_le_m0AQ_add` (landed 2026-09-16) proves
`mAQ ≤ m0AQ + S*(3/Q+1)`. Since `3/Q = 0` in ℕ-division for `Q > 3`, this
constant is `S ≈ B/20` — but `lemma_5_5_row_stability` demands `≤ C*(1+B/Q)`,
which at `Q ≈ B` is `≈ 2C`. The proved bound is too weak by a factor `~S` and
no hard-direction work fixes it; this was missed because prior numerics
probed the *value* `|mAQ-m0AQ|` (ratio 0.34, fine) rather than the *proved
constant*.

**The fix:** the per-index `FNQ` difference `FNQ(Ndim,Q,i) - FNQ(Ndim0,Q,i)`
is **always 0 or 1** for `Q > 3` (never the `3/Q+1 = 2` the old bound
allowed), and is nonzero only when `(Ndim0-1-i) % Q` lands in the top three
residues `{Q-1,Q-2,Q-3}` — at most 3 residue classes. So the sum over any
card-`S` set is `≤ min(S, 3*(Ndim0/Q)+3) ≤ 15*(1+B/Q)`, genuinely `O(1+B/Q)`.
Verified independently in Python (fresh script re-deriving `Ndim`/`Ndim0`/
`FNQ` from the Lean defs): max per-index difference `= 1` across
`B ∈ [200,10^5]`; worst adversarial `sum/(1+B/Q) = 6.14`, saturating rather
than growing.

**Landed in Lean** (`Lemma55.lean`, unconditional, `lake build` clean, 0
sorry, axioms ⊆ classical three):
- `FNQ_shift_nonneg`: `FNQ(Ndim0) ≤ FNQ(Ndim)` pointwise, for any `Q > 0`.
- `FNQ_shift_le_one`: the difference is `≤ 1`, but **only for `Q > 3`** —
  false at `Q ∈ {1,2,3}` (e.g. `Q=1` gives `FNQ(N,1,i)=N-1`, so the
  difference is exactly `3`). This split into `FNQ_shift_nonneg` (always
  true) vs `FNQ_shift_le_one` (needs `Q>3`) is itself worth remembering —
  the natural single combined lemma is simply false as stated.
- `card_filter_FNQ_shift_ne`: the counting lemma — at most `3*(Ndim0/Q)+3`
  indices have a nonzero difference, via injecting into 3 residue classes
  and reusing `card_range_filter_mod_eq` (de-privatized in `Thm51.lean`,
  the only other file touched this session — a one-word change, no logic
  change, safe since the lemma was only used within `Thm51.lean` itself).
- `sum_FNQ_shift_le`: assembles the above into `∑(FNQ(Ndim)-FNQ(Ndim0)) ≤
  15*(1+B/Q)` over any card-`S` subset, splitting `Q>3` (sharp count) from
  `Q≤3` (crude `≤4S ≤4*(B/Q)` route, using `S*20≤B` — the only place that
  hypothesis is needed in this session's work).
- `mAQ_le_m0AQ_add_sharp`: `mAQ ≤ m0AQ + 9*(1+B/Q)` — the corrected easy
  direction. Doesn't even need `sum_FNQ_shift_le`'s counting argument: since
  `FNQ_shift_nonneg` makes the whole `FNQ`-difference sum (over `m0AQ`'s
  *arbitrary* minimizing set `I₀`, not just the consecutive block) already
  `≤ 0`, the bound `≤ 9*(1+B/Q)` holds trivially. `sum_FNQ_shift_le` is kept
  as a standalone lemma since it's the piece the *hard* direction will need
  (there, the sum runs the other way and isn't automatically `≤ 0`).

**Debugging notes for next time (Lean arithmetic pitfalls hit this
session):** all in `ℕ`-division lemmas, none in the underlying combinatorics:
- `rw [Nat.div_eq_of_lt h]` on a goal that is an *inequality* (e.g.
  `3/Q ≤ 1`) doesn't close it — `rw` rewrites `3/Q` to `0` leaving `0 ≤ 1`
  unclosed; follow with `omega`, or better, state `Nat.div_eq_of_lt` as an
  equation (`3/Q = 0`) via `have` and let `omega` use it directly.
  `Nat.mul_add_div` is **not** a real Mathlib/core lemma name (used it twice
  under the wrong assumption it existed, both times it silently failed to
  even parse/resolve until the actual error surfaced downstream) — the
  robust pattern that always worked: `have hdm := (Nat.div_add_mod x
  Q).symm`, `nlinarith` to get a strict `<` bound in `a < b*Q` shape
  (`Q` on the **right**), then `(Nat.div_lt_iff_lt_mul hQ).mpr`.
- `Nat.div_lt_iff_lt_mul hQ : a/Q < n ↔ a < n*Q` — `Q` must be the **second**
  factor on the RHS; `Q*n` silently fails to unify via `.mpr` with a type
  mismatch error, not a tactic failure, so it's easy to miss which side
  needs fixing.
- `omega` cannot relate `Q*(y/Q)` and `(y/Q)*Q` (or any two syntactically
  different-order products of the same two terms) even though they're
  trivially equal by `mul_comm` — it treats each as an opaque atom. Keep a
  single multiplication order throughout a proof; don't introduce a second
  `have` restating the same fact with factors swapped.
- A leftover doc-comment (`/-- ... -/`) directly above a *replacement*
  doc-comment, left behind by a partial `Edit` that only swapped the body
  and not the header, produces a confusing "unexpected token `/--`" parse
  error pointing at the *next* declaration, not the actual duplicate —
  worth double-checking doc-comment boundaries after any edit that touches
  them.

**Numerics — the (5.3) ledger sum, m0 minimized on both sides** (workplan's
stated "recommended first step" from the prior entry, finally done): fixed
the broken `exec` path in `.scratchpad/lemma55/l55g.py`/`l55h.py`/`l55j.py`
(pointed at a deleted `C:\Users\danie\.claude\jobs\...\tmp\` session
directory; now `.scratchpad/lemma55/l55b.py`), and wrote a fresh script
(`.scratchpad/lemma55/l53min.py`) re-running the full (5.3) sum:

| B | S | layers | nonzero | maxterm | SUM | SUM/B² |
|---|---|---|---|---|---|---|
| 100 | 5 | 106 | 66 | 205 | 3193.1 | 0.3193 |
| 200 | 10 | 184 | 119 | 410 | 7281.4 | 0.1820 |
| 400 | 20 | 323 | 202 | 820 | 16157.9 | 0.1010 |
| 600 | 30 | 455 | 283 | 1230 | 25775.1 | 0.0716 |
| 800 | 40 | 578 | 363 | 1640 | 35632.6 | 0.0557 |

`SUM/B²` **decays monotonically** — under the old fixed-set `m0AQ`, the
`|m0-mA|` half of this sum sat flat at `≈B²/2` instead. Minimizing `m0AQ`
rescues (5.3), not just (5.2). Shape is consistent with `Θ(B log²B)`, i.e.
the Chebyshev route flagged in the prior entry, though this has not been
checked more precisely (e.g. against `B*log(B)^2` directly) nor started in
Lean.

**Corrections to the prior entry's proof-route sketch** (found while
scoping the hard direction, not yet acted on in Lean):
1. `collisionSum_move` (`Thm51.lean:578`) is the **wrong tool** for bounding
   a single row-swap's effect on the collision-sum term: its hypothesis
   `c b + 2 ≤ c a` only covers balance-*improving* moves, but the hard
   direction needs an unconditional two-sided bound (a swap could go either
   way). Prove that bound directly via `Finset.sum` splitting instead.
   `collisionSum_move` remains correct and useful for its original purpose
   (bounding the *minimum*, not an arbitrary swap).
2. `mAQ_eq_ellAQN_min` — the `mAQ` analogue of the already-proved
   `m0AQ_eq_ellAQN_min` (`Lemma55.lean:334`, extracting a minimizing witness
   set) — **does not exist yet** and must be added (mechanical copy) before
   the hard direction can extract `mAQ`'s minimizer.
3. Every term of the per-index additive part `g(i) := 2*NKQ(B,Q,i) -
   NKQ(S,Q,i) - 2*indicatorQle(Q,i) - FNQ(N,Q,i)` is *individually*
   `O(1+B/Q)` (`NKQ_le`, already proved, handles the `NKQ` terms;
   `indicatorQle ≤ 1`; `FNQ(N,Q,i) ≤ (N-1)/Q+1 ≤ 3B/Q+1` since `N≤3B`), so
   the hard direction's single-swap cost bound does **not** need a
   residue-occupancy argument for this half — only the collision-sum term
   (point 1 above) needs genuine combinatorics. This substantially
   undercuts the "15-25 new lemmas" estimate in the prior entry; a fuller
   scoping pass put it closer to ~13 lemmas, with only two stages
   (the residue-counting lemma here, already landed as
   `card_filter_FNQ_shift_ne`, and a `≤3`-fold descent induction for the
   row-replacement argument) being genuinely new combinatorics.

**Not attempted this session:** the hard direction itself
(`m0AQ ≤ mAQ + O(1+B/Q)`), and (5.3) in Lean. See "Next target: Lemma 5.5"
below for the fuller staged plan (still applies; the corrections above
refine stages B/C of it).

---

**2026-09-16 (newest of all): found and fixed the actual bug — `m0AQ` was
scaffolded as a fixed set, not a minimum. (5.2)'s easy direction and the
`a0QB`/`aQB` bound are now proved; unblocked.**

The prior three entries below (all dated 2026-09-16, now superseded)
concluded with increasing confidence that Lemma 5.5 is genuinely false and
that this is a real gap in the paper. That conclusion was correct about the
*Lean proposition as stated* but wrong about the cause.

**The bug:** in `Thm51.lean`, `mAQ` is a **minimum** over all card-`S`
subsets of `Fin (Ndim B S)`. In the original `Lemma55.lean` scaffold, `m0AQ`
was defined as `ell0AQ` — the value at the single **fixed** consecutive row
set, no minimization. Lemma 5.5 compares `mAQ` and `m0AQ`. For large `Q` the
fixed consecutive set is far from optimal, so the difference grows like `S`,
not like `1 + B/Q`, and the stated bound fails — exactly what the sessions
below found, repeatedly and correctly. The failure was in the scaffold, not
the paper.

**The fix:** redefine `m0AQ` as a minimum over card-`S` subsets of
`Fin (Ndim0 B S)`, mirroring `mAQ` exactly. Independently re-derived numerics
(fresh Python, not reusing prior sessions' scripts) confirm this closes the
gap:

| `m0AQ` definition | worst `\|mAQ - m0AQ\| / (1+B/Q)` measured |
|---|---|
| fixed consecutive set (old scaffold) | 140.3, growing without bound |
| minimum over card-`S` subsets (fix) | 0.34, exactly 0 for large `Q` |

`docs/catalan-constant-irrational.md:112` independently reads the paper this
way: "the **minimum** of a certain function over S-element index sets."

**Landed in Lean** (`Lemma55.lean`, unconditional, `lake build` clean):
- `mAQ_le_m0AQ_add`: the easy direction of (5.2), `mAQ ≤ m0AQ + S*(3/Q+1)`,
  via `m0AQ`'s minimizing witness `I₀` cast into `Fin (Ndim B S)` and the
  generalized `FNQ`-shift bound (`abs_FNQ_shift_le`, now stated for any row
  in the common range, not just the consecutive block).
- `abs_a0QB_sub_aQB_le`: `|a0QB - aQB| ≤ 6*(1+B/Q)`, exact and
  self-contained — the two models differ by exactly three rows, each `NKQ`
  term bounded via the new `NKQ_le` (arithmetic-progression count).

**Also found:** (5.3) as stated is false *independently* of (5.2), under the
old fixed-set `m0AQ` — the `|m0-mA|` half of the (5.3) sum sits flat at
`≈ B²/2` (not decaying) while the `|a0-a|` half decays properly. This means
fixing `m0AQ` isn't just cosmetic for (5.2); it's necessary for (5.3) to be
reachable at all. Not yet re-measured against the corrected minimized `m0AQ`
— recommended first step for whoever continues.

**Also found:** the paper's own layer-count claim ("`O(√B log B)` odd prime
powers below `5B`") undercounts — it omits primes themselves (`~5B/log 5B`
of them; measured 348,918 layers at `B = 10^6`, not ~15,000). The `o(B²)`
conclusion of (5.3) still appears to survive via Chebyshev (`∑ log p ≈ 5B`
gives `Θ(B log² B)` for an `O(1+B/Q)`-per-layer bound), but should be derived
that way in Lean rather than by reproducing the paper's count.

**Not attempted this session:** the hard direction of (5.2)
(`m0AQ ≤ mAQ + O(1+B/Q)`, the genuine row-swap/replacement argument) and
(5.3) itself. See "Next target: Lemma 5.5" below for the recommended
continuation (the row-swap plan there still applies, now against the
corrected `m0AQ`; the `O(√B log B)` step should be replaced with Chebyshev
as above).

Scratch scripts from this session (not committed; session scratchpad only,
`C:\Users\danie\.claude\jobs\191c9820\tmp\`): `l55b.py` (shared
`NKQ_all`/`gvec`/`ell_noC` core, reused by the rest), `l55j.py` (the decisive
minimized-`m0` sweep, worst ratio 0.34), `l55g.py`/`l55h.py` (the (5.3) split
into `a0-a`/`m0-mA` halves, run against the OLD fixed-set `m0AQ` — worth
re-running against the corrected minimized version before further Lean work
on (5.3)).

---

**2026-09-16 (superseded by the entry above): re-verification REFUTES the "minimizer-free" numeric
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

**2026-09-16 (superseded — see top of file): numerical counterexample found to
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

**2026-09-16 (superseded — see top of file): scoped the hard direction of (5.2); numerically
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
- **OBSOLETE (2026-09-17) — do not follow this route.** It was written when
  `m0AQ` was still the fixed consecutive set. Under the corrected minimized
  `m0AQ`, step 1 below ("the actual hard content", via `phiQ` machinery and a
  joint additive/collision bound) collapses to the single already-proved line
  `m0AQ_le_ellAQN`, and the greedy/occupancy reasoning it assumes is
  unnecessary — any free replacement index works. (5.2) was proved without it;
  see the top-of-file entry. Kept only as history.
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
