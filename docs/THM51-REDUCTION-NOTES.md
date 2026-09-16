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
