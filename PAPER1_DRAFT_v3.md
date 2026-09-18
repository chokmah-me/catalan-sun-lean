<p class="hebrew-epigraph" dir="rtl" lang="he">אִם יִרְצֶה הַשֵּׁם</p>

<p class="hebrew-date" dir="rtl" lang="he">ח׳ תִשְׁרֵי ותשפ״ז</p>

# A Numerical Test of the Quadratic Estimate in arXiv:2609.04176v1

Daniyel Yaacov Bilar, Chokmah LLC, chokmah-dyb@pm.me
ORCID: [0000-0002-9040-6914](https://orcid.org/0000-0002-9040-6914)
Licensed under [CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Abstract

Zhi-Wei Sun's preprint arXiv:2609.04176v1 claims that Catalan's constant $G$ is irrational. Its final step, Theorem 9.1, asserts that a height quantity built from a fixed scalar is bounded above by $-\delta_0 B^2 + o(B^2)$ with $\delta_0 > 0.00966$. The preprint proves that assertion along one chain, through equations (3.5), (5.13) and (5.24), and that chain passes through a quantity here called $\mathrm{SCALAR}(B)$, an upper bound on the height built from three directly computable terms. Evaluating it at $B = 200, 400, 800, 1000, 1200$ gives $+1.826, +1.846, +1.851, +1.854, +1.855$ for the coefficient of $B^2$, converging upward, where the chain needs a value below $-0.00966$. The preprint's proof of Theorem 9.1 therefore cannot deliver its conclusion. Because $\mathrm{SCALAR}$ bounds the height from above, this refutes the proof route rather than the assertion itself. The discrepancy has two independent parts. The larger is a real-place term $v_2(F_B)\log 2 \to 2\log 2 = 1.386$, which Remark 9.3 names and folds into a constant $c_{\rm odd} = 0.00628$ that is 220.9 times too small to hold it. Subtracting it leaves $+0.468$, which is 48.5 times $\delta_0$ and still the wrong sign, in the cancellation that Proposition 9.5 asserts. Section 9 supplies no displayed derivation of its factor grouping, so the grouping is reconstructed here term by term; it confirms both the $B^2\log B$ cancellation the preprint relies on and the $+0.475$ residue. All scripts and data are archived.

## 1. What is tested, and what is not

The preprint under examination is Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1 [1], posted September 2026 to math.GM and unrefereed. Its stated result would settle a question open since the 1860s.

This note reports one measurement. It follows the chain by which [1] proves Theorem 9.1, isolates the quantity that chain must bound, and evaluates it numerically at five values of $B$. The measured coefficient of $B^2$ is positive where the chain requires it to be below $-0.00966$: a failure of sign, with the measured value $192$ times the magnitude of the required bound at $B = 1200$.

What this does and does not settle turns on one direction. Equation (5.24) of
[1] bounds $\log H_B^{\min}$ from above, so the measured quantity is an upper
bound on the height, not the height. A positive upper bound does not prove the height is positive. What it does prove is that the preprint's own route to Theorem 9.1 cannot reach $-\delta_0 B^2$, because that route establishes the theorem by bounding the height with exactly this quantity. The result is a refutation of the proof as given, and the distinction is kept throughout.

Four things are outside the scope of this note. It does not claim that Catalan's constant is rational; nothing here bears on the truth of $G \notin \mathbb{Q}$. It does not claim that the statement of Theorem 9.1 is false; only its proof is tested, for the reason given above. It does not claim that the approach of [1] cannot be repaired; whether the two gaps identified below can be closed was not tested. It does not report an error in any single line of Section 9, because Section 9's proof does not proceed line by line.

Some context on why the claim drew attention. Calegari, Dimitrov and Tang proved the linear independence of $1$, $\zeta(2)$ and $L(2,\chi_{-3})$ [3], which settles the conductor-3 case, but their method does not reach Catalan's constant $G = L(2,\chi_{-4})$, where the even conductor changes the denominator arithmetic. Reference [3] is cited in [1] as well. The preprint claims to cross that barrier by elementary means, without arithmetic holonomy or $p$-adic analysis, which is what makes the final quadratic estimate worth checking directly.

A companion Lean 4 formalization of the structural lemmas of Sections 2 to 5 of
[1] is archived alongside this note [2]. That formalization claims no part of
Section 9 and is unaffected by what follows.

## 2. Notation

Symbols follow [1]. $B$ is the construction parameter, $S = \lfloor B/20\rfloor$ the number of selected rows, $N$ the dimension of the completed square matrix, and $\rho = S/B = 1/20$.

| symbol | meaning |
|---|---|
| $F_B$ | $\prod_{r<2B} r!$, the factorial factor of (3.5) |
| $\Pi_i$ | the odd-linear product $\prod_{h=1}^{B}(2(h+i)+1)^2$ of (2.1) |
| $\mathcal{R}[A,J]$ | the residual minor on row set $A$, column set $J$ |
| $q$ | the denominator in the hypothesis $G = a/q$, a fixed integer, independent of $B$ |
| $\widehat q_B$ | the fixed scalar, $\det \mathcal{A}_B$; unrelated to $q$ above |
| $H_B^{\min}$ | the minimal integerizer of $\widehat q_B$ |
| $Q = p^\nu$ | an odd prime power, the layer index |
| $a_{Q,B}$ | the denominator layer exponent of Section 5 of [1] |
| $m^A_{Q,B}$ | the test residual layer exponent, a minimum over card-$S$ row sets |
| $\delta_0$ | the claimed margin, $\delta_0 > 0.00966242652523235$ |
| $c_{\rm odd}$ | the small-prime constant, $Q \le S$ |
| $\Lambda_{\rm mid}$ | the middle-prime integral, $S < p < B$ |
| $\Xi_I$ | the Cauchy-Binet summand at row set $I$, eq. (4.5) |
| $\Psi_A(I)$ | the integer cofactor of the Pascal alternant, $|\Psi_A(I)| \ge 1$ |
| $V(I)$, $V(J)$ | Vandermonde products over the row and column index sets |

## 3. The reduction

Three equations of [1] combine to eliminate everything that is not computable. Write $F_B = \prod_{r < 2B} r!$, let $\Pi_i$ be the odd-linear products of (2.1), let $\mathcal{R}[A,J]$ be the residual minor, and let $a_{Q,B}$ and $m^A_{Q,B}$ be the layer quantities of Section 5.

From (3.5),

$$\widehat q_B = \pm \frac{F_B \det \mathcal{R}[A,J]}{\prod_{i=0}^{N-1}\Pi_i}.$$

From (5.13), summed over odd $p$, and using that each $\Pi_i$ is odd so that only the odd part of $F_B$ is counted on the left,

$$\sum_{Q \text{ odd}} a_{Q,B}\log p = \log\prod_i \Pi_i - \log F_B + v_2(F_B)\log 2.$$

From (5.24), the positive-part height bridge,

$$\log H_B^{\min} \le \sum_{Q \text{ odd}} \bigl(a_{Q,B} - m^A_{Q,B}\bigr)\log p.$$

Adding the first two to the third, every term cancels except three:

$$\log H_B^{\min} + \log|\widehat q_B| \;\le\; \log|\det \mathcal{R}[A,J]| + v_2(F_B)\log 2 - \sum_{Q \text{ odd}} m^A_{Q,B}\log p,$$

up to the $O(B)$ contributed by the fixed factor $q^S$. That factor is $O(B)$ and not larger because $q$ is the denominator in the hypothesis $G = a/q$, one fixed integer chosen before $B$ varies, so $S\log q = O(B) = o(B^2)$ however large $q$ may be. Call the right side $\mathrm{SCALAR}(B)$. Theorem 9.1 of [1] asserts exactly that $\mathrm{SCALAR}(B) \le -\delta_0 B^2 + o(B^2)$ with $\delta_0 > 0.00966242652523235$.

Each of the three terms is computable without choosing a row set $I$ and without passing through the Cauchy-Binet maximum. The $m^A_{Q,B}$ come from an exact dynamic program over residue classes, $v_2(F_B)$ from Legendre's formula, and $\det \mathcal{R}[A,J]$ from (2.1) with the entries as exact rationals over a common denominator.

## 4. Measurement

Table 1 gives $\mathrm{SCALAR}(B)/B^2$ at $S = \lfloor B/20 \rfloor$, the regime [1] uses.

| $B$ | 200 | 400 | 800 | 1000 | 1200 |
|---|---|---|---|---|---|
| $\mathrm{SCALAR}(B)/B^2$ | +1.826146 | +1.845926 | +1.851237 | +1.854020 | +1.854615 |

**Table 1.** The coefficient the proof of Theorem 9.1 requires to be below $-0.00966$, measured at five values of $B$ with $S = \lfloor B/20\rfloor$. Across the two doublings present, increments fall from $+0.019780$ to $+0.005311$, a factor of $3.7$; a $c + k/B$ fit gives a limit of $+1.8607$. The sequence converges rather than drifting logarithmically.

Two values were computed as blind prediction tests. Before the $B = 1000$ run, an extrapolation from the first three points predicted $+1.854003$, against $+1.854020$ measured. Before the $B = 1200$ run, an extrapolation from the first four predicted $+1.855875$, against $+1.854615$ measured. The two errors, $1.7\times10^{-5}$ and $1.3\times10^{-3}$, differ by about two orders of magnitude, so the second prediction is much the weaker test; the extrapolations were recorded at the time rather than reconstructed here, and no claim is made about the form used. A least-squares $c + k/B$ fit over all five points, which is reproducible from the archived data, gives a limit of $+1.8607$. Every prediction and every fit lands near $+1.86$, and none near $-0.00966$.

Three independent derivations of $\mathrm{SCALAR}$ agree: the algebraic route of Section 3 above, a direct evaluation from (3.5), and the (5.13) identity, which reproduces to $1.6 \times 10^{-16}$. The determinant was checked against brute-force polygamma sums at $B = 20, 40, 60$, against an exact-integer evaluation at $B = 200$ and $400$, and across four different row sets $A$. Each floating-point determinant is evaluated at escalating precision, $P \mapsto 1.6P + 8000$ bits, until consecutive runs agree to $10^{-9}$ relative. The accepted precisions were 66115 bits at $B = 200$, 82787 at $B = 400$, and 40000 at $B = 800$, 1000 and 1200.

One caveat on that acceptance rule, since it is easy to misread. The implementation also tests a quantity it calls the cancellation, the spread between the largest single term and the smallest entry, 1484 bits at $B = 200$. That spread measures cancellation inside the entry sums $R_{a,j} = \sum_i \pm c_{a,i}\Pi_i u_{i+j}$, which is what the fixed-point entry construction needs to control. It does not measure cancellation in the subsequent LU determinant, and it should not be read as doing so: at $B = 200$ the largest entry term is $2^{70301}$ against $|\det\mathcal{R}| = 2^{27421}$, and at $B = 400$ the determinant is larger than any single entry term, so the difference is not a cancellation measure at all.

The guarantee on $\log|\det\mathcal{R}|$ is therefore empirical rather than a bit-budget argument, and rests on two checks. Held at $B = 200$ across $P = 40000, 66115, 90000$ and $120000$, a threefold range, the value is constant at $19006.571555426$ to nine decimals. Independently, the exact-integer route, which carries $X$ and $Y$ as exact rationals over a common denominator and never forms a floating entry, returns $19006.571555$ at the same $B$. Agreement of two unrelated code paths to six decimals is the reason the value is trusted.

## 5. Two independent components

The gap does not reduce to a single mispriced constant. Subtracting the real-place term and nothing else leaves the second column of Table 2.

| $B$ | $\mathrm{SCALAR}/B^2$ | $\mathrm{SCALAR}/B^2 - 2\log 2$ |
|---|---|---|
| 200 | +1.826146 | +0.439852 |
| 400 | +1.845926 | +0.459632 |
| 800 | +1.851237 | +0.464942 |
| 1000 | +1.854020 | +0.467726 |
| 1200 | +1.854615 | +0.468320 |

**Table 2.** Removing the $2\log 2$ real-place term leaves a residue converging to about $+0.47$, which is 48.5 times $\delta_0$, with the sign that Theorem 9.1 needs to be negative.

**The real-place term.** $F_B$ sits in the numerator of (3.5) and $v_2(F_B) \sim 2B^2$, while (5.24) sums over odd $p$ only, so that mass is never removed by the odd-prime ledger. Measured, $v_2(F_B)\log 2 / B^2$ runs $+1.354, +1.368, +1.376, +1.378, +1.379$, approaching $2\log 2 = 1.38629$ from below. Remark 9.3 of [1] names this exact quantity, calling it "the residual real power of $2$ from $F_D$," and states that it is included in the derivation of the odd small-scale expression, which is why "the applicable cost is $c_{\rm odd}$." But $c_{\rm odd} = 0.006276744728100983$ in [1], and $2\log 2 / c_{\rm odd} = 220.9$. The constant is 220.9 times too small to absorb the term assigned to it. Remark 6.2's $(19/200)\log 2 = 0.0658$ is 21 times too small. Lemma 5.4 concerns the 2-part of $H_B^{\min}$, not the real place.

**The Proposition 9.5 residue.** What remains after that repair is visible without extrapolation. The difference $\log|\det\mathcal{R}|/B^2 - \sum m^A_{Q,B}\log p / B^2$ measures $+0.472152, +0.477515, +0.474750, +0.475949, +0.475175$ at the five values of $B$. The sequence is not monotone, rising then falling, but it oscillates at the $5\times10^{-3}$ level about a mean of $+0.4751$ across a sixfold range in $B$, with no trend toward zero. This sits in the cancellation Proposition 9.5 asserts. The mechanism is real and visible in the data: $\log|\det \mathcal{R}|/B^2$ rises by $+0.0692$ then $+0.0693$ over the first two doublings, while $-\sum m\log p/B^2$ falls by $-0.0638$ then $-0.0720$, so the two track each other to within about 8 percent. That is the $B^2\log B$ cancellation the preprint claims. Their difference converges to $+0.475$ rather than to zero. The cancellation fires and does not close.

The two components share a sign, so they add. Repairing Remark 9.3's constant alone would leave the residue at $48.5$ times the magnitude of $\delta_0$, and still positive where the proof needs it negative.

## 6. Section 9's factor grouping, reconstructed

A reader may object that the reduction of Section 3 above mis-transcribes what Section 9 actually does. The objection deserves a direct answer, because Proposition 9.5's proof in [1] contains no displayed derivation to compare against. Its grouping step is one sentence:

> "The factorial, odd-linear, Cauchy, Vandermonde, and tail factors are then
> grouped by prime-power scale. The $B^2\log B$ terms cancel because the
> denominator baseline $a_{Q,B}$ and the real normalization come from the same
> fixed scalar. The remaining raw quadratic coefficient is $4\rho - 2\rho^2 =
> 39/200$."

Every step that could be mis-transcribed lives in that sentence. So the five named groups were evaluated separately from the exact identity (4.5) of [1], in which $V(I)$ and $V(J)$ are the Vandermonde products over the row and column index sets and $\Psi_A(I)$ is the integer cofactor left by factoring the Pascal alternant, satisfying $|\Psi_A(I)| \ge 1$:

$$|\Xi_I| = 2^{S(S-1)}V(J)V(I)^2|\Psi_A(I)|\frac{\prod_{a\in A}(a+2B)!}{\prod_{i\in I}i!(N-1-i)!}\prod_{i\in I}\frac{|qT_{i+1}|\Pi_i}{\prod_{j=1}^{S}(2(i+j)+1)}.$$

| $B$ | factorial | Cauchy | Vandermonde | odd-linear | tail | total |
|---|---|---|---|---|---|---|
| 200 | +0.059303 | +0.002784 | +0.002448 | +0.624880 | -0.003185 | +0.686229 |
| 400 | +0.060289 | +0.003628 | +0.003964 | +0.692216 | -0.001765 | +0.758333 |
| 800 | +0.060479 | +0.004482 | +0.005586 | +0.759675 | -0.000969 | +0.829253 |
| 1000 | +0.060430 | +0.004759 | +0.006121 | +0.781407 | -0.000797 | +0.851919 |
| 1200 | +0.060360 | +0.004985 | +0.006562 | +0.799167 | -0.000680 | +0.870394 |

**Table 3.** The five factor groups of (4.5) evaluated separately, each divided by $B^2$, at $S = \lfloor B/20\rfloor$ and the row set maximizing the total among four candidates. The Cauchy column is $2^{S(S-1)}V(J)$, the Vandermonde column $V(I)^2$, the odd-linear column $\prod\Pi_i / \prod(2(i+j)+1)$, and the tail column $\prod T_{i+1}$. The total column is the quantity fitted in the next paragraph.

The $B^2\log B$ term is real and the preprint's cancellation claim is structurally correct. Fitting $\log|\Xi_I|/B^2$ to $c_2 + c_L\log B$ gives $c_L \approx +0.1013$, stable across $B = 200$ to $1200$, so the grouped summand does carry $B^2\log B$. The $a$-ledger removes it: the (5.13) identity reproduces to $8\times 10^{-16}$. This part of Section 9 works as described.

Reconstructed this way, the grouping bounds the direct route from above, which is the direction Proposition 9.5 requires. Dropping $|\Psi_A(I)| \ge 1$, which [1] also never bounds below by more than 1, and taking a maximum over $I$ rather than a sum, overestimates $\log|\det\mathcal{R}|$ by $+0.2111$ to $+0.2163$ times $B^2$ across the five values of $B$. Both routes therefore measure the same object, and the grouped one is conservative.

The reconstruction does not, however, give a second measurement of the Proposition 9.5 residue. The residue quoted in Section 5, $+0.472152$ at $B = 200$, is computed from the direct route, $\log|\det\mathcal{R}|/B^2 - \sum m^A_{Q,B}\log p/B^2$. Its grouped counterpart is larger by exactly the slack above, $+0.683$ at $B = 200$, and the two agree only after that slack is removed. Nothing in this section is independent evidence for the value $+0.475$; what it establishes is that the grouped and direct routes describe the same object, with the grouped one conservative by a stable margin.

Run end to end, the preprint's own grouping gives $+2.037, +2.060, +2.067, +2.070, +2.071$ for the coefficient of $B^2$. These follow from Table 3 by the same assembly as in Section 3: at $B = 1200$, the total $+0.870394$ plus $v_2(F_B)\log 2/B^2 = +1.379440$ minus $\sum m^A_{Q,B}\log p/B^2 = +0.178961$ gives $+2.070873$. That is a larger positive coefficient than the direct determinant route gives, because discarding $\Psi_A(I) \ge 1$ removes a positive quantity from the bound.

## 7. Caveats

The grouped column of Section 6 drops $\Psi_A(I)$ and is therefore an upper bound rather than an equality. It cannot by itself establish that Theorem 9.1 is false, which is why the direct determinant route of Sections 3 and 4 carries the primary evidence.

The maximum over $I$ in Section 6 is taken over four candidate row sets, consecutive, top, centered and spread, not over all $\binom{N}{S}$. The centered set wins at every $B$ tested.

The factor $q$ is dropped from the tail group, contributing $O(S\log q) = o(B^2)$.

Every number here assumes the Python mirror of $a_{Q,B}$ and $m^A_{Q,B}$ is faithful to [1]. The regression check guards that mirror against the Lean definitions of [2] and asserts $a_{Q,B} \ge m^A_{Q,B}$ numerically at every layer tested, but the step from [1]'s prose to those definitions is human reading. Three transcription-class discrepancies were found during the formalization, so the risk is not hypothetical. This is the largest single dependency of the result.

The measurement locates two gaps. It does not identify which line of Section 9 is wrong, and no claim is made that either gap is irreparable.

All values are computed at $S = \lfloor B/20\rfloor$, the regime of [1]. The behavior at other ratios was not tested.

## 8. Reproduction

The scripts and data are in the archived repository [2], under `scripts/gates`. Every number in this note comes from the tree at commit `66eb131`. A regression check, `check.py`, asserts that the Python mirror of the layer definitions still agrees with the formalized Lean definitions and that $a_{Q,B} \ge m^A_{Q,B}$ holds numerically at every layer tested. The verdict of Sections 4 and 5 is produced by `gate_scalar.py`, with the per-layer data in `data/scalar_S_B20.csv`; the reconstruction of Section 6 is produced by `gate_grouping.py`, whose `compare` mode regenerates Table 3 and the slack figures. Readers checking the determinant should note that the `cancel_bits` field reported by `gate_scalar.py` is the entry-sum spread discussed in Section 4, not a determinant-level cancellation, and that the acceptance test in `det_R_verified` compares it against `P/2`; the guarantee relied on here is the precision sweep and the exact-integer cross-check, not that comparison.

## AI Utilization Statement

This work was produced with AI assistance. The author used Claude Opus 5 for drafting, editing, code generation, and mathematical checking. All substantive claims, analytical decisions, and final editorial judgments were made by the author. AI-generated content was reviewed and corrected by the author before inclusion. No AI system is listed as a co-author.

Affiliation: Chokmah LLC, Norwich, VT. Contact: chokmah-dyb@pm.me.

## References

[1] Zhi-Wei Sun, "Catalan's constant is irrational," *arXiv preprint*,
arXiv:2609.04176, 2026. [Online]. Available: https://arxiv.org/abs/2609.04176

[2] Daniyel Yaacov Bilar, "CatalanSun: a Lean 4 slice of arXiv:2609.04176v1,"
Zenodo, 2026. doi: DOI-PENDING. [Online]. Available: https://github.com/chokmah-me/catalan-sun-lean

[3] Frank Calegari, Vesselin Dimitrov, and Yunqing Tang, "The linear
independence of $1$, $\zeta(2)$, and $L(2,\chi_{-3})$," *arXiv preprint*, arXiv:2408.15403, 2024. [Online]. Available: https://arxiv.org/abs/2408.15403
