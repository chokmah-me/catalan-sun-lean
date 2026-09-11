# Robustness Check: Catalan's Constant Is Irrational

**Mode: Full-text.** Coverage: all 20 pages of arXiv:2609.04176v1 (PDF). No released code; no supplementary materials; no formal verification artifacts. The interval arithmetic (Propositions 6.3, 7.4) was not independently recomputed because no code or CAS worksheet was provided with the preprint. Every "recomputation" below is from the paper's own stated inputs; anything I could not verify from those inputs is marked.

**Surface: 22 rows frozen; 0 post-freeze addenda.**

---

## Verdict

**Author-anchored (T0-T2 only, 14 rows).** The headline claim ("G is irrational") survives every perturbation the paper itself exposes. The proof architecture is internally consistent: the five stages depend on each other in a single linear chain, and no stage's own stated alternative weakens the conclusion. The paper discloses one explicit alternative (Remark 6.2: forming a full local sum before the positive-part operation changes the 2-adic cost), handles it correctly, and routes through $c_{\text{odd}}$ rather than the full-local constant. The two parameters the paper varies ($\rho = S/B$ is fixed at 1/20; $B \geq 20$) are not presented as tuned; $\rho = 1/20$ is chosen to make the margin positive, and the paper does not claim optimality.

**Full surface (all 22 rows).** Three keystones emerge. (1) The interval-arithmetic computation of $c_{\text{odd}}$ (Proposition 6.3): this is a single certified computation across 178 merged cells; no independent recomputation is available; the margin $\delta_0$ is about 0.00966, meaning an error in $c_{\text{odd}}$ of roughly 0.01 (less than twice its own magnitude) would flip the sign. (2) The asymptotic absorption of the $o(B^2)$ term from Lemma 5.5 (corrected full-row stability): the implicit constant is not bounded, and no finite $B_0$ is stated. (3) The prime-2 treatment in Lemma 5.4: a single-prime argument whose failure would invalidate the entire denominator bookkeeping. The claim is not fragile in the conventional sense (many perturbations, many flips); it is fragile in the Apery sense (one long chain, and a break at any link is fatal).

---

## Claim Object

There is one headline claim.

| Component | Value | Locator |
|---|---|---|
| Outcome / conclusion concept | The Catalan constant $G$ is irrational | Theorem 1.1, p. 2 |
| Exposure / driver concept | The weighted-tail residual-matrix construction at $S/B = 1/20$ produces a nonzero integer $N_B$ with $\|N_B\| < 1$ for large $B$ | Theorem 9.1, proof of Theorem 1.1, p. 19 |
| Estimand / claim type | Existence (irrationality = nonexistence of $a/q$ representation) | |
| Target population / scope | The single constant $G = \sum_{k=0}^{\infty} (-1)^k/(2k+1)^2$ | |
| Focal parameter | $\delta_0 > 0.00966242652523235$ (Theorem 9.1, eq. 9.5) | p. 19 |

Secondary claim (implicit): the weighted-tail method is a new proof technique for irrationality of L-function values.

---

## Frozen Perturbation Surface

22 rows. Frozen now.

| # | Axis | Namespace | Tier | Baseline value | Perturbed values | Estimand relation | Load-bearing for | Given as |Runnable?|
|---|------|-----------|------|----------------|------------------|-------------------|------------------|----------|---------|
| 1 | $\rho = S/B$ ratio | rc/ | T0 | 1/20 | 1/10, 1/30, 1/40 | preserving | $\delta_0 > 0$ | chosen (not optimized) | partial [est.] |
| 2 | $B \geq 20$ threshold | rc/ | T0 | 20 | 10, 50, 100 | preserving | Theorem 5.1 | assumed | no (would need full recomputation) |
| 3 | $c_{\text{odd}}$ interval (Prop 6.3) | rc/ | T0 | $\approx 0.006276\ldots$ (eq. 6.23) | $\pm 0.005$, $\pm 0.01$ | preserving | $\delta_0 > 0$ | measured (interval arithmetic) | partial |
| 4 | $\Lambda_{\text{mid}}$ interval (Prop 7.4) | rc/ | T0 | $\approx 0.17636\ldots$ (eq. 7.15-7.16) | $\pm 0.01$ | preserving | $\delta_0 > 0$ | measured (interval arithmetic) | partial |
| 5 | $\Delta_{>B} = 83/2400$ (eq. 8.5) | rc/ | T0 | 83/2400 | re-derive from eq. 8.4 | preserving | $\delta_0 > 0$ | derived (exact) | yes |
| 6 | Raw quadratic $39/200$ (eq. 9.4) | rc/ | T0 | 39/200 | re-derive from $4\rho - 2\rho^2$ | preserving | $\delta_0 > 0$ | derived (exact) | yes |
| 7 | Number of merged cells (178) | rc/ | T2 | 178 | verify from 238 raw, eq. 6.24 | preserving | $c_{\text{odd}}$ | stated | partial |
| 8 | Euler-Maclaurin remainder through $B_{24}$ | rc/ | T2 | $B_{24}$ sufficient | $B_{20}$, $B_{28}$ | preserving | $c_{\text{odd}}$ bound | assumed sufficient | no |
| 9 | $o(B^2)$ implicit constant in Lemma 5.5 | sens/ | T0 | unstated | finite bound needed | preserving | final contradiction | unstated | no |
| 10 | Prime-2 treatment (Lemma 5.4) | sens/ | T0 | $[A_{2,B} - R_{2,B}]_+ = 0$ | remove; include 2-adic layer | preserving | denominator bound | derived | partial |
| 11 | Full column rank (Theorem 2.1) | sens/ | T0 | rank $\mathcal{R} = S$ via rational-function impossibility | alternative rank proof | preserving | existence of nonvanishing minor | derived (proof by contradiction) | yes (verify the functional equation argument) |
| 12 | Cauchy determinant formula (Remark 4.1) | sens/ | T0 | standard identity | verify applicability conditions | preserving | factorization in (4.4)-(4.5) | standard result | yes |
| 13 | 2-adic positive part = 0 claimed exact | diag/ | T4 | exact zero | construct a case where $v_2(F_B) > 0$ | preserving | Lemma 5.4 | derived | partial |
| 14 | Full-local vs. $c_{\text{odd}}$ (Remark 6.2) | rc/ | T2 | use $c_{\text{odd}}$ (odd primes only) | use full-local $c_{\text{odd}} + \frac{19}{200}\log 2$ | preserving | coefficient in (9.3) | author-disclosed alternative | yes |
| 15 | Breakpoint set $\mathcal{B}$ (eq. 6.24) | rc/ | T2 | 10 specific rational families | verify completeness | preserving | $c_{\text{odd}}$ cell decomposition | stated | no (would need independent derivation) |
| 16 | 235 affine cells for $\Lambda_{\text{mid}}$ | rc/ | T2 | 235 | verify from the six $x$-boundaries and floor-function splits | preserving | $\Lambda_{\text{mid}}$ | stated | no |
| 17 | Theorem 5.1 for $B < 20$ | diag/ | T4 | not claimed | check $B = 10, 15, 19$ | preserving | whether the bound extends | n.a. below stated scope | no |
| 18 | Order of limits ($S \to \infty$ with $B$, vs. fixed $S$) | sens/ | T4 | $S = \lfloor B/20 \rfloor$, $B \to \infty$ | fix $S$, send $B \to \infty$; or $S/B \to 0$ | explore/ (changes estimand) | n.a. | analyst-proposed | no |
| 19 | Nonvanishing of $\hat{q}_B$ (Prop 3.1) | sens/ | T0 | follows from Corollary 2.1 and (3.5) | verify the chain | preserving | $N_B \neq 0$ | derived | yes (trace the logic) |
| 20 | Mertens' formula remainder (eq. 9.1) | rc/ | T0 | $\sum \log p / p^{\nu} = \log x - \gamma + o(1)$ | standard; verify applicability | preserving | prime-sum asymptotics | standard result | yes |
| 21 | "Passed verification of ChatGPT 5.6 Solar" | quote/ | T0 | stated in Acknowledgments | LLM verification vs. formal proof assistant | n.a. (provenance) | community confidence | stated | n.a. |
| 22 | math.GM vs. math.NT posting | quote/ | T0 | math.GM | if posted to math.NT | n.a. (provenance) | community confidence | observed | n.a. |

---

## Survival Table

| Claim | A1 params | A2 assumptions | A3 re-derive | A4 diag | A5 alt model | A6 quotation | Overall (T0-2) | Overall (all) |
|-------|-----------|----------------|--------------|---------|--------------|--------------|----------------|---------------|
| $G \notin \mathbb{Q}$ | survives: $\rho$ has margin | survives: no structural assumption removable without new proof | survives: $\Delta_{>B}$, $39/200$ re-derive exactly | undetermined: cannot run without code | n.a.: no alternative model applicable | weakens: LLM verification, math.GM posting | **survives** | **survives with 3 keystones** |

---

## Keystones

### Keystone 1: The interval for $c_{\text{odd}}$ (Proposition 6.3)

**What it is.** The constant $c_{\text{odd}} = -I_{\text{odd}}$ is evaluated by partitioning $[0,1]$ into cells where the integrand (involving $\zeta(2, 1+v)$, $Q_0(v)\zeta(3, 1+v)$, and related terms) is piecewise polynomial-times-special-function, then integrating each cell exactly and bounding remainders via Euler-Maclaurin through $B_{24}$. The result: $I_{\text{odd}}$ lies in an interval of width less than $10^{-30}$ (eq. 6.22).

**How the paper justifies it.** Equations 6.20-6.26. The cell decomposition comes from the breakpoint set $\mathcal{B}$ in eq. 6.24. The antiderivative $\mathfrak{F}_J(v)$ in eq. 6.26 is stated but not mechanically verified. The Euler-Maclaurin remainder is bounded by $|B_{26}|/(26 X^{26})$ and two companion terms. The argument shift by 64 is stated to ensure all special-function arguments are at least 65.

**Why it is a keystone.** The margin $\delta_0 \approx 0.00966$. The value $c_{\text{odd}} \approx 0.00628$. If $c_{\text{odd}}$ were wrong by $+0.01$ (less than twice its magnitude), $\delta_0$ would flip sign and the proof would fail. This is not a wide margin. The computation is not reproducible from the paper alone; it requires implementing the 178-cell integration with certified arithmetic.

**Cheapest additional evidence.** Independent recomputation of $I_{\text{odd}}$ using Arb (the C library for ball arithmetic) or SageMath's `RealBallField`. This is a finite, deterministic computation; it does not require mathematical insight, only careful implementation. Estimated effort: days, not months, for someone familiar with the libraries.

### Keystone 2: The $o(B^2)$ term in Lemma 5.5

**What it is.** Lemma 5.5 shows that replacing the exact selected-row model (which uses $U = N - 1 = 2B + S + 2$) with the consecutive ideal model (which uses $U_0 = 2B + S - 1$) changes the denominator/numerator ledger by $o(B^2)$. The proof bounds the symmetric difference of the two row sets at "at most six" and argues each row contribution is $O(1 + B/Q)$.

**How the paper justifies it.** The argument in Lemma 5.5 is qualitative: "at most three replacements," each changing the local cost by $O(1 + B/Q)$, summed over $O(B^{1/2} \log B)$ prime powers below $5B$, giving $O(B \log B)$ which is $o(B^2)$.

**Why it is a keystone.** The final proof (Theorem 1.1, p. 19) requires that $\log|N_B| \leq -\delta_0 B^2 + o(B^2)$ tends to $-\infty$. If the implicit constant in the $o(B^2)$ term is large, the contradiction requires correspondingly large $B$, and the existence of such $B$ is not questioned. But the proof does not construct a finite $B_0$ above which the contradiction holds. This is standard in analytic number theory and is not, by itself, a flaw. It becomes a keystone only if someone finds a reason why the $o(B^2)$ bound is not valid.

**Cheapest additional evidence.** Compute the ledger difference for $B = 100, 200, 500, 1000$ and verify that it grows slower than $B^2$. This requires the same CAS infrastructure as Keystone 1.

### Keystone 3: The prime-2 treatment (Lemma 5.4)

**What it is.** The main saturation theorem (Theorem 5.1) handles only odd prime powers. Lemma 5.4 handles $p = 2$ by showing $[A_{2,B} - R_{2,B}]_+ = 0$, where $A_{2,B} = -v_2(F_B) < 0$ because $\Pi_i$ is odd. The argument: $qT_m$ has only odd denominators; division by $2m+1$ preserves 2-integrality; every entry of $q\mathcal{R}$ belongs to $\mathbb{Z}_{(2)}$; therefore $R_{2,B} = v_2(q^S \det \mathcal{R}[A,J]) \geq 0$; and since $A_{2,B} < 0$, the positive part is zero.

**How the paper justifies it.** Five lines on p. 12. The chain: $\Pi_i$ is odd $\Rightarrow$ $A_{2,B} = -v_2(F_B) < 0$; $qT_m$ has only odd denominators $\Rightarrow$ $q\mathcal{R}$ entries are 2-integral $\Rightarrow$ $R_{2,B} \geq 0$ $\Rightarrow$ positive part is zero.

**Why it is a keystone.** If the 2-adic positive part were not zero, a $\log 2$ term would enter the denominator bound (Corollary 5.2, eq. 5.24), potentially overwhelming $\delta_0$. The argument is short and clean but depends on the 2-integrality of every entry of $q\mathcal{R}$, which in turn depends on the recurrence structure and the fact that $2m+1$ is always odd. A subtle error here (e.g., if the weighted tails introduce an even denominator somewhere) would be catastrophic.

**Cheapest additional evidence.** Verify 2-integrality of $q\mathcal{R}$ entries for small $B$ (say $B = 20, 30, 50$) by direct computation. This is a finite matrix computation.

---

## Scope Limits (explore/)

**Row 18: Order of limits.** The proof fixes $\rho = S/B = 1/20$ and sends $B \to \infty$. Fixing $S$ and sending $B \to \infty$ (so $\rho \to 0$) changes the estimand: the raw quadratic $4\rho - 2\rho^2 \to 0$ and there is no margin. This is not fragility; it is the nature of the method. The proof requires $\rho > 0$.

**Alternative $\rho$.** At $\rho = 1/10$, the raw quadratic is $39/100 - 2/100 = 37/100 = 0.37$. The prime corrections would also change (larger $S$ means more cells, different $c_{\text{odd}}$, different $\Lambda_{\text{mid}}$). The paper does not claim $\rho = 1/20$ is the only working value; it is the one evaluated. Trying $\rho = 1/10$ or $\rho = 1/15$ might yield a larger margin or might fail; this is an extension, not a test of the stated claim.

---

## Perturbation Log

**Row 1** ($\rho = S/B$). At $\rho = 1/20$, the raw quadratic is $4(1/20) - 2(1/20)^2 = 1/5 - 1/200 = 39/200 = 0.195$. At $\rho = 1/10$: $4/10 - 2/100 = 38/100 = 0.38$. At $\rho = 1/30$: $4/30 - 2/900 = 118/900 \approx 0.1311$. The raw quadratic is maximized at $\rho = 1$ (value 2) and is positive for all $\rho > 0$. The question is whether the prime corrections remain smaller than the raw quadratic. At $\rho = 1/20$, the corrections sum to about $0.195 - 0.00966 = 0.18534$, consuming 95% of the margin. [Est.] At $\rho = 1/10$, the corrections would be larger (more cells, more primes in the "small" range), but the raw quadratic nearly doubles. Direction: likely survives at $\rho = 1/10$ with more margin, but cannot confirm without recomputation. **Survives [est.].**

**Row 2** ($B \geq 20$). Not run: would require full recomputation of Theorem 5.1 at lower $B$. The statement of Theorem 5.1 explicitly requires $B \geq 20$; the bound $33B/160 - 21/8 > 0$ used on p. 11 requires $B > 160 \cdot 21/(8 \cdot 33) = 12.7\ldots$, so $B \geq 13$ might suffice. **Not run: no code.**

**Row 3** ($c_{\text{odd}}$ interval). The paper claims (eq. 6.22): $I_{\text{odd}} > -0.00627674472810098\ldots49$ and $I_{\text{odd}} < -0.00627674472810098\ldots48$, an interval of width $< 10^{-30}$. If $c_{\text{odd}} = -I_{\text{odd}}$ were perturbed by $+0.005$, the net margin becomes $\delta_0 - 0.005 \approx 0.00466$: still positive. If perturbed by $+0.01$: $\delta_0 - 0.01 \approx -0.00034$: **flips**. The sign-flip threshold is $c_{\text{odd}} + \delta_0 \approx 0.01594$. An error in $c_{\text{odd}}$ of $+153\%$ of its value would kill the proof. This is a meaningful but not razor-thin margin. **Survives at $\pm 0.005$; flips at $\pm 0.01$. Scale: full.**

**Row 4** ($\Lambda_{\text{mid}}$ interval). The paper claims (eq. 7.15): $0.17635583792 < \Lambda_{\text{mid}} < 0.17635583794$. If $\Lambda_{\text{mid}}$ were perturbed by $-0.01$: $\delta_0$ drops by about $0.01$, flips. The sign-flip threshold is the same total budget. **Survives at $\pm 0.005$; flips at $\pm 0.01$. Scale: full.**

**Row 5** ($\Delta_{>B}$). Re-derived: $\Delta_{>B} = (2/3)\rho + (1/2)\rho^2$ (eq. 8.4). At $\rho = 1/20$: $(2/3)(1/20) + (1/2)(1/400) = 1/30 + 1/800 = 80/2400 + 3/2400 = 83/2400$. **Matches exactly. Survives.**

**Row 6** (Raw quadratic). Re-derived: $4\rho - 2\rho^2 = 4/20 - 2/400 = 200/1000 - 5/1000 = 195/1000 = 39/200$. **Matches exactly. Survives.**

**Row 7** (178 merged cells). The breakpoint set $\mathcal{B}$ in eq. 6.24 yields a partition of $[0,1]$ whose raw cell count depends on the number of distinct breakpoints. The paper states 238 raw cells and 178 after merging. Not independently verified. **Not run: would need to enumerate the partition from (6.24).**

**Row 8** (Euler-Maclaurin through $B_{24}$). Not run: the argument that $B_{24}$ suffices depends on the magnitude of the special-function arguments (all shifted by 64 to be $\geq 65$). Plausible that $B_{20}$ would also suffice (the remainders decrease factorially), but not verified. **Not run: no code.**

**Row 9** ($o(B^2)$ implicit constant). Not run: the bound is qualitative. The paper argues the error is $O(B \log B)$, which is $o(B^2)$, and this is standard. No reason to doubt the rate, but the constant is not tracked. **Not run: qualitative bound only.**

**Row 10** (Prime-2). The argument that $[A_{2,B} - R_{2,B}]_+ = 0$ follows a clean chain. Removing this (i.e., including a 2-adic positive-part term) would add $\leq A_{2,B} \cdot \log 2$ to the denominator bound. Since $A_{2,B} = -v_2(F_B) < 0$ and $F_B = \prod_{r=0}^{2B-1} r!$, we have $v_2(F_B) = \sum_{r=0}^{2B-1} v_2(r!) = \sum_{r=0}^{2B-1} \sum_{\nu \geq 1} \lfloor r/2^{\nu} \rfloor$, which is $\Theta(B^2)$. If the 2-adic positive part were even slightly positive, the added $\log 2$ term would be $\Theta(B^2)$ and would overwhelm any fixed $\delta_0 B^2$. **Structural: if Lemma 5.4 fails, the entire proof fails regardless of margin.**

**Row 11** (Full column rank). The proof of Theorem 2.1 uses the functional equation $S_0(z) + S_0(z+1) = 1/(4z^2)$ and shows no rational function satisfies it by a pole-location argument (p. 6). Verified: if $S_0$ had a pole with maximal real part at $z_0$, then $S_0(z_0 + 1)$ is regular, so the equation forces a pole at $z_0$ from the RHS, which has poles only at $z = 0$; but then $z_0 = 0$, and inspecting $z = 1$ forces a pole there too, contradiction. **Survives. The argument is self-contained and clean.**

**Row 12** (Cauchy determinant). The Cauchy determinant formula (Remark 4.1) is a classical result. The application in (4.4) requires the $x_i + y_j$ denominators to be nonzero and distinct. Since $i_{\nu} \in \{0, \ldots, N-1\}$ and $j \in \{1, \ldots, S\}$, the quantities $2(i_{\nu} + j) + 1$ are distinct positive odd integers. **Survives.**

**Row 13** (2-adic diagnostic). Attempted to construct a scenario where $v_2(q^S \det \mathcal{R}[A,J]) < 0$. This would require some entry of $q\mathcal{R}$ to have a factor of 2 in its denominator. Since $q\mathcal{R}_{a,j} = \sum (-1)^i \binom{a+2B}{i} \Pi_i u_{i+j}$ and $qu_{i+j} = qT_{i+j}/(2(i+j)+1)$, the denominator of $qu_{i+j}$ involves $(2(i+j)+1)$ which is odd, and the terms $(2(i+k)+1)^{-2}$ in $T_{i+j}$ also have odd denominators. The binomial coefficients $\binom{a+2B}{i}$ are integers. $\Pi_i = \prod_{h=1}^{B}(2(h+i)+1)^2$ is a product of odd squares. So every term is a product of integers, odd squares, and reciprocals of odd numbers. No factor of 2 enters the denominator. **Failed to construct counterexample. Survives.**

**Row 14** (Full-local vs. $c_{\text{odd}}$). Remark 6.2 states that using the full-local constant (before the positive-part operation) changes the displayed value because the prime 2 contributes $(19/200)\log 2$. But Lemma 5.4 shows the 2-adic positive part is zero, so the applicable constant is $c_{\text{odd}}$, not $c_{\text{odd}} + (19/200)\log 2 \approx 0.00628 + 0.0659 = 0.0722$. If one mistakenly used the full-local constant, the correction would be much larger and $\delta_0$ would be deeply negative ($0.195 - 0.0722 - 0.176 - 0.035 = -0.088$). The paper correctly uses $c_{\text{odd}}$. **Survives: the author's disclosed alternative is correctly handled.**

**Row 15** (Breakpoint set). Not run: verifying completeness of $\mathcal{B}$ requires independently deriving all points where the floor functions $\lfloor 20v \rfloor$, $\lfloor 41v \rfloor$, $\lfloor 40v \rfloor$ and the derived quantities $z(y)$, $\alpha(v)$, $\beta(v)$, $\gamma(v)$ change value, plus the points where the cumulative measure below a marginal level equals $\rho$. **Not run: no code.**

**Row 16** (235 affine cells for $\Lambda_{\text{mid}}$). Not run: same class of verification as Row 15. **Not run: no code.**

**Row 17** (Theorem 5.1 below $B = 20$). Not run: the theorem is stated for $B \geq 20$. The inequality $33B/160 - 21/8 > 0$ requires $B > 10.18$, so $B \geq 11$ might work for the particular bound used. This is a diagnostic, not a fragility. **Not run: out of stated scope.**

**Row 18** (Order of limits). Explore/: changing $\rho \to 0$ as $B \to \infty$ changes the estimand. The proof requires $\rho$ fixed and positive. **Estimand-changing. Logged under Scope Limits.**

**Row 19** (Nonvanishing of $\hat{q}_B$). Traced: $\hat{q}_B \neq 0$ follows from eq. (3.5), which follows from $\det \mathcal{R}[A,J] \neq 0$ (Corollary 2.1, from Theorem 2.1's rank result) and the explicit formula for $F_B$ (all factorials, nonzero). The chain is: rank $S$ $\Rightarrow$ exists nonvanishing $S \times S$ minor $\Rightarrow$ $\det \mathcal{R}[A,J] \neq 0$ $\Rightarrow$ $\hat{q}_B \neq 0$. **Survives.**

**Row 20** (Mertens' formula). The prime-sum asymptotic $\sum_{p^{\nu} \leq x} \log p / p^{\nu} = \log x - \gamma + o(1)$ is a standard refinement of Mertens' theorem. Applied in Section 9 to convert the discrete prime-power sums into the continuous integrals evaluated in Sections 6-8. Standard result, well within its domain of applicability. **Survives.**

**Row 21** (ChatGPT verification). Not a mathematical perturbation. Provenance assessment: LLM "verification" of a 20-page analytic number theory proof is not comparable to formal verification (Lean, Coq, Isabelle) or even to a careful human expert read. LLMs can miss subtle sign errors, off-by-one errors in floor functions, and incorrect interval bounds. The paper's statement that the proof "passed the verification of ChatGPT 5.6 Solar" should not be treated as evidence of correctness by the mathematical community. **Provenance: weak. This does not affect the mathematics but affects trust calibration.**

**Row 22** (math.GM posting). Not a mathematical perturbation. The paper is posted to arXiv's General Mathematics section, which is unmoderated. Papers in math.GM do not pass through the endorsement system that math.NT requires. This is a credibility signal, not evidence of error. **Provenance: the posting lowers prior confidence; it does not affect the internal logic.**

---

## What This Check Could Not Do

**Denominator: 22 frozen rows. Attempted: 22. Recomputed or verified: 10. Estimated: 2. Not run: 8. Provenance-only: 2.**

The following could not be done without released code or a CAS implementation:

1. **Independent recomputation of $c_{\text{odd}}$ and $\Lambda_{\text{mid}}$.** These are the two certified-arithmetic constants. Together they are the single most important verification target. The paper provides formulas but not code. Rows 3, 4, 7, 8, 15, 16 all depend on this.

2. **Explicit computation of the $o(B^2)$ constant.** Row 9 is qualitative by nature, but a numerical check at finite $B$ would strengthen confidence.

3. **Enumeration of cell partitions.** Rows 7, 15, 16 require enumerating breakpoints from the stated formulas and verifying the cell counts (178 merged cells for $c_{\text{odd}}$, 235 for $\Lambda_{\text{mid}}$).

4. **Theorem 5.1 at small $B$.** Row 17 is a diagnostic that would test whether the bound extends below the stated threshold.

The re-derivable quantities (Rows 5, 6, 11, 12, 13, 14, 19, 20) all verified successfully. The proof's internal logic chain is consistent: no perturbation of the *structure* broke the argument. The vulnerability is concentrated in the *numerical* evaluation of two integrals, which is where independent verification should focus.
