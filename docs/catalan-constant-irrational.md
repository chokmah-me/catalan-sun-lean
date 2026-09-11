# The Weighted Tail That Closed a 160-Year Gap

Published on [[HEBREW DATE PLACEHOLDER]]

[[HEBREW EPIGRAPH PLACEHOLDER]]

## TL;DR

**Expert.** Sun constructs a weighted finite-difference residual matrix at ratio $S/B = 1/20$, factors its determinant via Pascal-Cauchy-Binet, proves a local saturation theorem converting all odd prime-power denominator layers into upper bounds on the positive-part height, and evaluates three prime ranges by exact integration to obtain a strict negative quadratic coefficient $\delta_0 > 0.00966$ in the $\log|\hat{q}_B| + \log H_B^{\min}$ bound. Assuming $G = a/q$ produces a nonzero integer $N_B$ with $|N_B| < 1$ for large $B$. Contradiction. The proof bypasses Calegari-Dimitrov-Tang entirely: no arithmetic holonomy, no $p$-adic analysis, no automorphic forms. If it holds, the conductor-4 barrier is broken by elementary (if intricate) methods.

**Practitioner.** This preprint claims to prove that Catalan's constant $G \approx 0.9159655\ldots$ is irrational, resolving a problem open since the 1860s. The technique is new: "weighted tails" of the alternating series, not Pade approximants or hypergeometric constructions. The author credits conversations with AI for the central idea and reports verification by ChatGPT 5.6 Solar. Not yet peer-reviewed. Posted to math.GM, not math.NT.

**General Public.** There is a number, about 0.916, that shows up across mathematics: in lattice path lengths, in quantum field theory integrals, in the geometry of tilings. It was introduced in the 1860s. For over 160 years, nobody could prove whether it can be written as a fraction. This paper claims to finally prove it cannot.

**Skeptic.** Posted to math.GM (unmoderated), not math.NT. The sole reported verification is by a language model, not a proof assistant. The critical computation (Proposition 6.3) involves interval arithmetic across 178 merged cells of Hurwitz zeta antiderivatives. One wrong cell boundary kills the margin. The author has a history of bold conjectures. Treat as serious but unverified.

**Decision-Maker.** If verified, this ranks with Apery's 1978 proof that $\zeta(3)$ is irrational. It validates a new proof template and represents the highest-profile mathematical result where AI played a substantive creative role. Expect 6 to 18 months before the community reaches consensus.

---

## The problem

Catalan's constant is the Dirichlet beta function at $s = 2$:

$$G = \beta(2) = \sum_{k=0}^{\infty} \frac{(-1)^k}{(2k+1)^2} = \frac{1}{1^2} - \frac{1}{3^2} + \frac{1}{5^2} - \frac{1}{7^2} + \cdots = 0.9159655941\ldots$$

We know $\pi$ is irrational (Lambert, 1761). We know $e$ is irrational (Euler, 1737). We know $\zeta(3)$ is irrational (Apery, 1978). In 2024, Calegari, Dimitrov, and Tang proved that $K = L(2, \chi_{-3})$ is irrational, the constant built from the Dirichlet character of conductor 3. But Catalan's $G = L(2, \chi_{-4})$, built from the character of conductor 4, resisted their method. The conductor is even. The prime 2 contaminates the denominator arithmetic in a way the odd-conductor case avoids.

The CDT team provided an adelic viewpoint of $G$ in their arithmetic-holonomy work but could not close the gap. They said so explicitly.

## What is not surprising and what is

The *result* is not surprising. Every number theorist expects $G$ to be irrational, and probably transcendental. The *method* is the surprise, if it holds. Sun does not use the Calegari-Dimitrov-Tang framework at all. No algebraic geometry. No $p$-adic analysis. No automorphic forms. Instead he builds a matrix directly from the tails of the series being studied, weighted by a factor of $1/(2m+1)$, and proves that if $G$ were rational, a certain sequence of nonzero integers would shrink below 1. The conceptual core, according to the author, came from conversations with AI.

---

## Jargon decoder

| Term | Translation |
|------|-------------|
| Dirichlet $L$-function | A generalization of the Riemann zeta function where each term is twisted by a periodic sign pattern. $G$ is $L(2, \chi_{-4})$: the sum $1/n^2$ with signs following $+, 0, -, 0, +, 0, -, 0, \ldots$ |
| Weighted tail | The tail of a series (what remains after chopping the first $m$ terms) divided by $2m+1$. Shrinks faster than the raw tail, better arithmetic properties. The central invention. |
| Residual matrix | A matrix whose entries encode differences between weighted tails at successive indices. If $G$ were rational, these entries would be "too nice" arithmetically. |
| Pascal-Cauchy factorization | The key determinant splits into a Pascal matrix (binomial coefficients) times a diagonal times a Cauchy matrix (entries $1/(x_i + y_j)$). Each factor has explicit, known structure. |
| Prime-power layer | For each prime $p$, how many times $p$ divides the key expression. The proof bounds these divisibilities by comparing an "actual" layer against a "test" layer from a reference set. |
| Positive-part bridge | Converting lower bounds on denominator divisibility into upper bounds on numerator height, via $[x]_+ = \max\{x, 0\}$. |
| $S/B = 1/20$ | The ratio of the two parameters controlling matrix dimensions. Fixed at $1/20$; $B \to \infty$. This ratio makes the final margin positive. |
| Interval arithmetic | Computing with intervals instead of floating-point numbers to guarantee rigorous bounds. Every intermediate value sits inside a provably correct interval. |

---

## The five-stage proof architecture

The proof is by contradiction. Assume $G = a/q$ with $a, q \in \mathbb{Z}^+$ and $\gcd(a,q) = 1$. Construct a sequence of nonzero integers $N_B$ whose absolute value eventually falls below 1. Impossible.

### Stage 1: Weighted residual matrix and full column rank

The recurrence $T_m + T_{m+1} = 1/(2m+1)^2$ is encoded in an $(S+3) \times S$ matrix $\mathcal{R}$ built from weighted tails $u_m = T_m / (2m+1)$. A polynomial-defect argument (no rational function satisfies the associated functional equation $R(X) + R(X+1) = 1/(2X+3)^2$) proves $\operatorname{rank} \mathcal{R} = S$. This guarantees a nonvanishing $S \times S$ minor exists.

### Stage 2: Newton completion and fixed scalar

Three binomial-Newton columns complete the selected minor into a square $(2B+S+3) \times (2B+S+3)$ matrix $\tilde{\mathcal{A}}_B$. Its determinant factors into known quantities times the "fixed scalar" $\hat{q}_B$. The minimal integerizer $H_B^{\min}$ is defined so that $q^S H_B^{\min} \hat{q}_B \in \mathbb{Z} \setminus \{0\}$.

### Stage 3: Pascal-Cauchy-Binet factorization

The Cauchy-Binet formula expands the residual determinant as a sum over $S$-element index sets $I$. Each summand $\Xi_I$ factors into a Vandermonde determinant (Pascal alternant), a Cauchy determinant ($1/(x+y)$ structure), and explicit factorial/tail factors. This makes the $p$-adic valuation of each summand computable.

### Stage 4: Local saturation and positive-part bridge

Theorem 5.1 is the technical core. For every odd prime power $Q$ and every $B \geq 20$, the denominator layer $a_{Q,B} \geq m^A_{Q,B}$ (the minimum local layer). The proof uses a residue-occupancy argument: the collision number of residue classes is minimized by balanced occupancy, invoking $\Phi_Q(n)$. This converts all local lower bounds on prime divisibility into a global upper bound on $\log H_B^{\min}$.

### Stage 5: Asymptotic ledger at $S/B = 1/20$

Three prime ranges evaluated separately:

**Small odd primes** ($Q \leq S$): exact integration over 178 merged cells yields $c_{\text{odd}} \approx 0.006276\ldots$ by interval arithmetic.

**Middle primes** ($S < p < B$): integration over 235 affine cells gives $\Lambda_{\text{mid}} \approx 0.17636\ldots$

**Large primes** ($p > B$): direct integration gives $\Delta_{>B} = 83/2400 \approx 0.03458\ldots$

The raw quadratic coefficient from Stirling's formula and the tail bounds is $4\rho - 2\rho^2 = 39/200$ at $\rho = 1/20$. The three corrections sum to more than $39/200$, leaving a strict positive margin:

$$\delta_0 > 0.00966242652523235$$

Therefore $\log|N_B| \leq -\delta_0 B^2 + o(B^2) \to -\infty$. Since $N_B \in \mathbb{Z} \setminus \{0\}$, contradiction. $\square$

---

## Where the proof is most fragile

**The interval arithmetic.** Proposition 6.3 is the single most delicate component. It partitions the unit interval into 238 raw cells (178 after merging adjacent identical formulas), evaluates exact rational antiderivatives involving the Hurwitz zeta function $\zeta(s, a)$, the digamma function $\psi$, and $\log \Gamma$, then bounds remainders using Euler-Maclaurin summation through the 24th Bernoulli number $B_{24}$. Any error in the cell boundaries, the piecewise formulas, or the remainder bounds invalidates the claimed interval for $I_{\text{odd}}$. This is where an independent recomputation would start.

**The math.GM posting.** The paper appears in arXiv's General Mathematics section, not Number Theory. math.GM is unmoderated and has historically hosted papers with errors. Not evidence against the proof, but it means the paper has not passed arXiv's NT moderators.

**AI verification versus formal verification.** The Acknowledgments section states that "the whole proof has passed the verification of ChatGPT 5.6 Solar." A language model is not a proof assistant. Its "verification" is categorically different from verification in Lean, Coq, or Isabelle. The author is candid about this, and about AI's role in the proof strategy: "the author's many rounds of conversations with AI provide the basis of this paper."

**The prime 2.** Lemma 5.4 handles $p = 2$ separately, showing that the 2-adic positive part is exactly zero. The argument relies on $\Pi_i$ being odd and on division by $2m+1$ preserving 2-integrality. This is the kind of prime-specific argument where an off-by-one or a sign error can hide.

**Implicit constants.** Lemma 5.5 (corrected full-row stability) introduces $o(B^2)$ when passing from the exact selected-row model to the consecutive ideal model. The implicit constants in this asymptotic are not tracked. The "sufficiently large $B$" in the final contradiction is not made explicit.

---

## What is new here

**Weighted tails as proof objects.** Standard irrationality proofs (Apery, Nesterenko, Rivoal, Zudilin) work with Pade approximants or hypergeometric constructions. Sun builds a matrix directly from the tails of the series under study, weighted to improve arithmetic divisibility. More elementary. If it generalizes, potentially more flexible.

**The local saturation principle.** Theorem 5.1's residue-occupancy argument, that the minimum of a certain function over $S$-element index sets is achieved or bounded by the balanced (consecutive) configuration, is a combinatorial inequality that may find applications beyond this proof. It replaces the detailed prime-by-prime analysis typical of irrationality proofs with a single uniform bound.

**AI as collaborator, not calculator.** Whatever the verdict on correctness, this paper is a data point for AI-assisted mathematics. The author credits AI with the key conceptual insight (weighted tails), not just computation. If verified, this would be the highest-profile mathematical result where AI played a substantive creative role in the proof strategy, not merely in brute-force search or formal verification.

---

## If it holds

The weighted-tail method could be attempted on other $L$-function values: $L(2, \chi_d)$ for various discriminants $d$, higher beta-function values $\beta(3)$, $\beta(4)$, and potentially $\zeta(5)$ or other odd zeta values. The method's reliance on the specific recurrence $T_m + T_{m+1} = 1/(2m+1)^2$ means adapting it requires finding analogous "nice" recurrences for other constants. The $S/B = 1/20$ ratio is not optimized. Tightening it might yield irrationality measures (quantitative bounds on how well $G$ can be approximated by rationals).

## If it has a gap

Even a flawed proof can advance the field if the architecture is sound and only the numerical verification fails. The residual-matrix construction, the Pascal-Cauchy factorization, and the local saturation principle are all independently interesting. A gap in the interval arithmetic for $c_{\text{odd}}$ or $\Lambda_{\text{mid}}$ might be fixable by more careful computation or by choosing a different $S/B$ ratio with more margin.

## Verification roadmap

1. Independently recompute $c_{\text{odd}}$ and $\Lambda_{\text{mid}}$ using a CAS with certified interval arithmetic (Arb/FLINT or SageMath with `RealBallField`).
2. Verify Theorem 5.1's combinatorial inequality.
3. Check the full-row stability argument in Lemma 5.5.
4. Formalize the finite-dimensional linear algebra (Sections 2 through 4) in Lean or Coq.

---

## Timeline

| Year | Event |
|------|-------|
| 1737 | Euler proves $e$ is irrational |
| 1761 | Lambert proves $\pi$ is irrational |
| ~1865 | Catalan introduces $G = \beta(2)$ |
| 1978 | Apery proves $\zeta(3)$ is irrational |
| 2024 | Calegari-Dimitrov-Tang prove $K = L(2, \chi_{-3})$ irrational |
| 2026 | Sun claims $G = L(2, \chi_{-4})$ irrational (**UNVERIFIED**) |

---

## Transparency

**Funding.** Natural Science Foundation of China (grant no. 12371004). No industry funding disclosed.

**Prior work.** Zhi-Wei Sun is a prolific conjecturer in combinatorial number theory. Some conjectures confirmed, some open. His series conjectures for $K$ (references [9], [12] in the paper) were confirmed by Hessami Pilehrood, Guillera, and Rogers, lending credibility.

**AI involvement.** The candid acknowledgment is commendable. The open question: how much of the conceptual architecture is the author's own versus AI-suggested? This is a form of disclosure the mathematical community has not yet developed norms for evaluating.

---

### Sources

- Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1 (3 Sep 2026)
- F. Calegari, V. Dimitrov, Y. Tang, *The linear independence of 1, $\zeta(2)$, and $L(2, \chi_{-3})$*, arXiv:2408.15403v2 (2024)
- Wikipedia, *Catalan's constant*
- Quanta Magazine, *Rational or Not? This Basic Math Question Took Decades to Answer* (8 Jan 2025)

---

*Daniyel Bilar, Chokmah LLC*
*ORCID [0000-0002-9040-6914](https://orcid.org/0000-0002-9040-6914)*
