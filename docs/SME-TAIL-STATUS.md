# Status note for the TailRecurrence author

**Repo (public):** https://github.com/chokmah-me/catalan-sun-lean  
**Your draft:** `incoming/TailRecurrence.lean` (archive stub; original Downloads file)  
**Live module:** [`CatalanSun/Tail.lean`](../CatalanSun/Tail.lean)

## What you handed off

A Lean 4 sketch of Sun eq. 1.4 from arXiv:2609.04176v1 §1:

- `oddReal`, `tailTerm`, `tail` \(T_m\), `weightedTail` \(u_m\)
- `tailTerm_shift` and the intended proof of `T_m + T_{m+1} = 1/(2m+1)^2`
- Status as received: **CAPABILITY-LIMITED** (not lake-built), two `sorry`s:
  1. `summable_tailTerm`
  2. `tail_pos`

The architecture of the recurrence proof was already right (`tsum_eq_zero_add` + shift + `linarith`). The two holes were the only blockers.

## What we did with it

We ported the draft into the Mathlib-pinned lake project (Lean 4.32.2 / Mathlib v4.32.2), dropped the barrel `import Mathlib`, and **discharged both sorries**. The module is on the default `CatalanSun` target.

| Your name | Now | How it was closed |
|-----------|-----|-------------------|
| `summable_tailTerm` | proved | \(\|t_{m,r}\| \le 1/(r+1)^2\), then `Real.summable_one_div_nat_add_rpow` + `Summable.of_norm_bounded` |
| `tail_pos` | proved | Consecutive pairs \(1/a^2 - 1/(a+2)^2 > 0\); even partial sums \(\ge\) first pair; pass to the tsum by `ge_of_tendsto` |
| `tail_add_succ` (eq. 1.4) | proved | Your sketch, using `Summable.tsum_eq_zero_add` on this Mathlib pin |
| `tail_lt_inv_sq` (eq. 1.3) | proved | Follows from eq. 1.4 + `tail_pos` on \(T_{m+1}\) |

`lean-proof-forge` on the repo: **pass** (0 `sorry`, axioms \(\subseteq\) `{propext, Classical.choice, Quot.sound}`). Load-bearing names: `CatalanSun.Tail.summable_tailTerm`, `tail_pos`, `tail_add_succ`, `tail_lt_inv_sq`.

## How this sits in the rest of the slice

Eq. 1.4 is the **definition layer** under the residual matrix. The same repo already has (sorry-free, but not the full paper):

- Ledger rationals \(39/200\), \(83/2400\)
- Lemma 5.4 **arithmetic core** (2-adic positive-part collapse + odd \(\Pi_i\)) — not yet the full residual-entry formula
- Cauchy determinant for \(n\le 2\) + odd-denom nonvanishing
- Theorem 2.1 **polynomial / constant-denominator** fragment of “no rational \(S_0\)”

**We do not claim Theorem 1.1** (\(G\notin\mathbb{Q}\)). Still out of Lean: full RatFunc pole-chain, general-\(n\) Cauchy, Props 6.3/7.4 interval arithmetic, Mertens/PNT, explicit \(B_0\).

## Suggested next Lean jobs (if you pick this up)

Highest leverage after your tail module:

1. ~~Residual entries \(R_{a,j}\) using `weightedTail`, then finish Lemma 5.4 (every \(q R_{a,j}\) is 2-integral when \(G\in\mathbb{Q}\)).~~
   **Entry-level done** in `CatalanSun/Residual.lean` (sorry-free): `Rmatrix B α j` implements eq. (2.1) directly from `weightedTail`, and `RmatrixRatWitness_twoIntegral` proves every entry `q·R_{α,j}` is 2-integral when `G = a/q`, via an induction on the eq. 1.4 recurrence (`ratWitness`) tracking `q·T_m` as an explicit rational — no need to construct the paper's finite partial sum `S_{m-1}`.
   **Still open:** the *det-level* Lemma 5.4 / Theorem 5.1, which needs `det R[A,J]` via the full Pascal–Cauchy factorization. Rank/Newton-completion (Thm 2.1, Cor 2.1, Prop 3.1), general-`n` Cauchy, and Cauchy–Binet are now in-repo; the remaining gap is the paper §4 Pascal–Cauchy factorization of the CB summands.
2. Full “no rational solution to \(S_0(z)+S_0(z+1)=1/(4z^2)\)” (pole chain), not just the polynomial case.
3. Independent of Lean: certified recomputation of \(c_{\mathrm{odd}}\) / \(\Lambda_{\mathrm{mid}}\) (Arb/Sage).

Build: `lake build` in the repo root.
