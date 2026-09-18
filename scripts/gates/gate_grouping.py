"""Reproduce the paper's Section 9 factor grouping term by term.

Prop 9.5's proof is one paragraph of prose:

  "The factorial, odd-linear, Cauchy, Vandermonde, and tail factors are then
   grouped by prime-power scale.  The B^2 log B terms cancel because the
   denominator baseline a_{Q,B} and the real normalization come from the same
   fixed scalar.  The remaining raw quadratic coefficient is 4rho-2rho^2=39/200."

No displayed derivation is given.  This script supplies one, by evaluating each
named factor of (4.5)=eq:summand separately and in the paper's own units.

  |Xi_I| = 2^{S(S-1)} V(J) V(I)^2 |Psi_A(I)|
           * prod_{a in A}(a+2B)! / prod_{i in I} i!(N-1-i)!
           * prod_{i in I} |q T_{i+1}| Pi_i / prod_{j=1}^{S} (2(i+j)+1)

The paper's five named groups map onto this as
  factorial   : prod_a (a+2B)! / prod_i i!(N-1-i)!
  cauchy      : 2^{S(S-1)} V(J)          (the Cauchy determinant prefactor)
  vandermonde : V(I)^2
  odd-linear  : prod_i Pi_i / prod_{i,j} (2(i+j)+1)
  tail        : prod_i |q T_{i+1}|

Psi_A(I) is an integer >= 1 in absolute value and is DROPPED here (the paper
likewise never bounds it below by more than 1); dropping it can only make
log|Xi_I| larger, so every coefficient below is an UPPER bound on the paper's
own quantity, which is the direction Prop 9.5 needs.

We evaluate at I = the consecutive block {0..S-1} (the "consecutive ideal
model" Lemma 5.5 licenses) and also at the argmax over a family of candidate
I, to check the "largest normalized summand" step.

Usage:  python gate_grouping.py B [B ...]
"""
import sys, os
from math import log, lgamma
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fast2 import Ndim  # noqa: E402

RHO = 1 / 20
LOG2 = log(2)


def lfac(n):
    return lgamma(n + 1)


def ldfact_odd(n):
    """log((2n+1)!!) = lgamma(2n+2) - n log 2 - lgamma(n+1)."""
    return lgamma(2 * n + 2) - n * LOG2 - lgamma(n + 1)


def log_T(m):
    """log T_m via trigamma:  T_m = (psi'((2m+1)/4) - psi'((2m+3)/4)) / 16.

    Validated against the alternating series to 1e-10 over m = 1..101; the
    series form is ~100x slower and was the original implementation.
    """
    return float(mp.log((mp.psi(1, (2 * m + 1) / mp.mpf(4))
                         - mp.psi(1, (2 * m + 3) / mp.mpf(4))) / 16))


def groups(B, I, S=None):
    """log of each named factor group of (4.5) at row set I."""
    if S is None:
        S = B // 20
    N = Ndim(B, S)
    A = list(range(S))

    # factorial: prod_{a in A} (a+2B)! / prod_{i in I} i! (N-1-i)!
    g_fact = sum(lfac(a + 2 * B) for a in A) - sum(lfac(i) + lfac(N - 1 - i) for i in I)

    # cauchy prefactor: 2^{S(S-1)} V(J),  V(J) = prod_{0<=u<v<S}(v-u) = superfactorial
    g_cauchy = S * (S - 1) * LOG2 + sum(lfac(k) for k in range(S))

    # vandermonde: V(I)^2
    g_vdm = 2 * sum(log(I[v] - I[u]) for u in range(S) for v in range(u + 1, S))

    # odd-linear: prod_{i in I} Pi_i / prod_{i in I} prod_{j=1}^S (2(i+j)+1)
    g_odd = 0.0
    for i in I:
        # 2*sum_{h=1..B} log(2(h+i)+1) in closed form (validated to 1e-12)
        g_odd += 2 * (ldfact_odd(B + i) - ldfact_odd(i))
        g_odd -= sum(log(2 * (i + j) + 1) for j in range(1, S + 1))

    # tail: prod_{i in I} |T_{i+1}|   (q is a fixed rational: O(S) = o(B^2))
    g_tail = sum(log_T(i + 1) for i in I)

    return dict(factorial=g_fact, cauchy=g_cauchy, vandermonde=g_vdm,
                odd_linear=g_odd, tail=g_tail,
                total=g_fact + g_cauchy + g_vdm + g_odd + g_tail)


def candidates(B, S, N):
    """A family of row sets to check the 'largest summand' step against."""
    yield "consecutive", list(range(S))
    yield "top", list(range(N - S, N))
    yield "centered", list(range((N - S) // 2, (N - S) // 2 + S))
    yield "spread", [round(k * (N - 1) / (S - 1)) for k in range(S)]


def compare(Bs):
    """Grouped route vs the direct LU route, using the recorded det R values."""
    import csv as _csv
    det = {}
    path = os.path.join(HERE, "data", "scalar_S_B20.csv")
    for r in _csv.reader(open(path)):
        det[int(r[0])] = dict(S=int(r[1]), logdet=float(r[2]), v2=int(r[3]),
                              m=float(r[4]), scalar=float(r[6]))
    print(f"{'B':>6} {'grouped/B2':>12} {'true logdetR/B2':>16} {'slack/B2':>10}"
          f" {'GROUPED SCAL':>13} {'TRUE SCAL':>11} {'Prop9.5 res':>12}")
    for B in sorted(Bs):
        if B not in det:
            continue
        d = det[B]; S = d["S"]; N = Ndim(B, S); B2 = B * B
        tot = max(groups(B, I, S)["total"] for _, I in candidates(B, S, N))
        gs = tot + d["v2"] * LOG2 - d["m"]
        print(f"{B:6d} {tot/B2:12.6f} {d['logdet']/B2:16.6f}"
              f" {(tot-d['logdet'])/B2:10.6f} {gs/B2:13.6f}"
              f" {d['scalar']/B2:11.6f} {(d['logdet']-d['m'])/B2:12.6f}")


def main():
    if sys.argv[1:] and sys.argv[1] == "compare":
        compare([int(x) for x in sys.argv[2:]] or [200, 400, 800, 1000, 1200])
        return
    for B in map(int, sys.argv[1:]):
        S = B // 20
        N = Ndim(B, S)
        B2 = B * B
        print(f"\n=== B={B} S={S} N={N} ===")
        best = None
        for name, I in candidates(B, S, N):
            g = groups(B, I, S)
            if best is None or g["total"] > best[1]["total"]:
                best = (name, g)
            print(f"  {name:12s} total/B^2 = {g['total']/B2:+.6f}")
        name, g = best
        print(f"  -> argmax: {name}")
        for k in ("factorial", "cauchy", "vandermonde", "odd_linear", "tail"):
            print(f"     {k:12s} {g[k]/B2:+.6f} B^2")
        print(f"     {'TOTAL':12s} {g['total']/B2:+.6f} B^2")
        print(f"     paper raw quadratic 4rho-2rho^2 = {4*RHO-2*RHO**2:+.6f}")


if __name__ == "__main__":
    main()
