"""Python re-implementation of CatalanSun.Thm51 layer definitions.

Mirrors the Lean defs verbatim so numeric gates test the *formalized*
quantities, not a paraphrase.  Cross-checked against thm_5_1 (aQB >= mAQ).

  Ndim B S    = 2B + S + 3            (NewtonCompletion.Ndim)
  NKQ K Q i   = #{1<=h<=K : Q | 2i+2h+1}
  phiQ Q n    = sum_{r<n} r//Q
  nQr Q r I   = #{i in I : i % Q == r % Q}
  CAQ B S Q f = sum_{a in f} (a + 2B)//Q
  FNQ N Q i   = i//Q + (N-1-i)//Q
  ind Q i     = [Q <= 2i+1]
  ellAQN      = CAQ + 2*sum_r C(nQr,2) + sum_{i in I}(2 NKQ(B) - NKQ(S) - 2 ind - FNQ)
  mAQ         = min over |I|=S subsets of Fin(Ndim)
  aQB B S Q   = 2*sum_{i<Ndim} NKQ(B,Q,i) - phiQ(Q, 2B)
"""
from itertools import combinations
from collections import Counter


def Ndim(B, S):
    return 2 * B + S + 3


def Ndim0(B, S):
    return 2 * B + S


def NKQ(K, Q, i):
    # #{1<=h<=K : Q | 2i+2h+1}.  2i+2h+1 runs over an arithmetic progression
    # of step 2; with Q odd, exactly floor(K/Q) or that +1 solutions.
    return sum(1 for h in range(1, K + 1) if (2 * i + 2 * h + 1) % Q == 0)


def phiQ(Q, n):
    return sum(r // Q for r in range(n))


def FNQ(N, Q, i):
    return i // Q + (N - 1 - i) // Q


def ind(Q, i):
    return 1 if Q <= 2 * i + 1 else 0


def CAQ(B, S, Q, f):
    return sum((a + 2 * B) // Q for a in f)


def ellAQN(B, S, Q, f, N, I):
    c = Counter(i % Q for i in I)
    coll = sum(v * (v - 1) // 2 for v in c.values())
    tail = sum(2 * NKQ(B, Q, i) - NKQ(S, Q, i) - 2 * ind(Q, i) - FNQ(N, Q, i)
               for i in I)
    return CAQ(B, S, Q, f) + 2 * coll + tail


def mAQ(B, S, Q, f):
    N = Ndim(B, S)
    return min(ellAQN(B, S, Q, f, N, I) for I in combinations(range(N), S))


def m0AQ(B, S, Q, f):
    """m^{(0)}: the MINIMUM at dimension Ndim0 (not the fixed consecutive set --
    see docs/FORMALIZATION-NOTES.md, the m0AQ scaffold bug)."""
    N0 = Ndim0(B, S)
    return min(ellAQN(B, S, Q, f, N0, I) for I in combinations(range(N0), S))


def aQB(B, S, Q):
    return 2 * sum(NKQ(B, Q, i) for i in range(Ndim(B, S))) - phiQ(Q, 2 * B)


def a0QB(B, S, Q):
    return 2 * sum(NKQ(B, Q, i) for i in range(Ndim0(B, S))) - phiQ(Q, 2 * B)


def odd_prime_powers(lo, hi):
    """(p, nu, p**nu) for odd primes p, nu>=1, lo <= p**nu <= hi."""
    if hi < 3:
        return []
    sieve = [True] * (hi + 1)
    sieve[0:2] = [False, False]
    for i in range(2, int(hi ** 0.5) + 1):
        if sieve[i]:
            for j in range(i * i, hi + 1, i):
                sieve[j] = False
    out = []
    for p in range(3, hi + 1, 2):
        if sieve[p]:
            q, nu = p, 1
            while q <= hi:
                if q >= lo:
                    out.append((p, nu, q))
                q *= p
                nu += 1
    return sorted(out, key=lambda t: t[2])
