"""O(1) NKQ + DP minimizer + fast aQB.  Validated against layers.py."""
from math import log


def NKQf(K, Q, i):
    """#{1<=h<=K : Q | 2i+2h+1}, Q odd."""
    inv2 = pow(2, -1, Q)
    h0 = (inv2 * ((-2 * i - 1) % Q)) % Q
    if h0 == 0:
        h0 = Q
    return 0 if h0 > K else (K - h0) // Q + 1


def phiQf(Q, n):
    """sum_{r<n} r//Q  in closed form."""
    q, r = divmod(n, Q)
    return Q * (q * (q - 1) // 2) + q * r


def Ndim(B, S):
    return 2 * B + S + 3


def Ndim0(B, S):
    return 2 * B + S


def aQBf(B, S, Q):
    N = Ndim(B, S)
    return 2 * sum(NKQf(B, Q, i) for i in range(N)) - phiQf(Q, 2 * B)


def _g(B, S, Q, N, i):
    return (2 * NKQf(B, Q, i) - NKQf(S, Q, i)
            - (2 if Q <= 2 * i + 1 else 0) - (i // Q + (N - 1 - i) // Q))


def _min_at(B, S, Q, f, N):
    classes = {}
    for i in range(N):
        classes.setdefault(i % Q, []).append(_g(B, S, Q, N, i))
    costs = []
    for r, gs in classes.items():
        gs.sort()
        pref = [0]
        for v in gs[:S]:
            pref.append(pref[-1] + v)
        costs.append([pref[k] + k * (k - 1) if k < len(pref) else None
                      for k in range(S + 1)])
    INF = float('inf')
    dp = [0] + [INF] * S
    for c in costs:
        nd = [INF] * (S + 1)
        for used in range(S + 1):
            if dp[used] == INF:
                continue
            for k in range(0, S - used + 1):
                if c[k] is None:
                    break
                v = dp[used] + c[k]
                if v < nd[used + k]:
                    nd[used + k] = v
        dp = nd
    CAQ = sum((a + 2 * B) // Q for a in f)
    return CAQ + dp[S]


def mAQf(B, S, Q, f):
    return _min_at(B, S, Q, f, Ndim(B, S))


def opp(lo, hi):
    if hi < 3:
        return []
    sieve = bytearray([1]) * (hi + 1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(hi ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    out = []
    for p in range(3, hi + 1, 2):
        if sieve[p]:
            q, nu = p, 1
            while q <= hi:
                if q >= lo:
                    out.append((p, nu, q))
                q *= p
                nu += 1
    return out
