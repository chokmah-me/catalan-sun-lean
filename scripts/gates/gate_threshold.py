"""Is 2(N-1)+2B+1 the exact threshold, or just an upper bound?

Structural guess: aQB counts solutions of Q | 2i+2h+1 for i < N, 1<=h<=B.
The largest such modulus value is 2(N-1)+2B+1.  For Q above that, no
2i+2h+1 is divisible by Q (since 0 < 2i+2h+1 < Q), so NKQ == 0 for all i,
hence aQB = -phiQ(Q,2B) = 0 for Q > 2B.  So aQB = 0 above the threshold.
Verify: is EVERY odd prime power in [5B, threshold] nonzero?
"""
from layers import aQB, mAQ, Ndim, NKQ, odd_prime_powers

for B in [20, 30, 40]:
    S = max(1, B // 20)
    f = list(range(S))
    N = Ndim(B, S)
    thr = 2 * (N - 1) + 2 * B + 1
    rows = []
    for (p, nu, Q) in odd_prime_powers(5 * B, thr + 40):
        a = aQB(B, S, Q); m = mAQ(B, S, Q, f); d = max(a - m, 0)
        rows.append((Q, a, m, d, Q <= thr))
    nz_in = sum(1 for (_, _, _, d, ok) in rows if d and ok)
    z_in = sum(1 for (_, _, _, d, ok) in rows if not d and ok)
    nz_out = sum(1 for (_, _, _, d, ok) in rows if d and not ok)
    print(f"B={B:3d} thr={thr:4d}: in [5B,thr] -> {nz_in} nonzero, {z_in} zero;"
          f"  above thr -> {nz_out} nonzero")
    # also confirm aQB == 0 strictly above threshold
    bad = [Q for (p,nu,Q) in odd_prime_powers(thr+1, thr+200) if aQB(B,S,Q) != 0]
    print(f"        odd prime powers > thr with aQB != 0: {bad}")
