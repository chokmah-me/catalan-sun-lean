"""Stage 0 gate: what is the exact support of [aQB - mAQ]_+ in Q?

layerIndex B filters Q = p^nu < 5B.  If [a-m]_+ is nonzero for some odd prime
power Q >= 5B, that filter silently truncates the Cor 5.2 ledger.

Also re-validates thm_5_1 (aQB >= mAQ) as a free consistency check on this
Python reimplementation.
"""
from layers import aQB, mAQ, Ndim, odd_prime_powers

print(f"{'B':>4} {'S':>3} {'N':>5} {'5B':>6} {'2(N-1)+2B+1':>12} {'maxQ':>6} {'#Q>=5B':>7} {'thm51 viol':>10}")
for B in [20, 25, 30, 35, 40, 45]:
    S = max(1, B // 20)
    f = list(range(S))
    N = Ndim(B, S)
    cand = 2 * (N - 1) + 2 * B + 1
    maxQ = 0
    n_out = 0
    viol = 0
    for (p, nu, Q) in odd_prime_powers(3, 3 * cand):
        a = aQB(B, S, Q)
        m = mAQ(B, S, Q, f)
        if a < m:
            viol += 1                       # would contradict thm_5_1
        d = max(a - m, 0)
        if d != 0:
            maxQ = max(maxQ, Q)
            if Q >= 5 * B:
                n_out += 1
    flag = "" if maxQ <= cand else "  <-- EXCEEDS cand!"
    print(f"{B:>4} {S:>3} {N:>5} {5*B:>6} {cand:>12} {maxQ:>6} {n_out:>7} {viol:>10}{flag}")
