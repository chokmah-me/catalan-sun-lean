"""How much ledger mass does the Q<5B truncation drop, and does it matter
asymptotically?  Uses S=1 (so mAQ's min is over N singletons: cheap) to reach
larger B than the exponential general case allows.
"""
from math import log
from layers import aQB, mAQ, Ndim, odd_prime_powers

print(f"{'B':>5} {'S':>2} {'in-range':>12} {'dropped':>10} {'drop%':>7} {'in/B^2':>8} {'drop/B^2':>9}")
for B in [20, 40, 80, 160, 320, 640]:
    S = 1
    f = list(range(S))
    N = Ndim(B, S)
    thr = 6 * B + 2 * S + 5
    inr = out = 0.0
    for (p, nu, Q) in odd_prime_powers(3, thr):
        d = max(aQB(B, S, Q) - mAQ(B, S, Q, f), 0)
        if not d:
            continue
        w = d * log(p)
        if Q < 5 * B:
            inr += w
        else:
            out += w
    pct = 100 * out / (inr + out) if inr + out else 0.0
    print(f"{B:>5} {S:>2} {inr:>12.1f} {out:>10.1f} {pct:>6.2f}% {inr/B**2:>8.3f} {out/B**2:>9.4f}")
