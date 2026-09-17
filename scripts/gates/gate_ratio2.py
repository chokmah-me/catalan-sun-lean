from math import log
from fast2 import aQBf, mAQf, opp

print("Paper regime S = B/20.  Ledger mass in-range (Q<5B) vs dropped (5B<=Q<=thr).")
print(f"{'B':>6} {'S':>4} {'in/B^2':>9} {'drop/B^2':>9} {'drop%':>7} {'#dropped':>9}")
for B in [100, 200, 400, 800, 1600, 3200]:
    S = B // 20
    f = list(range(S))
    thr = 6 * B + 2 * S + 5
    inr = out = 0.0
    nd = 0
    for (p, nu, Q) in opp(3, thr):
        d = aQBf(B, S, Q) - mAQf(B, S, Q, f)
        if d <= 0:
            continue
        w = d * log(p)
        if Q < 5 * B:
            inr += w
        else:
            out += w; nd += 1
    pct = 100 * out / (inr + out) if inr + out else 0.0
    print(f"{B:>6} {S:>4} {inr/B**2:>9.4f} {out/B**2:>9.4f} {pct:>6.2f}% {nd:>9}")
