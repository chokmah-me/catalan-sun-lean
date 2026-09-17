"""Gate for re-proving (5.3) over `layerIndexFull B S` (cutoff 6B+2S+5).

The Lean proof (Cor52.lean, Stage F) uses the crudest bound with every layer
quantity capped by `12*B`:

    L := layerBound B (B/20) = 6B + 2*(B/20) + 5   <= 12*B   (B >= 1)
    #layers <= L <= 12B,   sum 1/Q <= harmonic(L) <= 1 + log(12B),
    log p <= log Q <= log(12B)

    SUM <= 111 * log(12B) * ( B*(1 + log 12B) + 12B )
         = 111 * B * log(12B) * (13 + log 12B)

This script checks (a) the `L <= 12B` arithmetic exhaustively for small B and
(b) that RHS/B^2 decays to 0, i.e. the bound is genuinely o(B^2). It is a
sanity gate on the *bound*, not on the layer definitions (see check.py).
"""
import math
import sys

bad = [B for B in range(1, 100_000) if 6 * B + 2 * (B // 20) + 5 > 12 * B]
print(f"[1] layerBound B (B/20) <= 12B for 1 <= B < 100000: {'ok' if not bad else bad[:5]}")

prev = None
mono = True
for B in [10**2, 10**3, 10**4, 10**5, 10**6, 10**7, 10**8]:
    L = math.log(12 * B)
    rhs = 111 * B * L * (13 + L)
    r = rhs / B**2
    old = 111 * B * math.log(5 * B) * (6 + math.log(5 * B)) / B**2
    print(f"    B={B:>10}  RHS/B^2 = {r:9.4f}   (old 5B bound: {old:9.4f}, ratio {r/old:.2f})")
    if prev is not None and r >= prev:
        mono = False
    prev = r
print(f"[2] RHS/B^2 strictly decreasing over the sweep: {'ok' if mono else 'FAIL'}")

ok = (not bad) and mono and prev is not None and prev < 1e-3
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
