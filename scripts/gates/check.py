"""Regression check for the CatalanSun numeric gates.

Run this before trusting any gate result, and after any change to the Lean
layer definitions (`Thm51.lean`'s `NKQ`/`phiQ`/`nQr`/`CAQ`/`FNQ`/`ellAQN`/
`mAQ`/`aQB`, or `Lemma55.lean`'s `Ndim0`/`a0QB`/`m0AQ`).

    python scripts/gates/check.py

It asserts three things:

1. `fast2.py` (O(1) NKQ + exact DP minimizer) agrees with `layers.py`
   (verbatim brute-force mirror of the Lean defs) on every layer of a small
   grid.  This is what licenses using `fast2` to reach B=1200, where the
   brute-force `C(2B+S+3, S)` minimum is hopeless.

2. `thm_5_1` holds numerically: `aQB >= mAQ` on every layer tested.  This is a
   FREE consistency check of the Python mirror against proved Lean -- if it
   ever fails, the mirror has drifted from the Lean definitions, not the other
   way round.

3. The support threshold: `[aQB - mAQ]_+` is nonzero somewhere in
   `[5B, layerBound]` and identically zero above `layerBound = 6B+2S+5`.
   This is the finding that forced `Cor52` off `Lemma55.layerIndex`.

Exit code 0 = all pass.  Non-zero = something drifted; read the output.
"""
import sys

from layers import aQB, mAQ, odd_prime_powers
from fast2 import aQBf, mAQf

# Small enough that brute force is tractable: C(Ndim, S) with S <= 2.
GRID = [(20, 1), (24, 2), (30, 1), (40, 2)]


def layer_bound(B, S):
    """The exact support cutoff, = 2*(Ndim B S - 1) + 2B + 1."""
    return 6 * B + 2 * S + 5


def check_fast_matches_brute():
    """fast2 must reproduce layers.py exactly."""
    bad = 0
    n = 0
    for B, S in GRID:
        f = list(range(S))
        for (p, nu, Q) in odd_prime_powers(3, layer_bound(B, S)):
            n += 1
            if aQBf(B, S, Q) != aQB(B, S, Q):
                print(f"  FAIL aQB  B={B} S={S} Q={Q}")
                bad += 1
            if mAQf(B, S, Q, f) != mAQ(B, S, Q, f):
                print(f"  FAIL mAQ  B={B} S={S} Q={Q}")
                bad += 1
    print(f"[1] fast2 vs brute force: {n} layers, {bad} mismatches")
    return bad == 0


def check_thm_5_1():
    """aQB >= mAQ everywhere -- the proved Lean theorem, as a mirror check."""
    viol = 0
    n = 0
    for B, S in GRID:
        f = list(range(S))
        for (p, nu, Q) in odd_prime_powers(3, layer_bound(B, S)):
            n += 1
            if aQB(B, S, Q) < mAQ(B, S, Q, f):
                print(f"  FAIL thm_5_1  B={B} S={S} Q={Q}")
                viol += 1
    print(f"[2] thm_5_1 (aQB >= mAQ): {n} layers, {viol} violations")
    return viol == 0


def check_support_threshold():
    """Nonzero layers exist in [5B, thr]; nothing is nonzero above thr."""
    ok = True
    for B, S in GRID:
        f = list(range(S))
        thr = layer_bound(B, S)
        band = [Q for (p, nu, Q) in odd_prime_powers(5 * B, thr)
                if max(aQBf(B, S, Q) - mAQf(B, S, Q, f), 0) != 0]
        above = [Q for (p, nu, Q) in odd_prime_powers(thr + 1, thr + 400)
                 if max(aQBf(B, S, Q) - mAQf(B, S, Q, f), 0) != 0]
        if not band:
            print(f"  FAIL B={B} S={S}: expected nonzero layers in [5B, thr]")
            ok = False
        if above:
            print(f"  FAIL B={B} S={S}: nonzero above thr={thr}: {above[:5]}")
            ok = False
        print(f"    B={B:3d} S={S}: {len(band)} nonzero in [5B={5*B}, thr={thr}],"
              f" {len(above)} above thr")
    print(f"[3] support threshold 6B+2S+5: {'ok' if ok else 'FAILED'}")
    return ok


def main():
    print("CatalanSun gate regression check")
    print("=" * 52)
    results = [
        check_fast_matches_brute(),
        check_thm_5_1(),
        check_support_threshold(),
    ]
    print("=" * 52)
    if all(results):
        print("PASS: all gates consistent with the Lean definitions.")
        return 0
    print("FAIL: a gate drifted. The Python mirror probably no longer")
    print("matches the Lean layer definitions -- re-read Thm51.lean.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
