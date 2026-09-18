"""Decompose the measured SCALAR/B^2 into its two independent components.

Answers the question "is the paper's B^2 failure exactly Remark 9.3's
mispriced 2-adic constant?"  It is not.  Writing the measured coefficient as

    SCALAR/B^2  =  [ v2(F_B) log2 / B^2 ]  +  [ log|det R|/B^2 - sum m log p/B^2 ]

the first bracket -> 2 log 2 = 1.3863 (Remark 9.3's term, mispriced 221x) and
the second is FLAT at about +0.475 across B = 200..1000 -- a second, wholly
separate gap of ~50x delta_0 living in Proposition 9.5's cancellation, which
fires (the two halves track to ~5% per doubling) but does not close.

Repairing Remark 9.3 alone would leave Theorem 9.1 failing by ~50x.

Reads the committed table; no recomputation.  See
docs/FORMALIZATION-NOTES.md#two-components.
"""
from math import log

LOG2 = log(2)
DELTA0 = 0.00966242652523235

# B, log|det R|/B^2, v2(F_B)log2/B^2, -sum m log p/B^2, SCALAR/B^2
TABLE = [
    (200,  0.475164, 1.353994, -0.003012, 1.826146),
    (400,  0.544358, 1.368411, -0.066843, 1.845926),
    (800,  0.613610, 1.376486, -0.138860, 1.851237),
    (1000, 0.635912, 1.378071, -0.159963, 1.854020),
]


def main():
    print(f"delta_0 needed: {-DELTA0:+.6f}    2log2 = {2*LOG2:.6f}\n")
    print("  B     SCALAR    -2log2 =   resid    | detR - sum_m   v2log2-2log2")
    for B, d, v, m, s in TABLE:
        print(f"{B:5d}  {s:+.6f}  {s-2*LOG2:+.6f}  |  {d+m:+.6f}     {v-2*LOG2:+.6f}")

    flat = [d + m for _, d, _, m, _ in TABLE]
    lo, hi = min(flat), max(flat)
    print(f"\nsecond component (detR - sum m): flat in [{lo:+.6f}, {hi:+.6f}]"
          f"  spread {hi-lo:.4f}")
    print(f"  = {(lo+hi)/2/DELTA0:.0f}x delta_0, wrong sign")

    res = [(B, s - 2 * LOG2) for B, _, _, _, s in TABLE]
    print("\nc+k/B fits on successive pairs of the residual:")
    for (b1, v1), (b2, v2) in zip(res, res[1:]):
        k = (v2 - v1) / (1 / b2 - 1 / b1)
        print(f"  {b1:5d},{b2:5d} -> c = {v1 - k/b1:+.6f}")

    print("\nVERDICT: two independent components, not one.")
    print(f"  2log2 (Remark 9.3, 221x off) = {2*LOG2:+.6f}")
    print(f"  Prop 9.5 residue             = {(lo+hi)/2:+.6f}")
    print(f"  total                        = {2*LOG2+(lo+hi)/2:+.6f}"
          f"   (needs {-DELTA0:+.6f})")


if __name__ == "__main__":
    main()
