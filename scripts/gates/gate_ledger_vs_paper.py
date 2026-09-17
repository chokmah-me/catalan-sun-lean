"""Exact (5.24) ledger at the paper's regime S = B/20, compared against the
paper's Sections 7-8 densities.

Two modes.

  python gate_ledger_vs_paper.py compute OUT.csv [B ...]
      One CSV row per nonzero layer: B, S, p, nu, Q, aQB, mAQ, [a-m]_+ log p.
      The mAQ minimisation is the expensive part (B=1200 takes ~1 min), so it
      runs once and everything else re-slices the CSV.

  python gate_ledger_vs_paper.py analyze OUT.csv
      Prints (a) the raw ledger / B^2 by the paper's three ranges, and (b)
      trapezoid-in-t integrals of the exact m/B profile over primes, which
      remove prime-discreteness noise, against the paper's Lambda_mid (7.14),
      the large-range integral (8.2), and the tail above (2+rho)B that
      Section 8 does not integrate.

What this established (2026-09-17, B = 200..1200):
  * The raw ledger sum(a-m) log p / B^2 is ~18..21 and grows like log B. That
    is expected: Prop 9.5 says the B^2 log B part of sum a log p cancels
    against log|q_hat_B|, so the raw ledger is NOT the paper's coefficient.
  * The m-density is the paper's E_rho(t): int_rho^1 m/B -> 0.1743 at B=1200
    vs Lambda_mid = 0.17636 (7.14), and int_1^{2+rho} m/B = -0.06986 vs
    (8.2) = -0.06979. The (8.1) branch values (-2rho on (1+rho,4/3), -rho on
    (4/3+.., 2), -2rho near 2+rho) are visible per prime.
  * Section 8 integrates only 1 < t < 2+rho. Above (2+rho)B the exact layers
    are not zero: m = -2S exactly for every prime in ((2+rho)B, 4B) (the term
    -2*1_{Q <= 2i+1} of (5.7) fires on S rows), so -sum m log p over the tail
    is +2rho(2-rho) B^2 = +0.195 B^2 = +(39/200) B^2 -- numerically identical
    to the paper's raw quadratic (9.4). Whether that is bookkeeping (already
    inside 39/200) or an omission (20x delta_0) cannot be decided without the
    fixed scalar q_hat_B; see docs/FORMALIZATION-NOTES.md#tail-band.
"""
import sys, csv, time
from math import log
from collections import defaultdict

RHO = 1 / 20
LAMBDA_MID = 0.17635583793          # (7.15)-(7.16)
INT_82 = -(4 / 3) * RHO - (5 / 4) * RHO ** 2   # (8.2)
RAW_94 = 4 * RHO - 2 * RHO ** 2     # (9.4) = 39/200


def compute(out, Bs):
    from fast2 import aQBf, mAQf, opp
    with open(out, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["B", "S", "p", "nu", "Q", "aQB", "mAQ", "term"])
        for B in Bs:
            t0 = time.time()
            S = B // 20
            f = list(range(S))
            thr = 6 * B + 2 * S + 5
            tot = 0.0
            for (p, nu, Q) in opp(3, thr):
                a = aQBf(B, S, Q)
                m = mAQf(B, S, Q, f)
                d = a - m
                if d < 0:
                    print(f"!! thm_5_1 violated at B={B} Q={Q}", file=sys.stderr)
                if d <= 0:
                    continue
                term = d * log(p)
                w.writerow([B, S, p, nu, Q, a, m, f"{term:.6f}"])
                tot += term
            fh.flush()
            print(f"B={B:5d} S={S:3d}  total/B^2={tot/B**2:.6f}  [{time.time()-t0:.0f}s]", flush=True)


def trap(pts):
    s = 0.0
    for (t0, y0), (t1, y1) in zip(pts, pts[1:]):
        s += (t1 - t0) * (y0 + y1) / 2
    return s


def analyze(path):
    rows = list(csv.DictReader(open(path)))
    byB = defaultdict(list)
    for r in rows:
        byB[int(r["B"])].append(r)

    print("(a) raw ledger / B^2 by range  [primes only for mid/large; nu>=2 and Q<=S separate]")
    print(f"{'B':>5} {'total':>8} | {'Q<=S (a-m)':>10} {'nu>=2,p>S':>10} | {'mid m':>8} {'mid a':>8} | "
          f"{'lg m':>8} {'lg a':>8} | {'tail m':>8} {'tail a':>8}")
    for B in sorted(byB):
        S = B // 20
        acc = defaultdict(float)
        for r in byB[B]:
            p, nu, Q, a, m = (int(r[k]) for k in ("p", "nu", "Q", "aQB", "mAQ"))
            lp = log(p)
            acc["tot"] += (a - m) * lp
            if Q <= S:
                acc["sm"] += (a - m) * lp
                continue
            if nu >= 2:
                acc["hi"] += (a - m) * lp
                continue
            k = "mid" if p < B else ("lg" if p < (2 + RHO) * B else "tail")
            acc[k + "_m"] += m * lp
            acc[k + "_a"] += a * lp
        b2 = B * B
        print(f"{B:>5} {acc['tot']/b2:8.3f} | {acc['sm']/b2:10.4f} {acc['hi']/b2:10.4f} | "
              f"{acc['mid_m']/b2:8.4f} {acc['mid_a']/b2:8.4f} | {acc['lg_m']/b2:8.4f} {acc['lg_a']/b2:8.4f} | "
              f"{acc['tail_m']/b2:8.4f} {acc['tail_a']/b2:8.4f}")

    print("\n(b) trapezoid-in-t integrals of the exact m/B profile over primes, vs the paper")
    print(f"{'B':>5} {'int m/B (rho,1)':>15} {'Lambda_mid':>11} | {'int m/B (1,2+rho)':>17} {'(8.2)':>9} | "
          f"{'int m/B (2+rho,thr)':>19} {'-2rho(2-rho)':>13}")
    for B in sorted(byB):
        pts = sorted((int(r["p"]) / B, int(r["mAQ"]) / B) for r in byB[B] if int(r["nu"]) == 1)
        mid = [(t, y) for t, y in pts if RHO < t < 1]
        lg = [(t, y) for t, y in pts if 1 < t < 2 + RHO]
        top = [(t, y) for t, y in pts if t > 2 + RHO]
        print(f"{B:>5} {trap(mid):15.5f} {LAMBDA_MID:11.5f} | {trap(lg):17.5f} {INT_82:9.5f} | "
              f"{trap(top):19.5f} {-2*RHO*(2-RHO):13.5f}")
    print(f"\n39/200 = {RAW_94}   2rho(2-rho) = {2*RHO*(2-RHO)}   (identical: 4rho-2rho^2 = 2rho(2-rho))")

    print("\n(c) B=max: mean m/B and a/B by t-bin for p > B")
    B = max(byB)
    rows1 = [r for r in byB[B] if int(r["nu"]) == 1 and int(r["p"]) > B]
    bins = [(1, 1 + RHO / 2), (1 + RHO / 2, 1 + RHO), (1 + RHO, 4 / 3), (4 / 3, 2), (2, 2 + RHO),
            (2 + RHO, 3), (3, 4), (4, 5), (5, 6), (6, 6.2)]
    for lo, hi in bins:
        sel = [r for r in rows1 if lo < int(r["p"]) / B <= hi]
        if not sel:
            continue
        mm = sum(int(r["mAQ"]) for r in sel) / len(sel) / B
        aa = sum(int(r["aQB"]) for r in sel) / len(sel) / B
        print(f"  t in ({lo:6.4f},{hi:6.4f}]  n={len(sel):3d}  m/B={mm:8.4f}  a/B={aa:8.4f}")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "compute"
    if mode == "compute":
        compute(sys.argv[2], [int(x) for x in sys.argv[3:]] or [200, 400, 800, 1200])
    elif mode == "analyze":
        analyze(sys.argv[2])
    else:
        sys.exit(__doc__)
