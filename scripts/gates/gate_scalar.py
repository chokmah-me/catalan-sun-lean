"""Direct numerical test of the paper's reduced B^2 claim (Prop 9.5 / Thm 9.1).

Derivation (paper eqs.; nothing here is Lean):

  (3.5)   qhat_B = +- F_B det R[A,J] / prod_i Pi_i
  (5.24)  log H_B^min <= sum_{p odd, nu} (a_{p^nu,B} - m^A_{p^nu,B}) log p
  (5.13)  sum_nu a_{p^nu,B} = v_p(prod Pi_i) - v_p(F_B)      (p odd)

Summing (5.13) over odd p:  sum_{odd Q} a_Q log p
     = log prod Pi_i - log F_B + v_2(F_B) log 2,
because Pi_i is odd and only the odd part of F_B is counted.  Adding (3.5):

  log H_B^min + log|qhat_B|
     <= log|det R[A,J]| + v_2(F_B) log 2 - sum_{odd Q} m_Q log p   (+ O(B) from q^S).

So Theorem 9.1's  log H + log|qhat| <= -delta_0 B^2 + o(B^2), *as the paper
proves it* (through (5.24)), is exactly the claim

  SCALAR(B) := log|det R[A,J]| + v_2(F_B) log 2 - sum_{odd Q} m_Q log p
            <= -delta_0 B^2 + o(B^2),      delta_0 > 0.00966.

Everything on the left is computable with no choice of I and no Cauchy-Binet
maximum:  the m_Q are the committed fast2 mirror (all odd prime powers Q, not
just the a-m>0 rows the ledger CSV keeps), v_2(F_B) is Legendre, and

  R_{a,j} = sum_i (-1)^i C(a+2B,i) Pi_i u_{i+j},   u_m = T_m/(2m+1),
  T_m = sum_{r>=0} (-1)^r/(2(m+r)+1)^2 = (-1)^m (G - P_m),
  P_m = sum_{k<m} (-1)^k/(2k+1)^2,

so R_{a,j} = (-1)^j (X_{a,j} G - Y_{a,j}) with X, Y exact rationals.  X and Y
are computed as exact integers over the common denominator D = L^3,
L = lcm of the odd numbers up to 2(N+S)+1; only G is floating, at `prec`
bits, and det is an mpmath LU at that precision.  The run is repeated at a
higher precision and accepted only if log|det R| agrees.

Modes
  python gate_scalar.py layers B ...        recompute all m_Q, a_Q (cached CSV)
  python gate_scalar.py detR B [P_bits]     log|det R[A,J]| with A={0..S-1} (fixed point)
  python gate_scalar.py detR-exact B prec   the same via exact X,Y (slow reference)
  python gate_scalar.py scalar B ...        the full verdict table
"""
import sys, os, csv, time
from math import log, lgamma, gcd
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fast2 import aQBf, mAQf, opp, Ndim  # noqa: E402

DATA = os.path.join(HERE, "data")
RHO = 1 / 20
DELTA0 = 0.00966242652523235
LOG2 = log(2)


# ---------------------------------------------------------------- layers
def layers_path(B):
    return os.path.join(DATA, f"layers_all_S_B20_B{B}.csv")


def compute_layers(B):
    """All odd prime powers Q <= 6B+2S+5 (= Lean layerBound), including a=m rows."""
    S = B // 20
    f = list(range(S))
    thr = 6 * B + 2 * S + 5
    path = layers_path(B)
    t0 = time.time()
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["B", "S", "p", "nu", "Q", "aQB", "mAQ"])
        for (p, nu, Q) in opp(3, thr):
            a = aQBf(B, S, Q)
            m = mAQf(B, S, Q, f)
            if a < m:
                print(f"!! thm_5_1 violated at B={B} Q={Q}", file=sys.stderr)
            w.writerow([B, S, p, nu, Q, a, m])
    print(f"layers B={B}: {time.time()-t0:.0f}s -> {path}", flush=True)


def load_layers(B):
    path = layers_path(B)
    if not os.path.exists(path):
        compute_layers(B)
    rows = list(csv.DictReader(open(path)))
    return [(int(r["p"]), int(r["nu"]), int(r["Q"]), int(r["aQB"]), int(r["mAQ"]))
            for r in rows]


# ---------------------------------------------------------------- exact pieces
def v2_factorial_product(B):
    """v_2(F_B), F_B = prod_{r<2B} r!  (Legendre)."""
    tot = 0
    for r in range(2 * B):
        p = 2
        while p <= r:
            tot += r // p
            p *= 2
    return tot


def lcm_odd_upto(n):
    L = 1
    for k in range(1, n + 1, 2):
        L = L * k // gcd(L, k)
    return L


def pi_factors(B, N):
    """Pi_i = prod_{h=1}^{B} (2(h+i)+1)^2 for i < N, exact ints (incremental)."""
    Pi = [0] * N
    v = 1
    for h in range(1, B + 1):
        v *= (2 * h + 1) ** 2
    Pi[0] = v
    for i in range(1, N):
        # Pi_i / Pi_{i-1} = (2(B+i)+1)^2 / (2i+1)^2
        v = v * (2 * (B + i) + 1) ** 2 // (2 * i + 1) ** 2
        Pi[i] = v
    return Pi


def det_R_exact(B, prec, S=None, A=None, verbose=True):
    """log|det R[A,J]| with X, Y as exact integers and G at `prec` bits.
    Reference implementation; O(S^2 N) products of ~50k-bit integers, so it is
    slow past B=400.  Validated against brute-force polygamma sums at
    B=20,40,60 (1e-13) and against det_R at B=200,400."""
    if S is None:
        S = B // 20
    if A is None:
        A = list(range(S))
    N = Ndim(B, S)
    t0 = time.time()
    M = 2 * (N + S) + 1                       # largest 2m+1 that occurs (m <= N-1+S)
    L = lcm_odd_upto(M)
    L2 = L * L
    PL2 = [0] * (N + S + 1)
    acc = 0
    for m in range(N + S + 1):
        PL2[m] = acc
        term = L2 // (2 * m + 1) ** 2
        acc += term if m % 2 == 0 else -term
    Lodd = [L // (2 * m + 1) for m in range(N + S + 1)]
    W = [PL2[m] * Lodd[m] for m in range(N + S + 1)]
    Pi = pi_factors(B, N)
    X = [[0] * S for _ in A]
    Y = [[0] * S for _ in A]
    for ra, a in enumerate(A):
        n = a + 2 * B
        c = 1
        for i in range(n + 1):
            if i > 0:
                c = c * (n - i + 1) // i
            cp = c * Pi[i]
            Xr = X[ra]
            Yr = Y[ra]
            for jj in range(S):
                m = i + jj + 1
                Xr[jj] += cp * Lodd[m]
                Yr[jj] += cp * W[m]
    # entries: R_{a,j} = (-1)^j (X L^2 G - Y) / D ,  D = L^3
    D = L * L2
    xbits = max(x.bit_length() for r in X for x in r) + L2.bit_length()
    mp.mp.prec = prec
    G = +mp.catalan
    E = mp.matrix(S, S)
    ebits_min = None
    for ra in range(S):
        for jj in range(S):
            e = mp.mpf(X[ra][jj] * L2) * G - mp.mpf(Y[ra][jj])
            E[ra, jj] = e
            eb = mp.mag(e) if e != 0 else mp.mpf("-inf")
            ebits_min = eb if ebits_min is None else min(ebits_min, eb)
    det = mp.det(E)
    logabs = float(mp.log(abs(det))) - S * log(D) if det != 0 else float("-inf")
    info = dict(S=S, N=N, xbits=xbits, ebits_min=float(ebits_min), prec=prec,
                secs=time.time() - t0)
    if verbose:
        print(f"  exact prec={prec}  X~2^{xbits}  min|E|~2^{float(ebits_min):.0f}  "
              f"log|det R|={logabs:.6f}  [{info['secs']:.0f}s]", flush=True)
    return logabs, info


def det_R(B, P, S=None, A=None, verbose=True):
    """log|det R[A,J]| in fixed point: u_m as integers scaled by 2^P (from G at
    P+64 bits and truncated 1/(2k+1)^2), the binomials and Pi_i exact, so each
    entry R_{a,j} 2^P is an exact integer sum with absolute error
    <= (N+S)^2 max|c_{a,i}| 2^-P.  det by mpmath LU at P bits.  Returns
    (log|det R|, info); info['cancel_bits'] is how many bits the alternating
    sum cancels, which P must exceed with margin (det_R_verified checks it
    by rerunning at a higher P)."""
    if S is None:
        S = B // 20
    if A is None:
        A = list(range(S))
    N = Ndim(B, S)
    t0 = time.time()
    mp.mp.prec = P + 64
    G = +mp.catalan
    Gs = int(mp.floor(mp.ldexp(G, P)))
    one = 1 << P
    U = [0] * (N + S + 1)
    acc = 0
    for m in range(N + S + 1):
        T = (Gs - acc) if m % 2 == 0 else (acc - Gs)     # T_m 2^P > 0
        U[m] = T // (2 * m + 1)
        t = one // (2 * m + 1) ** 2
        acc += t if m % 2 == 0 else -t
    Pi = pi_factors(B, N)
    Rm = [[0] * S for _ in A]
    maxterm = 0
    for ra, a in enumerate(A):
        n = a + 2 * B
        c = 1
        row = Rm[ra]
        for i in range(n + 1):
            if i > 0:
                c = c * (n - i + 1) // i
            cp = c * Pi[i]
            if cp.bit_length() > maxterm:
                maxterm = cp.bit_length()
            if i % 2:
                cp = -cp
            for jj in range(S):
                row[jj] += cp * U[i + jj + 1]
    maxterm += U[1].bit_length()               # bits of the largest single term
    minent = min(abs(x).bit_length() for r in Rm for x in r)
    mp.mp.prec = P
    E = mp.matrix(S, S)
    for ra in range(S):
        for jj in range(S):
            E[ra, jj] = mp.mpf(Rm[ra][jj])
    det = mp.det(E)
    logabs = float(mp.log(abs(det))) - S * P * LOG2 if det != 0 else float("-inf")
    info = dict(S=S, N=N, P=P, maxterm_bits=maxterm, minentry_bits=minent,
                cancel_bits=maxterm - minent, secs=time.time() - t0)
    if verbose:
        print(f"  P={P}  max term 2^{maxterm}  min entry 2^{minent}  "
              f"(cancels {maxterm-minent} bits)  log|det R|={logabs:.6f}  "
              f"[{info['secs']:.0f}s]", flush=True)
    return logabs, info


def det_R_verified(B, P0=None):
    """det_R at P0 and at 1.6*P0+8000; accept when log|det R| agrees to 1e-9
    relative and the cancellation is under P0/2."""
    P = int(P0) if P0 else 20000
    prev = None
    for _ in range(6):
        v, info = det_R(B, P)
        if prev is not None and info["cancel_bits"] < P / 2 and abs(v - prev) <= 1e-9 * max(1.0, abs(v)):
            info["prec"] = P
            return v, info
        prev = v
        P = int(P * 1.6) + 8000
    raise RuntimeError("det_R did not stabilise")


# ---------------------------------------------------------------- verdict
def scalar(B, prec=None):
    S = B // 20
    N = Ndim(B, S)
    rows = load_layers(B)
    m_all = sum(m * log(p) for (p, nu, Q, a, m) in rows)
    m_upto = sum(m * log(p) for (p, nu, Q, a, m) in rows if Q <= (2 + RHO) * B)
    a_all = sum(a * log(p) for (p, nu, Q, a, m) in rows)
    am_pos = sum((a - m) * log(p) for (p, nu, Q, a, m) in rows if a > m)
    v2 = v2_factorial_product(B)
    # consistency: sum_odd a log p  ==  log prod Pi - log F_B + v2 log 2  (5.13 summed)
    logPi = sum(2 * sum(log(2 * (h + i) + 1) for h in range(1, B + 1)) for i in range(N))
    logFB = sum(lgamma(r + 1) for r in range(2 * B))
    lhs513 = logPi - logFB + v2 * LOG2
    logdet, info = det_R_verified(B, prec)
    scal = logdet + v2 * LOG2 - m_all
    scal_upto = logdet + v2 * LOG2 - m_upto
    return dict(B=B, S=S, N=N, logdet=logdet, v2=v2, m_all=m_all, m_upto=m_upto,
                a_all=a_all, am_pos=am_pos, check513=(a_all, lhs513),
                scalar=scal, scalar_upto=scal_upto, info=info)


def main():
    mode = sys.argv[1]
    if mode == "layers":
        for B in map(int, sys.argv[2:]):
            compute_layers(B)
    elif mode == "detR":
        B = int(sys.argv[2])
        prec = int(sys.argv[3]) if len(sys.argv) > 3 else None
        if prec:
            det_R(B, prec)
        else:
            det_R_verified(B)
    elif mode == "detR-exact":
        det_R_exact(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "scalar":
        out = []
        for B in map(int, sys.argv[2:]):
            r = scalar(B)
            out.append(r)
            B2 = B * B
            print(f"\nB={B} S={r['S']} N={r['N']}")
            print(f"  (5.13) check: sum_odd a log p = {r['check513'][0]:.3f}   "
                  f"log prodPi - log F_B + v2 log2 = {r['check513'][1]:.3f}")
            print(f"  log|det R|/B^2          = {r['logdet']/B2:+.6f}")
            print(f"  v2(F_B) log2 /B^2       = {r['v2']*LOG2/B2:+.6f}")
            print(f"  -sum m log p /B^2 (all) = {-r['m_all']/B2:+.6f}   "
                  f"(Q<=(2+rho)B only: {-r['m_upto']/B2:+.6f})")
            print(f"  raw ledger sum(a-m)+ log p /B^2 = {r['am_pos']/B2:+.6f}")
            print(f"  SCALAR/B^2  (all Q)     = {r['scalar']/B2:+.6f}    paper needs <= {-DELTA0:+.6f}")
            print(f"  SCALAR/B^2  (Q<=2.05B)  = {r['scalar_upto']/B2:+.6f}")
        with open(os.path.join(DATA, "scalar_S_B20.csv"), "a", newline="") as fh:
            w = csv.writer(fh)
            for r in out:
                w.writerow([r["B"], r["S"], f"{r['logdet']:.6f}", r["v2"], f"{r['m_all']:.6f}",
                            f"{r['m_upto']:.6f}", f"{r['scalar']:.6f}", f"{r['scalar_upto']:.6f}",
                            r["info"]["prec"]])
    else:
        print(__doc__)


if __name__ == "__main__":
    main()
