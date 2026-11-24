#!/usr/bin/env python3
"""Regression and finite evidence for #184. No nonhalting claim."""
import argparse
import hashlib


def lean(x, b):
    """Literal highLevelNext with ℕ subtractions known nonnegative in selected branches."""
    if not x:
        return ((b // 2 + 1, 3) if b % 2 == 0 else (b // 2 + 3, 0))
    a = x - 1
    if b % 2 == 0:
        k = b // 2
        if k <= a + 3:
            return a + 4 - k, 6 * k + 6
        if k <= a + 5:
            return None
        return k - a - 5, 6 * a + 33
    k = b // 2 + 2
    if k > a:
        return k - a, 6 * a + 6
    if a <= k + 1:
        return None
    return a - k - 1, 6 * k + 9


def encode(x, b):
    assert x > 0
    return (2*x+12, b+3) if b % 2 == 0 else (b+9, 2*x+1)


def step(e, o):
    d = e - o
    if d in (1, 3):
        return None
    if d > 0:
        return d + 9, 3 * o
    assert d < 0
    return 3 * e, 2 - d


def run(e, o):
    L = e > o
    M, m = (e, o) if L else (o, e)
    c = 9 if L else 2
    def val(j):
        n = 3**j * m
        return M + c*j - (n-m)//2, n
    def done(j):
        Mj, mj = val(j)
        return Mj - mj <= (3 if L else 0)
    if L and done(0):
        return 0, (e, o), True
    lo, hi = 0, 1
    while not done(hi):
        lo, hi = hi, 2*hi
    while hi - lo > 1:
        mid = (lo + hi)//2
        if done(mid):
            hi = mid
        else:
            lo = mid
    Mj, mj = val(hi)
    trap = L and Mj > mj
    return hi, (Mj, mj) if L else (mj, Mj), trap


def check(limit, eras):
    assert encode(*lean(0,3)) == (20,3)
    cases = 0
    for x in range(1, limit+1):
        for b in range(limit+1):
            s = lean(x,b)
            assert (encode(*s) if s else None) == step(*encode(x,b))
            cases += 1
    print(f'one-step equivalence checked on {cases:,} inputs')
    for e in range(14, limit+14, 2):
        for o in range(3, limit+3, 2):
            k, z, trap = run(e,o)
            t = e,o
            for j in range(k):
                assert (t[0]>t[1]) == (e>o)
                t = step(*t)
                assert t is not None
            assert t==z
            if trap:
                assert step(*t) is None
            else:
                assert (t[0]>t[1]) != (e>o)
                assert 5*sum(t)>=6*(e+o)
    print('era thresholds, iterate values and complete-era growth checked')
    e,o = 20,3
    ksum = 0
    low_clearance = []
    residues = [0]*9
    for h in range(eras):
        L = e>o
        M,m = (e,o) if L else (o,e)
        T = 1 + 2*M//m
        J = 0
        while T >= 3:
            J += 1
            T //= 3
        D = m - M%m
        W = 9*J-1 if L else 2*J+3
        if D<=W:
            low_clearance.append((h,L,J,D))
        if L:
            residues[(2*e+o)%9]+=1
        k,z,trap = run(e,o)
        ksum += k
        if trap:
            print(f'TRAP after {ksum:,} updates; completed eras={h:,}')
            return
        assert 5*sum(z)>=6*(e+o)
        e,o=z
    print(f'launches failing D>W: {len(low_clearance)}; first 20 (zero-based era,L,J,D): {low_clearance[:20]}')
    print(f'L-launch histogram of (2e+o) mod 9: {residues}')
    def digest(x):
        return hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest()
    print(f'no trap encountered in {eras:,} completed sign runs ({ksum:,} updates) from (20,3)')
    print(f'endpoint bits and unsigned big-endian SHA-256: e {e.bit_length():,} {digest(e)}; o {o.bit_length():,} {digest(o)}')

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--limit',type=int,default=300)
    ap.add_argument('--eras',type=int,default=10000)
    a=ap.parse_args()
    check(a.limit,a.eras)
