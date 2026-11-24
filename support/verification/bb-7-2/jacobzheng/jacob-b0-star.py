#!/usr/bin/env python3
"""Classify all 27 defined B0 alternatives. No third-party dependencies."""
from itertools import product
from pathlib import Path
from runpy import run_path

common = run_path(str(Path(__file__).with_name('jacob-turn-check.py')))
table, checkpoint, run = (common[k] for k in ['table','checkpoint','run'])

def certify(rules, k):
    # Neighborhood masks are encoded near-to-far (nearest bit least significant).
    # CL/CR allow k-grams starting at distances >=2 in the corresponding half.
    top = 1 << (k-1); mask = 2*top-1
    centers = {('A',0,0,0)}; CL, CR = {0}, {0}
    while True:
        old = len(centers) + len(CL) + len(CR)
        for q,L,b,R in list(centers):
            if (q,b) not in rules: return None # abstract halt: no certificate
            w,d,s = rules[q,b]; w = int(w)
            if d == 'R':
                CL.add(L); Ln = (2*L+w) & mask
                for Rn in [R//2, R//2 + top]:
                    if Rn in CR: centers.add((s,Ln,R%2,Rn))
            else:
                CR.add(R); Rn = (2*R+w) & mask
                for Ln in [L//2, L//2 + top]:
                    if Ln in CL: centers.add((s,Ln,L%2,Rn))
        if len(centers) + len(CL) + len(CR) == old:
            return len(centers), len(CL), len(CR)

def check_arithmetic():
    rules = table('0RE')
    for k in range(9):
        for h in range(1,9):
            cfg = run(checkpoint(2*k,2*h),rules,3*(k+h)**2+2*k+6*h+5)
            assert cfg == checkpoint(3*(k+h),2,cfg[1])
    for k in range(9):
        for m in range(9):
            cfg = run(checkpoint(2*k+1,m),rules,3*k*k+8*k+6)
            assert cfg == checkpoint(3*k+1,m+2,cfg[1])
    c = run(('A',0,set()),rules,20)
    assert c == checkpoint(4,2,c[1])

def main():
    counts = {2:0,6:0}
    for t in product('01','LR','ABCDEFG'):
        b0 = ''.join(t)
        if b0 in ['1RE','0RE','0RG']: continue
        k = 6 if b0 == '0RB' else 2
        cert = certify(table(b0),k); assert cert is not None
        print(b0, 'nonhalting', k, *cert); counts[k] += 1
    assert counts == {2:24,6:1}
    check_arithmetic(); print('0RE nonhalting by paired-run parity macro (checks passed)')
    rules = table('0RG'); q,h,ones = run(('A',0,set()),rules,45)
    assert (q,int(h in ones)) == ('E',0)
    print('0RG reaches E0 after 45 defined transitions')
    print('1RE original: not classified here')

if __name__ == '__main__': main()
