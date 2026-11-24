#!/usr/bin/env python3
"""All 351 one-defined-entry replacements of Jacobzheng's table. --list gives per-edit output."""
from itertools import product
from pathlib import Path
from runpy import run_path
import sys

basecode = run_path(str(Path(__file__).with_name('jacob-b0-star.py')))
base = basecode['table']('1RE'); certify = basecode['certify']
run = basecode['run']; C = basecode['checkpoint']

def raw(rules, budget, first=None):
    q='A'; h=0; ones=set()
    for t in range(budget+1):
        key = q,int(h in ones)
        if key not in rules: return t
        if first is not None: first.setdefault(key,t)
        if t == budget: break
        w,d,q = rules[key]; (ones.add if w=='1' else ones.discard)(h); h += 1 if d=='R' else -1
    return None

def P(n,m,h=0):
    q,_,ones = C(n,m,h); ones.add(h-1); return q,h,ones

def exceptions():
    basecode['check_arithmetic']() # B0->0RE (proof in jacob-b0-star.md)
    # Coalescence of G0 edits.
    for ins,dt in [('0LC',8),('1RF',5)]:
        rules = base | {('G',0):ins}
        c = run(('A',0,set()),rules,dt); assert c == C(3,0,c[1])
    # F0->0RA shifted section, and conjugacy after the three transient sweeps.
    rules = base | {('F',0):'0RA'}
    c = run(('A',0,set()),rules,5); assert c == P(1,0,c[1])
    for n in range(20):
        k,e=divmod(n,2)
        for m in range(5):
            if e==0 and m==0:
                q,h,ones = run(P(n,m),rules,3*k*k+7*k+2); assert q=='E' and h not in ones
            else:
                nn,mm=(3*k,m+2) if e else (3*k+2,m-1)
                c=run(P(n,m),rules,3*k*k+10*k+9); assert c==P(nn,mm,c[1])
    # G1->0LF raw-macro consistency on small inputs and exact blank blank-to-E0 clock.
    rules = base | {('G',1):'0LF'}
    for n in range(20):
        k,e=divmod(n,2)
        for m in range(5):
            if e==0 and m==0:
                q,h,ones=run(C(n,m),rules,3*k*k+5*k+2); assert q=='E' and h not in ones
            else:
                nn,mm=(3*k+2,m+1) if e else (3*k+3,m-1)
                c=run(C(n,m),rules,3*k*k+8*k+6); assert c==C(nn,mm,c[1])
    n,m,t,j=3,0,3,0
    while not (n%2==0 and m==0):
        k,e=divmod(n,2); t+=3*k*k+8*k+6
        n,m=(3*k+2,m+1) if e else (3*k+3,m-1); j+=1
        assert j <= 48
    assert (j,n,m,t)==(48,1390542348,0,1160164811207160354)
    k=n//2; t+=3*k*k+5*k+2
    assert t==2610370830869531054
    return {('G',0,'0LC'):('iff','raw prefix'), ('G',0,'1RF'):('iff','raw prefix'),
            ('F',0,'0RA'):('iff','shifted macro'), ('B',0,'0RE'):('N','parity macro'),
            ('G',1,'0LF'):('H',t)}

def main():
    exc = exceptions(); first={}; assert raw(base,44,first) is None
    assert set(first)==set(base) and max(first.values())==43
    totals=[0]*3; longest=0; ks={}
    print('entry first-read-time H N iff-original')
    for site,original in sorted(base.items()):
        num=[0]*3
        for ins in map(''.join,product('01','LR','ABCDEFG')):
            if ins==original: continue
            rules=base | {site:ins}; t=raw(rules,800); a,b=site
            if t is not None:
                kind,reason='H',t; longest=max(t,longest)
            elif (a,b,ins) in exc: kind,reason=exc[a,b,ins]
            else:
                for k in [2,4,6,10]:
                    c=certify(rules,k)
                    if c is not None:
                        kind,reason='N',('window',k,c);ks[k]=ks.get(k,0)+1;break
                else: raise AssertionError(('unresolved edit',site,ins))
            if '--list' in sys.argv: print(a+str(b),ins,kind,reason)
            num[['H','N','iff'].index(kind)]+=1
        print(a+str(b), first[site], *num); totals=[x+y for x,y in zip(totals,num)]
    print('total', *totals,'; longest directly replayed halt:',longest,'; k-gram counts:',ks)
    assert totals==[176,172,3] and longest==740

if __name__=='__main__': main()
