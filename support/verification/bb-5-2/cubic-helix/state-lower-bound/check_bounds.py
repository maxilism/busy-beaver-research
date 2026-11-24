#!/usr/bin/env python3
"""Replay an all-DFA lower bound. Only the literal table and Python 3 are used."""
import json
from pathlib import Path

def require(p, why):
    if not p: raise ValueError(why)

T='1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD'.split('_')

def step(tape,h,q):
    i=3*(h in tape); w,d,n=T[ord(q)-ord('A')][i:i+3]
    if w=='-':return None
    (tape.add if w=='1' else tape.discard)(h)
    return (h+ (1 if d=='R' else -1),n)

def encode(tape,h,q):
    pts=tape|{h};lo,hi=min(pts),max(pts)
    return ''.join((q if j==h else '')+('1' if j in tape else '0') for j in range(lo,hi+1))

def decode(w):
    heads=[(j,c) for j,c in enumerate(w) if c in 'ABCDE'];require(len(heads)==1,'head')
    h,q=heads[0]; b=w[:h]+w[h+1:];require(h<len(b) and not (set(b)-set('01')),'bits')
    tape={j for j,c in enumerate(b) if c=='1'};require(encode(tape,h,q)==w,'canonical word')
    return tape,h,q

def check(data, kind):
    us=data['prefixes']; pairs=data['pairs'];k=len(us)
    require(len(set(us))==k,'duplicate prefix');seen=set();times={t for a,b,t,d in pairs}.union(data['extensions']);W={}
    tape=set(); h,q=0,'A'
    for t in range(max(times)+1):
        if t in times:W[t]=encode(tape,h,q)
        if t<max(times):h,q=step(tape,h,q)
    require(len(data['extensions'])==k, 'missing positive extensions')
    for u,t in zip(us,data['extensions']):
        require(W[t].startswith(u),'positive extension')
        require(sum(c in 'ABCDE' for c in u)==kind,'head count')
    for a,b,t,d in pairs:
        require(0<=a<k and 0<=b<k and a!=b,'pair indices');require(t>=0 and d>=0,'negative time')
        seen.add(tuple(sorted((a,b))));require(W[t].startswith(us[a]),'positive prefix')
        z=W[t][len(us[a]):];tape,h,q=decode(us[b]+z)
        for _ in range(d):h,q=step(tape,h,q)
        require(q=='D' and h in tape,'D1 not reached')
    require(len(seen)==len(pairs)==k*(k-1)//2,'incomplete pair coverage')
    print(f'{k} pairwise distinguishable prefixes, {len(pairs)} common-suffix witnesses; all hybrid words canonical.')
    print(f'Maximum recorded blank time: {max(times)}. Maximum steps to D1: {max(d for a,b,t,d in pairs)}.')
    return k

def main():
    groups=json.loads(Path(__file__).with_name('lower-bounds.json').read_text());require(len(groups)==2,'group count')
    k,l=(check(g,i) for i,g in enumerate(groups))
    print(f'At least {max(k,l)} live states even with malformed inputs unspecified.')
    print(f'If all malformed words must be rejected: at least {k+l} live states, and {k+l+1} in a complete DFA.')

if __name__=='__main__': main()
