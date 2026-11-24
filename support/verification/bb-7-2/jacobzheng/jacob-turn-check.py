#!/usr/bin/env python3
"""Raw tape sweep checks and exact regular-certificate inclusion checks (stdlib only)."""
from collections import defaultdict
from itertools import product

ORIGINAL = '1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE'
STATES = 'ABCDEFG'

def table(b0):
    rows = ORIGINAL.split('_'); rows[1] = b0 + rows[1][3:]
    return {(s, i): row[3*i:3*i+3] for s, row in zip(STATES, rows)
            for i in range(2) if row[3*i:3*i+3] != '---'}

def run(cfg, tab, steps):
    q, h, ones = cfg
    ones = set(ones)
    for _ in range(steps):
        w, d, q = tab[q, int(h in ones)]
        (ones.add if w == '1' else ones.discard)(h)
        h += 1 if d == 'R' else -1
    return q, h, ones

def checkpoint(n, m, h=0):
    return 'C', h, set(range(h+1, h+n+1)) | set(range(h+n+2, h+n+m+2))

def macro(b0, n, m):
    k, e = divmod(n, 2)
    return (3*k + (1 if b0 == '1LE' else e),
            m + (1+e if b0 == '1LE' else 2), 3*k*k + 8*k + 4 + 2*e)

def check_sweeps(b0):
    tab = table(b0)
    for n in range(1, 40):
        for m in range(7):
            nn, mm, dt = macro(b0, n, m)
            q, h, ones = run(checkpoint(n, m), tab, dt)
            assert (q, h, ones) == checkpoint(nn, mm, h)
    cfg = run(('A', 0, set()), tab, 3)
    n, m, t = 3, 0, 3
    first = []
    for _ in range(12):
        assert cfg == checkpoint(n, m, cfg[1]); first.append((t,n,m))
        n, m, dt = macro(b0,n,m); t += dt
        cfg = run(cfg, tab, dt)
    print(b0, 'first blank checkpoints', first[:7])

# Regular invariant as full-tape templates. Upper case scans 0, lower case scans 1.
# Every character (including its attached quantifier, if any) is a single cell atom.
PATTERNS = '''A G1 F11
1+C1*01* 1*C1+01*
11+B1* 1+b1*01* 11+A1* 11+a1*01*
1*d1*01*01* D1+01*01* 1+c1*01*01*
1+g1+ 1*e1+ 1*f1*01+ F1*01+'''.split()
ALPHABET = '01' + STATES + STATES.lower()

def make_dfa():
    import re
    # Extensional config language: add any blank padding on either side, and
    # allow zero-only suffixes of templates to be trimmed off at acceptance.
    adj = []; eps = []
    def node():
        adj.append(defaultdict(set)); eps.append(set()); return len(adj)-1
    start, end = node(), node()
    for pat in PATTERNS:
        p = node(); eps[start].add(p)
        for c, op in re.findall(r'([A-Za-z01])([*+]?)', '0*'+pat+'0*'):
            r = node(); adj[p][c].add(r)
            if op: adj[r][c].add(r)
            if op == '*': eps[p].add(r)
            p = r
        eps[p].add(end)
    accept = {end} # reverse closure over epsilon and 0: right quotient by 0*
    while True:
        z = {p for p in range(len(adj)) if (eps[p] | adj[p]['0']) & accept}
        if z <= accept: break
        accept |= z
    def clos(S):
        v = list(S); S = set(v)
        while v:
            for r in eps[v.pop()] - S: S.add(r); v.append(r)
        return frozenset(S)
    initial = clos([start]); ids = {initial:0}; subsets = [initial]; rows = []; final = set()
    for i, S in enumerate(subsets):
        if S & accept: final.add(i)
        row = {}
        for c in ALPHABET:
            nxt = clos(r for p in S for r in adj[p][c]); j = ids.get(nxt)
            if j is None: j = ids[nxt] = len(subsets); subsets.append(nxt)
            row[c] = j
        rows.append(row)
    return rows, final

def check_box(rows, final):
    # Greatest suffix-language inclusion relation: (p,q) survives iff, for
    # every word v, accepting from p on v implies accepting from q on v.
    N = len(rows)
    I = {(p,q) for p,q in product(range(N), repeat=2) if p not in final or q in final}
    while True:
        J = {(p,q) for p,q in I if all((rows[p][c], rows[q][c]) in I for c in ALPHABET)}
        if I == J: break
        I = J
    assert rows[0]['A'] in final
    dead = rows[rows[0]['A']]['A']
    assert dead not in final and all(r == dead for r in rows[dead].values())
    assert all((rows[p]['E'], dead) in I for p in range(N))
    def mark(q,b): return q.lower() if b == '1' else q
    def factor(p,s): return rows[rows[p][s[0]]][s[1]]
    valid = {}
    for s,b in product(STATES, '01'):
        if (s,b) == ('E','0'): continue
        ok = []
        for w,d,r in product('01','LR',STATES):
            def safe(p,a):
                if d == 'R': old,new = mark(s,b)+a, w+mark(r,a)
                else: old,new = a+mark(s,b), mark(r,a)+w
                return (factor(p,old), factor(p,new)) in I
            if all(safe(p,a) for p,a in product(range(N),'01')): ok.append(w+d+r)
        valid[s,int(b)] = ok; print(s+b,len(ok),' '.join(ok))
    from math import prod
    count = prod(map(len,valid.values()))
    assert count == 324403200
    print(N,'reachable DFA states;',count,'labeled tables certified')
    for b0 in ['1LE','1LG']:
        for entry, instr in table(b0).items(): assert instr in valid[entry]

def main():
    for b0 in ['1LE','1LG']: check_sweeps(b0)
    check_box(*make_dfa())
    cfg=('A',0,set()); t=0; tab=table('1RE')
    while (cfg[0],int(cfg[1] in cfg[2])) != ('B',0): cfg=run(cfg,tab,1); t+=1
    print('first B0 read after',t,'defined steps; successors differ on step',t+1)

if __name__ == '__main__': main()
