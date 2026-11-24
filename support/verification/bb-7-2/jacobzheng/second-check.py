#!/usr/bin/env python3
"""Compare derived checkpoint rules with the seven-state TM, including E0."""
TM = '1LG0LD_1RE1RA_1RB1RC_1RC1LD_---0LF_1LC1LF_1LF1LE'
TABLE = {(q,b): row[3*b:3*b+3]
         for q,row in zip('ABCDEFG', TM.split('_')) for b in (0,1)}

def raw(ones, head, state, ticks):
    for _ in range(ticks):
        w,d,state = TABLE[state,int(head in ones)]
        assert w != '-', 'passed an undefined transition'
        (ones.add if w == '1' else ones.discard)(head)
        head += 1 if d == 'R' else -1
    return head,state

def shape(n,m,h):
    return set(range(h+1,h+1+n)) | set(range(h+n+2, h+n+2+m))

def check(n,m,ones,h):
    k,r = divmod(n,2)
    if r == 0 and m == 0:
        dt = 3*k*k + 5*k + 2  # E scans 0, before undefined action
        h,s = raw(ones,h,'C',dt)
        assert s == 'E' and h not in ones
        return None,None,h,dt
    dt = 3*k*k + 8*k + 6
    n,m = (3*k+1, m+2) if r else (3*k+3, m-1)
    h,s = raw(ones,h,'C',dt)
    assert s == 'C' and ones == shape(n,m,h)
    return n,m,h,dt

if __name__=='__main__':
    for n in range(32):
        for m in range(8):
            check(n,m,shape(n,m,0),0)
    print('Passed 256 independent checkpoint transitions (including E0).')
    ones = set()
    h,s = raw(ones,0,'A',3); n,m = 3,0; t = 3
    assert s == 'C' and ones == shape(n,m,h)
    for _ in range(11):
        print(f'blank: {t=:6} {n=:4} {m=:2}')
        n,m,h,dt = check(n,m,ones,h); t += dt
    h,n,m,t = 0,7,0,0; ones=shape(n,m,h)
    while n is not None:
        print(f'nonblank: {t=:6} {n=:4} {m=:2}')
        n,m,h,dt = check(n,m,ones,h); t += dt
    print(f'nonblank: {t=:6} E scans 0')
