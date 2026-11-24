#!/usr/bin/env python3
"""Check the cubic helix separator using Python 3 (standard library only).

Run `python3 check-dfa.py` with extract_dfa.py and dfa.json alongside this
file. Regenerate the DFA in a temporary directory and compare bytes, then
run finite regression tests against the literal machine. The all-input proof
is in results/bb-5-2/cubic-helix.pdf.

maxilism, November 24, 2026. CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
"""
import sys, json, itertools, hashlib, tempfile, subprocess
from pathlib import Path
if not __debug__:
 raise SystemExit("Run without -O: this checker uses assertions.")
proj=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'regen.json';subprocess.run([sys.executable,str(proj/'extract_dfa.py'),str(out)],check=True);assert out.read_bytes()==(proj/'dfa.json').read_bytes()
print('sha256:',hashlib.sha256((proj/'dfa.json').read_bytes()).hexdigest());D=json.loads((proj/'dfa.json').read_text());final=set(D['final']); col={c:i for i,c in enumerate(D['alphabet'])}; rows=D['delta']; TM='1RB0RC_1LC0LE_0LD0LB_1RA---_1LB0RD'.split('_')
def run_dfa(w):
 p=D['initial']
 for c in w:
  p=rows[p][col[c]]
  if p<0: return False
 return p in final
def tape(S,h,q):
 w=''.join('1' if x in S else '0' for x in range(min(S|{h}),max(S|{h})+1));i=h-min(S|{h});return w[:i]+q+w[i:]
def step(S,h,q):
 t=TM[ord(q)-65];i=int(h in S)*3; z,r,n=t[i:i+3]
 if z=='-':return None
 (S.add if z=='1' else S.discard)(h)
 return S,h+(1 if r=='R' else -1),n
x=set(),0,'A'
for n in range(100001):
 w=tape(*x); assert run_dfa(w),(n,w); x=step(*x)
print('All 100001 configurations at t=0..100000 accepted.')
halted=0;accepted=0;total=0
for n in range(1,8):
 for bits in itertools.product('01',repeat=n):
  for h in range(n):
   if (h and bits[0]=='0') or (h<n-1 and bits[-1]=='0'):continue
   S={j for j in range(n) if bits[j]=='1'}
   for q in 'ABCDE':
    w=''.join(bits[:h])+q+''.join(bits[h:]); acc=run_dfa(w);accepted+=acc;total+=1;x=S.copy(),h,q
    for _ in range(33):
     x=step(*x)
     if x is None:
      halted+=1; assert not acc,w;break
print(f'All {halted} configurations entering D1 by time 32 rejected among {total} canonical inputs of span <=7 ({accepted} accepted).')
# Breadth-first enumerate accepted words without expanding missing arcs; all represent canonical configurations
level=[('',D['initial'])]
for n in range(30):
 witness=None
 for w,p in level:
  if p not in final:continue
  h=next(i for i,c in enumerate(w) if c in 'ABCDE');q=w[h];bits=w[:h]+w[h+1:];S={i for i,b in enumerate(bits) if b=='1'};x=step(S,h,q)
  if x is not None and not run_dfa(v:=tape(*x)):
   witness=w,v;break
 if witness:break
 level=[(w+c,r) for w,p in level for c,r in zip(D['alphabet'],rows[p]) if r>=0]
assert witness;print(f'Accepted word {witness[0]} -> rejected successor {witness[1]}.')
