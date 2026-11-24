#!/usr/bin/env python3
"""Build the DFA accompanying results/bb-5-2/cubic-helix.pdf (machine 4817065).

Run `python3 extract_dfa.py OUTPUT.json`; only the standard library is used.
The JSON gives a partial transition table. Start at `initial`. For state q and
letter c, use delta[q][alphabet.index(c)]; -1 is an absorbing rejecting sink.
Accept at the end of the word exactly when the state is in `final`.

Read the tape from left to right, trimming to all ones and the head. The
uppercase state goes BEFORE the scanned bit, including a scanned blank (A0
is the initial configuration). Lowercase b in the construction is internal:
it marks state B scanning the preceding bit. It is absent from the output.

maxilism, November 24, 2026. CC BY 4.0: https://creativecommons.org/licenses/by/4.0/
"""
import sys,json
from itertools import product
from collections import defaultdict,deque
A='01ABCDEb'
class N:
 def __init__(s):s.n=0;s.t=defaultdict(set);s.f=set();s.i=s.new()
 def new(s):s.n+=1;return s.n-1
 def edge(s,p,a,q):s.t[p,a].add(q)
 def path(s,p,w,q):
  if not w:s.edge(p,'',q);return
  for j,a in enumerate(w):
   r=s.new() if j+1<len(w) else q;s.edge(p,a,r);p=r
 def expr(s,parts): # each part literal or ('*',literal)
  p=s.i
  for w in parts:
   q=s.new()
   if isinstance(w,tuple):s.edge(p,'',q);s.path(q,w[1],q)
   else:s.path(p,w,q)
   p=q
  s.f.add(p)
 def dfa(s):
  rev=defaultdict(list)
  for (p,a),qs in s.t.items():
   for q in qs:rev[q].append(p)
  good=set(s.f);todo=list(good)
  while todo:
   for p in rev[todo.pop()]:
    if p not in good:good.add(p);todo.append(p)
  def close(x):
   y=x & good;z=list(y)
   while z:
    for r in s.t.get((z.pop(),''),()):
     if r not in y and r in good:y.add(r);z.append(r)
   return frozenset(y)
  x=close({s.i});arr=[x];ids={x:0};t=[];f=set()
  for i,x in enumerate(arr):
   if x & s.f:f.add(i)
   row=[]
   for a in A:
    y=close({r for p in x for r in s.t.get((p,a),())})
    if not y:row.append(-1);continue
    if y not in ids:ids[y]=len(arr);arr.append(y)
    row.append(ids[y]);
   t.append(row)
  # Moore refine, treat missing arc as its own sink
  g=[int(i in f) for i in range(len(t))]
  while True:
   seen={};ng=[]
   for i,row in enumerate(t):
    k=(i in f,tuple(g[j] if j>=0 else -1 for j in row));ng.append(seen.setdefault(k,len(seen)))
   if ng==g:break
   g=ng
  nr=[None]*(max(g)+1);nf=set()
  for i,row in enumerate(t):
   nr[g[i]]=[g[j] if j>=0 else -1 for j in row]
   if i in f:nf.add(g[i])
  assert g[0]==0
  return nr,nf

def union(parts):
 # combine all in one disjoint union NFA, then minimize
 n=N()
 for t,f in parts:
  off=n.n;n.n+=len(t);n.edge(n.i,'',off)
  for i,row in enumerate(t):
   for a,q in zip(A,row):
    if q>=0:n.edge(i+off,a,q+off)
  n.f.update(q+off for q in f)
 return n.dfa()

def image(df,patterns):
 # image under exactly one selected context rewrite from patterns.
 # pattern (x,y,z): consume x/output y, optional arbitrary copies of pair(s)
 # using (consume,output) placed between the start and end rewrites
 # overall schema p (a1=>b1) (x=>y)* (a2=>b2) s.
 n=N();t,f=df
 def block():off=n.n;n.n+=len(t);return off
 p=block();s=block();n.edge(n.i,'',p);n.f={s+i for i in f}
 for i,row in enumerate(t):
  for a,q in zip(A,row):
   if q>=0:n.edge(p+i,a,p+q);n.edge(s+i,a,s+q)
 def action(po,so,x,y):
  for i in range(len(t)):
   q=i
   for a in x:
    q=t[q][A.index(a)]
    if q<0:break
   if q>=0:n.path(po+i,y,so+q)
 for (a,b),rep,(c,d) in patterns:
  if rep is None:action(p,s,a+c,b+d)
  else:
   h=block();action(p,h,a,b);action(h,h,*rep);action(h,s,c,d)
 return n.dfa()

def pat(x,y):return ((x,y),None,('',''))
atoms=[pat(x,y) for x,y in [('A01','01A'),('A10','1A0'),('A00','b01'),('A11','0b0'),('01b','b10'),('10b','b01'),('11b','01A'),('000b','1A01')]]
sweeps=[(('A',''),('01','01'),('','A')),(('','b'),('01','10'),('b','')),(('','b'),('10','01'),('b',''))]
I='0'*7

def phases():
 # T starts at an R checkpoint of the paper. K and U start one D0 step after
 # its regular P and Q checkpoints. Seven exterior zeros on each side suffice
 # for one sweep. Only the four-blank entry is needed on the blank run.
 nt=N();nt.expr([I,'1','01'*2,('*','01'*3),'A0',I]);T=nt.dfa()
 nk=N()
 for z in [1,2,3]:
  m=(1-z)%3;r=z
  nk.expr([I,'1','0'*z,('*','000'),'1A','10'*m,('*','10'*3),'0','1'*r,('*','111'),I]);
 K=nk.dfa();nu=N();nu.expr([I,'10',('*','000'),'1A',('*','01'*3),'01',('*','111'),I]);U=nu.dfa()
 res=[T,K,U]
 # At each cycle we only need the finite local atoms inside or partial sweeps.
 for d,steps in [(T,[2,'L',4,7,0]),(K,[1,'R',2,'L',6]),(U,['R',3,'M',7]),(U,['R'])]:
  for i in steps:
   p={'R':sweeps[0],'L':sweeps[1],'M':sweeps[2]}[i] if isinstance(i,str) else atoms[i]
   d=image(d,[p]);res.append(d)
 return union(res)

def standard(d):
 # mixed->standard replacing xb by Bx only if b is present. Filter d without b.
 t,f=d;raw=([row[:7]+[-1] for row in t],f)
 return union([raw,image(d,[pat(x+'b','B'+x) for x in '01'])])

def bits(d):
 # All real bit-steps, input convention uppercase before symbol; contexts padded
 tab={'A':('1RB','0RC'),'B':('1LC','0LE'),'C':('0LD','0LB'),'D':('1RA',None),'E':('1LB','0RD')}
 pats=[]
 for s,ts in tab.items():
  for x,tr in zip('01',ts):
   if tr is None:continue
   y,r,h=tr
   if r=='R':pats.append(pat(s+x,y+h))
   else:pats.extend(pat(z+s+x,h+z+y) for z in '01')
 return image(d,pats)

def trims(d):
 # remove arbitrary exterior zeros; implement 0* left- and right-quotients
 t,f=d;n=N();off=n.n;n.n+=len(t);p=0;seen=set()
 while p>=0 and p not in seen:
  seen.add(p);n.edge(n.i,'',off+p);p=t[p][0]
 for i,row in enumerate(t):
  p=i;seen=set()
  while p>=0 and p not in seen:
   if p in f:n.f.add(i+off);break
   seen.add(p);p=t[p][0]
  for a,q in zip(A,row):
   if q>=0:n.edge(i+off,a,q+off)
 return n.dfa()

def prefix():
 t={'A':('1RB','0RC'),'B':('1LC','0LE'),'C':('0LD','0LB'),'D':('1RA',None),'E':('1LB','0RD')};s='A';a=set();i=0;n=N()
 for _ in range(15):
  n.expr([''.join((s if j==i else '')+str(int(j in a)) for j in range(min(a|{i}),max(a|{i})+1))]);y,r,s=t[s][i in a]
  if y=='1':a.add(i)
  else:a.discard(i)
  i+=1 if r=='R' else -1
 return n.dfa()

def canonical(d):
 # intersect with canonical word syntax (must include scanned cell)
 mask=N()
 # (empty or 1[01]*) q ([01] or [01][01]*1)
 # implement using a hand DFA with left,head,posthead phases.
 t,f=d;n=N();ids={(0,0):n.i};todo=[(0,0)]
 for i,j in todo:
  if i in f and j in [3,4]:n.f.add(ids[i,j])
  for a,k in zip(A,t[i]):
   if k<0:continue
   if j in [0,1]:
    if a in 'ABCDE':m=2
    elif a=='1' or (a=='0' and j):m=1
    else:continue
   elif a not in '01':continue
   elif j==2:m=3 # single scanned bit OK
   else:m=4 if a=='1' else 5 # nontrivial suffix must end 1
   if (k,m) not in ids:ids[k,m]=n.new();todo.append((k,m))
   n.edge(ids[i,j],a,ids[k,m])
 return n.dfa()

if __name__=='__main__':
 p=standard(phases());ds=[p]
 for _ in range(3):ds.append(bits(ds[-1]))
 d=canonical(union([trims(union(ds)),prefix()]))
 t,f=d;out={'alphabet':A[:7],'initial':0,'final':sorted(f),'delta':[r[:7] for r in t],'missing':-1}
 with open(sys.argv[1] if len(sys.argv)>1 else 'dfa.json','w') as h:json.dump(out,h,separators=(',',':'));h.write('\n')
 print(f'{len(t)} states (+ rejecting sink), {len(f)} accepting')
