"""Exact nine-slice filters; run from any directory, no big data needed."""
import os,sys
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from pred import *
from mod import R
from mutual import fwd,back
from runpy import run_path
step=run_path(os.path.join(os.path.dirname(__file__),'exc-check.py'))['step']
cs=(4*L//23+2,7,219261)
for c in cs:
 a=L-2*c;cc=c;n=0
 while True:
  r,aa,cd=step(a,cc);n+=1
  if r in 'defgh':break
  a,cc=aa,cd
  assert n<3000
 print('c, forward full letters, terminal row, total macros, H-c_h, depth:',c if c<=219261 else 'c*',fwd(L,c,1000),r,n,H-cd,back(L,c,30))
 if c!=219261:
  a=L-2*c;assert len(inv(L,c))==0 and a%3==0 and a//3>1;cp=c+a//3-4;assert cp>=a//3 and cp%2==0 and step(a//3,cp)==('i',a,c)
 else:
  S=L;cc=c
  for w in 'J J bc cb bb bc cb J J cc J bb bb J cc J cc J bc cc cc bb J J cb J cb'.split():
   _,S,cc=next(x for x in inv(S,cc) if x[0]==w)
  print('oldest preimage: S_old=L0',S-L,'c_old=',cc)
  while S<L:
   r,a,c1=step(S-2*cc,cc);S=a+2*c1;cc=c1
  assert (S,cc)==(L,c)
for n in range(3,7):
 v=[len(R(n,(L+2*j)%3**n)) for j in range(9)];print(n,v)
A=[1,1]
for _ in range(2,291):A.append(A[-1]+4*A[-2]);
for j in range(9):
 N=(L+2*j+1)//4 ; n=290;
 upper=3*(9*n+1)+A[n]*((N-1)//3**n+1)+4*A[n-1]*((N-1)//3**(n+1)+1)
 assert upper*10**23 < 1377*N # <1.377e-20 of odd inputs
A={(L,219261)};profiles=[]
for i in range(29):
 profiles.append(len(A));assert all(v-2*u>3 and u>1 for v,u in A)
 A={(q,k) for v,u in A for _,q,k in inv(v,u)}
assert sum(profiles)==92 and profiles[-2:]==[2,0]
print('inverse tree sizes',profiles)
