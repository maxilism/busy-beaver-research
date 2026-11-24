from math import gcd
from fractions import Fraction as Q
from itertools import product

def step(a,c):
 if c<=a-1 and c%2==0: return (a-c-1,3*c//2+2,'a')
 if c<=a-2 and c%4==1: return (a-c-2,3*(c-1)//2+5,'b')
 if c<=a-4 and c%4==3: return (a-c-4,3*(c-1)//2+8,'c')
 if c==a-3 and c%4==3: return (None,None,'d')
 if c==a-2 and c%4==3: return (3*c+8,1,'e')
 if c==a-1 and c%2==1: return (None,None,'f')
 if c>=a and a%2==0 and c%2==0:return(None,None,'g')
 if c>=a and a%2==0 and c%2==1:return(1,a//2+c+2,'h')
 if c>=a and a%2 and c%2==0:return(3*a,c-a+4,'i')
 if c>=a and a%2 and c%2:return(3*a+2,c-a+1,'j')
 raise ValueError(a,c)

def move(T,w): # c'=A*c+B*S+E, S'=S+D
 A,B,E,D=T
 if w=='b':return 3*A/2,3*B/2,(3*E+7)/2,D+5
 if w=='c':return 3*A/2,3*B/2,(3*E+13)/2,D+9
 if w=='j':return 3*A,3*B-1,3*E-D+1,D+4
 raise ValueError(w)

def wline(w):
 T=(Q(1),Q(0),Q(0),0)
 for l in w:T=move(T,l)
 A,B,E,D=T;r=-B/(A-1);k=(r*D-E)/(A-1);return r,k,D

def find(N):
 for n in range(2,N+1):
  for tail in product(['bb','bc','cb','cc','j'],repeat=n-1):
   W=('j',)+tail
   if W!=min([W[i:]+W[:i] for i in range(n) if W[i]=='j']) or all(z=='j' for z in W):continue
   w=''.join(W);r,k,D=wline(w)
   if (r*D).denominator>1:continue
   if k.denominator%r.denominator==0 and k.denominator>r.denominator:continue
   for S in range(1000,1000+8*r.denominator):
    c=r*S+k
    if c.denominator>1:continue
    c=int(c);a=S-2*c
    if a<0 or c<0:continue
    for char in w*4:
     a,c,z=step(a,c)
     if z!=char:break
    else:print('FOUND',w,r,k,D,'start',S,flush=True);break
if __name__=='__main__':find(6)
