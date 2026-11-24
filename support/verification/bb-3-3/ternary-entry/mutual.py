from pred import *
from functools import lru_cache
import sys
@lru_cache(500000)
def fwd(S,c,cap):
 for i in range(cap):
  if S<=3*c: S,c=S+4,3*c-S+1;continue
  for _ in range(2):
   k=2 if c%4==1 else 4
   if S<3*c+k: return i
   S,c=S+k*2+1,(3*c+(7 if k==2 else 13))//2
  if S<=3*c and S%2==0:return i
 return cap
# Correction strict a<=c even/odd; odd,odd enough. P second lower test excludes h via guard.
@lru_cache(500000)
def back(S,c,n):
 out=inv(S,c) if n else []
 return max([(0,'')]+[(1+j,w+' '+p)for w,Q,z in out for j,p in [back(Q,z,n-1)]])
if __name__=='__main__':
 for c in (7,4*L//23+2):print('probe',c if c<100 else 'c*',fwd(L,c,1000));
 best=(0,0,0,''); nf=0;nb=0; K=int(sys.argv[1]) if len(sys.argv)>1 else 25000
 for c in range(1,K,2):
  if not inv(L,c):continue
  b,w=back(L,c,50)
  if b>best[0] and fwd(L,c,396)==396:
   best=(b,c,fwd(L,c,500),w);print(best,flush=True)
