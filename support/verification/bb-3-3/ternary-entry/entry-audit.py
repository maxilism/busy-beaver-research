"""Verify the first-entry-anchor summaries from the 16M return-delta table and scalar examples."""
from pathlib import Path
import sys,hashlib
from array import array
sys.path.insert(0,str(Path(__file__).resolve().parent));from phase import step
M=13959275;H=(3**307-8282708212)//M;N=8000000;L=1+2*(H-N)
f=open(sys.argv[1],'rb');v=array('H');v.fromfile(f,2*N+1);assert sys.byteorder=='little' and v.itemsize==2
p=array('H',[0])*(N+1)
for i in range(1,N+1):
 delta=v[N+i];assert 0<delta<=1468
 j=i-delta; p[i]=i if j<=0 else p[j]
assert hashlib.sha256(p.tobytes()).hexdigest()=='e32bc4b56f6397eb99562460668bb9832f75cac0b0e3f06d073ada4e54500b2a'
for P,c in [({105},4267280),({105,144},1855111),({105,144,1190},479604)]:
 assert 1+max(i for i,x in enumerate(p) if x not in P)==c
for i in [105,144,1190]:
 a,c=1,H-N-i; ls=''
 for j in range(2000):
    if a+2*c>=L:break
    a,c,z=step(a,c);ls+=z;assert z not in 'dhfg'
 else:raise AssertionError
 print('anchor',i,'first_physical',j,a+2*c-L,'a',a)
 if i==105:assert ls=='i'+'j'*51 and a+2*c==L+2 and a==4*3**51-1
 if i==144:assert ls=='j'*72 and a+2*c==L and a==2*3**72-1
 if i==1190:assert j==582 and not a%2 and (a+2*c)-L==5 and step(a,c)[2]=='h'
for S,c,r in [(L+6,362553523,14),(L,8*3**291-L,290)]:
 a=S-2*c;assert a>3 and c>1 and c%9 not in [2,5] and (S+c-5)%3 and a%3==0
 aa,cc=a//3,c+a//3-4;assert step(aa,cc)==(a,c,'i')
 for _ in range(r):
    prev,rr=divmod(2*(cc-2),3);assert not rr
    assert step(aa+prev+1,prev)==(aa,cc,'a');aa,cc=aa+prev+1,prev
 if r==14:
    labels=[]
    while True:
        a,c,z=step(a,c);labels.append(z)
        if z not in 'bcj':break
    assert labels.count('j')==8 and sum(labels.count(z) for z in 'bc')==783 and labels[-1]=='h'
print('funnel SHA256',hashlib.sha256(p.tobytes()).hexdigest())

def ret(c):
 a=1; w=''
 while True:
  a,c,l=step(a,c);w+=l
  if l in 'hdfg':return c,w
c=3;tr=[c]
while c<218:c=ret(c)[0];tr.append(c)
assert c==218 and ret(c)[0]==298 and ret(220)[0]==264
assert ret(3)[0]==45 and ret(7)[0]==ret(9)[0]==18
print('blank h-prefix',tr,'then',ret(218),'alternative',ret(220))
