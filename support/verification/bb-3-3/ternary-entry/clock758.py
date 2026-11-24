"""Integer checks for the #758 timed area estimates and small raw timing matches."""
import runpy
module=runpy.run_path(__file__.replace('clock758.py','exc-check.py'));step=module['step'];H=module['H']
def cost(r,a,c):
 return {'a':3*c*c+8*c+5,'b':(6*c*c+31*c+37)//2,'c':3*c*c+29*c+65,'d':(6*c*c+43*c+75)//2,'e':(6*c*c+37*c+63)//2,'f':3*c*c+8*c+6,'g':3*a*a+5*a+9*c+24,'h':3*a*a+3*a+5*c+11,'i':3*a*a-9*a+14*c+30,'j':3*a*a+5*c+6}[r]

def tape(a,c):
 return dict([(-a,1)]+[(i,2)for i in range(-a+1,1)]+[(2*i+1,2)for i in range(c)])

def sim(a,c):
 r,A,C=step(a,c); tlim=cost(r,a,c); s='C';x=0;T=tape(a,c);tar=tape(A,C)
 for t in range(1,tlim+2):
  op={'A':('1RB','2LC','1RC'),'B':('2LC','---','2RB'),'C':('2LA','0LB','0RA')}[s][T.get(x,0)]
  if op=='---':return 'halt',t-tlim
  w,d,s=op
  if w=='0':T.pop(x,None)
  else:T[x]=int(w)
  x+=1 if d=='R' else -1
  if t==tlim and r not in 'dfg':assert s=='C' and {p-x:q for p,q in T.items()}==tar;return 'ok',0
 raise AssertionError((a,c,r,tlim))
tags={}
for a in range(14):
 for c in range(14):
  r=step(a,c)[0];out=sim(a,c);assert out[0]==('halt' if r in 'dfg' else 'ok');tags.setdefault(r,set()).add(out[1]);
print('small raw time offsets (undefined counts as one):',tags)
a,c=1,H
for n in range(1,700):
 r,A,C=step(a,c)
 if r in 'dfg':break
 a,c=A,C
X=a+2*c;print('final chain rules, halt, S - 2H',n,r,X-2*H)
assert n==307 and r=='d' and X==2*H+1258
M=10**8
assert 3**792>2**792*(H+1000) and 3**293>2*H+2000
assert 3*315**2*M**2*25000 > 1000**2*7200*(M+7200)**2
assert 3*M**2*25000 > 5**2*2700*(M+2700)**2
assert 3*M**2*25000 > 50**2*9*(M+9)**2
assert (2*H+1)**3-(M+7200)**3 > 75000*10**414
assert 5*X**3+43200*(X+10)**2<432*10**417
from decimal import Decimal as D,getcontext
getcontext().prec=12
print('bounds upon capture:',(D((2*H+1)**3)-D((M+7200)**3))/75000,D(5*X**3)/432+100*D(X+10)**2)
