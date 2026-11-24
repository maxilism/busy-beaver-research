from itertools import groupby
H=(3**307-8282708212)//13959275

def step(a,c):
 if c>=a:
  if a%2==0:return ('h',1,a//2+c+2) if c%2 else ('g',0,0)
  if c%2==0:return 'i',3*a,c-a+4
  return 'j',3*a+2,c-a+1
 if c%2==0:return 'a',a-c-1,3*c//2+2
 z=3*(c-1)//2
 if a==c+1:return 'f',0,0
 if c%4==1:return 'b',a-c-2,z+5
 if c==a-3:return 'd',0,0
 if c==a-2:return 'e',3*c+8,1
 return 'c',a-c-4,z+8

def act(c,guard=2*H):
 a=1;w=[];S0=a+2*c
 while True:
  r,a,c=step(a,c);w.append(r)
  if r in 'dfgh' or a==1:break
  if guard is not None and a+2*c>=guard:return 'escape'
  assert len(w)<5000
 s=''.join(w); z=''.join('B' if a in 'bc' else a for a in w);g=[(r,len(list(l))) for r,l in groupby(z)];k=0
 for i in range(1,len(g)-1,2):
  if g[i:i+2]!=[('B',2),('j',1)]:break
  k+=1
 return len(g),k,g[:4],g[-8:],len(w),r,a,c,(1+2*c-S0)//2

if __name__=='__main__':
 for t,h,guard,expected in [(291,-6,2*H,(341,167,803,2117)),(900,0,None,(1035,516,2450,6493))]:
  c=2*((23*3**t)//30)+1-2*t+h; result=act(c,guard); observed=(result[0],result[1],result[4],result[-1]);assert observed==expected
  print('t, shift, below cap, (pieces, initial LR cycles, rules, section increase):',t,h,c<=H-8000000,observed)
 V=(900,1503,1098,1305);S=set(range(-65,-39));
 for _ in range(2):
  S={k for k in S if any((27*k+v)%4==0 and (27*k+v)//4 in S for v in V)};print('strip survivors:',sorted(S))
 assert not S and 3*27**171>(23*8*H+1503)*4**171
