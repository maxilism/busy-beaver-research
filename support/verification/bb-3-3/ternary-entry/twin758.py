"""Check the previously reported raw #153/#758 merger, including unit cost and local table conjugacy."""
tables=['1RB2LC1RC_2LC---2RB_2LA0LB0RA','1RB0LB0RC_2LC2LA1RA_1RA1LC---']
Q=lambda s:dict(zip('ABC','CAB'))[s]
B=lambda b:(0,2,1)[b]
def parse(s):return {(q,b):z[3*b:3*b+3] for q,z in zip('ABC',s.split('_')) for b in range(3)}
a,b=map(parse,tables)
for (q,i),e in b.items():
 v='---' if e=='---' else str(B(int(e[0])))+('R' if e[1]=='L' else 'L')+Q(e[2]);assert a[Q(q),B(i)]==v

def run(tab,n):
 T={};q='A';x=0
 for _ in range(n):
  w,d,q=tab[q,T.get(x,0)];assert q!='-'
  if w=='0':T.pop(x,None)
  else:T[x]=int(w)
  x+=1 if d=='R' else -1
 return q,x,T
s,x,T=run(a,1841608);ss,y,U=run(b,1790901);assert s==Q(ss) and T=={x-(i-y):B(v) for i,v in U.items()}
print('Matched raw #758 and #153 post-step states, positions and nonblank counts:',s,x,len(T),ss,y,len(U),'clock offset:',1841608-1790901)
