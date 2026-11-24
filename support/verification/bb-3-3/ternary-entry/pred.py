from functools import lru_cache
H=(3**307-8282708212)//13959275
L=1+2*(H-8000000)
F=((10,35),(14,47),(14,53),(18,65))

def inv(S,c):
 a=S-2*c; out=[]
 if (a-2)%3==0:
  aa=(a-2)//3; cc=c+aa-1
  if aa>=1 and cc>=aa and cc%2 and aa%2:out.append(('J',S-4,cc))
 for (word,(D,b)) in zip(('bb','bc','cb','cc'),F):
  if (4*c-b)%9: continue
  cc=(4*c-b)//9; Q=S-D
  if cc<1:continue
  u=cc;v=Q
  for w in word:
   k=2 if w=='b' else 4
   if u%4!=(1 if w=='b' else 3) or v<3*u+k:break
   u=(3*u+(7 if w=='b' else 13))//2;v+=5 if w=='b' else 9
  else:assert u==c and v==S;out.append((word,Q,cc))
 return out
if __name__=='__main__':
 for c in (L*4//23+2,7):
  a=L-2*c;print('c mod9, S mod9, J residue',c%9,L%9,(5-L)%3,'preimages',inv(L,c),'i', (a%3,(a//3)%2,(c+a//3-4)%2,c+a//3-4>=a//3))
