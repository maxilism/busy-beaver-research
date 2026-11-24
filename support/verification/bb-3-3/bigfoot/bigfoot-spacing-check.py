# Independent finite table/trace/congruence checks from the six primitive sweeps.
from itertools import product
p,q=256,81

def block(y):
    b,c=4*y+1,2
    w=[]
    for t in range(4):
        k,r=divmod(b,6)
        w.append((0,1,-1,0,1,0)[r]); b,c=8*k+c+(-1,-1,3,1,3,5)[r],(2,3,2,5,2,3)[r]
    assert c==2 and b%4==1
    return (b-1)//4,tuple(w)

def e(y):return q*block(y)[0]-p*y
pairs=[(5,43),(2,40),(4,47),(1,44),(8,46),(17,55)]
expected=[(259,251,(0,0,-1,-1)),(217,209,(0,0,0,-1)),(191,199,(0,0,-1,1)),(149,157,(0,1,1,-1)),(139,131,(0,1,0,1)),(103,95,(0,1,1,1))]
for v,((r,s),(d,f,w)) in enumerate(zip(pairs,expected),-2):
    assert (e(r),e(s),block(r)[1],block(s)[1],sum(w),abs(d-f))==(d,f,w,w,v,8)
    print(v,r,s,d,f,w)
assert sum(sum(block(i)[1])==4 for i in range(q))==1
N=49; y,h=0,2
for i in range(N):
    y,dl=block(y)
    for v in dl: h+=v;assert h>=0
assert (y,h)==(3021335427802676475075229,27)
dy=535992208665470815;true=y;h_true=h;z=y+dy;h_bad=h;rs=[];sweep=0
for i in range(14):
    rs.append(z%q);true,a=block(true);z,b=block(z);assert b==(0,0,-1,-1)
    for v,w in zip(a,b):
        sweep+=1;h_true+=v;h_bad+=w;assert h_true>=0 and ((h_bad<0)==(sweep==56))
assert h_true-h==11
print('block49: y,h,perturbation,net of true next 14,other rows',y,h,dy,h_true-h,rs)
# Compare 3-block subfamilies for all 6^3 net words and all 2^3 row choices
# using both inverse address formula and forward determination of rows.
for word in product(range(6),repeat=3):
    for rows in product(*(pairs[i] for i in word)):
        m=q**len(rows); iv=pow(p,-1,m); z=q*iv%m
        size=-sum(e(r)*iv*pow(z,j,m) for j,r in enumerate(rows))%m
        got=[]
        for _ in rows: got.append(size%q);size=block(size)[0]
        assert tuple(got)==rows
print('1728 exact inverse-congruence checks passed')
