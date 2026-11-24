from pred import *
@lru_cache(None)
def R(n,s):
 M=3**n;s=s%M
 if n==0:return frozenset({0})
 if n==1:return frozenset({(5-s)%3,2})
 A={(3*k+5-s)%M for k in R(n-1,(s-4)%(M//3))}
 for D,b in F:A.update(( (9*k+b)*pow(4,-1,M))%M for k in R(n-2,(s-D)%(M//9)))
 return frozenset(A)
if __name__=='__main__':
 for n in range(1,12):
  a=R(n,L%3**n);print(n,len(a),len(a)/3**n,3**(.731774*n),float(len(a))**(1/n))
