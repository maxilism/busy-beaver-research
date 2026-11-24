// Exact DP on a finite section basin for #758; native unsigned arithmetic, 512 checked bits.
// g++ -std=c++17 -O3 -Wall basin758.cpp -o basin && ./basin [N [table.bin]]
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <algorithm>
#include <vector>
using u64=uint64_t;using u128=__uint128_t;
struct U{
 std::array<u64,8> x{}; U(u64 a=0){x[0]=a;}
 int sz()const{for(int i=7;i>=0;i--)if(x[i])return i+1;return 0;}
 long double approx()const{int n=sz();return n?std::ldexp((long double)x[n-1],64*(n-1)):0;}
 int cmp(const U&z)const{for(int i=7;i>=0;i--)if(x[i]!=z.x[i])return x[i]<z.x[i]?-1:1;return 0;}
 U plus(const U&z)const{U r;u64 carry=0;for(int i=0;i<8;i++){u128 v=(u128)x[i]+z.x[i]+carry;r.x[i]=v;carry=v>>64;}assert(!carry);return r;}
 U add(u64 a)const{U r=*this;for(int i=0;i<8&&a;i++){u64 old=r.x[i];r.x[i]+=a;a=r.x[i]<old;}assert(!a);return r;}
 U minus(const U&z)const{U r;u64 b=0;for(int i=0;i<8;i++){u64 t=x[i]-b;u64 bb=x[i]<b;r.x[i]=t-z.x[i];b=bb||(t<z.x[i]);}assert(!b);return r;}
 U times(u64 a)const{U r;u64 c=0;for(int i=0;i<8;i++){u128 v=(u128)x[i]*a+c;r.x[i]=v;c=v>>64;}assert(!c);return r;}
 U mul(const U&z)const{int n=sz(),m=z.sz();if(n==1)return z.times(x[0]);if(m==1)return times(z.x[0]);U r;for(int i=0;i<n;i++){u64 c=0;for(int j=0;j<m;j++){assert(i+j<8);u128 v=(u128)x[i]*z.x[j]+r.x[i+j]+c;r.x[i+j]=v;c=v>>64;}if(c){assert(i+m<8);r.x[i+m]=c;}}return r;}
 U half()const{U r;for(int i=0;i<8;i++)r.x[i]=(x[i]>>1)|(i<7?(x[i+1]<<63):0);return r;}
 U divide_exact(unsigned a)const{U r;unsigned c=0;for(int i=7;i>=0;i--){u128 v=((u128)c<<64)+x[i];r.x[i]=v/a;c=v%a;}assert(!c);return r;}
};
U pw[320],H;
// Sufficient input guards: odd a,c and 3a<=S. Check maximality with integers.
int init_run(const U&a,const U&S){U A=a.add(1);int k=std::max(1,(int)(std::log(S.approx()/A.approx())/std::log((long double)3)));auto ok=[&](int h){assert(h>0&&h<319);return pw[h].mul(A).cmp(S.add(4*h-1))<=0;};while(k>1&&!ok(k))--k;assert(ok(k));while(ok(k+1))++k;return k;}
struct Start{U a,c;int ds,steps;};
Start head(int d){U c0=H.minus(U(d));bool even=!(c0.x[0]&1);U a=even?3:1,c=even?c0.add(3):c0,S=a.plus(c.times(2));int k=init_run(a,S);a=pw[k].mul(a.add(1)).minus(U(1));c=S.add(4*k).minus(a).half();return{a,c,4*k+(even?8:0),k+(even?1:0)};}
int max_steps=0,max_jump=0,halt_d=0,halt_f=0;u64 calls=0;int loop(int d,const Start&st){U a=st.a,c=st.c.minus(U(d&~1));int ds=st.ds,t=st.steps;
 while(t<5000){++calls;++t;
  if(c.cmp(a)<0){assert(c.x[0]&1);U gap=a.minus(c);int r=c.x[0]%4;int sh=r==1?2:4;
   if(gap.cmp(U(sh))>=0){a=gap.minus(U(sh));c=c.times(3).add(r==1?7:13).half();ds+=r==1?5:9;}
   else if(gap.x[0]==2&&r==3){a=c.times(3).add(8);c=1;ds+=8;}
   else if(gap.x[0]==3&&r==3){++halt_d;max_steps=std::max(max_steps,t);return 0;}
   else {assert(gap.x[0]==1);++halt_f;max_steps=std::max(max_steps,t);return 0;}
  }else if(!(a.x[0]&1)){assert(c.x[0]&1);ds+=5;assert(!(ds&1));max_steps=std::max(max_steps,t);return ds/2;}
  else {assert(c.x[0]&1);
   // Small-a mixed rerun is accelerated. For all other cases do the original single j.
   if(a.sz()<=4&&c.sz()>=6){U S=a.plus(c.times(2));int k=init_run(a,S);a=pw[k].mul(a.add(1)).minus(U(1));c=S.add(4*k).minus(a).half();ds+=4*k;t+=k-1;}
   else {c=c.minus(a).add(1);a=a.times(3).add(2);ds+=4;}
  }
 }
 std::abort(); // finite cap; never infer a halt from timeout.
}
int main(int argc,char**argv){int N=argc>1?std::atoi(argv[1]):8000000;assert(N>=2&&N<=100000000);pw[0]=1;for(int k=1;k<320;k++)pw[k]=pw[k-1].times(3);H=pw[307].minus(U(8282708212ULL)).divide_exact(13959275);
 Start st[2]={head(0),head(1)};
 for(int i=0;i<2;i++){int d=N-((N-i)&1);auto end=head(d);assert(end.ds==st[i].ds&&end.steps==st[i].steps&&end.a.cmp(st[i].a)==0&&end.c.cmp(st[i].c.minus(U(d-i)))==0);}
 // Thus every intervening d of each parity has this leading run length (j guard monotone in seed c).
 std::vector<uint16_t> ret(N+1);std::vector<unsigned char> good(N+1);good[0]=1;int lastbad=-1,count=1;
 for(int d=0;d<=N;d++){int v=loop(d,st[d&1]);assert(v>=0&&v<65536);ret[d]=v;max_jump=std::max(max_jump,v);if(!d){assert(v==0);continue;}good[d]=v>0&&v<=d&&good[d-v];if(good[d])count++;else lastbad=d;}
 printf("N=%d lastbad=%d count=%d max_c_jump=%d max_macros=%d halt_d=%d halt_f=%d core_iterations=%llu\n",N,lastbad,count,max_jump,max_steps,halt_d,halt_f,(unsigned long long)calls);
 if(argc>2){FILE*f=fopen(argv[2],"wb");assert(f);assert(fwrite(ret.data(),2,ret.size(),f)==ret.size());fclose(f);}
 if(N==8000000){assert(lastbad==3403054);}
}
