// Heat-bath for the literal output law of connected(n,beta,j,e,d,q,r,u,0,0):
// action = beta*kin(u,v0) + beta*sum_{t<j}kin(v_t,v_{t+1}) + beta*sum_t pot(v_t), fixed input u, SU(2) quaternions.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef struct{double a,b,c,d;}Q;
static inline Q mul(Q x,Q y){Q r;r.a=x.a*y.a-x.b*y.b-x.c*y.c-x.d*y.d;r.b=x.a*y.b+x.b*y.a+x.c*y.d-x.d*y.c;r.c=x.a*y.c-x.b*y.d+x.c*y.a+x.d*y.b;r.d=x.a*y.d+x.b*y.c-x.c*y.b+x.d*y.a;return r;}
static inline Q inv(Q x){Q r={x.a,-x.b,-x.c,-x.d};return r;}
static unsigned long long s[2];
static inline double U(){unsigned long long a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return ((s[1]+b)>>11)*(1.0/9007199254740992.0);}
int n,J; double beta; Q *V,*IN,*H;
#define HI(t,x) ((t)*n*n*n+(x))
static inline int X(int x,int y,int z){return ((x+n)%n)+n*(((y+n)%n)+n*((z+n)%n));}
static inline int idx(int t,int x,int i){return (t*n*n*n+x)*3+i;}
int stp[3];
static inline int step(int x,int i){int a=x%n,b=(x/n)%n,c=x/(n*n);if(i==0)a++;if(i==1)b++;if(i==2)c++;return X(a,b,c);}
static inline int back(int x,int i){int a=x%n,b=(x/n)%n,c=x/(n*n);if(i==0)a--;if(i==1)b--;if(i==2)c--;return X(a,b,c);}
// Wilson weight exp(+beta*tr(v*A)) with tr=2*a; A = sum of "closing" factors
static Q staple(int t,int x,int i){Q A={0,0,0,0};
 for(int j=0;j<3;j++){if(j==i)continue;
  int xi=step(x,i),xj=step(x,j),xmj=back(x,j),ximj=back(xi,j);
  // U(x,i)U(xi,j)U(xj,i)^-1U(x,j)^-1 -> closing = U(xi,j)U(xj,i)^-1U(x,j)^-1
  Q S=mul(mul(V[idx(t,xi,j)],inv(V[idx(t,xj,i)])),inv(V[idx(t,x,j)]));
  Q B=mul(mul(inv(V[idx(t,ximj,j)]),inv(V[idx(t,xmj,i)])),V[idx(t,xmj,j)]);
  A.a+=S.a+B.a;A.b+=S.b+B.b;A.c+=S.c+B.c;A.d+=S.d+B.d;}
 // kinetic: tr(u^-1 v)=tr(v u^-1)
 int xi=step(x,i);
 // v_t(x,i) couples to slice t-1 via h_{t-1}(x) v h_{t-1}(xi)^-1 v_{t-1}^-1 (first step: no h, literal boundaryAction)
 Q k1= t==0? inv(IN[idx(0,x,i)]) : mul(mul(inv(H[HI(t-1,xi)]),inv(V[idx(t-1,x,i)])),H[HI(t-1,x)]);
 A.a+=k1.a;A.b+=k1.b;A.c+=k1.c;A.d+=k1.d;
 // and to slice t+1 via h_t(x) v_{t+1}(x,i) h_t(xi)^-1 v_t^-1
 if(t<J){Q k2=mul(mul(H[HI(t,xi)],inv(V[idx(t+1,x,i)])),inv(H[HI(t,x)]));A.a+=k2.a;A.b+=k2.b;A.c+=k2.c;A.d+=k2.d;}
 return A;}
// sample g with density ∝ exp(2*bk*g.a) on S^3 (Creutz/KP style)
static Q hb(double k){Q g;double a;
 if(k<1e-9){a=2*U()-1;}else{for(;;){double x=U();double y=exp(-2*k*2);(void)y;a=1+log(x+(1-x)*exp(-4*k))/(2*k);if(U()*U()<=1-a*a&&0)break;double acc=sqrt(fmax(0,1-a*a));if(U()<acc)break;}}
 double r=sqrt(fmax(0,1-a*a)),c=2*U()-1,ph=2*M_PI*U(),sn=sqrt(fmax(0,1-c*c));g.a=a;g.b=r*sn*cos(ph);g.c=r*sn*sin(ph);g.d=r*c;return g;}
static void sweepH(double b){int N=n*n*n;for(int t=0;t<J;t++)for(int x=0;x<N;x++){Q A={0,0,0,0};
 for(int i=0;i<3;i++){int xi=step(x,i),xb=back(x,i);
  Q a=mul(mul(V[idx(t+1,x,i)],inv(H[HI(t,xi)])),inv(V[idx(t,x,i)]));
  Q c=mul(mul(inv(V[idx(t+1,xb,i)]),inv(H[HI(t,xb)])),V[idx(t,xb,i)]);
  A.a+=a.a+c.a;A.b+=a.b+c.b;A.c+=a.c+c.c;A.d+=a.d+c.d;}
 double k=sqrt(A.a*A.a+A.b*A.b+A.c*A.c+A.d*A.d);Q Ah={A.a/k,A.b/k,A.c/k,A.d/k};H[HI(t,x)]=mul(hb(b*k),inv(Ah));}}
static void sweep(double b){sweepH(b);int T=J+1,N=n*n*n;for(int t=0;t<T;t++)for(int x=0;x<N;x++)for(int i=0;i<3;i++){
 Q A=staple(t,x,i);double k=sqrt(A.a*A.a+A.b*A.b+A.c*A.c+A.d*A.d);
 // weight exp(b*tr(vA))=exp(2b Re(vA)); w=vA/k => density exp(2bk w.a); v=w*(A/k)^-1
 if(k<1e-12){Q g=hb(0);V[idx(t,x,i)]=g;continue;}
 Q Ah={A.a/k,A.b/k,A.c/k,A.d/k};Q w=hb(b*k);V[idx(t,x,i)]=mul(w,inv(Ah));}}
static double energy(){double E=0;int N=n*n*n;for(int t=0;t<=J;t++)for(int x=0;x<N;x++)for(int i=0;i<3;i++){
  for(int j=i+1;j<3;j++){int xi=step(x,i),xj=step(x,j);Q P=mul(mul(mul(V[idx(t,x,i)],V[idx(t,xi,j)]),inv(V[idx(t,xj,i)])),inv(V[idx(t,x,j)]));E+=2-2*P.a;}
  int xi=step(x,i);Q k=t==0?mul(inv(IN[idx(0,x,i)]),V[idx(0,x,i)]):mul(mul(mul(H[HI(t-1,x)],V[idx(t,x,i)]),inv(H[HI(t-1,xi)])),inv(V[idx(t-1,x,i)]));E+=2-2*k.a;}
 return E;}
int main(int ac,char**av){n=atoi(av[1]);J=atoi(av[2]);beta=atof(av[3]);int kind=atoi(av[4]);int therm=atoi(av[5]),meas=atoi(av[6]);int seed=atoi(av[7]);
 s[0]=88172645463325252ULL+seed*1000003ULL;s[1]=0x9E3779B97F4A7C15ULL^seed;for(int i=0;i<20;i++)U();
 int N=n*n*n,L=3*N,T=J+1;IN=malloc(sizeof(Q)*L);V=malloc(sizeof(Q)*L*T);H=malloc(sizeof(Q)*N*(J+1));for(int k=0;k<N*(J+1);k++)H[k]=hb(0);
 for(int x=0;x<N;x++){int a=x%n,b=(x/n)%n;for(int i=0;i<3;i++){double sg=1;if(kind==1){if(i==1)sg=(a%2)?-1:1;if(i==2)sg=((a+b)%2)?-1:1;}Q q={sg,0,0,0};IN[idx(0,x,i)]=q;}}
 for(int k=0;k<L*T;k++)V[k]=hb(0);
 // anneal then thermalize
 for(int it=0;it<therm;it++){double f=fmin(1.0,0.2+0.8*it/(0.5*therm));sweep(beta*f);}
 // correlator of X_e=u_e^-1 v_e (slice 0, direction 0), vs reference e=(0,dir0)
 double A1=0,A2=0,xx=0;double hs0=1/(2*beta);if(hs0>1)hs0=1;double th0=2*asin(hs0),qa=cos(th0),qk=sin(th0);
 int far=X(n/2,n/2,n/2);double Ee=0,Ed=0,Eed=0;long NS=0;
 double *c3=calloc(N,sizeof(double)),*c0=calloc(N,sizeof(double)),*m0=calloc(N,sizeof(double)),E=0,plaq=0;
 // translation-averaged over reference sites for dir 0 : use a few references
 int nref=N<512?N:512;
 for(int it=0;it<meas;it++){for(int sk=0;sk<5;sk++)sweep(beta);E+=energy();
  Q *W=malloc(sizeof(Q)*N);for(int x=0;x<N;x++)W[x]=mul(inv(IN[idx(0,x,0)]),V[idx(0,x,0)]);
  for(int x=0;x<N;x++)m0[x]+=W[x].a;for(int x=0;x<N;x++)xx+=1-W[x].a*W[x].a;
  for(int rr=0;rr<30;rr++){Q g=hb(0);Q xe=mul(mul(g,W[0]),inv(g)),xd=mul(mul(g,W[far]),inv(g));
    double Fe=2*beta*((qa-1)*xe.a+qk*xe.d),Fd=2*beta*((qa-1)*xd.a+qk*xd.d);Ee+=exp(Fe);Ed+=exp(Fd);Eed+=exp(Fe+Fd);NS++;}
  Q w0=W[0];for(int x=0;x<N;x++){c3[x]+=w0.b*W[x].b+w0.c*W[x].c+w0.d*W[x].d;c0[x]+=w0.a*W[x].a;}
  free(W);}
 for(int x=0;x<N;x++){c3[x]/=meas;c0[x]/=meas;m0[x]/=meas;}
 // exact source covariance with rotation q=cos th+k sin th, beta*||q-1||=1 ; rotation about axis: Cov via SO(3) symmetrization (central u)
 double hs=1/(2*beta);if(hs>1)hs=1;double th=2*asin(hs);double q0=cos(th),q3=sin(th);
 // F=beta*(tr(q^-1 X)-tr X)=2beta((q0-1)x0 + q3 x3)
 double farS=0,sum=0,farmax=0;int cnt=0;
 for(int x=0;x<N;x++){int a=x%n,b=(x/n)%n,c=x/(n*n);int da=a<n-a?a:n-a,db=b<n-b?b:n-b,dc=c<n-c?c:n-c;int r=da>db?da:db;r=r>dc?r:dc;
   double cov=4*beta*beta*((q0-1)*(q0-1)*(c0[x]-m0[0]*m0[x])+q3*q3*c3[x]/3.0);
   if(r>=1)sum+=fabs(cov);
   if(r>=n/2){farS+=fabs(cov);cnt++;if(fabs(cov)>farmax)farmax=fabs(cov);}}
 printf("n=%d j=%d beta=%g kind=%s E/link=%.4f  Cov(r>=n/2): mean|.|=%.5f max=%.5f  sum_d|Cov|(dir0)=%.3f  decayBound16^-k: %.2e (k=log2(n/2))\n",n,J,beta,kind?"pi-flux":"flat",E/meas/(L*T),farS/cnt,farmax,sum,pow(16,-log2(n/2.)));
 printf("   <|x|^2>=%.4f\n",xx/meas/N);Ee/=NS;Ed/=NS;Eed/=NS;double ml=log(Eed)-log(Ee)-log(Ed);printf("   mixedLog(e,antipode,q,q)=%.5f  |exp(mixedLog)-1|=%.5f\n",ml,fabs(exp(ml)-1));
 return 0;}
