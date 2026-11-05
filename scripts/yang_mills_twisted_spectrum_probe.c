// Heat bath for S = beta*sum_p (2 - z_p tr U_p) on N^4 with spatial twist n12=1, SU(2) quaternions.
// Writes binned time correlators of phi_c,phi_s = sum_{x2,x3} {cos,sin}(pi(x2+1/2)/N) trW1, the k3=0, k2=pi/L projection:
// C1 = <phi phi> (one-gluon, electric flux), Cn = connected <O O> with O = phi_c^2+phi_s^2 (neutral, zero momentum).
// C3 = <P P> with P = mean over x1,x2 of trW3: the electric flux e3 sector, which tunnels between the W3 valleys.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef struct{double a,b,c,d;}Q;
static inline Q mul(Q x,Q y){Q r;r.a=x.a*y.a-x.b*y.b-x.c*y.c-x.d*y.d;r.b=x.a*y.b+x.b*y.a+x.c*y.d-x.d*y.c;r.c=x.a*y.c-x.b*y.d+x.c*y.a+x.d*y.b;r.d=x.a*y.d+x.b*y.c-x.c*y.b+x.d*y.a;return r;}
static inline Q inv(Q x){Q r={x.a,-x.b,-x.c,-x.d};return r;}
static unsigned long long s[2];
static inline double R(){unsigned long long a=s[0],b=s[1];s[0]=b;a^=a<<23;s[1]=a^b^(a>>17)^(b>>26);return ((s[1]+b)>>11)*(1.0/9007199254740992.0);}
int N,T,V,tw;double beta;Q*U;int *up[4],*dn[4];int (*co)[4];
static inline Q L(int x,int m){return U[x*4+m];}
static inline double zp(int x,int m,int n){ // sign on plaquette at x in plane (m,n)
 if(!tw)return 1;int a=m<n?m:n,b=m<n?n:m;return (a==1&&b==2&&co[x][1]==0&&co[x][2]==0)?-1:1;}
static Q hb(double k){Q g;double a;
 if(k<1e-9)a=2*R()-1;else for(;;){double x=R();a=1+log(x+(1-x)*exp(-4*k))/(2*k);if(R()<sqrt(fmax(0,1-a*a)))break;}
 double r=sqrt(fmax(0,1-a*a)),c=2*R()-1,ph=2*M_PI*R(),sn=sqrt(fmax(0,1-c*c));g.a=a;g.b=r*sn*cos(ph);g.c=r*sn*sin(ph);g.d=r*c;return g;}
static void sweep(){for(int x=0;x<V;x++)for(int m=0;m<4;m++){Q A={0,0,0,0};
 for(int n=0;n<4;n++){if(n==m)continue;int xm=up[m][x],xn=up[n][x],xdn=dn[n][x],xmdn=dn[n][xm];
  Q S=mul(mul(L(xm,n),inv(L(xn,m))),inv(L(x,n)));double z=zp(x,m,n);
  Q B=mul(mul(inv(L(xmdn,n)),inv(L(xdn,m))),L(xdn,n));double zb=zp(xdn,m,n);
  A.a+=z*S.a+zb*B.a;A.b+=z*S.b+zb*B.b;A.c+=z*S.c+zb*B.c;A.d+=z*S.d+zb*B.d;}
 double k=sqrt(A.a*A.a+A.b*A.b+A.c*A.c+A.d*A.d);Q Ah={A.a/k,A.b/k,A.c/k,A.d/k};U[x*4+m]=mul(hb(beta*k),inv(Ah));}}
int main(int ac,char**av){N=atoi(av[1]);beta=atof(av[2]);tw=atoi(av[3]);int therm=atoi(av[4]),bins=atoi(av[5]),per=atoi(av[6]);T=atoi(av[8]);s[0]=88172645463325252ULL+atoi(av[7])*1000003ULL;s[1]=0x9E3779B97F4A7C15ULL;for(int i=0;i<20;i++)R();
 V=T*N*N*N;U=malloc(sizeof(Q)*V*4);co=malloc(sizeof(int[4])*V);for(int m=0;m<4;m++){up[m]=malloc(sizeof(int)*V);dn[m]=malloc(sizeof(int)*V);}
 int p[4]={1,T,T*N,T*N*N};int sz[4]={T,N,N,N};for(int x=0;x<V;x++)for(int m=0;m<4;m++)co[x][m]=(x/p[m])%sz[m];
 for(int x=0;x<V;x++)for(int m=0;m<4;m++){int c=co[x][m],M=sz[m];up[m][x]=x+(((c+1)%M)-c)*p[m];dn[m][x]=x+(((c-1+M)%M)-c)*p[m];}
 // start at the flat twisted field
 Q one={1,0,0,0},I={0,1,0,0},J={0,0,1,0};for(int x=0;x<V;x++)for(int m=0;m<4;m++){Q q=one;if(tw&&m==1&&co[x][1]==0)q=I;if(tw&&m==2&&co[x][2]==0)q=J;U[x*4+m]=q;}
 for(int i=0;i<therm;i++)sweep();
 double *c3=calloc(T,sizeof(double)),*P3=calloc(T,sizeof(double));double *c1=calloc(T,sizeof(double)),*cn=calloc(T,sizeof(double)),*O=calloc(T,sizeof(double));double *w=malloc(sizeof(double)*T*N*N),*PC=calloc(T,sizeof(double)),*PS=calloc(T,sizeof(double));
 for(int b=0;b<bins;b++){for(int k=0;k<T;k++){c1[k]=cn[k]=c3[k]=0;}double om=0,w3a=0,w3m=0,w0a=0,pl=0;
  for(int it=0;it<per;it++){for(int sk=0;sk<3;sk++)sweep();
   for(int t=0;t<T;t++){O[t]=0;for(int a=0;a<N;a++)for(int c=0;c<N;c++){ // winding in direction 1 at (x0=t,x2=a,x3=c)
      int x=t*p[0]+a*p[2]+c*p[3];Q W=one;int y=x;for(int k=0;k<N;k++){W=mul(W,L(y,1));y=up[1][y];}
      double v=2*W.a;w[t*N*N+a*N+c]=v;}
     double pc=0,ps=0;for(int a=0;a<N;a++)for(int c=0;c<N;c++){double v=w[t*N*N+a*N+c];pc+=cos(M_PI*(a+.5)/N)*v;ps+=sin(M_PI*(a+.5)/N)*v;}
     pc/=N*N;ps/=N*N;PC[t]=pc;PS[t]=ps;O[t]=pc*pc+ps*ps;om+=O[t];}
   for(int t=0;t<T;t++){double v3=0;for(int a=0;a<N;a++)for(int b=0;b<N;b++){int x=t*p[0]+a*p[1]+b*p[2];Q W=one;int y=x;for(int k=0;k<N;k++){W=mul(W,L(y,3));y=up[3][y];}v3+=2*W.a;}P3[t]=v3/(N*N);}
   for(int t=0;t<T;t++)for(int d=0;d<T;d++){int t2=(t+d)%T;cn[d]+=O[t]*O[t2];c1[d]+=PC[t]*PC[t2]+PS[t]*PS[t2];c3[d]+=P3[t]*P3[t2];}
   for(int a=0;a<8;a++){int x=(int)(R()*V);Q W=one;int y=x;for(int k=0;k<N;k++){W=mul(W,L(y,3));y=up[3][y];}w3a+=fabs(2*W.a);w3m+=2*W.a;W=one;y=x;for(int k=0;k<T;k++){W=mul(W,L(y,0));y=up[0][y];}w0a+=fabs(2*W.a);}
  }
  printf("B %.6f %.6f %.6f %.6f",om/(T*per),w3a/(8*per),w3m/(8*per),w0a/(8*per));for(int d=0;d<T;d++)printf(" %.8e",c1[d]/(T*per));for(int d=0;d<T;d++)printf(" %.8e",cn[d]/(T*per));for(int d=0;d<T;d++)printf(" %.8e",c3[d]/(T*per));printf("\n");fflush(stdout);}
 return 0;}
