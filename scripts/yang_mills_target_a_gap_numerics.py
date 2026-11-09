"""Numerical test of the Target A neutral gap on the twisted heatbath (numerics, not a proof).

Law: SU(2) Wilson action S = beta_std * sum_p (1 - z_p Re U_p) on T x N^3, twist n12 = 1 (z_p = -1 on the plaquettes of
plane (1,2) at x1 = x2 = 0), the law of yang_mills_twisted_step_scaling.py but with T free. Same update: heatbath plus three
overrelaxation sweeps. README's beta is beta_std/2.

Prediction under test (Twisted/README.md, Target A, item 4). At fixed twisted coupling u, the neutral gap obeys E1 L >= c > 0
uniformly in N, with c -> 2 pi as u -> 0. Neutral there, and in the Lean NeutralWindow, has no momentum restriction. This sentence
first said "neutral zero momentum gap", which was wrong; stage 1 below measures zero momentum only, and stage 2 adds the rest. On the lattice the tree value is E1 = 2 omega_N, omega_N =
2 asinh(sin(pi/(2N))), since the lowest neutral state is two gluons of momenta +-pi/L. u is the twisted gradient-flow coupling at
c = sqrt(8t)/L = 0.3 from the Wilson plaquette, normalized here by the exact lattice tree value for the same Euler flow.

WRITTEN BEFORE ANY PRODUCTION RUN. What counts against the prediction, on ensembles with T = 3L, using the fit energy of the
constant-free estimator below at tau >= L/4:
  F1 (uniformity). On a line of fixed u (all points within 10% of the line's u): E1 L at N = 12 (or the largest N reached) below
     E1 L at N = 6 by more than 25% and by more than 3 sigma.
  F2 (limit). Fitting E1 L - 2 N omega_N = a + b u on points with u < 1 at fixed N: |a| > 3 sigma and |a| > 0.5.
  F3 (low state). Any neutral channel with u < 1 with E1 L < pi at more than 3 sigma. That is below half the prediction.
Against the wrap-around account of the too-low T = L masses (next paragraph):
  F4. The constant-free estimator at T = L disagreeing with T = 3L at the same (N, beta) by more than 3 sigma. That would mean
     thermal effects beyond a constant in tau, and T = L would then not be usable at all.
What does NOT count for the prediction: agreement at N <= 12 cannot show uniformity as N -> infinity. An effective mass decreases to the
lowest level the operators couple to, so it is an upper bound on that level only, and a state with small overlap can hide. The theorem
wants a lower bound on E1; numerics at finite tau can only fail to find something lower. If there is no plateau the result is
reported as inconclusive, not as agreement. The result is also only as good as the operator basis: mixed polarization two-gluon states,
which at tree level are degenerate with those measured, have no dedicated operator here.

T = L and wrap-around, stated before the run. Neutral operators have no matrix element between flux sectors, but the law is
Tr T^T, which sums over all sectors. So a state of flux e contributes exp(-E_e (T-tau) - E' tau) |<e|O|e'>|^2. For e' = e this
is CONSTANT in tau and survives the vacuum subtraction. In free theory O = |Phi|^2 has connected correlator exactly proportional to
cosh^2(omega (tau-T/2)) = (cosh(2 omega (tau-T/2)) + 1)/2, so with E = 2 omega the constant is as large as the cosh coefficient at
every T. Its share at tau is 2 exp(-E (T/2 - tau)), which at E L = 2 pi is 0.41 at tau = L/4, T = L, and 0.0037 at tau = L/2, T = 3L.
This should explain README's low T = L masses. So the primary estimator uses D(tau) = C(tau) - C(tau+1), which removes
the constant and needs no vacuum subtraction, and obeys the same arccosh recursion. Beyond the constant, at order g^2 the transition
from a one-gluon state (E = pi/L) to a state of the same flux and momentum gives a rate as low as (sqrt(2)+1-1) pi/L = 4.44/L, weighted
by exp(-pi T/L). The estimator cannot remove it. It should be visible at T = L only.

Observables on each slice, spatial links only, so the positive transfer matrix structure is kept, at three APE levels with center
signs (n = 0, round((N/4)^2), round((0.45 N)^2) steps of U -> proj(U + rho sum z staple), rho = 1/4, so a fixed smearing radius in units of L):
  flux-carrying, as controls: Phi1 = mean over x2,x3 of phase(x2) tr W1, the k2 = pi/L projection; Phi2 with x1, x2 exchanged; P3 = mean tr W3.
  neutral: O1 = |Phi1|^2, O2 = |Phi2|^2, L_i = mean (tr W_i)^2, and Q_ij = mean z Re P on spatial plane ij.
Neutrality is exact and is checked in selftest by applying the Z2^3 flips. tr W_1 changes sign across the twist between x2 = 0 and 1, so
the phase is continuous on x2 = 1..N. Channels are split by the exact symmetry x1 <-> x2. A: O1+O2, L1+L2, L3, Q12, Q13+Q23.
B: O1-O2, L1-L2, Q13-Q23.

Errors: delete-one-bin jackknife, with a report of how the error changes with bin size.

STAGE 2, WRITTEN 2026-10-31 AFTER AN INDEPENDENT REVIEW OF STAGE 1, BEFORE ITS RUNS AND BEFORE ANY ANALYSIS OF ITS CHANNELS, INCLUDING
ON THE STAGE 1 RAW DATA. Stage 1 has no operator for most of the tree-level lowest neutral multiplet. In the (1,0) colour the lowest gluons
are k = (0, +-pi/L, 0) with polarization 1 or 3, in (0,1) the mirror images with polarization 2 or 3. Two of them have E = 2 omega_N. They
make 20 states: total momentum p = +-2 pi/L along x2 or x1 with polarization pairs 11, 13, 33 (12 states), and p = 0 with pairs 11, 13, 31, 33
in each colour (8 states). Stage 1 reaches only p = 0 with pairs 11 and 33. Operators added, built from a second flux-carrying field:
  a = Phi1 = mean phase(x2) tr W1 (polarization 1), b = mean over x1,x2,x3 of phase(x2) tr[W1(x) F23(x)] (polarization 3), with W1(x) the
  line starting at x and F the vector part of the clover, a', b' the images under x1 <-> x2. Under x3 -> -x3, a is even and b is odd,
  exactly, so one a and one b make an R3-odd neutral operator.
  Z_even_A, B (p = 0, R3 even): |a|^2 +- |a'|^2, |b|^2 +- |b'|^2, with the stage 1 operators of that symmetry.
  Z_odd_A, B (p = 0, R3 odd, pairs 13, 31): ZS = Re(a b*) +- mirror, ZA = Im(a b*) +- mirror, T = F12.F23 + mirror (local) and its difference.
  P_even (|p| = 2 pi/L, R3 even): a^2, b^2, Q12(p), Q23(p). P_odd (|p| = 2 pi/L, R3 odd): a b, T(p).
Stage 2 ensembles have T = 3L and are listed in plan2(). Estimator and GEVP as in stage 1, at APE level 2, level 1 reported as well. a^2 is also read
from the stage 1 raw data, which have no b.
Plateau rule, applied to every channel, stage 1 too. At tau >= L/4, 3L/8, L/2: "no_plateau" if a later window differs from L/4 by more than 2 jackknife
errors of the difference or if chi2_diag/dof > 3 at L/4; otherwise "unresolved" if the error at the last window exceeds 0.75, or a fit is pinned at the
grid bound, or the signal to noise at the start of L/4 is below 1; otherwise "plateau". Only "plateau" values are read as an energy. For stage 1 this
rule is post hoc, since the review had already shown the window dependence.
What counts, with E L the fit at tau >= L/4:
  S1 (the operator check, which voids stage 2 if it fails). At beta_std = 32, N = 6 and 8, the one-gluon energy from b agrees with tree within max(3 sigma, 10%).
  F5 (a lower state stage 1 missed). A new channel with "plateau", below the lower of stage 1's GEVP_A, GEVP_B in the same ensemble by more than 3 jackknife
     sigma of the difference and by more than 0.5. This would lower c(u); it does not count against Target A by itself.
  F6 (uniformity). On a fixed u line, a new channel falling from N = 6 to the largest N by more than 25% and more than 3 sigma. The power of this is low:
     the bound that can actually be read is reported, with the slope of E L against ln N.
  F7 (limit). At u near 0.13, a new channel below tree by more than max(3 sigma, 0.5).
  F3b (low state). A new channel at u < 1, not flagged pinned or low signal, with E L + 3 sigma < pi.
There are about 20 channels on about 18 ensembles, so an isolated 3 sigma hit is expected by chance and would be reported as such.
Expected, not a criterion: at small u all channels agree with tree, and at larger u the lowest p != 0 level is not below the lowest p = 0 level.
What this cannot do: it covers the tree-level lowest multiplet only. A level descending from a higher multiplet with small overlap is still invisible, every
number is an upper bound on the lowest coupled level, and all ensembles stay in one e3 valley, so they see e3-even and e3-odd neutral levels together.

RESULT (added after the runs; the two pre-registered blocks above are unchanged). None of F1-F4, F5-F7 or F3b triggered, and S1 passed. This does not establish
the prediction: every number is an upper bound on the lowest coupled level at N <= 16. The lowest channel at u >= 1 stays the stage 1 p = 0, x1 <-> x2 even one, so
p != 0 and mixed polarization show no lower level among the 20 tree-level states. Most channels are "unresolved" under the plateau rule, and at N >= 12 nearly all of them,
so these are fit values with a status, not established plateaus. F1 and F6 are weak: see detectable_fall and fall_upper_95 in the JSON.
Added after seeing the data: the second stage 1 streams at N = 6, 8, 12 on the u = 2 line and N = 16 there, chasing a fall of 0.54 +- 0.30 from N = 6 to 12 which was not
reproduced (at N = 12 the two streams disagree at 2.4 sigma, recorded under "streams"); N = 16 goes beyond the sizes requested, see plan(). Also after the data: the slopes,
fall limits and combined_stage1_stage2, as descriptions. The T = L account above is consistent with the data but not derived: B/A near 1.5 at u near 1 has no calculation
behind it, the 4.44/L transition was not tested, and at tau >= L/4 the T = L errors are too large to separate T = L from T = 3L. Corrections made after the review are
listed under meta.corrections_after_review in the JSON.
Commands: selftest | selftest2 | run N T beta_std n_therm n_meas per flow_every seed | list JSON | plan | plan2 | phase [N T beta_std n] | analyze. Raw data go to RAW below.
"""
import os
for v in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','VECLIB_MAXIMUM_THREADS','MKL_NUM_THREADS','NUMBA_NUM_THREADS'): os.environ[v]='1'
RAW='/private/tmp/claude-501/ym-swarm/target_a_gap'
os.makedirs(RAW,exist_ok=True)
os.environ['NUMBA_CACHE_DIR']=RAW+'/numba'
import sys, json, time, glob, math, resource, multiprocessing
import numpy as np
from numba import njit
from scipy.optimize import minimize_scalar
OUT='/Users/thomasdifiore/unifiedtheory/data/yang_mills_target_a_gap_2026_10_31.json'
NAMES=['Phi1c','Phi1s','Phi2c','Phi2s','P3','O1','O2','L1','L2','L3','Q12','Q13','Q23']
NOP=len(NAMES)
# Stage 2 fields. B, Bp: phase(x) tr[W F] in the two mirror images. T1 = F12.F23, T2 = F21.F13 (mirror images). Suffix p: phase exp(2 pi i x2/N),
# suffix q: phase exp(2 pi i x1/N). c, s: real and imaginary parts.
NAMES2=['Bc','Bs','Bpc','Bps','T1','T2','Q12pc','Q12ps','Q23pc','Q23ps','Q12qc','Q12qs','Q13qc','Q13qs','T1pc','T1ps','T2qc','T2qs']
ALL=NAMES+NAMES2
RAW2=RAW+'/stage2'

def geom(N,T):
    V=T*N*N*N; sz=np.array([T,N,N,N]); p=np.array([1,T,T*N,T*N*N])
    co=np.stack([(np.arange(V)//p[m])%sz[m] for m in range(4)],1)
    up=np.stack([np.arange(V)+(((co[:,m]+1)%sz[m])-co[:,m])*p[m] for m in range(4)])
    dn=np.stack([np.arange(V)+(((co[:,m]-1+sz[m])%sz[m])-co[:,m])*p[m] for m in range(4)])
    tw=(co[:,1]==0)&(co[:,2]==0)
    return V,co,up.astype(np.int64),dn.astype(np.int64),tw

def flat(N,T):
    V,co,up,dn,tw=geom(N,T); U=np.zeros((V,4,4)); U[:,:,0]=1.
    U[co[:,1]==0,1]=np.array([0.,1,0,0]); U[co[:,2]==0,2]=np.array([0.,0,1,0])
    return U

@njit(inline='always')
def qm(a0,a1,a2,a3,b0,b1,b2,b3):
    return (a0*b0-a1*b1-a2*b2-a3*b3,a0*b1+a1*b0+a2*b3-a3*b2,a0*b2-a1*b3+a2*b0+a3*b1,a0*b3+a1*b2-a2*b1+a3*b0)

@njit(inline='always')
def zsign(tw,x,m,n):
    return -1. if (tw[x] and m+n==3 and m*n==2) else 1.

@njit(inline='always')
def tri(U,x,m,y,n,w,k,s1,s2,s3):
    # U[x,m]^s1 U[y,n]^s2 U[w,k]^s3 with s = +1 or -1 for the inverse
    q=qm(U[x,m,0],s1*U[x,m,1],s1*U[x,m,2],s1*U[x,m,3],U[y,n,0],s2*U[y,n,1],s2*U[y,n,2],s2*U[y,n,3])
    return qm(q[0],q[1],q[2],q[3],U[w,k,0],s3*U[w,k,1],s3*U[w,k,2],s3*U[w,k,3])

@njit
def staple(U,up,dn,tw,x,m,mlo):
    # A with Re(U[x,m] A) the plaquettes through the link. Directions n >= mlo only.
    a0=a1=a2=a3=0.
    xm=up[m,x]
    for n in range(mlo,4):
        if n==m: continue
        xn=up[n,x]; xdn=dn[n,x]; xmdn=dn[n,xm]
        z=zsign(tw,x,m,n); q=tri(U,xm,n,xn,m,x,n,1.,-1.,-1.)
        a0+=z*q[0];a1+=z*q[1];a2+=z*q[2];a3+=z*q[3]
        z=zsign(tw,xdn,m,n); q=tri(U,xmdn,n,xdn,m,xdn,n,-1.,-1.,1.)
        a0+=z*q[0];a1+=z*q[1];a2+=z*q[2];a3+=z*q[3]
    return a0,a1,a2,a3

@njit
def seed_rng(s):
    np.random.seed(s)

@njit
def sweep_hb(U,up,dn,tw,beta_std):
    V=U.shape[0]
    for x in range(V):
        for m in range(4):
            A=staple(U,up,dn,tw,x,m,0); k=math.sqrt(A[0]*A[0]+A[1]*A[1]+A[2]*A[2]+A[3]*A[3])
            if k<1e-12: continue
            kap=beta_std*k  # weight exp(kap a0): beta_std Re(U A)
            while True:
                r1=1.-np.random.random(); r2=np.random.random(); r3=1.-np.random.random(); r4=np.random.random()
                c=math.cos(2*math.pi*r2); lam2=-(math.log(r1)+c*c*math.log(r3))/(2*kap)
                if r4*r4<=1-lam2: break
            a0=1-2*lam2; r=math.sqrt(max(0.,1-a0*a0))
            cs=2*np.random.random()-1; sn=math.sqrt(max(0.,1-cs*cs)); ph=2*math.pi*np.random.random()
            g=qm(a0,r*sn*math.cos(ph),r*sn*math.sin(ph),r*cs,A[0]/k,-A[1]/k,-A[2]/k,-A[3]/k)
            U[x,m,0],U[x,m,1],U[x,m,2],U[x,m,3]=g

@njit
def sweep_or(U,up,dn,tw):
    V=U.shape[0]
    for x in range(V):
        for m in range(4):
            A=staple(U,up,dn,tw,x,m,0); k=math.sqrt(A[0]*A[0]+A[1]*A[1]+A[2]*A[2]+A[3]*A[3])
            if k<1e-12: continue
            h0,h1,h2,h3=A[0]/k,-A[1]/k,-A[2]/k,-A[3]/k
            q=qm(h0,h1,h2,h3,U[x,m,0],-U[x,m,1],-U[x,m,2],-U[x,m,3])
            q=qm(q[0],q[1],q[2],q[3],h0,h1,h2,h3)
            n=math.sqrt(q[0]*q[0]+q[1]*q[1]+q[2]*q[2]+q[3]*q[3])
            U[x,m,0],U[x,m,1],U[x,m,2],U[x,m,3]=q[0]/n,q[1]/n,q[2]/n,q[3]/n

@njit
def energy(U,up,tw):
    # mean over points and planes of 2 - 2 z Re P
    V=U.shape[0]; tot=0.
    for x in range(V):
        for m in range(4):
            for n in range(m+1,4):
                q=tri(U,up[m,x],n,up[n,x],m,x,n,1.,-1.,-1.)
                # Re(U[x,m] q)
                re=U[x,m,0]*q[0]-U[x,m,1]*q[1]-U[x,m,2]*q[2]-U[x,m,3]*q[3]
                tot+=2-2*zsign(tw,x,m,n)*re
    return tot/(6*V)

@njit
def flow_step(U,W,up,dn,tw,eps):
    # Euler step of the Wilson flow, U -> exp(-eps Im(U A)) U, all links at once
    V=U.shape[0]
    for x in range(V):
        for m in range(4):
            A=staple(U,up,dn,tw,x,m,0)
            q=qm(U[x,m,0],U[x,m,1],U[x,m,2],U[x,m,3],A[0],A[1],A[2],A[3])
            t1,t2,t3=-eps*q[1],-eps*q[2],-eps*q[3]
            th=math.sqrt(t1*t1+t2*t2+t3*t3); c=math.cos(th); s=math.sin(th)/th if th>1e-12 else 1.
            g=qm(c,s*t1,s*t2,s*t3,U[x,m,0],U[x,m,1],U[x,m,2],U[x,m,3])
            n=math.sqrt(g[0]*g[0]+g[1]*g[1]+g[2]*g[2]+g[3]*g[3])
            W[x,m,0],W[x,m,1],W[x,m,2],W[x,m,3]=g[0]/n,g[1]/n,g[2]/n,g[3]/n

@njit
def ape_step(U,W,up,dn,tw,rho):
    # spatial links only; the temporal links are copied
    V=U.shape[0]
    for x in range(V):
        W[x,0,0],W[x,0,1],W[x,0,2],W[x,0,3]=U[x,0,0],U[x,0,1],U[x,0,2],U[x,0,3]
        for i in range(1,4):
            s0,s1,s2,s3=U[x,i,0],U[x,i,1],U[x,i,2],U[x,i,3]
            for j in range(1,4):
                if j==i: continue
                # U_j(x) U_i(x+j) U_j^-1(x+i), which equals z U_i(x) on a zero-action field
                z=zsign(tw,x,i,j); q=tri(U,x,j,up[j,x],i,up[i,x],j,1.,1.,-1.)
                s0+=rho*z*q[0];s1+=rho*z*q[1];s2+=rho*z*q[2];s3+=rho*z*q[3]
                xd=dn[j,x]; z=zsign(tw,xd,i,j); q=tri(U,xd,j,xd,i,up[i,xd],j,-1.,1.,1.)
                s0+=rho*z*q[0];s1+=rho*z*q[1];s2+=rho*z*q[2];s3+=rho*z*q[3]
            n=math.sqrt(s0*s0+s1*s1+s2*s2+s3*s3)
            W[x,i,0],W[x,i,1],W[x,i,2],W[x,i,3]=s0/n,s1/n,s2/n,s3/n

@njit
def wind(U,up,x,m,n):
    a0,a1,a2,a3=1.,0.,0.,0.; y=x
    for _ in range(n):
        a0,a1,a2,a3=qm(a0,a1,a2,a3,U[y,m,0],U[y,m,1],U[y,m,2],U[y,m,3]); y=up[m,y]
    return 2*a0

@njit
def measure(U,up,tw,N,T,out,offset_phase):
    # out[t, op]. offset_phase = 1 is the correct phase, continuous on x = 1..N. 0 is the phase pi(a+1/2)/N, kept for comparison.
    cs=np.empty(N); sn=np.empty(N)
    for a in range(N):
        b=(a-offset_phase)%N
        cs[a]=math.cos(math.pi*(b+.5)/N); sn[a]=math.sin(math.pi*(b+.5)/N)
    p1,p2,p3=T,T*N,T*N*N
    for t in range(T):
        f1c=f1s=f2c=f2s=l1=l2=l3=p=0.
        for a in range(N):
            for c in range(N):
                w=wind(U,up,t+a*p2+c*p3,1,N); f1c+=cs[a]*w; f1s+=sn[a]*w; l1+=w*w
                w=wind(U,up,t+a*p1+c*p3,2,N); f2c+=cs[a]*w; f2s+=sn[a]*w; l2+=w*w
                w=wind(U,up,t+a*p1+c*p2,3,N); p+=w; l3+=w*w
        nn=N*N
        f1c/=nn;f1s/=nn;f2c/=nn;f2s/=nn;p/=nn;l1/=nn;l2/=nn;l3/=nn
        q12=q13=q23=0.
        for a in range(N):
            for b in range(N):
                for c in range(N):
                    x=t+a*p1+b*p2+c*p3
                    for k in range(3):
                        m,n=(1,2) if k==0 else ((1,3) if k==1 else (2,3))
                        q=tri(U,up[m,x],n,up[n,x],m,x,n,1.,-1.,-1.)
                        re=zsign(tw,x,m,n)*(U[x,m,0]*q[0]-U[x,m,1]*q[1]-U[x,m,2]*q[2]-U[x,m,3]*q[3])
                        if k==0: q12+=re
                        elif k==1: q13+=re
                        else: q23+=re
        v3=N*N*N
        out[t,0]=f1c;out[t,1]=f1s;out[t,2]=f2c;out[t,3]=f2s;out[t,4]=p
        out[t,5]=f1c*f1c+f1s*f1s;out[t,6]=f2c*f2c+f2s*f2s;out[t,7]=l1;out[t,8]=l2;out[t,9]=l3
        out[t,10]=q12/v3;out[t,11]=q13/v3;out[t,12]=q23/v3

def levels(N):
    return [0,max(1,round((N/4)**2)),max(2,round((0.45*N)**2))]

def measure_all(U,up,dn,tw,N,T,offset_phase=1):
    lv=levels(N); out=np.empty((T,len(lv),NOP)); A=U.copy(); B=np.empty_like(U); done=0
    for il,n in enumerate(lv):
        while done<n:
            ape_step(A,B,up,dn,tw,0.25); A,B=B,A; done+=1
        measure(A,up,tw,N,T,out[:,il],offset_phase)
    return out

@njit
def clover(U,up,dn,tw,x,m,n):
    # vector part of the mean of the four plaquettes of plane (m,n) based at x, all oriented m -> n, each with its twist sign, in the frame at x
    xm,xn,xdm,xdn=up[m,x],up[n,x],dn[m,x],dn[n,x]
    v1=v2=v3=0.
    q=tri(U,x,m,xm,n,xn,m,1.,1.,-1.); q=qm(q[0],q[1],q[2],q[3],U[x,n,0],-U[x,n,1],-U[x,n,2],-U[x,n,3]); z=zsign(tw,x,m,n)
    v1+=z*q[1];v2+=z*q[2];v3+=z*q[3]
    y=dn[m,xn]; q=tri(U,x,n,y,m,xdm,n,1.,-1.,-1.); q=qm(q[0],q[1],q[2],q[3],U[xdm,m,0],U[xdm,m,1],U[xdm,m,2],U[xdm,m,3]); z=zsign(tw,xdm,m,n)
    v1+=z*q[1];v2+=z*q[2];v3+=z*q[3]
    w=dn[n,xdm]; q=tri(U,xdm,m,w,n,w,m,-1.,-1.,1.); q=qm(q[0],q[1],q[2],q[3],U[xdn,n,0],U[xdn,n,1],U[xdn,n,2],U[xdn,n,3]); z=zsign(tw,w,m,n)
    v1+=z*q[1];v2+=z*q[2];v3+=z*q[3]
    y=up[m,xdn]; q=tri(U,xdn,n,xdn,m,y,n,-1.,1.,1.); q=qm(q[0],q[1],q[2],q[3],U[x,m,0],-U[x,m,1],-U[x,m,2],-U[x,m,3]); z=zsign(tw,xdn,m,n)
    v1+=z*q[1];v2+=z*q[2];v3+=z*q[3]
    return v1/4,v2/4,v3/4

@njit
def measure2(U,up,dn,tw,N,T,out):
    # out[t, op] for NAMES2, on one slice at a time. tr[W(x) F(x)] = 2 Re(W F) = -2 W.F, with W running along the line by W(x+1) = U(x)^-1 W(x) U(x).
    cs=np.empty(N); sn=np.empty(N); c2=np.empty(N); s2=np.empty(N)
    for a in range(N):
        b=(a-1)%N
        cs[a]=math.cos(math.pi*(b+.5)/N); sn[a]=math.sin(math.pi*(b+.5)/N)
        c2[a]=math.cos(2*math.pi*a/N); s2[a]=math.sin(2*math.pi*a/N)
    p1,p2,p3=T,T*N,T*N*N
    F12=np.empty((N,N,N,3)); F13=np.empty((N,N,N,3)); F23=np.empty((N,N,N,3))
    v3=float(N*N*N)
    for t in range(T):
        r=np.zeros(18)
        for a1 in range(N):
            for a2 in range(N):
                for a3 in range(N):
                    x=t+a1*p1+a2*p2+a3*p3
                    F12[a1,a2,a3,0],F12[a1,a2,a3,1],F12[a1,a2,a3,2]=clover(U,up,dn,tw,x,1,2)
                    F13[a1,a2,a3,0],F13[a1,a2,a3,1],F13[a1,a2,a3,2]=clover(U,up,dn,tw,x,1,3)
                    F23[a1,a2,a3,0],F23[a1,a2,a3,1],F23[a1,a2,a3,2]=clover(U,up,dn,tw,x,2,3)
                    t1=F12[a1,a2,a3,0]*F23[a1,a2,a3,0]+F12[a1,a2,a3,1]*F23[a1,a2,a3,1]+F12[a1,a2,a3,2]*F23[a1,a2,a3,2]
                    t2=-(F12[a1,a2,a3,0]*F13[a1,a2,a3,0]+F12[a1,a2,a3,1]*F13[a1,a2,a3,1]+F12[a1,a2,a3,2]*F13[a1,a2,a3,2])
                    q=tri(U,up[1,x],2,up[2,x],1,x,2,1.,-1.,-1.); q12=zsign(tw,x,1,2)*(U[x,1,0]*q[0]-U[x,1,1]*q[1]-U[x,1,2]*q[2]-U[x,1,3]*q[3])
                    q=tri(U,up[1,x],3,up[3,x],1,x,3,1.,-1.,-1.); q13=U[x,1,0]*q[0]-U[x,1,1]*q[1]-U[x,1,2]*q[2]-U[x,1,3]*q[3]
                    q=tri(U,up[2,x],3,up[3,x],2,x,3,1.,-1.,-1.); q23=U[x,2,0]*q[0]-U[x,2,1]*q[1]-U[x,2,2]*q[2]-U[x,2,3]*q[3]
                    r[4]+=t1; r[5]+=t2
                    r[6]+=c2[a2]*q12; r[7]+=s2[a2]*q12; r[8]+=c2[a2]*q23; r[9]+=s2[a2]*q23
                    r[10]+=c2[a1]*q12; r[11]+=s2[a1]*q12; r[12]+=c2[a1]*q13; r[13]+=s2[a1]*q13
                    r[14]+=c2[a2]*t1; r[15]+=s2[a2]*t1; r[16]+=c2[a1]*t2; r[17]+=s2[a1]*t2
        for k in range(4,18): r[k]/=v3
        for a in range(N):
            for c in range(N):
                # direction 1, at x2 = a, x3 = c
                x0=t+a*p2+c*p3; w0,w1,w2,w3=1.,0.,0.,0.; y=x0
                for _ in range(N):
                    w0,w1,w2,w3=qm(w0,w1,w2,w3,U[y,1,0],U[y,1,1],U[y,1,2],U[y,1,3]); y=up[1,y]
                val=0.; y=x0
                for a1 in range(N):
                    val+=-2*(w1*F23[a1,a,c,0]+w2*F23[a1,a,c,1]+w3*F23[a1,a,c,2])
                    g=qm(U[y,1,0],-U[y,1,1],-U[y,1,2],-U[y,1,3],w0,w1,w2,w3); w0,w1,w2,w3=qm(g[0],g[1],g[2],g[3],U[y,1,0],U[y,1,1],U[y,1,2],U[y,1,3]); y=up[1,y]
                r[0]+=cs[a]*val; r[1]+=sn[a]*val
                # direction 2, at x1 = a, x3 = c
                x0=t+a*p1+c*p3; w0,w1,w2,w3=1.,0.,0.,0.; y=x0
                for _ in range(N):
                    w0,w1,w2,w3=qm(w0,w1,w2,w3,U[y,2,0],U[y,2,1],U[y,2,2],U[y,2,3]); y=up[2,y]
                val=0.; y=x0
                for a2 in range(N):
                    val+=-2*(w1*F13[a,a2,c,0]+w2*F13[a,a2,c,1]+w3*F13[a,a2,c,2])
                    g=qm(U[y,2,0],-U[y,2,1],-U[y,2,2],-U[y,2,3],w0,w1,w2,w3); w0,w1,w2,w3=qm(g[0],g[1],g[2],g[3],U[y,2,0],U[y,2,1],U[y,2,2],U[y,2,3]); y=up[2,y]
                r[2]+=cs[a]*val; r[3]+=sn[a]*val
        for k in range(4): r[k]/=v3
        for k in range(18): out[t,k]=r[k]

def measure_all2(U,up,dn,tw,N,T):
    lv=levels(N); out=np.empty((T,len(lv),len(ALL))); A=U.copy(); B=np.empty_like(U); done=0
    for il,n in enumerate(lv):
        while done<n:
            ape_step(A,B,up,dn,tw,0.25); A,B=B,A; done+=1
        measure(A,up,tw,N,T,out[:,il,:NOP],1)
        measure2(A,up,dn,tw,N,T,out[:,il,NOP:])
    return out

def tree_E(N,T,nsteps,eps):
    # E_plaq/g^2 at tree level for nsteps Euler flow steps of size eps: (3/2)/V sum_{colour,k} (1 - eps khat^2)^(2 nsteps)
    tot=0.; V=T*N**3
    g0=2*np.pi*np.arange(T)/T; g=2*np.pi*np.arange(N)/N
    h0=4*np.sin(g0/2)**2
    for e1,e2 in ((1,0),(0,1),(1,1)):
        h1=4*np.sin((g+np.pi*e1/N)/2)**2; h2=4*np.sin((g+np.pi*e2/N)/2)**2; h3=4*np.sin(g/2)**2
        kh=h0[:,None,None,None]+h1[None,:,None,None]+h2[None,None,:,None]+h3[None,None,None,:]
        tot+=((1-eps*kh)**(2*nsteps)).sum()
    return 1.5*tot/V

def flow_u(U,up,dn,tw,N,T,c=0.3,nsteps=32):
    t=(c*N)**2/8; eps=t/nsteps; A=U.copy(); B=np.empty_like(U)
    for _ in range(nsteps):
        flow_step(A,B,up,dn,tw,eps); A,B=B,A
    return 12*energy(A,up,tw)/tree_E(N,T,nsteps,eps),A

def tag(N,T,bstd,seed): return f"{RAW}/raw_N{N}_T{T}_b{bstd:.4f}_s{seed}.npz"

def run(N,T,bstd,nt,nm,per,fe,seed,verbose=True):
    fn=tag(N,T,bstd,seed)
    if os.path.exists(fn):
        d=np.load(fn)
        if int(d['n'])>=nm:
            print('have',fn,flush=True); return fn
    V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(seed+1000*N+int(bstd*1000))
    def upd():
        sweep_hb(U,up,dn,tw,bstd)
        for _ in range(3): sweep_or(U,up,dn,tw)
    t0=time.time()
    for i in range(nt): upd()
    t1=time.time()
    ops=np.empty((nm,T,len(levels(N)),NOP)); us=[]; es=[]; last=time.time()
    for i in range(nm):
        for _ in range(per): upd()
        ops[i]=measure_all(U,up,dn,tw,N,T)
        if fe>0 and i%fe==0:
            us.append(flow_u(U,up,dn,tw,N,T)[0]); es.append(energy(U,up,tw))
        if time.time()-last>600 or i==nm-1:
            last=time.time(); tmp=fn+'.tmp.npz'
            np.savez(tmp,N=N,T=T,beta_std=bstd,n=i+1,ops=ops[:i+1],u=np.array(us),e=np.array(es),per=per,fe=fe,nt=nt,lev=np.array(levels(N)),therm_s=t1-t0,run_s=time.time()-t1)
            os.replace(tmp,fn)
            if verbose: print(f"N={N} T={T} b={bstd} {i+1}/{nm} t={time.time()-t0:.0f}s u={np.mean(us) if us else 0:.3f} e={np.mean(es) if es else 0:.4f}",flush=True)
    return fn

def run2(N,T,bstd,nt,nm,per,fe,seed,verbose=True):
    """Stage 2 run: NAMES and NAMES2 on the same smeared fields."""
    os.makedirs(RAW2,exist_ok=True); fn=f"{RAW2}/raw2_N{N}_T{T}_b{bstd:.4f}_s{seed}.npz"
    if os.path.exists(fn):
        d=np.load(fn)
        if int(d['n'])>=nm:
            print('have',fn,flush=True); return fn
    V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(seed+1000*N+int(bstd*1000))
    def upd():
        sweep_hb(U,up,dn,tw,bstd)
        for _ in range(3): sweep_or(U,up,dn,tw)
    t0=time.time()
    for i in range(nt): upd()
    t1=time.time()
    ops=np.empty((nm,T,len(levels(N)),len(ALL))); us=[]; es=[]; last=time.time()
    for i in range(nm):
        for _ in range(per): upd()
        ops[i]=measure_all2(U,up,dn,tw,N,T)
        if fe>0 and i%fe==0:
            us.append(flow_u(U,up,dn,tw,N,T)[0]); es.append(energy(U,up,tw))
        if time.time()-last>600 or i==nm-1:
            last=time.time(); tmp=fn+'.tmp.npz'
            np.savez(tmp,N=N,T=T,beta_std=bstd,n=i+1,ops=ops[:i+1],u=np.array(us),e=np.array(es),per=per,fe=fe,nt=nt,lev=np.array(levels(N)),therm_s=t1-t0,run_s=time.time()-t1)
            os.replace(tmp,fn)
            if verbose: print(f"N={N} T={T} b={bstd} {i+1}/{nm} t={time.time()-t0:.0f}s u={np.mean(us) if us else 0:.3f} e={np.mean(es) if es else 0:.4f}",flush=True)
    return fn

def reflect3(U,co,N,T):
    """x3 -> -x3: link m != 3 at x goes to the reflected site; U3(x) becomes the inverse of the link between -x and -x-1."""
    p=[1,T,T*N,T*N*N]; r=co[:,0]*p[0]+co[:,1]*p[1]+co[:,2]*p[2]+((-co[:,3])%N)*p[3]; rm=co[:,0]*p[0]+co[:,1]*p[1]+co[:,2]*p[2]+((-co[:,3]-1)%N)*p[3]
    R=np.empty_like(U)
    for m in range(3): R[r,m]=U[:,m]
    R[rm,3]=U[:,3]*np.array([1.,-1,-1,-1])
    return R

def selftest2():
    """Exact symmetry checks of the stage 2 operators on a sampled field, then the weak-coupling polarization 3 one-gluon mass is left to S1."""
    ok=True
    def chk(name,cond,info=''):
        nonlocal ok
        print(('PASS ' if cond else 'FAIL ')+name,info,flush=True); ok=ok and cond
    N,T=4,6; V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(5)
    for _ in range(3):
        sweep_hb(U,up,dn,tw,8.); sweep_or(U,up,dn,tw)
    ix={k:i for i,k in enumerate(ALL)}
    O0=measure_all2(U,up,dn,tw,N,T)
    O1=np.empty((T,len(levels(N)),NOP)); A=U.copy(); B=np.empty_like(U); done=0
    for il,n in enumerate(levels(N)):
        while done<n:
            ape_step(A,B,up,dn,tw,.25); A,B=B,A; done+=1
        measure(A,up,tw,N,T,O1[:,il],1)
    chk('stage 2 run reproduces the stage 1 operators',np.abs(O0[:,:,:NOP]-O1).max()==0.)
    rng=np.random.default_rng(1); g=rng.normal(size=(V,4)); g/=np.linalg.norm(g,axis=1,keepdims=True)
    def Q(a,b):
        return np.stack([a[...,0]*b[...,0]-a[...,1]*b[...,1]-a[...,2]*b[...,2]-a[...,3]*b[...,3],a[...,0]*b[...,1]+a[...,1]*b[...,0]+a[...,2]*b[...,3]-a[...,3]*b[...,2],a[...,0]*b[...,2]-a[...,1]*b[...,3]+a[...,2]*b[...,0]+a[...,3]*b[...,1],a[...,0]*b[...,3]+a[...,1]*b[...,2]-a[...,2]*b[...,1]+a[...,3]*b[...,0]],-1)
    gc=g*np.array([1.,-1,-1,-1]); G=np.empty_like(U)
    for m in range(4): G[:,m]=Q(Q(g,U[:,m]),gc[up[m]])
    d=np.abs(measure_all2(G,up,dn,tw,N,T)-O0).max(); chk('all stage 2 operators gauge invariant',d<1e-10,d)
    zm=[ix[k] for k in ('Bc','Bs')]; zp=[ix[k] for k in ('Bpc','Bps')]; phi1=[ix['Phi1c'],ix['Phi1s']]; phi2=[ix['Phi2c'],ix['Phi2s']]
    local=[ix[k] for k in NAMES2[4:]]
    for dr in (1,2,3):
        F=U.copy(); s0=int(rng.integers(N)); F[co[:,dr]==s0,dr]*=-1; OF=measure_all2(F,up,dn,tw,N,T)
        d=np.abs(OF[:,:,local]-O0[:,:,local]).max(); chk(f'flip {dr} fixes the local stage 2 operators',d<1e-10,d)
        sg1=-1 if dr==1 else 1; sg2=-1 if dr==2 else 1
        d=np.abs(OF[:,:,zm]-sg1*O0[:,:,zm]).max(); chk(f'flip {dr} acts on b as on a',d<1e-10,d)
        d=np.abs(OF[:,:,zp]-sg2*O0[:,:,zp]).max(); chk(f"flip {dr} acts on b' as on a'",d<1e-10,d)
    p=[1,T,T*N,T*N*N]; idx=co[:,0]+co[:,2]*p[1]+co[:,1]*p[2]+co[:,3]*p[3]; X=np.empty_like(U)
    for m,mp in ((0,0),(1,2),(2,1),(3,3)): X[idx,mp]=U[:,m]
    OX=measure_all2(X,up,dn,tw,N,T)
    for a,b in (('Bc','Bpc'),('Bs','Bps'),('T1','T2'),('Q12pc','Q12qc'),('Q12ps','Q12qs'),('Q23pc','Q13qc'),('Q23ps','Q13qs'),('T1pc','T2qc'),('T1ps','T2qs')):
        d=max(np.abs(OX[:,:,ix[a]]-O0[:,:,ix[b]]).max(),np.abs(OX[:,:,ix[b]]-O0[:,:,ix[a]]).max()); chk(f'x1<->x2 exchanges {a}, {b}',d<1e-10,d)
    R=reflect3(U,co,N,T); d=abs(energy(R,up,tw)-energy(U,up,tw)); chk('x3 -> -x3 preserves the action',d<1e-11,d)
    OR=measure_all2(R,up,dn,tw,N,T)
    d=np.abs(OR[:,:,phi1+phi2]-O0[:,:,phi1+phi2]).max(); chk('x3 -> -x3 fixes a, a\'',d<1e-10,d)
    d=np.abs(OR[:,:,zm+zp]+O0[:,:,zm+zp]).max(); chk('x3 -> -x3 reverses b, b\'',d<1e-10,d)
    d=np.abs(OR[:,:,[ix['T1'],ix['T2'],ix['T1pc'],ix['T1ps'],ix['T2qc'],ix['T2qs']]]+O0[:,:,[ix['T1'],ix['T2'],ix['T1pc'],ix['T1ps'],ix['T2qc'],ix['T2qs']]]).max(); chk('x3 -> -x3 reverses T',d<1e-10,d)
    print('SELFTEST2','OK' if ok else 'FAILED',flush=True)
    return ok

def selftest():
    ok=True
    def chk(name,cond,info=''):
        nonlocal ok
        print(('PASS ' if cond else 'FAIL ')+name,info,flush=True); ok=ok and cond
    N,T=4,6; V,co,up,dn,tw=geom(N,T); U=flat(N,T)
    chk('flat field has zero action',abs(energy(U,up,tw))<1e-13,energy(U,up,tw))
    W=np.empty_like(U); ape_step(U,W,up,dn,tw,.25)
    chk('APE fixes the flat field',np.abs(W-U).max()<1e-12)
    flow_step(U,W,up,dn,tw,.05); chk('flow fixes the flat field',np.abs(W-U).max()<1e-12)
    seed_rng(5); sweep_hb(U,up,dn,tw,8.); sweep_or(U,up,dn,tw)
    e0=energy(U,up,tw); O0=measure_all(U,up,dn,tw,N,T)
    # overrelaxation preserves the action only link by link, on the staple; test one link
    W=U.copy(); sweep_or(W,up,dn,tw); e1=energy(W,up,tw); O=measure_all(W,up,dn,tw,N,T)
    chk('overrelaxation is microcanonical',abs(e1-e0)<1e-10,abs(e1-e0))
    # Gauge transformation
    rng=np.random.default_rng(1); g=rng.normal(size=(V,4)); g/=np.linalg.norm(g,axis=1,keepdims=True)
    def Q(a,b):
        return np.stack([a[...,0]*b[...,0]-a[...,1]*b[...,1]-a[...,2]*b[...,2]-a[...,3]*b[...,3],a[...,0]*b[...,1]+a[...,1]*b[...,0]+a[...,2]*b[...,3]-a[...,3]*b[...,2],a[...,0]*b[...,2]-a[...,1]*b[...,3]+a[...,2]*b[...,0]+a[...,3]*b[...,1],a[...,0]*b[...,3]+a[...,1]*b[...,2]-a[...,2]*b[...,1]+a[...,3]*b[...,0]],-1)
    gc=g*np.array([1.,-1,-1,-1]); G=np.empty_like(U)
    for m in range(4): G[:,m]=Q(Q(g,U[:,m]),gc[up[m]])
    chk('action gauge invariant',abs(energy(G,up,tw)-e0)<1e-11)
    O2=measure_all(G,up,dn,tw,N,T)
    chk('all operators gauge invariant',np.abs(O2-O0).max()<1e-10,np.abs(O2-O0).max())
    # Center flips: all links of direction d on one slab x_d = s change sign. Each plaquette has two or zero of them.
    for d in (1,2,3):
        F=U.copy(); s=int(rng.integers(N)); F[co[:,d]==s,d]*=-1
        chk(f'flip {d} preserves action',abs(energy(F,up,tw)-e0)<1e-12)
        OF=measure_all(F,up,dn,tw,N,T)
        neutral=np.abs(OF[:,:,5:]-O0[:,:,5:]).max()
        chk(f'flip {d} leaves every neutral operator fixed',neutral<1e-10,neutral)
        odd={1:(0,1),2:(2,3),3:(4,)}[d]
        chk(f'flip {d} reverses its flux operators',np.abs(OF[:,:,list(odd)]+O0[:,:,list(odd)]).max()<1e-10)
        other=[k for k in range(5) if k not in odd]
        chk(f'flip {d} fixes the other flux operators',np.abs(OF[:,:,other]-O0[:,:,other]).max()<1e-10)
    # x1 <-> x2 is a symmetry: exchange the coordinates and directions on a sampled field
    perm=np.empty(V,dtype=np.int64); sz=[T,N,N,N]; pp=[1,T,T*N,T*N*N]
    idx=co[:,0]+co[:,2]*pp[1]+co[:,1]*pp[2]+co[:,3]*pp[3]
    X=np.empty_like(U)
    for m,mp in ((0,0),(1,2),(2,1),(3,3)): X[idx,mp]=U[:,m]
    chk('x1<->x2 preserves action',abs(energy(X,up,tw)-e0)<1e-11,abs(energy(X,up,tw)-e0))
    OX=measure_all(X,up,dn,tw,N,T)
    chk('x1<->x2 exchanges O1,O2',np.abs(OX[:,:,5]-O0[:,:,6]).max()<1e-10 and np.abs(OX[:,:,6]-O0[:,:,5]).max()<1e-10)
    chk('x1<->x2 exchanges Q13,Q23, fixes Q12',np.abs(OX[:,:,11]-O0[:,:,12]).max()<1e-10 and np.abs(OX[:,:,10]-O0[:,:,10]).max()<1e-10)
    # Plaquette against the table in README (3 Re c = 2.711 at beta_std = 8, N = 8, so 2 - 2 Re P = 0.1927)
    N,T=8,8; V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(7); es=[]
    for i in range(160):
        sweep_hb(U,up,dn,tw,8.); sweep_or(U,up,dn,tw); sweep_or(U,up,dn,tw); sweep_or(U,up,dn,tw)
        if i>=60: es.append(energy(U,up,tw))
    print('plaquette energy N=8, beta_std=8',np.mean(es),'README 2 - 2*2.711/3 =',2-2*2.711/3,flush=True)
    chk('plaquette matches earlier heatbath',abs(np.mean(es)-(2-2*2.711/3))<0.002,np.mean(es))
    # Flow coupling at very weak coupling is close to g^2 = 4/beta_std
    for bstd in (512.,128.):
        N,T=6,18; V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(11); us=[]
        for i in range(60):
            sweep_hb(U,up,dn,tw,bstd); sweep_or(U,up,dn,tw); sweep_or(U,up,dn,tw); sweep_or(U,up,dn,tw)
            if i>=20 and i%4==0: us.append(flow_u(U,up,dn,tw,N,T)[0])
        print(f'beta_std={bstd} u={np.mean(us):.5f} +- {np.std(us)/np.sqrt(len(us)):.5f} g^2={4/bstd:.5f}',flush=True)
        chk(f'u/g^2 near 1 at beta_std={bstd}',abs(np.mean(us)*bstd/4-1)<0.12,np.mean(us)*bstd/4)
    # A flowed field is smooth, so its tr W1 profile shows where the sign jump of the antiperiodic mode sits
    u,A=flow_u(U,up,dn,tw,N,T,c=0.6,nsteps=80)
    p2=T*N
    prof=np.array([wind(A,up,a*p2,1,N) for a in range(N)])
    print('tr W1 against x2 on a flowed field (expected: smooth on 1..N, sign change between x2 = 0 and 1):',np.round(prof/np.abs(prof).max(),3).tolist(),flush=True)
    print('SELFTEST','OK' if ok else 'FAILED',flush=True)
    return ok

# ---------- analysis ----------
class LazyOps:
    """Operators computed on request, so an ensemble of 90000 configurations stays under the memory limit."""
    def __init__(self): self.f={}
    def __setitem__(self,k,fn): self.f[k]=fn
    def __getitem__(self,k): return self.f[k]()
    def __iter__(self): return iter(self.f)
    def items(self):
        for k in self.f: yield k,self.f[k]()

def combine(o):
    """o: n,T,lev,NOP. Returns the operators of channels A and B."""
    g=lambda s,l: o[:,:,l,NAMES.index(s)]
    A,B=LazyOps(),LazyOps()
    for l in range(o.shape[2]):
        A[f'O1+O2/{l}']=lambda l=l: g('O1',l)+g('O2',l); A[f'L1+L2/{l}']=lambda l=l: g('L1',l)+g('L2',l); A[f'L3/{l}']=lambda l=l: g('L3',l)
        A[f'Q12/{l}']=lambda l=l: g('Q12',l); A[f'Q13+Q23/{l}']=lambda l=l: g('Q13',l)+g('Q23',l)
        B[f'O1-O2/{l}']=lambda l=l: g('O1',l)-g('O2',l); B[f'L1-L2/{l}']=lambda l=l: g('L1',l)-g('L2',l); B[f'Q13-Q23/{l}']=lambda l=l: g('Q13',l)-g('Q23',l)
    return A,B

def binned_corr(X,Y,nb,center=True):
    """X,Y: n,T. Returns bins x T of (1/T) sum_t X(t+tau) Y(t), and the bin means of X and Y. With center, X and Y first lose their ensemble means. D(tau)
    and every connected correlator computed from what is returned are unchanged, and at weak coupling, where Q is 1 - 1e-5, this removes FFT round-off
    that the first version carried into some Q fits at N = 12. center = False is for flux operators, whose correlator is read with no subtraction."""
    n,T=X.shape; bs=n//nb
    mx,my=(X.mean(),Y.mean()) if center else (0.,0.)
    c=np.empty((nb,T))   # bin by bin, so the transforms never hold the whole ensemble
    for i in range(nb):
        x=X[i*bs:(i+1)*bs]-mx; y=Y[i*bs:(i+1)*bs]-my
        c[i]=np.fft.irfft(np.fft.rfft(x,axis=1)*np.conj(np.fft.rfft(y,axis=1)),n=T,axis=1).mean(0)/T
    return c,X[:bs*nb].reshape(nb,bs,T).mean((1,2))-mx,Y[:bs*nb].reshape(nb,bs,T).mean((1,2))-my

def sym(C): return 0.5*(C+np.roll(C[...,::-1],1,axis=-1))
def jk_samples(Cb):
    nb=Cb.shape[0]; return (Cb.sum(0,keepdims=True)-Cb)/(nb-1)
def jk_err(v):
    nb=v.shape[0]
    with np.errstate(invalid='ignore'):
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            return np.sqrt((nb-1)*np.nanmean((v-np.nanmean(v,0))**2,0))
def clean(a): return [None if not np.isfinite(v) else float(v) for v in a]

def meff_cosh(C):
    C=np.asarray(C)
    with np.errstate(invalid='ignore',divide='ignore'):
        r=(np.roll(C,1,-1)+np.roll(C,-1,-1))/(2*C)
        return np.where((r>1)&(C>0),np.arccosh(np.where(r>1,r,1.)),np.nan)

def diff(C): return C-np.roll(C,-1,-1)   # D(tau) = C(tau) - C(tau+1), no constant

def fit1(y,sig,ts,f,Emax=8.):
    """Best E and chi^2 for y = a f(E, ts), diagonal weights, by variable projection."""
    w=1/sig**2
    def chi(E):
        v=f(E,ts); a=(w*v*y).sum()/(w*v*v).sum()
        return (w*(y-a*v)**2).sum()
    Es=np.linspace(0.02,Emax,300); V=f(Es[:,None],ts); A=(w*V*y).sum(1)/(w*V*V).sum(1); i=int(np.argmin((w*(y-A[:,None]*V)**2).sum(1)))
    r=minimize_scalar(chi,bounds=(Es[max(i-1,0)],Es[min(i+1,len(Es)-1)]),method='bounded',options=dict(xatol=1e-5))
    v=f(float(r.x),ts)
    return float(r.x),float(r.fun),float((w*v*y).sum()/(w*v*v).sum())

def windows(N,T):
    """Fit windows (t1,t2) in tau. Upper end L or the last usable point, fixed in advance, with no selection on the data."""
    last=min(N,T//2-1); out={}
    for name,t1 in (('L/8',max(1,math.ceil(N/8))),('L/4',math.ceil(N/4)),('3L/8',math.ceil(3*N/8)),('L/2',math.ceil(N/2))):
        if last>=t1+1: out[name]=(t1,last)
    return out

def same_windows(N):
    """Windows that exist at T = L, used at T = L and T = 3L alike for F4."""
    last=N//2-1; out=[]
    for t1 in (1,2,math.ceil(N/4)):
        if last>=t1+1 and (t1,last) not in out: out.append((t1,last))
    return out

def plateau_status(fits,jE,N):
    """The stage 2 plateau rule (docstring), from the fits at L/4, 3L/8, L/2 and their jackknife samples."""
    base=fits.get('L/4')
    if not base: return dict(status='unresolved',why='no L/4 window')
    later=[w for w in ('3L/8','L/2') if w in fits and fits[w]['t1']!=base['t1']]
    nb=len(jE['L/4']); zs={}
    for w in later:
        d=(jE[w]-jE['L/4'])*N; e=math.sqrt((nb-1)*((d-d.mean())**2).mean()); dE=fits[w]['EL']-base['EL']
        zs[w]=dict(diff=dE,err=e,z=dE/e if e>0 else None)
    vals=[base['EL']]+[fits[w]['EL'] for w in later]
    out=dict(chi2_L4=base['chi2_diag_per_dof'],window_diffs=zs,spread=max(vals)-min(vals))
    if base['chi2_diag_per_dof']>3 or any(z['z'] is not None and abs(z['z'])>2 for z in zs.values()):
        out['status']='no_plateau'; return out
    bad=[w for w in ['L/4']+later if fits[w]['pinned']]
    if not later or fits[later[-1]]['ELerr']>0.75 or bad or base['low_snr']:
        out['status']='unresolved'; return out
    out['status']='plateau'; return out

def measure_C(Cb,T,N,keep_j=False):
    """From a bins x T symmetric correlator: the constant-free effective mass and the fit energies with jackknife errors."""
    Cb=np.real(Cb); nb=Cb.shape[0]; jC=jk_samples(Cb); D=diff(jC); Dm=diff(Cb.mean(0)[None])[0]; sD=jk_err(D)
    md=meff_cosh(Dm); mdj=meff_cosh(D)
    out=dict(meff_diff=clean(md[1:T//2-1]),meff_diff_err=clean(jk_err(mdj)[1:T//2-1]),fits={},same_window={})
    f=lambda E,ts: np.sinh(E*(T/2-ts-.5)); lo,hi=np.linspace(0.02,8.,300)[[1,-2]]; jE={}
    def one(t1,t2):
        ts=np.arange(t1,t2+1); s=sD[t1:t2+1]
        if not (s>0).all(): return None,None
        E,chi,a=fit1(Dm[t1:t2+1],s,ts,f)
        js=np.array([fit1(D[i][t1:t2+1],s,ts,f)[0] for i in range(nb)])
        err=math.sqrt((nb-1)*((js-js.mean())**2).mean())
        return dict(t1=t1,t2=t2,E=E,EL=E*N,ELerr=err*N,chi2_diag_per_dof=chi/max(1,t2-t1-1),snr_at_t1=float(Dm[t1]/sD[t1]),snr_at_t2=float(Dm[t2]/sD[t2]),pinned=bool(E<=lo or E>=hi or (js<=lo).any() or (js>=hi).any()),low_snr=bool(Dm[t1]/sD[t1]<1)),js
    for name,(t1,t2) in windows(N,T).items():
        r,js=one(t1,t2)
        if r: out['fits'][name]=r; jE[name]=js
    for t1,t2 in same_windows(N):
        if t2<=T//2-1:
            r,js=one(t1,t2)
            if r: out['same_window'][f'{t1}-{t2}']=r
    if 'L/4' in jE: out['plateau']=plateau_status(out['fits'],jE,N)
    else: out['plateau']=dict(status='unresolved',why='no L/4 fit')
    if keep_j: out['_jE']=jE
    return out

def fixed_vector(Dm,names,t0,tv):
    """Fixed-vector GEVP on the constant-free matrix; the vector comes from all data. Returns the leading vector."""
    M0=np.array([[Dm[a,b][t0] for b in names] for a in names]); M1=np.array([[Dm[a,b][tv] for b in names] for a in names])
    M0=.5*(M0+M0.conj().T); M1=.5*(M1+M1.conj().T)
    s=np.sqrt(np.abs(np.diag(M0))); M0=M0/np.outer(s,s); M1=M1/np.outer(s,s)
    w,v=np.linalg.eigh(M0); keep=w>1e-3*w.max(); P=v[:,keep]/np.sqrt(w[keep])
    mw,mv=np.linalg.eigh(P.conj().T@M1@P)
    return P@mv[:,-1]/s

def channel(ops,names,T,nb,N):
    Cs={}
    for a in names:
        for b in names:
            if a<=b:
                c=binned_corr(ops[a],ops[b],nb)[0]; c=sym(.5*(c+binned_corr(ops[b],ops[a],nb)[0])); Cs[a,b]=c; Cs[b,a]=c
    t0=max(1,round(N/8)); tv=t0+max(1,round(N/8))
    Dm={k:diff(v.mean(0)[None])[0] for k,v in Cs.items()}
    vec=fixed_vector(Dm,names,t0,tv)
    return vec,sum(vec[i]*vec[j]*Cs[a,b] for i,a in enumerate(names) for j,b in enumerate(names))

def crossval(ops,names,T,nb,N):
    """Fixed vector from one half of the bins, energy from the other, both ways. Removes the bias of choosing the vector on the same data."""
    Cs={}
    for a in names:
        for b in names:
            if a<=b:
                c=binned_corr(ops[a],ops[b],nb)[0]; c=sym(.5*(c+binned_corr(ops[b],ops[a],nb)[0])); Cs[a,b]=c; Cs[b,a]=c
    t0=max(1,round(N/8)); tv=t0+max(1,round(N/8)); h=nb//2; out={}; vals=[]
    for tag,(ia,ib) in (('a_to_b',(slice(0,h),slice(h,nb))),('b_to_a',(slice(h,nb),slice(0,h)))):
        Dm={k:diff(v[ia].mean(0)[None])[0] for k,v in Cs.items()}
        vec=fixed_vector(Dm,names,t0,tv)
        C=sum(vec[i]*vec[j]*Cs[a,b][ib] for i,a in enumerate(names) for j,b in enumerate(names))
        f=measure_C(C,T,N)['fits'].get('L/4')
        if f: out[tag]=dict(EL=f['EL'],err=f['ELerr'],pinned=f['pinned']); vals.append((f['EL'],f['ELerr']))
    if len(vals)==2:
        out['mean']=.5*(vals[0][0]+vals[1][0]); out['err']=.5*math.hypot(vals[0][1],vals[1][1])
    return out

def valley_slices(o,N):
    """P3(t) at level 2, signed so the ensemble mean is positive. The whole-lattice mean over T slices is insensitive at T = 3L, so look at slices."""
    p=o[:,:,2,4]; n,T=p.shape; sg=1. if p.mean()>=0 else -1.; x=sg*p; neg=x<0
    ep=[]; 
    for row,xrow in zip(neg,x):
        if not row.any(): continue
        if row.all(): ep.append((T,float(xrow.mean()))); continue
        st=int(np.argmin(row))   # a non-negative slice; walk the ring from it
        run=0; tot=0.
        for k in range(1,T+1):
            t=(st+k)%T
            if row[t]: run+=1; tot+=xrow[t]
            elif run: ep.append((run,tot/run)); run=0; tot=0.
    bulk=float(x[~neg].mean()); m=float(x.mean()); sd=float(x.std())
    from math import erfc
    lens=np.array([e[0] for e in ep]) if ep else np.zeros(1)
    amps=np.array([e[1] for e in ep]) if ep else np.zeros(1)
    long=[e for e in ep if e[0]>=math.ceil(N/2)]
    return dict(updates=n,slices_per_config=T,negative_slice_fraction=float(neg.mean()),gaussian_expected_fraction=.5*erfc(m/sd/math.sqrt(2)),mean=m,std=sd,mean_on_positive=bulk,mean_on_negative=float(x[neg].mean()) if neg.any() else None,
        episodes=len(ep),mean_episode_length=float(lens.mean()) if ep else 0.,max_episode_length=int(lens.max()) if ep else 0,episodes_length_ge_L_over_2=len(long),of_those_with_amplitude_ge_half_bulk=len([e for e in long if -e[1]>=.5*bulk]),
        percentiles=dict(zip(('0.1','1','5','25','50','75','95','99','99.9'),[float(v) for v in np.percentile(x,[.1,1,5,25,50,75,95,99,99.9])])))

def corr_c(X,Y,nb):
    """X,Y complex, n x T: bins x T of (1/T) sum_t X(t+tau) conj Y(t)."""
    n,T=X.shape; bs=n//nb; mx,my=X.mean(),Y.mean()   # D is unchanged by the centering
    c=np.empty((nb,T),dtype=complex)
    for i in range(nb):
        x=X[i*bs:(i+1)*bs]-mx; y=Y[i*bs:(i+1)*bs]-my
        c[i]=np.fft.ifft(np.fft.fft(x,axis=1)*np.conj(np.fft.fft(y,axis=1)),axis=1).mean(0)/T
    return c

def op_corr(cx,cy,nb):
    return sum(corr_c(x,y,nb) for x,y in zip(cx,cy))/len(cx)

def gevp_c(ops,names,T,nb,N):
    """Fixed-vector GEVP on a hermitian correlator matrix. Operators are lists of mirror images, whose correlators are averaged."""
    Cs={}
    for i,a in enumerate(names):
        for j,b in enumerate(names):
            if i<=j:
                c=sym(op_corr(ops[a],ops[b],nb)); Cs[a,b]=c; Cs[b,a]=np.conj(c)
    t0=max(1,round(N/8)); tv=t0+max(1,round(N/8))
    Dm={k:diff(v.mean(0)[None])[0] for k,v in Cs.items()}
    vec=fixed_vector(Dm,names,t0,tv)
    return vec,sum(np.conj(vec[i])*vec[j]*Cs[a,b] for i,a in enumerate(names) for j,b in enumerate(names))

OLD_OPS={'O1+O2','L3','Q12','Q13+Q23','O1-O2','L1-L2','Q13-Q23'}
def stage2_ops(o,l):
    v=lambda k:o[:,:,l,ALL.index(k)]
    z=lambda a,b:v(a)+1j*v(b)
    a,ap,b,bp=z('Phi1c','Phi1s'),z('Phi2c','Phi2s'),z('Bc','Bs'),z('Bpc','Bps')
    ab,abp=a*np.conj(b),ap*np.conj(bp)
    return dict(
      Z_even_A={'O1+O2':[abs(a)**2+abs(ap)**2],'Zbb+':[abs(b)**2+abs(bp)**2],'L3':[v('L3')],'Q12':[v('Q12')],'Q13+Q23':[v('Q13')+v('Q23')]},
      Z_even_B={'O1-O2':[abs(a)**2-abs(ap)**2],'Zbb-':[abs(b)**2-abs(bp)**2],'L1-L2':[v('L1')-v('L2')],'Q13-Q23':[v('Q13')-v('Q23')]},
      Z_odd_A={'ZS+':[ab.real+abp.real],'ZA+':[ab.imag+abp.imag],'T+':[v('T1')+v('T2')]},
      Z_odd_B={'ZS-':[ab.real-abp.real],'ZA-':[ab.imag-abp.imag],'T-':[v('T1')-v('T2')]},
      P_even={'aa':[a*a,ap*ap],'bb':[b*b,bp*bp],'Q12p':[z('Q12pc','Q12ps'),z('Q12qc','Q12qs')],'Q23p':[z('Q23pc','Q23ps'),z('Q13qc','Q13qs')]},
      P_odd={'ab':[a*b,ap*bp],'Tp':[z('T1pc','T1ps'),z('T2qc','T2qs')]})

def analyze_two(fn,nb=50):
    d=np.load(fn); N,T=int(d['N']),int(d['T']); bstd=float(d['beta_std']); o=d['ops'][:int(d['n'])]; n=o.shape[0]; u=d['u']; e=d['e']; nb=min(nb,n//4)
    res=dict(file=os.path.basename(fn),N=N,T=T,beta_std=bstd,n=n,nbins=nb,run_seconds=float(d['run_s']),tree_E1L=tree_E1(N)*N,tree_1gluon_EL=tree_E1(N)*N/2)
    if len(u)>1: res.update(u=float(u.mean()),u_err=float(u.std(ddof=1)/np.sqrt(len(u))),u_n=len(u),plaq_e=float(e.mean()))
    res['valley']=valley_slices(o,N)
    # one gluon in each polarization, level 2 and 1
    fc=lambda E,ts: np.cosh(E*(ts-T/2)); gl={}
    for l in (2,1):
        for name,ks in (('pol1',('Phi1c','Phi1s','Phi2c','Phi2s')),('pol3',('Bc','Bs','Bpc','Bps'))):
            C1=sum(sym(binned_corr(o[:,:,l,ALL.index(k)],o[:,:,l,ALL.index(k)],nb,center=False)[0]) for k in ks)/4
            jC=jk_samples(C1); mC=C1.mean(0); sg=jk_err(jC); t1=math.ceil(N/4); t2=min(T//2,t1+N); ts=np.arange(t1,t2+1)
            E,chi,_=fit1(mC[t1:t2+1],sg[t1:t2+1],ts,fc); js=np.array([fit1(jC[i][t1:t2+1],sg[t1:t2+1],ts,fc)[0] for i in range(nb)])
            gl[f'{name}/{l}']=dict(EL=E*N,err=math.sqrt((nb-1)*((js-js.mean())**2).mean())*N,chi2_diag_per_dof=chi/max(1,t2-t1-1),snr_at_t1=float(mC[t1]/sg[t1]),meff=clean(meff_cosh(mC)[1:T//2]),meff_err=clean(jk_err(meff_cosh(jC))[1:T//2]))
    res['one_gluon']=gl
    # the a-b cross correlator vanishes by x3 -> -x3; a check that this holds in the data
    zs=[]
    for x,y in (('Phi1c','Bc'),('Phi1s','Bs'),('Phi2c','Bpc'),('Phi2s','Bps')):
        C=sym(binned_corr(o[:,:,2,ALL.index(x)],o[:,:,2,ALL.index(y)],nb,center=False)[0]); j=jk_samples(C); ee=jk_err(j); zs+=[float(C.mean(0)[t]/ee[t]) for t in (0,1,max(2,N//4),max(3,N//2))]
    res['pol1_pol3_cross_z']=dict(rms=float(np.sqrt(np.mean(np.square(zs)))),max=float(np.max(np.abs(zs))),count=len(zs))
    A,B=combine(o)
    ref={}
    for ch,ops,basis in (('A',A,['O1+O2/2','L3/2','Q12/2','Q13+Q23/2']),('B',B,['O1-O2/2','Q13-Q23/2'])):
        vec,Cb=channel(ops,basis,T,nb,N); ref[ch]=measure_C(Cb,T,N,keep_j=True); ref[ch].update(basis=basis,vector=[float(x) for x in vec])
    res['chan']={}
    for l in (2,1):
        ch2=stage2_ops(o,l)
        for chn,ops in ch2.items():
            c=res['chan'].setdefault(chn,dict(single={}))
            for k,X in ops.items():
                r=measure_C(sym(op_corr(X,X,nb)),T,N,keep_j=(l==2)); r['new']=k not in OLD_OPS; r['level']=l; c['single'][f'{k}/{l}']=r
            if l==2:
                names=list(ops); vec,Cb=gevp_c(ops,names,T,nb,N); r=measure_C(Cb,T,N,keep_j=True); r.update(basis=names,vector=[[float(x.real),float(x.imag)] for x in vec],new=True); c['gevp']=r
        del ch2
    # stage 2 difference against the stage 1 readout, jackknifed on the same bins, at L/4
    fa,fb=ref['A']['fits'].get('L/4'),ref['B']['fits'].get('L/4')
    res['reference']=dict(GEVP_A=fa and dict(EL=fa['EL'],err=fa['ELerr'],plateau=ref['A']['plateau']['status']),GEVP_B=fb and dict(EL=fb['EL'],err=fb['ELerr'],plateau=ref['B']['plateau']['status']))
    rk='A' if (fa and (not fb or fa['EL']<=fb['EL'])) else 'B'; jr=ref[rk]['_jE'].get('L/4'); fr=ref[rk]['fits'].get('L/4')
    def against(r):
        f=r['fits'].get('L/4')
        if not f or jr is None: return None
        d=(r['_jE']['L/4']-jr)*N; return dict(ref=rk,diff=f['EL']-fr['EL'],err=math.sqrt((nb-1)*((d-d.mean())**2).mean()))
    for c in res['chan'].values():
        for r in list(c['single'].values())+([c['gevp']] if 'gevp' in c else []):
            if '_jE' in r: r['vs_stage1']=against(r); del r['_jE']
    return res

def verdict2(res):
    """The stage 2 criteria of the docstring."""
    v={}; pts=[r for r in res if 'u' in r]
    def rows(r):
        """Every new channel at level 2, as (channel, op, EL, err, status, fit, vs_stage1)."""
        out=[]
        for chn,c in r['chan'].items():
            for k,x in c['single'].items():
                if x['new'] and x['level']==2: out.append((chn,k,x))
            if 'gevp' in c: out.append((chn,'GEVP',c['gevp']))
        return [(a,b,x,x['fits'].get('L/4')) for a,b,x in out]
    s1=[]
    for r in pts:
        if r['beta_std']==32. and r['N'] in (6,8):
            g=r['one_gluon']['pol3/2']; t=r['tree_1gluon_EL']
            s1.append(dict(N=r['N'],u=r['u'],EL=g['EL'],err=g['err'],tree=t,passed=bool(abs(g['EL']-t)<=max(3*g['err'],.1*t)),pol1=r['one_gluon']['pol1/2']['EL'],pol1_err=r['one_gluon']['pol1/2']['err'],snr_at_t1=g['snr_at_t1']))
    v['S1']=s1
    f5=[];f7=[];f3=[];count=0
    for r in pts:
        for chn,k,x,f in rows(r):
            if not f: continue
            count+=1; st=x['plateau']['status']; vs=x.get('vs_stage1')
            if vs and st=='plateau' and vs['diff']<-.5 and vs['diff']<-3*vs['err']: f5.append(dict(N=r['N'],beta_std=r['beta_std'],u=r['u'],channel=chn,op=k,EL=f['EL'],err=f['ELerr'],**vs))
            if r['beta_std']==32. and f['EL']<r['tree_E1L']-max(3*f['ELerr'],.5) and not f['pinned'] and not f['low_snr']: f7.append(dict(N=r['N'],channel=chn,op=k,EL=f['EL'],err=f['ELerr'],tree=r['tree_E1L'],plateau=st))
            if r['u']<1 and f['EL']+3*f['ELerr']<math.pi and not f['pinned'] and not f['low_snr']: f3.append(dict(N=r['N'],beta_std=r['beta_std'],u=r['u'],channel=chn,op=k,EL=f['EL'],err=f['ELerr'],plateau=st))
    v['channels_scanned']=count; v['F5_triggered']=f5; v['F7_triggered']=f7; v['F3b_triggered']=f3
    # Descriptive, not a criterion: the same comparison without requiring a plateau, since most channels come out "unresolved" under the rule.
    v['F5_like_without_plateau']=[dict(N=r['N'],beta_std=r['beta_std'],u=r['u'],channel=chn,op=k,EL=f['EL'],err=f['ELerr'],plateau=x['plateau']['status'],**x['vs_stage1']) for r in pts for chn,k,x,f in rows(r) if f and x.get('vs_stage1') and not f['pinned'] and not f['low_snr'] and x['vs_stage1']['diff']<-.5 and x['vs_stage1']['diff']<-3*x['vs_stage1']['err']]
    lines={}
    for name,target in (('u=1',1.),('u=2',2.),('u=3.3',3.3)):
        P=sorted([r for r in pts if abs(r['u']/target-1)<.1],key=lambda r:r['N'])
        tab={}
        for r in P:
            for chn,k,x,f in rows(r):
                if f: tab.setdefault(f'{chn}:{k}',{})[str(r['N'])]=dict(EL=f['EL'],err=f['ELerr'],plateau=x['plateau']['status'],u=r['u'])
            for key in ('GEVP_A','GEVP_B'):
                q=r['reference'][key]
                if q: tab.setdefault('stage1_'+key,{})[str(r['N'])]=dict(EL=q['EL'],err=q['err'],plateau=q['plateau'],u=r['u'])
        f6={}
        for op,t in tab.items():
            big=max(t,key=int)
            if '6' in t and int(big)>6:
                a,b=t['6'],t[big]; dd=a['EL']-b['EL']; e=math.hypot(a['err'],b['err'])
                ns=[int(n) for n in t]; 
                row=dict(N_large=int(big),drop=dd,err=e,fall_upper_95=dd+1.645*e,detectable_fall=max(.25*a['EL'],3*e),triggered=bool(dd>.25*a['EL'] and dd>3*e))
                if len(ns)>=3:
                    xs=np.log(np.array(ns,float)); ys=np.array([t[str(n)]['EL'] for n in ns]); es=np.array([t[str(n)]['err'] for n in ns]); W=1/es**2
                    X=np.stack([np.ones(len(xs)),xs],1); Cov=np.linalg.inv((X.T*W)@X); pp=Cov@((X.T*W)@ys); row.update(slope_lnN=float(pp[1]),slope_err=float(math.sqrt(Cov[1,1])))
                f6[op]=row
        lines[name]=dict(table=tab,F6=f6,F6_triggered=[k for k,x in f6.items() if x['triggered']])
    v['lines']=lines
    low=[]
    for r in pts:
        cands=[(f['EL'],f['ELerr'],chn,k,x['plateau']['status']) for chn,k,x,f in rows(r) if f and not f['pinned'] and not f['low_snr']]
        pl=[c for c in cands if c[4]=='plateau']
        low.append(dict(N=r['N'],beta_std=r['beta_std'],u=r['u'],reference=r['reference'],lowest_plateau=pl and dict(zip(('EL','err','channel','op','status'),min(pl))),lowest_any=cands and dict(zip(('EL','err','channel','op','status'),min(cands)))))
    v['lowest_by_ensemble']=low
    v['pol1_pol3_cross_z']=[dict(N=r['N'],beta_std=r['beta_std'],**r['pol1_pol3_cross_z']) for r in pts]
    return v

def combined(res,res2):
    """Stage 1 and stage 2 are independent streams at the same (N, beta_std), with the same GEVP_A, GEVP_B bases. Added after both were in, as a description, not a criterion."""
    r2={(r['N'],r['beta_std']):r for r in res2}; out={}
    for name,target in (('u=0.13',.132),('u=0.5',.5),('u=1',1.),('u=2',2.),('u=3.3',3.3)):
        for key in ('GEVP_A','GEVP_B'):
            ch=key[-1]; rows={}
            for r in res:
                if 'gevp' not in r or r['T']!=3*r['N'] or abs(r['u']/target-1)>=.1: continue
                f=r['gevp'][ch]['fits'].get('L/4')
                if not f: continue
                vals=[(f['EL'],f['ELerr'])]; q=r2.get((r['N'],r['beta_std']))
                if q and q['reference'][key]: vals.append((q['reference'][key]['EL'],q['reference'][key]['err']))
                w=np.array([1/e**2 for _,e in vals]); x=np.array([v for v,_ in vals]); m=float((w*x).sum()/w.sum())
                row=dict(EL=m,err=float(1/math.sqrt(w.sum())),tree=r['tree_E1L'],u=r['u'],streams=[dict(EL=v,err=e) for v,e in vals])
                if len(vals)==2: row['z_between']=(vals[0][0]-vals[1][0])/math.hypot(vals[0][1],vals[1][1])
                rows[str(r['N'])]=row
            e=dict(by_N=rows)
            for tag,keep in (('all_N',lambda n:True),('N_ge_6',lambda n:n>=6)):
                ns=[int(n) for n in rows if keep(int(n))]
                if len(ns)>=3:
                    xs=np.log(np.array(ns,float)); ys=np.array([rows[str(n)]['EL'] for n in ns]); es=np.array([rows[str(n)]['err'] for n in ns]); W=1/es**2
                    X=np.stack([np.ones(len(xs)),xs],1); Cov=np.linalg.inv((X.T*W)@X); pp=Cov@((X.T*W)@ys)
                    e['slope_lnN_'+tag]=dict(slope=float(pp[1]),err=float(math.sqrt(Cov[1,1])),chi2=float((((ys-X@pp)/es)**2).sum()),dof=len(ns)-2)
            out.setdefault(name,{})[key]=e
    return out

def tree_E1(N): return 4*math.asinh(math.sin(math.pi/(2*N)))

def free_neutral_fraction(N,T):
    """Free lattice gluons, 2 polarizations per mode: weight of e1 = e2 = 0 in Tr T^T, by projecting with the Z2^2 flips."""
    g=2*np.pi*np.arange(N)/N; logs=[]
    w={}
    for e1,e2 in ((1,0),(0,1),(1,1)):
        k2=4*np.sin((g+np.pi*e1/N)/2)[:,None,None]**2+4*np.sin((g+np.pi*e2/N)/2)[None,:,None]**2+4*np.sin(g/2)[None,None,:]**2
        w[e1,e2]=2*np.arcsinh(np.sqrt(k2)/2).ravel()
    tot=0.
    for s1,s2 in ((1,1),(1,-1),(-1,1),(-1,-1)):
        lg=0.
        for (e1,e2),om in w.items():
            sg=(s1**e1)*(s2**e2)
            lg+=2*np.sum(np.log1p(-np.exp(-om*T))-np.log1p(-sg*np.exp(-om*T)))
        tot+=math.exp(lg)
    return tot/4

def thermal_constant(X,T,N,nb,E):
    """C_conn(tau) = A cosh(E(tau-T/2)) + B with E fixed: B/A with jackknife. In free theory B/A = 1 for O1, O2."""
    C,m,_=binned_corr(X,X,nb); C=sym(C); j=jk_samples(C); jm=(m.sum()-m)/(nb-1); con=j-(jm**2)[:,None]
    ts=np.arange(max(1,math.ceil(N/8)),T//2+1); err=jk_err(con)[ts]; w=1/err**2; V=np.stack([np.cosh(E*(ts-T/2)),np.ones(len(ts))],1)
    M=np.linalg.solve(V.T@(V*w[:,None]),V.T*w)
    r=lambda c: (lambda p: p[1]/p[0])(M@c[ts])
    vals=np.array([r(c) for c in con])
    cm=C.mean(0)-m.mean()**2
    return dict(ratio=float(r(cm)),err=float(jk_err(vals)))

def analyze_one(fns,nb=50):
    # several files are independent streams of one ensemble; correlators are per configuration, so they concatenate
    ds=[np.load(fn) for fn in fns]; d=ds[0]; N,T=int(d['N']),int(d['T']); bstd=float(d['beta_std'])
    ln=[int(x['n']) for x in ds]; o=None; k=0
    for x,m in zip(ds,ln):
        a=x['ops']
        if o is None: o=np.empty((sum(ln),)+a.shape[1:])
        o[k:k+m]=a[:m]; k+=m; del a
    n=o.shape[0]; u=np.concatenate([x['u'] for x in ds]); e=np.concatenate([x['e'] for x in ds])
    nb=min(nb,n//4)
    lens=[int(x['n']) for x in ds]
    res=dict(files=[os.path.basename(fn) for fn in fns],N=N,T=T,beta_std=bstd,n=n,per=int(d['per']),nbins=nb,levels=[int(x) for x in d['lev']],run_seconds=float(sum(float(x['run_s']) for x in ds)))
    if len(u)>1: res.update(u=float(u.mean()),u_err=float(u.std(ddof=1)/np.sqrt(len(u))),u_n=len(u),plaq_e=float(e.mean()))
    res.update(tree_E1L=tree_E1(N)*N,tree_1gluon_EL=tree_E1(N)*N/2,free_neutral_fraction=free_neutral_fraction(N,T))
    p3=o[:,:,:,4]; res['P3_mean']=float(p3[:,:,0].mean()); res['P3_abs']=float(np.abs(p3[:,:,0].mean(1)).mean())
    s=np.sign(p3[:,:,0].mean(1)); res['valley_fraction_positive']=float((s>0).mean()); res['valley_flips']=int((s[1:]!=s[:-1]).sum())
    res['valley_slices']=valley_slices(o,N)
    if n<40: return res
    # one-gluon reference: mean of the four flux operators, pure cosh, no vacuum subtraction
    gl={}
    fc=lambda E,ts: np.cosh(E*(ts-T/2))
    for l in range(o.shape[2]):
        C1=sum(sym(binned_corr(o[:,:,l,k],o[:,:,l,k],nb,center=False)[0]) for k in range(4))/4
        jC=jk_samples(C1); mC=C1.mean(0); sg=jk_err(jC)
        r=dict(meff=clean(meff_cosh(mC)[1:T//2]),err=clean(jk_err(meff_cosh(jC))[1:T//2]))
        t1=math.ceil(N/4); t2=min(T//2,t1+N); ts=np.arange(t1,t2+1)
        if t2>t1:
            E,chi,_=fit1(mC[t1:t2+1],sg[t1:t2+1],ts,fc)
            js=np.array([fit1(jC[i][t1:t2+1],sg[t1:t2+1],ts,fc)[0] for i in range(nb)])
            r.update(EL=E*N,ELerr=math.sqrt((nb-1)*((js-js.mean())**2).mean())*N,t1=t1,t2=t2,chi2_diag_per_dof=chi/max(1,t2-t1-1))
        gl[str(l)]=r
    res['one_gluon']=gl
    A,B=combine(o)
    single={}
    for ch,ops in (('A',A),('B',B)):
        for k,X in ops.items():
            C,m,_=binned_corr(X,X,nb); C=sym(C)
            r=measure_C(C,T,N)
            # the raw vacuum-subtracted cosh estimator, kept to show the wrap-around
            jC=jk_samples(C); jm=(m.sum()-m)/(nb-1); conn=jC-(jm**2)[:,None]; cm=C.mean(0)-m.mean()**2
            r['meff_raw']=clean(meff_cosh(cm)[1:T//2]); r['meff_raw_err']=clean(jk_err(meff_cosh(conn))[1:T//2])
            single[f'{ch}:{k}']=r
    res['single']=single
    gev={}
    for ch,ops,basis in (('A',A,['O1+O2/2','L3/2','Q12/2','Q13+Q23/2']),('B',B,['O1-O2/2','Q13-Q23/2'])):
        vec,Cb=channel(ops,basis,T,nb,N)
        r=measure_C(Cb,T,N); r.update(basis=basis,vector=[float(v) for v in vec]); gev[ch]=r
    res['gevp']=gev
    # Wider bases, which the first report did not try: L1-L2 was left out of B, and only level 2 was used. Fit values only bound the lowest level from above.
    wider={}
    for name,ops,basis in (('B3',B,['O1-O2/2','L1-L2/2','Q13-Q23/2']),('B5',B,['O1-O2/2','L1-L2/2','Q13-Q23/2','O1-O2/1','Q13-Q23/1']),('A7',A,['O1+O2/2','L3/2','Q12/2','Q13+Q23/2','L1+L2/2','O1+O2/1','Q12/1'])):
        vec,Cb=channel(ops,basis,T,nb,N); r=measure_C(Cb,T,N); r.update(basis=basis,vector=[float(v) for v in vec]); wider[name]=r
    res['gevp_wider']=wider
    res['gevp_crossval']={ch:crossval(ops,basis,T,nb,N) for ch,ops,basis in (('A',A,['O1+O2/2','L3/2','Q12/2','Q13+Q23/2']),('B',B,['O1-O2/2','Q13-Q23/2']))}
    # Streams separately, where an ensemble has more than one
    if len(ds)>1:
        st={}; off=0; vals={'A':[],'B':[]}
        for x,ln in zip(ds,lens):
            sub=o[off:off+ln]; off+=ln; Asub,Bsub=combine(sub); nbs=min(nb,ln//4); row={}
            for ch,ops,basis in (('A',Asub,['O1+O2/2','L3/2','Q12/2','Q13+Q23/2']),('B',Bsub,['O1-O2/2','Q13-Q23/2'])):
                f=measure_C(channel(ops,basis,T,nbs,N)[1],T,N)['fits'].get('L/4')
                if f: row[ch]=dict(EL=f['EL'],err=f['ELerr']); vals[ch].append((f['EL'],f['ELerr']))
            st[f"n={ln}"]=row
        sc={}
        for ch,vv in vals.items():
            if len(vv)==2:
                z=(vv[0][0]-vv[1][0])/math.hypot(vv[0][1],vv[1][1]); sc[ch]=dict(z=z,scale_factor=max(1.,abs(z)))
        res['streams']=dict(by_stream=st,disagreement=sc)
    # Momentum 2 pi/L from the stage 1 raw data: a^2 and its mirror image (stage 2, pre-registered). No polarization 3 here.
    mom={}
    for l in (2,1):
        a=o[:,:,l,0]+1j*o[:,:,l,1]; ap=o[:,:,l,2]+1j*o[:,:,l,3]; X=[a*a,ap*ap]
        mom[f'aa/{l}']=measure_C(sym(op_corr(X,X,nb)),T,N)
    res['momentum_aa']=mom
    # the constant in tau, at the tree energy, for T = L mostly
    res['thermal_constant_O1+O2_level2']=thermal_constant(A['O1+O2/2'],T,N,nb,tree_E1(N))
    # flux coupling: neutral operators against flux operators, at level 2. Exact symmetry requires zero for Phi1, Phi2.
    fx={}; l=2
    for fname,fk in (('Phi1c',0),('Phi1s',1),('Phi2c',2),('Phi2s',3),('P3',4)):
        row={}
        for k in (f'O1+O2/{l}',f'Q12/{l}',f'L3/{l}'):
            X=A[k]; Y=o[:,:,l,fk]; C,mx,my=binned_corr(X,Y,nb); j=jk_samples(C); jx=(mx.sum()-mx)/(nb-1); jy=(my.sum()-my)/(nb-1)
            con=j-(jx*jy)[:,None]; m=C.mean(0)-mx.mean()*my.mean(); e=jk_err(con)
            ts=[1,max(2,N//4),max(3,N//2)]
            cxx=binned_corr(X,X,nb)[0].mean(0)[0]-mx.mean()**2; cyy=binned_corr(Y,Y,nb)[0].mean(0)[0]-my.mean()**2
            nrm=math.sqrt(abs(cxx*cyy))+1e-300
            row[k]=dict(tau=ts,rho=[float(m[t]/nrm) for t in ts],z=[float(m[t]/e[t]) for t in ts])
        fx[fname]=row
    res['flux_coupling']=fx
    # tr W3 on one valley behaves as a neutral operator. Constant-free energy of its slice mean.
    res['P3_constant_free']=measure_C(sym(binned_corr(o[:,:,2,4],o[:,:,2,4],nb)[0]),T,N)
    # error against bin size, for the D of the leading operator
    stab={}
    for nbb in (10,20,40,80,160):
        if n//nbb<2: continue
        C=sym(binned_corr(A['O1+O2/2'],A['O1+O2/2'],nbb)[0]); stab[str(nbb)]=[float(v) for v in jk_err(diff(jk_samples(C)))[[1,max(2,N//4),max(3,N//2)]]]
    res['bin_stability_D_err']=stab
    return res

def best(r,win='L/4'):
    """Pre-registered readout, by operator class: GEVP A, GEVP B, and the leading single operators."""
    out={}
    for name,g in (('GEVP_A',r['gevp']['A']),('GEVP_B',r['gevp']['B']),('O1+O2',r['single']['A:O1+O2/2']),('O1-O2',r['single']['B:O1-O2/2']),('L3',r['single']['A:L3/2']),('Q12',r['single']['A:Q12/2'])):
        f=g['fits'].get(win)
        if f: out[name]=(f['EL'],f['ELerr'],f['chi2_diag_per_dof'],g['plateau']['status'])
    return out

def verdict(res):
    v={}
    prod=[r for r in res if 'gevp' in r and 'u' in r]
    sel=lambda r: best(r)
    # F1: lines of nearly fixed u, T = 3L
    lines={}
    for name,target in (('u=0.5',0.5),('u=1',1.),('u=2',2.),('u=3.3',3.3)):
        pts=[r for r in prod if r['T']==3*r['N'] and abs(r['u']/target-1)<0.1]
        rows={}
        for r in sorted(pts,key=lambda r:r['N']):
            b=sel(r); rows[str(r['N'])]=dict(beta_std=r['beta_std'],u=r['u'],u_err=r['u_err'],tree_E1L=r['tree_E1L'],one_gluon_EL=r['one_gluon']['2'].get('EL'),one_gluon_err=r['one_gluon']['2'].get('ELerr'),**{k:dict(EL=x[0],err=x[1],chi2=x[2],plateau=x[3]) for k,x in b.items()})
        res_line=dict(points=rows,F1={})
        Ns=[n for n in rows if int(n)>=12]
        if '6' in rows and Ns:
            big=max(Ns,key=int)
            for op in ('GEVP_A','GEVP_B','O1+O2','O1-O2'):
                if op in rows['6'] and op in rows[big]:
                    a,b=rows['6'][op],rows[big][op]; dd=a['EL']-b['EL']; s=math.hypot(a['err'],b['err'])
                    # detectable_fall: what F1 needs to fire. fall_upper_95: one-sided limit on the fall the data allow. F1 is a weak test, and these say how weak.
                    res_line['F1'][op]=dict(N_large=int(big),drop=dd,drop_err=s,detectable_fall=max(0.25*a['EL'],3*s),fall_upper_95=dd+1.645*s,triggered=bool(dd>0.25*a['EL'] and dd>3*s))
            for op in ('GEVP_A','GEVP_B','O1+O2','O1-O2'):
                ns=[int(n) for n in rows if op in rows[n]]
                if len(ns)>=3:
                    xs=np.log(np.array(ns,float)); ys=np.array([rows[str(n)][op]['EL'] for n in ns]); es=np.array([rows[str(n)][op]['err'] for n in ns]); W=1/es**2
                    X=np.stack([np.ones(len(xs)),xs],1); Cov=np.linalg.inv((X.T*W)@X); pp=Cov@((X.T*W)@ys); chi=float((((ys-X@pp)/es)**2).sum())
                    res_line.setdefault('slope_lnN',{})[op]=dict(slope=float(pp[1]),err=float(math.sqrt(Cov[1,1])),chi2=chi,dof=len(ns)-2,Ns=ns)
        lines[name]=res_line
    v['lines']=lines
    # F2: limit u -> 0, by N, T = 3L
    f2={}
    for N in sorted({r['N'] for r in prod}):
        pts=[r for r in prod if r['N']==N and r['T']==3*N and r['u']<1]
        for op in ('GEVP_A','O1+O2','GEVP_B','O1-O2'):
            xs=[];ys=[];es=[]
            for r in pts:
                b=sel(r)
                if op in b: xs.append(r['u']);ys.append(b[op][0]-r['tree_E1L']);es.append(b[op][1])
            if len(xs)<3: continue
            xs,ys,es=map(np.array,(xs,ys,es)); W=np.diag(1/es**2); X=np.stack([np.ones(len(xs)),xs],1); Cov=np.linalg.inv(X.T@W@X); p=Cov@X.T@W@ys
            a,sa=float(p[0]),float(math.sqrt(Cov[0,0])); r2=float(((ys-X@p)**2/es**2).sum())
            f2[f'N={N},{op}']=dict(a=a,a_err=sa,b=float(p[1]),b_err=float(math.sqrt(Cov[1,1])),chi2=r2,dof=len(xs)-2,u=xs.tolist(),triggered=bool(abs(a)>3*sa and abs(a)>.5))
    v['F2']=f2
    # F3
    f3=[]
    for r in prod:
        if r['T']==3*r['N'] and r['u']<1:
            for k,x in sel(r).items():
                if x[0]+3*x[1]<math.pi: f3.append(dict(N=r['N'],beta_std=r['beta_std'],op=k,EL=x[0],err=x[1]))
    v['F3_triggered']=f3
    # "Any neutral channel" as the docstring says: every single operator and every GEVP at L/4, not just the six readouts. Fits pinned at the grid bound or with signal to noise below 1 at the start of the window are not fits, and are listed apart.
    scan=[];arte=[];cnt=0
    for r in prod:
        if r['T']==3*r['N'] and r['u']<1:
            for k,g in list(r['single'].items())+[('GEVP_'+c,x) for c,x in r['gevp'].items()]+[('GEVP_'+c,x) for c,x in r['gevp_wider'].items()]+[('P:'+c,x) for c,x in r['momentum_aa'].items()]:
                f=g['fits'].get('L/4')
                if not f: continue
                cnt+=1
                if f['EL']+3*f['ELerr']<math.pi:
                    row=dict(N=r['N'],beta_std=r['beta_std'],op=k,EL=f['EL'],err=f['ELerr'],pinned=f['pinned'],low_snr=f['low_snr'],snr_at_t1=f['snr_at_t1'])
                    (arte if (f['pinned'] or f['low_snr']) else scan).append(row)
    v['F3_all_channels']=dict(scanned=cnt,triggered=scan,flagged_not_fits=arte)
    # F4: T = L against T = 3L at the same (N, beta), in IDENTICAL windows that exist at T = L. The first version compared fits.get('L/8') at both, whose windows differ.
    f4=[]
    for r in prod:
        if r['T']!=r['N']: continue
        for q in prod:
            if q['N']==r['N'] and q['T']==3*r['N'] and q['beta_std']==r['beta_std']:
                row=dict(N=r['N'],beta_std=r['beta_std'],free_neutral_fraction_T_L=r['free_neutral_fraction'],free_neutral_fraction_T_3L=q['free_neutral_fraction'],thermal_B_over_A_T_L=r['thermal_constant_O1+O2_level2'],thermal_B_over_A_T_3L=q['thermal_constant_O1+O2_level2'])
                for op,key in (('O1+O2','A:O1+O2/2'),('O1-O2','B:O1-O2/2')):
                    a=r['single'][key]; b=q['single'][key]; row[op]={}
                    ma,ea=a['meff_diff'],a['meff_diff_err']; mb,eb=b['meff_diff'],b['meff_diff_err']; ra,rea=a['meff_raw'],a['meff_raw_err']; rb,reb=b['meff_raw'],b['meff_raw_err']
                    row[op]['tau']=list(range(1,len(ma)+1))
                    row[op]['T_L_diff_EL']=[None if x is None else x*r['N'] for x in ma]; row[op]['T_L_diff_err']=[None if x is None else x*r['N'] for x in ea]
                    row[op]['T_3L_diff_EL']=[None if x is None else x*r['N'] for x in mb[:len(ma)]]; row[op]['T_3L_diff_err']=[None if x is None else x*r['N'] for x in eb[:len(ma)]]
                    row[op]['T_L_raw_EL']=[None if x is None else x*r['N'] for x in ra[:len(ma)]]; row[op]['T_L_raw_err']=[None if x is None else x*r['N'] for x in rea[:len(ma)]]
                    row[op]['T_3L_raw_EL']=[None if x is None else x*r['N'] for x in rb[:len(ma)]]; row[op]['T_3L_raw_err']=[None if x is None else x*r['N'] for x in reb[:len(ma)]]
                    row[op]['same_window']={}
                    for w,fa in a['same_window'].items():
                        fb=b['same_window'].get(w)
                        if fa and fb:
                            e=math.hypot(fa['ELerr'],fb['ELerr']); z=(fa['EL']-fb['EL'])/e
                            row[op]['same_window'][w]=dict(T_L=fa['EL'],T_L_err=fa['ELerr'],T_3L=fb['EL'],T_3L_err=fb['ELerr'],z=z,triggered=bool(abs(z)>3))
                f4.append(row)
    v['F4']=f4
    zs=[(abs(x['z']),row['N'],row['beta_std'],op,w) for row in f4 for op in ('O1+O2','O1-O2') for w,x in row[op]['same_window'].items()]
    v['F4_summary']=dict(windows_compared=len(zs),max_abs_z=max(zs) if zs else None,triggered=[z for z in zs if z[0]>3],
        power='the comparison is resolved only in windows starting at tau = 1 or 2, which those early points dominate; at tau >= L/4 the T = L errors are large (see the same_window entries)',
        g2_transition_4_44='not tested. The docstring predicts a rate near 4.44/L at T = L only; there is no amplitude prediction and no resolved departure to attribute to it',
        constant='a constant in tau is a consistent account of the low raw T = L masses, not a derived one: B/A is near 1.5 at u near 1 and nothing here computes that value')
    # flux coupling across all ensembles
    zmax={}
    for fname in ('Phi1c','Phi1s','Phi2c','Phi2s','P3'):
        zs=[abs(z) for r in prod for row in r['flux_coupling'][fname].values() for z in row['z'] if np.isfinite(z)]
        zmax[fname]=dict(max_abs_z=float(max(zs)),rms_z=float(np.sqrt(np.mean(np.square(zs)))),count=len(zs))
    v['flux_coupling_summary']=zmax
    return v

def analyze():
    groups={}
    for fn in sorted(glob.glob(RAW+'/raw_*.npz')):
        groups.setdefault(os.path.basename(fn).rsplit('_s',1)[0],[]).append(fn)
    # One ensemble per short-lived worker, one worker at a time: in a single process freed arrays stay in the footprint and the peak passes the 1.5 GB limit.
    ctx=multiprocessing.get_context('spawn')
    with ctx.Pool(1,maxtasksperchild=1) as pool: res=pool.map(analyze_one,list(groups.values()),chunksize=1)
    res.sort(key=lambda r:(r['T']!=3*r['N'],r['N'],r['beta_std']))
    meta=dict(script='scripts/yang_mills_target_a_gap_numerics.py',note='numerics, not a proof',repo_beta='beta_std/2',raw_data=RAW,
        criteria='F1-F4 are stated in the script docstring, written before production',
        stage2_criteria='S1, F5, F6, F7, F3b and the plateau rule are in the docstring, written before the stage 2 runs; the plateau rule is post hoc for stage 1',
        post_hoc='second streams at N = 6, 8, 12 on the u = 2 line and N = 16 at u = 2 were added after a 1.8 sigma fall appeared there; merged streams are one ensemble. combined_stage1_stage2, the slopes and the fall limits were added after seeing data, as descriptions',
        caveats=['upper bound on the lowest coupled level only','operators reach the 20 states of the tree-level lowest neutral multiplet (stage 2) but nothing else by design; a level from a higher multiplet with small overlap is invisible',
            'on the whole-lattice mean of tr W3 there are no valley flips in any ensemble, so e3-even and e3-odd neutral levels are not separated. Per slice P3(t) does change sign rarely: see valley_summary',
            'fits use diagonal weights; chi2 is only indicative. Most channels are "unresolved" under the plateau rule, and at N >= 12 nearly all of them: see plateau_counts','N <= 16 only, with large errors at N = 16; F1 and F6 are weak tests, see detectable_fall and fall_upper_95',
            'the stage 1 streams at N = 12 on the u = 2 line disagree at 2.4 sigma in GEVP_A: see streams. The merged error does not include this'],
        corrections_after_review=['Target A item 4 has no momentum restriction; the first docstring said zero momentum. Stage 2 adds p != 0 and mixed polarization',
            'F4 compared unequal windows through fits.get("L/8"), although its comment said otherwise; it now compares identical windows, and its first reported closest case (2.8 sigma) is replaced by 2.57 sigma on identical windows',
            '"the constant explains T = L" is weakened to "is a consistent account": B/A near 1.5 at u near 1 is not derived and the g^2 transition at 4.44/L was not tested',
            'F3 in the first version checked six readouts, not "any neutral channel". It now scans every fit and lists pinned and low signal fits apart as non-fits',
            '"the fall at u = 2 was noise" is weakened to "not reproduced", with the streams recorded separately',
            'c(u) "4.2 to 4.9" as a plateau value is withdrawn; each value now carries a plateau status and its window spread',
            'correlators are now centered before the FFT. This changes GEVP values by at most 0.001 but some weak coupling single Q fits by up to 0.18, always well inside their error'])
    out=dict(meta=meta,ensembles=res,verdict=verdict(res))
    if os.path.exists(RAW+'/phase.json'): out['phase_check_N8_beta64']=json.load(open(RAW+'/phase.json'))
    for fn in sorted(glob.glob(RAW+'/phase_N*.json')): out.setdefault('phase_checks_more',{})[os.path.basename(fn)[:-5]]=json.load(open(fn))
    fns=sorted(glob.glob(RAW2+'/raw2_*.npz'))
    with ctx.Pool(1,maxtasksperchild=1) as pool: res2=pool.map(analyze_two,fns,chunksize=1)
    res2.sort(key=lambda r:(r['N'],r['beta_std']))
    out['stage2_ensembles']=res2; out['stage2_verdict']=verdict2(res2); out['combined_stage1_stage2']=combined(res,res2)
    def statuses(gs):
        c={}
        for g in gs: c[g['plateau']['status']]=c.get(g['plateau']['status'],0)+1
        return c
    out['plateau_counts']=dict(stage1_GEVP=statuses([r['gevp'][c] for r in res if 'gevp' in r and r['T']==3*r['N'] for c in 'AB']),
        stage1_GEVP_N_ge_12=statuses([r['gevp'][c] for r in res if 'gevp' in r and r['T']==3*r['N'] and r['N']>=12 for c in 'AB']),
        stage2_all_channel_GEVP=statuses([c['gevp'] for r in res2 for c in r['chan'].values()]),
        stage2_channel_GEVP_N_ge_12=statuses([c['gevp'] for r in res2 if r['N']>=12 for c in r['chan'].values()]))
    out['valley_summary']=[dict(stage=1,N=r['N'],beta_std=r['beta_std'],**{k:v for k,v in r['valley_slices'].items() if k!='percentiles'}) for r in res if r['beta_std']<3.3 and r['T']==3*r['N']]+[dict(stage=2,N=r['N'],beta_std=r['beta_std'],**{k:v for k,v in r['valley'].items() if k!='percentiles'}) for r in res2 if r['beta_std']<3.3]
    print('peak GB, largest worker',round(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/2**30,2),'parent',round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**30,2),flush=True)
    tmp=OUT+'.tmp'; json.dump(out,open(tmp,'w'),indent=1); os.replace(tmp,OUT)
    for r in res:
        line=f"N={r['N']:2d} T={r['T']:2d} b={r['beta_std']:<7.4g} n={r['n']:6d} u={r.get('u',float('nan')):7.3f} tree={r['tree_E1L']:.2f} flips={r.get('valley_flips',0):5d} P3={r['P3_abs']:.2f}"
        if 'gevp' in r:
            b=best(r)
            for k in ('GEVP_A','GEVP_B','O1+O2','O1-O2'):
                if k in b: line+=f" {k}:{b[k][0]:.2f}({b[k][1]:.2f})"
            g=r['one_gluon']['2']
            if 'EL' in g: line+=f" 1g:{g['EL']:.2f}({g['ELerr']:.2f})"
        print(line,flush=True)
    return out

def phase_check(N=8,T=24,bstd=64.,n=3000):
    """The phase of Phi. The correct phase is continuous on x = 1..N; the earlier probe's phase pi(a+1/2)/N has the jump one site off."""
    V,co,up,dn,tw=geom(N,T); U=flat(N,T); seed_rng(77)
    def upd():
        sweep_hb(U,up,dn,tw,bstd)
        for _ in range(3): sweep_or(U,up,dn,tw)
    for _ in range(300): upd()
    a=np.empty((n,T,2)); b=np.empty((n,T,2)); w=np.empty((T,NOP)); 
    for i in range(n):
        upd()
        measure(U,up,tw,N,T,w,1); a[i,:,0]=w[:,0]; a[i,:,1]=w[:,1]
        measure(U,up,tw,N,T,w,0); b[i,:,0]=w[:,0]; b[i,:,1]=w[:,1]
    nb=50; out={}
    for name,x in (('continuous',a),('earlier_probe',b)):
        C=sum(sym(binned_corr(x[:,:,k],x[:,:,k],nb,center=False)[0]) for k in range(2))/2; j=jk_samples(C)
        out[name]=dict(meffL=[float(v)*N for v in meff_cosh(C.mean(0))[1:6]],err=[float(v)*N for v in jk_err(meff_cosh(j))[1:6]],C0=float(C.mean(0)[0]),C1=float(C.mean(0)[1]))
    out['tree_1gluon_EL']=tree_E1(N)*N/2
    print(json.dumps(out,indent=1),flush=True)
    json.dump(out,open(RAW+('/phase.json' if (N,bstd)==(8,64.) else f'/phase_N{N}_b{bstd:g}.json'),'w'))
    return out

def plan():
    """The production runs in the order made: [N, T, beta_std, n_therm, n_meas, per, flow_every, seed].
    beta_std on the fixed-u lines came from a pilot grid of u (200 + 60 updates) by interpolating 1/u."""
    L=[]
    def add(N,T,b,nm,fe=80,seed=1): L.append([N,T,b,300 if N<=8 else 500,nm,1,fe,seed])
    for N,b,nm in ((4,5.38,40000),(6,5.67,30000),(8,5.80,20000),(12,5.95,6000)): add(N,3*N,b,nm)          # u = 1
    for N,b,nm in ((6,5.67,40000),(8,5.80,30000),(12,5.95,12000)): add(N,N,b,nm)                            # T = L
    for b in (16.,32.,64.): add(8,24,b,15000)
    add(8,8,32.,30000)
    for N,b,nm in ((4,3.47,40000),(6,3.73,30000),(8,3.82,20000),(12,4.00,6000)): add(N,3*N,b,nm)            # u = 2
    for N,b,nm in ((4,9.32,40000),(6,9.72,30000),(8,9.72,20000),(12,9.85,6000)): add(N,3*N,b,nm)            # u = 0.5
    for N,b,nm in ((4,2.72,40000),(6,2.93,30000),(8,3.04,20000),(12,3.21,6000)): add(N,3*N,b,nm)            # u = 3.3
    for N,nm in ((4,20000),(6,15000)):
        for b in (16.,32.,64.): add(N,3*N,b,nm)
    for b in (16.,64.): add(12,36,b,4000)
    add(16,48,6.06,2000,60)
    # Added after seeing N = 6 -> 12 fall by 0.54 +- 0.30 on the u = 2 line, so these are not part of the pre-registered sample.
    add(6,18,3.73,60000,80,2); add(8,24,3.82,20000,80,2); add(12,36,4.0,8000,80,2); add(16,48,4.1,2000,60)
    return L

def plan2():
    """Stage 2 runs, in order. Same beta_std as the stage 1 lines. Seed 11 so the streams are new."""
    L=[]
    def add(N,b,nm,fe=80): L.append([N,3*N,b,300 if N<=8 else 500,nm,1,fe,11])
    add(6,32.,15000); add(8,32.,10000)
    for b in (5.38,3.47,2.72): add(4,b,20000)
    for b in (9.72,5.67,3.73,2.93): add(6,b,20000)
    for b in (9.72,5.80,3.82,3.04): add(8,b,15000)
    for b in (5.95,4.0,3.21): add(12,b,5000)
    add(16,4.1,1500,60)
    return L

if __name__=='__main__':
    c=sys.argv[1]
    if c=='selftest': sys.exit(0 if selftest() else 1)
    elif c=='selftest2': sys.exit(0 if selftest2() else 1)
    elif c=='plan2':
        for e in plan2(): run2(*e)
    elif c=='run':
        a=sys.argv[2:]; print(run(int(a[0]),int(a[1]),float(a[2]),int(a[3]),int(a[4]),int(a[5]),int(a[6]),int(a[7])))
    elif c=='list':
        for e in json.loads(sys.argv[2]): run(*e)
    elif c=='plan':
        for e in plan(): run(*e)
    elif c=='phase':
        a=sys.argv[2:]
        if a: phase_check(int(a[0]),int(a[1]),float(a[2]),int(a[3]))
        else: phase_check()
    elif c=='analyze': analyze()
