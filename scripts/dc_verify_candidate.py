#!/usr/bin/env python3
r"""
dc_verify_candidate.py

Skeptical verification of a candidate NON-UNIQUE minimal-bending DC decomposition.
A real counterexample requires TWO decompositions (P1,Q1),(P2,Q2) that all satisfy:
  - Q_i convex AND P_i = Q_i + f convex            (valid DC)
  - total bending Σ slack(Q1) == Σ slack(Q2) == B*  (both MINIMAL, not just feasible)
  - Q1 - Q2 non-affine                              (genuinely different)
We extract them as argmin/argmax of one bending coordinate over the optimal face and
check every clause. We also re-derive B* and confirm both sit exactly on it.
"""
import numpy as np
from scipy.optimize import linprog
import importlib.util, os
spec = importlib.util.spec_from_file_location(
    "rig", os.path.join(os.path.dirname(__file__), "dc_uniqueness_rigorous.py"))
# avoid executing the search in that module: rebuild the pieces here instead.

import itertools
def grid2d(m):
    Vv = [(i, j) for j in range(m) for i in range(m)]
    idx = {v: k for k, v in enumerate(Vv)}
    tris = []
    for j in range(m-1):
        for i in range(m-1):
            a,b,c,d = idx[(i,j)],idx[(i+1,j)],idx[(i+1,j+1)],idx[(i,j+1)]
            tris += ([(a,b,d),(b,c,d)] if (i+j)%2==0 else [(a,b,c),(a,c,d)])
    from collections import defaultdict
    em = defaultdict(list)
    for t in tris:
        a,b,c = t
        for (u,v,w) in [(a,b,c),(b,c,a),(c,a,b)]:
            em[frozenset((u,v))].append((u,v,w))
    inter = [(tuple(e), l[0][2], l[1][2]) for e,l in em.items() if len(l)==2]
    return np.array([(x,y) for x,y in Vv], float), tris, inter

def plane_row(pts, simplex, w, V):
    M = np.column_stack([pts[list(simplex)], np.ones(len(simplex))])
    coeff = np.append(pts[w],1.0) @ np.linalg.inv(M)
    row = np.zeros(V)
    for cc,vtx in zip(coeff,simplex): row[vtx]+=cc
    return row

def build(pts,tris,inter):
    V=len(pts); conv=[]; slack=[]
    for t in tris:
        ts=set(t)
        for w in range(V):
            if w in ts: continue
            r=np.zeros(V); r[w]+=1; r-=plane_row(pts,t,w,V); conv.append(r)
    for (e,c1,c2) in inter:
        r=np.zeros(V); r[c2]+=1; r-=plane_row(pts,tuple(e)+(c1,),c2,V); slack.append(r)
    return np.array(conv), np.array(slack)

m=5; pts,tris,inter=grid2d(m); conv,slack=build(pts,tris,inter); V=len(pts)
xs=pts[:,0]/(m-1)*2-1; ys=pts[:,1]/(m-1)*2-1
A_aff=np.column_stack([np.ones(V),pts])
def aff_res(d):
    c,*_=np.linalg.lstsq(A_aff,d,rcond=None); return np.linalg.norm(d-A_aff@c)

def solve_min(h):
    cf=conv@h
    A_ub=np.vstack([-conv,-conv]); b_ub=np.concatenate([np.zeros(conv.shape[0]),cf])
    r=linprog(slack.sum(0),A_ub=A_ub,b_ub=b_ub,bounds=[(None,None)]*V,method="highs")
    return r,A_ub,b_ub

# reproduce the search to recover the SAME best f (seed 0, same recipe)
rng=np.random.default_rng(0); best=(-1,None)
for k in range(400):
    if k%3==0: h=rng.standard_normal(V)
    elif k%3==1:
        a=rng.standard_normal(6)
        h=a[0]*xs*ys+a[1]*xs*xs*ys+a[2]*xs*ys*ys+a[3]*xs**3+a[4]*ys**3+a[5]*xs*ys*(xs+ys)
    else:
        h=(xs**3-3*xs*ys*ys)+0.4*rng.standard_normal(V)
    r,A_ub,b_ub=solve_min(h)
    if not r.success: continue
    Bstar=float(slack.sum(0)@r.x)
    Af=np.vstack([A_ub,slack.sum(0)]); bf=np.append(b_ub,Bstar+1e-9)
    worst=0; arg=None
    for e in range(slack.shape[0]):
        hi=linprog(-slack[e],A_ub=Af,b_ub=bf,bounds=[(None,None)]*V,method="highs")
        lo=linprog(slack[e],A_ub=Af,b_ub=bf,bounds=[(None,None)]*V,method="highs")
        if hi.success and lo.success:
            rng_e=float(slack[e]@hi.x)-float(slack[e]@lo.x)
            if rng_e>worst: worst, arg=rng_e,(e,hi.x.copy(),lo.x.copy(),Bstar)
    if worst>best[0]: best=(worst,h.copy(),arg)

rng_val,h,(e,Qhi,Qlo,Bstar)=best
print("="*70); print(f"candidate f recovered; flagged edge e={e}, bending-range={rng_val:.4f}")
print("="*70)

def report(tag,Q):
    P=Q+h
    cQ=(conv@Q).min(); cP=(conv@P).min()
    tot=float(slack.sum(0)@Q)
    print(f"  {tag}: Q convex(min conv·Q)={cQ:+.2e}  P=Q+f convex={cP:+.2e}  "
          f"total bending={tot:.6f}")
    return tot,cQ,cP
print(f"  B* (claimed min total bending) = {Bstar:.6f}\n")
tH,cQH,cPH=report("Q_hi",Qhi)
tL,cQL,cPL=report("Q_lo",Qlo)
res=aff_res(Qhi-Qlo)
print(f"\n  Q_hi - Q_lo affine residual = {res:.4e}  (non-affine if >1e-6)")

# skeptical clauses
ok_feasible = min(cQH,cPH,cQL,cPL) >= -1e-6
ok_minimal  = abs(tH-Bstar)<1e-6 and abs(tL-Bstar)<1e-6
ok_distinct = res>1e-6
# extra paranoia: confirm B* is truly minimal by re-solving from scratch
r2,_,_=solve_min(h); Bstar2=float(slack.sum(0)@r2.x)
ok_Bstar = abs(Bstar-Bstar2)<1e-6
print("\nVERDICT")
print(f"  both decompositions feasible (convex P,Q):        {ok_feasible}")
print(f"  both achieve the minimum total bending B*:        {ok_minimal}")
print(f"  they differ by a non-affine function:             {ok_distinct}")
print(f"  B* reproducible / truly minimal:                  {ok_Bstar}")
if ok_feasible and ok_minimal and ok_distinct and ok_Bstar:
    print("\n  => GENUINE COUNTEREXAMPLE: minimal-bending DC is NON-UNIQUE for this f.")
    print("     My earlier 'unique in 2D/3D' was a blind-detector + biased-case artifact.")
else:
    print("\n  => NOT verified — detector bug; the 5.64 was spurious. Do not claim non-uniqueness.")
