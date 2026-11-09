"""Analyze yang_mills_sl_gpu.py output: required vs measured integral of alpha along the localization path.
required(t) = log(V0 / V(t)), a lower bound on int_0^t alpha (localization identity + Cauchy-Schwarz).
measured(t) = trapezoid of alpha_struct_oos (structured-span lower bound on alpha), with alpha = 1/4 on [0, t_min].
Usage: python3 yang_mills_sl_gpu_analyze.py file.json [file2.json ...]"""
import sys, json, math, collections
for f in sys.argv[1:]:
    rows=json.load(open(f)); mu={(r['N'],r['bstd']):r for r in rows if r['kind']=='mu'}   # keyed by (N, beta)
    path=collections.defaultdict(list)
    for r in rows:
        if r['kind']=='path': path[(r['N'],r['bstd'],r['t'])].append(r)
    for (N,b) in sorted(mu):
        m=mu[(N,b)]; extra=' '.join(f"{k}={v:.4f}" for k,v in m.items() if k.startswith('R_poly'))
        print(f"N={N} beta={b} plaq={m['plaq']:.4f} R={m['R']:.4f} (gauss {m['R_gauss_pred']:.3f}) {extra} tau~{m['tau_int_proxy']:.2f}")
        ts=sorted(t for (n,bb,t) in path if n==N and bb==b); integ=0.25*ts[0] if ts else 0; prev=None
        for t in ts:
            rs=path[(N,m['bstd'],t)]; V=sum(r['V_over_V0'] for r in rs)/len(rs); a=sum(r['alpha_struct_oos'] for r in rs)/len(rs)
            if prev: integ+=0.5*(a+prev[1])*(t-prev[0])
            prev=(t,a)
            req=-math.log(max(V,1e-12))
            grp=' '.join(f"req_{k[10:]}={-math.log(max(sum(r[k] for r in rs)/len(rs),1e-12)):+.3f}" for k in rs[0] if k.startswith('V_over_V0_'))
            print(f"   t={t:<6} V/V0={V:.3f} required_int={req:+.3f} {grp} alpha_struct={a:.3f} measured_int={integ:.3f} ny={len(rs)}")
