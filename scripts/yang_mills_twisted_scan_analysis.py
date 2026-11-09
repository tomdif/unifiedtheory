import numpy as np,glob,math
def load(L,b):
    T=3*L
    d=np.array([[float(x) for x in l.split()[1:]] for l in open(f"r_{L}_{b}.txt")])
    return d[:,:4],d[:,4:4+T],d[:,4+T:4+2*T],d[:,4+2*T:4+3*T],T
def sym(c): return (c+np.roll(c[:,::-1],1,axis=1))/2
def meff(C,tm):
    o=[]
    for t in range(1,tm):
        if C[t]<=0: o.append(np.nan);continue
        r=(C[t-1]+C[t+1])/(2*C[t]); o.append(np.arccosh(r) if r>1 else (0.0 if r>0 else np.nan))
    return np.array(o)
def jk(f,n):
    v=np.array([f(np.delete(np.arange(n),i)) for i in range(n)]);m=f(np.arange(n))
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        e=np.sqrt((n-1)*np.nanmean((v-np.nanmean(v,0))**2,0))
    return m,e
for b in ["1.1","1.2","1.3","1.5","2.0","3.0"]:
    print(f"beta_repo={b} beta_std={2*float(b):.1f}")
    for L in [6,8,10]:
        h,c1,cn,c3,T=load(L,b);c1,cn,c3=sym(c1),sym(cn),sym(c3);n=len(h)
        # plaquette-free readouts
        m1,e1=jk(lambda I:meff(c1[I].mean(0),6),n)
        mn,en=jk(lambda I:meff(cn[I].mean(0)-h[I,0].mean()**2,5),n)
        m3,e3=jk(lambda I:meff(c3[I].mean(0),7),n)
        f=lambda m,e:" ".join(f"{a*L:6.2f}({c*L:4.2f})" for a,c in zip(m,e))
        print(f" L={L:2d} |trW3|={h[:,1].mean():.3f} <trW3>={h[:,2].mean():+.3f}")
        print(f"    one-gluon E*L t=1..5: {f(m1,e1)}  tree={2*L*math.asinh(math.sin(math.pi/(2*L))):.2f}")
        print(f"    neutral   E*L t=1..4: {f(mn,en)}")
        print(f"    e3-flux   E*L t=1..6: {f(m3,e3)}")
