import numpy as np,sys
def an(fn,N,T):
    d=np.array([[float(x) for x in l.split()[1:]] for l in open(fn)])
    head=d[:,:4];c1=d[:,4:4+T];cn=d[:,4+T:4+2*T]
    c1=(c1+np.roll(c1[:,::-1],1,axis=1))/2; cn=(cn+np.roll(cn[:,::-1],1,axis=1))/2
    print(fn,"N",N,"T",T,"bins",len(d),"<O>=%.4f <|trW3|>=%.3f <trW3>=%.3f <|trW0|>=%.3f"%tuple(head.mean(0)))
    def meff(C,tm):
        out=[]
        for t in range(1,tm):
            r=(C[t-1]+C[t+1])/(2*C[t]); out.append(np.arccosh(r) if r>1 else np.nan)
        return np.array(out)
    def jk(f):
        n=len(d);v=np.array([f(np.delete(np.arange(n),i)) for i in range(n)])
        return f(np.arange(n)),np.sqrt((n-1)*np.nanmean((v-np.nanmean(v,0))**2,0))
    p1=2*np.arcsinh(np.sin(np.pi/(2*N)))
    m,e=jk(lambda I:meff(c1[I].mean(0),min(T//2,10)))
    print(" one-gluon m_eff:",np.round(m,3),"\n          +-   :",np.round(e,3)," tree=%.3f"%p1)
    conn=lambda I:cn[I].mean(0)-head[I,0].mean()**2
    m,e=jk(lambda I:meff(conn(I),min(T//2,8)))
    print(" neutral conn C:",np.array2string(conn(np.arange(len(d)))[:9],precision=2))
    print(" neutral m_eff:",np.round(m,3),"\n          +-   :",np.round(e,3)," tree 2-gluon=%.3f"%(2*p1))
for a in sys.argv[1:]:
    f,N,T=a.split(',');an(f,int(N),int(T))
