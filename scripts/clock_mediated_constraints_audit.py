#!/usr/bin/env python3
"""Local clock mediation of a supplied nonlinear quantum constraint sector."""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la

from covariant_constraint_transport_audit import PAULI, at_site


def comm(a,b):return a@b-b@a


def kron(*args):
    ans=np.ones((1,1),complex)
    for a in args:ans=np.kron(ans,a)
    return ans


def path_laplacian(t):
    lap=np.zeros((t+1,t+1))
    for j in range(t):
        lap[j,j]+=1;lap[j+1,j+1]+=1
        lap[j,j+1]-=1;lap[j+1,j]-=1
    return lap


def prefixes(gates):
    result=[np.eye(len(gates[0]),dtype=complex)]
    for gate in gates:result.append(gate@result[-1])
    return result


def legal_model(gates,normal,normal_sum,initial):
    t=len(gates);n=t+1;d=len(normal);v=prefixes(gates)
    gauge=la.block_diag(*v)
    c=kron(path_laplacian(t)/t,np.eye(d))
    c[:d,:d]+=normal/normal_sum
    history=np.concatenate([u@initial for u in v],axis=0)/np.sqrt(n)
    return gauge@c@gauge.conj().T,history,v


def example(lam,rounds):
    x,y,z=PAULI;i=np.eye(2);number=(i-z)/2
    g1=kron(y,i,np.diag([1.,2.]),x)
    g2=kron(i,y,i,z)
    gates=[];supports=[]
    for _ in range(rounds):
        gates += [la.expm(-1j*lam*g1/rounds),la.expm(-1j*lam*g2/rounds)]
        supports += [{0,2,3},{1,3}]
    normal=kron(number,i,i,i)+kron(i,number,i,i)
    initial=np.eye(16,dtype=complex)[:,:4]
    base=kron(i,i,.3*x,i)+kron(i,i,i,.5*z)
    bare=-lam*.25*kron(x,i,i,x)+.4*kron(i,number,i,i)
    return gates,supports,normal,initial,base,bare


def full_clock(gates,supports,normal,normal_sum):
    t=len(gates);dc=2**t;dw=len(normal);nwork=int(np.log2(dw))
    eye=np.eye(dc);num=np.diag([0.,1.]);raise_=np.array([[0,0],[1,0]],complex)
    ns=[at_site(num,j,t) for j in range(t)]
    illegal=np.zeros((dc,dc),complex);prop=np.zeros((dc*dw,dc*dw),complex)
    load=np.zeros(t+nwork);max_support=0
    for j in range(t-1):
        illegal+=(eye-ns[j])@ns[j+1]
        load[j:j+2]+=1
    for j,gate in enumerate(gates):
        guard=(ns[j-1] if j else eye)@(eye-ns[j+1] if j+1<t else eye)
        raising=at_site(raise_,j,t)
        prop+=(kron(guard,np.eye(dw))-kron(guard@raising,gate)
               -kron(guard@raising.conj().T,gate.conj().T))/t
        clocks={k for k in [j-1,j,j+1] if 0<=k<t}
        support=clocks|{t+k for k in supports[j]}
        load[list(support)]+=2/t;max_support=max(max_support,len(support))
    # In this concrete example the input is two on-site number terms.
    load[0]+=1
    load[t:t+2]+=.5
    full=kron(illegal,np.eye(dw))+prop+kron(eye-ns[0],normal/normal_sum)
    indices=[sum(1<<(t-j-1) for j in range(k)) for k in range(t+1)]
    rows=np.concatenate([np.arange(k*dw,(k+1)*dw) for k in indices])
    return full,rows,float(max(load)),max_support,np.diag(illegal).real


def full_clock_tests():
    out=[]
    for rounds in [1,2,3]:
        for lam in [.25,.7]:
            gates,supports,normal,initial,base,bare=example(lam,rounds)
            full,rows,budget,support,violations=full_clock(gates,supports,normal,2.)
            legal,history,v=legal_model(gates,normal,2.,initial)
            t=len(gates);gamma=1/(2*(t+1)*max(t*t,2.))
            restricted=full[np.ix_(rows,rows)]
            other=np.setdiff1d(np.arange(len(full)),rows)
            illegal_gap=la.eigh(full[np.ix_(other,other)],eigvals_only=True,subset_by_index=[0,0])[0]
            vals=la.eigh(full,eigvals_only=True,subset_by_index=[0,4])
            residual=la.norm(legal@history)
            assert la.norm(restricted-legal)<2e-12 and residual<2e-12
            assert la.norm(full[np.ix_(other,rows)])<2e-12
            assert max(abs(vals[:4]))<2e-12 and vals[4]>=gamma-2e-12
            assert illegal_gap>=1-2e-12 and budget<=9 and support<=6
            assert la.norm(history.conj().T@history-np.eye(4))<2e-12
            out.append(dict(events=t,coupling=lam,full_qubit_dimension=len(full),kernel_dimension=4,
                            kernel_residual=residual,normal_gap=float(vals[4]),gap_lower_bound=gamma,
                            illegal_clock_gap=float(illegal_gap),summed_strength_budget=budget,
                            largest_term_support=support,scope='Full clock and work tensor product, including illegal clocks'))
    return out


def clock_gap_tests():
    out=[]
    for t in [1,2,5,12,40]:
        lap=path_laplacian(t)/t
        for ratio in [1.,.1]:
            pinned=lap.copy();pinned[0,0]+=ratio
            actual=min(la.eigvalsh(lap)[1],la.eigvalsh(pinned)[0],1.)
            bound=1/(2*(t+1)*max(t*t,1/ratio))
            assert actual>=bound-2e-13
            out.append(dict(events=t,input_gap_divided_by_norm_sum=ratio,gap=float(actual),lower_bound=bound))
    return out


def band_tests():
    gates,supports,normal,initial,base,bare=example(.7,2)
    c,j,v=legal_model(gates,normal,2.,initial)
    n=len(gates)+1;dw=len(normal);gamma=1/(2*n*max(len(gates)**2,2.))
    slow=np.zeros_like(c);slow[:dw,:dw]=n*base;slow[-dw:,-dw:]+=n*bare
    target=initial.conj().T@(base+v[-1].conj().T@bare@v[-1])@initial
    assert la.norm(j.conj().T@slow@j-target)<2e-12
    b=n*(la.norm(base,2)+la.norm(bare,2));expected=la.eigvalsh(target)
    # A boundary observable has correct first moment, but not its bare products.
    obs=np.zeros_like(c);obs[:dw,:dw]=n*np.eye(dw)
    first=j.conj().T@obs@j;second=j.conj().T@obs@obs@j
    assert la.norm(first-np.eye(4))<2e-12 and la.norm(second-n*np.eye(4))<2e-12
    out=[];previous=None
    for factor in [16,64,256,1024]:
        epsilon=gamma/(factor*b)
        h=c/epsilon+slow
        vals,vecs=la.eigh(h)
        error=float(max(abs(vals[:4]-expected)))
        estimate=epsilon*b*b/(gamma-2*epsilon*b)
        p=vecs[:,:4]@vecs[:,:4].conj().T
        leakage=la.norm(p-j@j.conj().T,2)
        pbound=epsilon*b/(gamma-2*epsilon*b)
        time=.6
        evolved=(vecs*np.exp(-1j*time*vals))@(vecs.conj().T@j)
        ideal=j@la.expm(-1j*time*target)
        time_error=la.norm(evolved-ideal,2)
        assert error<=estimate+2e-9 and leakage<=pbound+2e-9
        assert time_error<=16*epsilon*b/gamma*(1+time*b)+2e-9
        if previous is not None:assert error<previous
        previous=error
        out.append(dict(epsilon=epsilon,eigenvalues=vals[:4].tolist(),target_eigenvalues=expected.tolist(),
                        spectral_error=error,spectral_bound=estimate,projector_error=leakage,
                        projector_bound=pbound,evolution_error=time_error,
                        boundary_identity_second_moment=float(np.trace(second).real/4),
                        scope='Supplied noncommuting four-dimensional physical sector; full legal clock band'))
    return out


def oscillator(n):
    a=np.diag(np.sqrt(np.arange(1,n+2)),1)
    q=(a+a.T)/np.sqrt(2);p=(a-a.T)/(1j*np.sqrt(2))
    return q[:n,:n],p[:n,:n],(q@q)[:n,:n],(p@p)[:n,:n]


def einstein_data():
    # The actual b_cos(2k), f_x,sin(k) source pair at k=hbar=1.
    # One qubit per physical oscillator; squares compressed BEFORE truncation.
    q,p,q2,p2=oscillator(2);i=np.eye(2)
    qs=[kron(q,i,i),kron(i,q,i),kron(i,i,q)]
    ps=[kron(p,i,i),kron(i,p,i),kron(i,i,p)]
    qs2=[kron(q2,i,i),kron(i,q2,i),kron(i,i,q2)]
    ps2=[kron(p2,i,i),kron(i,p2,i),kron(i,i,p2)]
    t=(ps2[1]-ps2[2])/np.sqrt(2)
    potential=(qs2[2]-qs2[1])/(4*np.sqrt(2))
    b=t+potential;a=7*t-potential
    f=(qs[0]@ps[1]-ps[0]@qs[1])/4
    h2=sum(ps2)+.25*(qs2[1]+qs2[2])
    qn,pn,qn2,_=oscillator(4);ia=np.eye(4);ip=np.eye(8)
    y0=kron(qn,ia)/np.sqrt(32);y1square=kron(ia,qn2)
    g1=kron(pn,ia,b)/np.sqrt(32);g2=kron(ia,pn,f)
    initial=np.eye(128,dtype=complex)[:,:8]
    target=-(a@b+b@a)/64+2*f@f
    return a,b,f,h2,g1,g2,y0,y1square,initial,target


def strang(g1,g2,lam,rounds):
    half=la.expm(-.5j*lam*g1/rounds);full=la.expm(-1j*lam*g2/rounds)
    gates=[]
    for _ in range(rounds):gates += [half,full,half]
    return gates


def einstein_response_tests():
    a,b,f,h2,g1,g2,y0,y1square,initial,target=einstein_data()
    out=[];previous=None
    for lam in [.24,.12,.06]:
        u=la.expm(-1j*lam*(g1+g2))
        bare=-lam*kron(y0,a)+kron(2*y1square-np.eye(16),np.eye(8))
        result=h2+initial.conj().T@u.conj().T@bare@u@initial
        error=la.norm(result-h2-lam*lam*target)
        raw_h2=initial.conj().T@u.conj().T@kron(np.eye(16),h2)@u@initial
        correction=-(comm(b,comm(b,h2))/32+comm(f,comm(f,h2)))/4
        raw_error=la.norm(raw_h2-h2-lam*lam*correction)
        assert la.norm(comm(b,f))>.1 and la.norm(correction)>1e-4
        if previous is not None:assert previous/error>14,(previous,error)
        previous=error
        out.append(dict(coupling=lam,quartic_response_error=error,bare_kinetic_remainder=raw_error,
                        known_bare_kinetic_correction=la.norm(correction),source_commutator_norm=la.norm(comm(b,f)),
                        scope='Actual Einstein source pair at fixed physical two-level and normal four-level cutoffs; not the full quartic or regulator removal'))
    return out


def circuit_tests():
    a,b,f,h2,g1,g2,y0,y1square,initial,target=einstein_data()
    lam=.6;u=la.expm(-1j*lam*(g1+g2))
    bare=-lam*kron(y0,a)+kron(2*y1square-np.eye(16),np.eye(8))
    exact=initial.conj().T@u.conj().T@bare@u@initial
    out=[];previous=None
    for rounds in [1,2,4,8,16]:
        gates=strang(g1,g2,lam,rounds);approx=prefixes(gates)[-1]
        delta=la.norm(approx-u,2)
        result=initial.conj().T@approx.conj().T@bare@approx@initial
        response_error=la.norm(result-exact,2)
        assert response_error<=2*la.norm(bare,2)*delta+1e-12
        if previous is not None:assert previous/delta>3.8
        previous=delta
        out.append(dict(rounds=rounds,events=len(gates),endpoint_unitary_error=delta,
                        response_error=response_error,response_error_bound=2*la.norm(bare,2)*delta,
                        largest_work_gate_support=4,clock_term_support_bound=7,
                        scope='Fixed seven-work-qubit Einstein source-pair circuit; exact history kernel for each supplied circuit'))
    return out


def diamond(a,b,lam,repair=False):
    ua=la.expm(-1j*lam*a);ub=la.expm(-1j*lam*b);d=len(a)
    last=ub@ua@ub.conj().T if repair else ua
    edges=[(0,1,ua),(0,2,ub),(1,3,ub),(2,3,last)]
    h=np.zeros((4*d,4*d),complex)
    for i,j,u in edges:
        h[i*d:(i+1)*d,i*d:(i+1)*d]+=np.eye(d)
        h[j*d:(j+1)*d,j*d:(j+1)*d]+=np.eye(d)
        h[j*d:(j+1)*d,i*d:(i+1)*d]-=u
        h[i*d:(i+1)*d,j*d:(j+1)*d]-=u.conj().T
    mismatch=ub@ua-last@ub
    holonomy=(last@ub).conj().T@ub@ua
    angles=np.angle(la.eigvals(holonomy))
    expected=np.sort([2-2*np.cos((angle+2*np.pi*m)/4) for angle in angles for m in range(4)])
    vals=la.eigvalsh(h)
    assert la.norm(vals-expected)<2e-12
    fixed=int(d-np.linalg.matrix_rank(mismatch,tol=1e-10))
    assert np.sum(abs(vals)<1e-11)==fixed
    return vals,fixed,la.norm(mismatch)


def loop_tests():
    x,y,z=PAULI
    _,b,f,*_=einstein_data()
    models=[('bounded_nonscalar',la.block_diag(x,2*x),la.block_diag(z,z)),('Einstein_source_pair',b,f)]
    out=[]
    for name,a,b in models:
        previous=None
        for lam in [.12,.06,.03]:
            vals,fixed,mismatch=diamond(a,b,lam)
            repaired,repair_fixed,repair_mismatch=diamond(a,b,lam,repair=True)
            assert repair_fixed==len(a) and repair_mismatch<2e-12
            assert fixed<len(a)
            target=la.eigvalsh(comm(a,b).conj().T@comm(a,b))/16
            error=la.norm(vals[:len(a)]/lam**4-target)
            if previous is not None:assert previous/error>3.6,(name,previous,error)
            previous=error
            out.append(dict(model=name,coupling=lam,physical_input_dimension=len(a),unrepaired_kernel_dimension=fixed,
                            repaired_kernel_dimension=repair_fixed,loop_mismatch=mismatch,
                            fourth_order_energy_error=error,
                            scope='A source-order diamond, not Einstein hypersurface-deformation generators'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(full_clock=full_clock_tests(),clock_gap=clock_gap_tests(),physical_band=band_tests(),
                Einstein_response=einstein_response_tests(),circuit_approximation=circuit_tests(),source_loops=loop_tests())
    paths=['CLOCK_MEDIATED_CONSTRAINTS.md','scripts/clock_mediated_constraints_audit.py',
           'POLYNOMIAL_SPIN_CONSTRAINTS.md','data/polynomial_spin_constraints_audit.json',
           'COVARIANT_CONSTRAINT_TRANSPORT.md','scripts/covariant_constraint_transport_audit.py',
           'data/covariant_constraint_transport_audit.json','LOCAL_CAUSAL_CLOCK.md',
           'NONLINEAR_CONSTRAINT_DRESSING.md','EINSTEIN_QUARTIC_CONSTRAINTS.md',
           'GRAVITY_FROM_CLOCK_CONSTRAINTS.md','SPIN_CLOCK_BRACKET.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    report['scope']={'proved':'Exact supplied-circuit kernel with bounded interaction order and strength; explicit shrinking gap and low-band error; source-order holonomy',
                     'not_proved':['Einstein refoliation algebra','autonomous gate selection','uniform spatial tensor phase',
                                   'physical cutoff removal','protected masslessness','physical Newton constant','TOE'],
                     'qualification':'Clock mediation encodes supplied dynamics. Boundary compression does not preserve bare observable products.'}
    target=root/'data/clock_mediated_constraints_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print('PASS:',sum(len(report[k]) for k in ['full_clock','clock_gap','physical_band','Einstein_response',
                                             'circuit_approximation','source_loops']),'numerical cases')
    print('Report:',target)
    print('Largest circuit response error:',report['circuit_approximation'][-1]['response_error'])


if __name__=='__main__':main()
