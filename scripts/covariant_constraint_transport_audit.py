#!/usr/bin/env python3
"""Covariant nonlinear constraint transport, with explicit microscopic cost tests."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from numpy.polynomial.hermite import hermgauss
import sympy as sy

from nonlinear_constraint_dressing_audit import comm, integrate


RNG=np.random.default_rng(9112713)


def hermitian(d,scale=1.):
    a=RNG.normal(size=(d,d))+1j*RNG.normal(size=(d,d))
    a=(a+a.conj().T)/2
    return scale*a/la.norm(a,2)


def exact_identities():
    q,y,lam,mu,hbar=sy.symbols('q y lambda mu hbar',real=True,positive=True)
    psi=sy.Function('psi')(q,y)
    def c(f):return hbar*sy.diff(f,y)+(mu*y-lam*q*q)*f
    def momentum(f):return -sy.I*hbar*(sy.diff(f,q)+2*lam*q*sy.diff(f,y)/mu)
    assert sy.simplify(c(momentum(psi))-momentum(c(psi)))==0
    assert sy.simplify(q*momentum(psi)-momentum(q*psi)-sy.I*hbar*psi)==0
    phi=sy.Function('phi')(q)
    gaussian=sy.exp(-mu*(y-lam*q*q/mu)**2/(2*hbar))
    assert sy.simplify(momentum(gaussian*phi)+sy.I*hbar*gaussian*sy.diff(phi,q))==0
    assert sy.simplify(momentum(momentum(gaussian*phi))+hbar*hbar*gaussian*sy.diff(phi,q,2))==0
    angle=sy.symbols('lambda',real=True)
    assert sy.simplify((1-sy.cos(angle))/8-sy.sin(angle/2)**2/4)==0
    return dict(covariant_momentum_preserves_constraint=True,canonical_commutator=True,
                kinetic_action_on_shifted_gaussian_exact=True,
                bare_induced_term='hbar*lambda^2*q^2/mu',covariant_induced_term=0,
                normal_gap='hbar*lambda_min(M), independent of dressing lambda',
                R2_five_qubit_coefficient='(1-cos(lambda))/8')


def unitary_response_tests():
    out=[]
    for d in [2,3]:
        t=hermitian(d);t=t@t
        v=hermitian(d);v=v@v
        b=t+v;a=7*t-v;f=hermitian(d)
        sources=[b,f];h2=hermitian(d);h3=hermitian(d,.2);local4=hermitian(d,.1)
        ell,k,hbar=1.1,1.7,.8
        mat=np.diag([8*ell,k]);inv=la.inv(mat);eye=np.eye(d)
        qquant=-(comm(b,comm(b,h2))/(8*ell)+comm(f,comm(f,h2))/k)/(4*hbar)
        target=local4-(a@b+b@a)/(16*ell)+2*f@f/k
        nodes,weights=hermgauss(20)
        root=np.diag(np.sqrt(hbar*np.diag(mat)))
        previous=None
        for lam in [.12,.06,.03]:
            bare=np.zeros((d,d),complex);cov=np.zeros_like(bare);norm=np.zeros_like(bare)
            raw_h2=np.zeros_like(bare);covariance_error=0.
            for index in itertools.product(range(20),repeat=2):
                p=root@nodes[list(index)];weight=np.prod(weights[list(index)])/np.pi
                exponent=-1j*lam/hbar*sum((v*s for v,s in zip(inv@p,sources)),np.zeros_like(bare))
                unitary=la.expm(exponent)
                derivatives=[]
                for j in range(2):
                    tangent=-1j*lam/hbar*sum((inv[i,j]*sources[i] for i in range(2)),np.zeros_like(bare))
                    du=la.expm_frechet(exponent,tangent,compute_expm=False)
                    derivatives.append(1j*hbar*du-1j*(inv@p)[j]*unitary)
                response=(-lam*unitary.conj().T@a@derivatives[0]
                          +2*k*derivatives[1].conj().T@derivatives[1]-hbar*eye)
                bare+=weight*(unitary.conj().T@(h2+lam*h3+lam**2*local4)@unitary+response)
                cov+=weight*(h2+lam*h3+lam**2*unitary.conj().T@local4@unitary+response)
                raw_h2+=weight*(unitary.conj().T@h2@unitary)
                norm+=weight*(unitary.conj().T@unitary)
                lifted=unitary@h2@unitary.conj().T
                covariance_error=max(covariance_error,la.norm(unitary.conj().T@lifted@unitary-h2))
            assert la.norm(norm-eye)<3e-12 and covariance_error<3e-12
            assert la.norm(bare-bare.conj().T)<3e-12 and la.norm(cov-cov.conj().T)<3e-12
            bare_error=la.norm(bare-h2-lam*h3-lam**2*(target+qquant))
            cov_error=la.norm(cov-h2-lam*h3-lam**2*target)
            _,old=integrate(sources,mat,lam,hbar,{'h2':lambda y:h2},order=20)
            embedding_compression_difference=la.norm(raw_h2-old['h2'])
            if previous is not None:
                assert previous[0]/cov_error>13
                assert previous[1]/embedding_compression_difference>13
            previous=(cov_error,embedding_compression_difference)
            out.append(dict(physical_dimension=d,lambda_value=lam,bare_remainder=bare_error,
                            covariant_remainder=cov_error,quantum_correction_norm=la.norm(qquant),
                            embedding_compression_difference=embedding_compression_difference,
                            covariance_identity_error=covariance_error,
                            scope='Noncommuting regulated source matrices; momentum-space Gaussian quadrature'))
    return out


def covariant_oscillator_matrix(nq,ny,lam,omega,mu,hbar,strength):
    # Extra rows retain every intermediate output of Pi^2 and q^4.
    qdim,ydim=nq+5,ny+5
    aq=sp.diags(np.sqrt(np.arange(1,qdim)),1,shape=(qdim,qdim),format='csr')
    ay=sp.diags(np.sqrt(np.arange(1,ydim)),1,shape=(ydim,ydim),format='csr')
    q=np.sqrt(hbar/(2*omega))*(aq+aq.T)
    p=1j*np.sqrt(hbar*omega/2)*(aq.T-aq)
    y=np.sqrt(hbar/(2*mu))*(ay+ay.T)
    py=1j*np.sqrt(hbar*mu/2)*(ay.T-ay)
    iq=sp.eye(qdim);iy=sp.eye(ydim)
    pi=sp.kron(p,iy)+2*lam/mu*sp.kron(q,py)
    q2=q@q
    normal=(hbar*mu*sp.kron(iq,sp.diags(np.arange(ydim)))
            -lam*mu*sp.kron(q2,y)+lam**2/2*sp.kron(q2@q2,iy))
    full=strength*normal+pi@pi/2+omega**2*sp.kron(q2,iy)/2
    rows=np.array([i*ydim+j for i in range(nq) for j in range(ny)])
    return full.tocsr()[rows][:,rows].tocsc()


def oscillator_tests():
    out=[]
    lam,omega,mu,hbar=.3,.7,1.2,1.
    target=hbar*omega*(np.arange(3)+.5)
    for strength in [2.,16.,64.]:
        spectra=[]
        for nq,ny in [(40,32),(58,48)]:
            mat=covariant_oscillator_matrix(nq,ny,lam,omega,mu,hbar,strength)
            vals,vecs=eigsh(mat,k=3,sigma=-.1,which='LM',tol=2e-12)
            indices=np.argsort(vals);vals=vals[indices];vecs=vecs[:,indices]
            residual=la.norm(mat@vecs-vecs*vals)
            assert residual<2e-8
            spectra.append(vals)
        error=float(np.max(abs(spectra[-1]-target)))
        assert np.min(spectra[-1]-target)>-2e-10
        assert error<3e-5,error
        out.append(dict(Lambda=strength,eigenvalues=spectra[-1].tolist(),exact_eigenvalues=target.tolist(),
                        error=error,cutoff_comparison=float(np.max(abs(spectra[0]-spectra[1]))),
                        residual=residual,physical_cutoff=58,normal_cutoff=48,
                        scope='Variational Galerkin compression with full intermediate outputs; no interval certificate'))
    return out


def regulated_band_tests():
    """A genuine noncommuting-source slow Hamiltonian, not a full conjugation."""
    hbar,ell,k,lam=.8,1.1,1.7,.12
    identity=np.eye(2);px,py,pz=PAULI
    t=(identity+.2*px)@(identity+.2*px)
    v=.3*(identity+.3*pz)@(identity+.3*pz)
    b=t+v;a=7*t-v;f=.4*py+.2*pz
    h2=np.diag([.3,.9]);h3=.07*px;local4=.03*pz
    matrices=[]
    for n in [12,18]:
        lower=np.diag(np.sqrt(np.arange(1,n+2)),1)
        q=(lower+lower.T)/np.sqrt(2)
        p=(lower-lower.T)/(1j*np.sqrt(2))
        q2=(q@q)[:n,:n];q=q[:n,:n];p=p[:n,:n]
        ia=np.eye(n);it=np.eye(n*n)
        y0=np.sqrt(hbar/(8*ell))*np.kron(q,ia)
        y1=np.sqrt(hbar/k)*np.kron(ia,q)
        y1square=hbar/k*np.kron(ia,q2)
        pi0=np.sqrt(hbar*8*ell)*np.kron(p,ia)
        pi1=np.sqrt(hbar*k)*np.kron(ia,p)
        generator=np.kron(pi0,b)/(8*ell)+np.kron(pi1,f)/k
        unitary=la.expm(-1j*lam*generator/hbar)
        normal=hbar*np.kron(8*ell*np.kron(np.diag(np.arange(n)),ia)
                            +k*np.kron(ia,np.diag(np.arange(n))),identity)
        bare_response=-lam*np.kron(y0,a)+np.kron(2*k*y1square-hbar*it,identity)
        slow=np.kron(it,h2+lam*h3)+unitary.conj().T@(bare_response+lam**2*np.kron(it,local4))@unitary
        effective=slow[:2,:2]
        matrices.append((normal,slow,effective))
    exact_target=la.eigvalsh(matrices[-1][2])
    target_comparison=la.norm(matrices[0][2]-matrices[1][2])
    assert target_comparison<1e-10
    out=[];previous=None
    for strength in [2.,8.,32.,128.]:
        eigenvalues=[]
        for normal,slow,_ in matrices:
            vals=la.eigh(strength*normal+slow,eigvals_only=True,subset_by_index=[0,2])
            eigenvalues.append(vals)
        vals=eigenvalues[-1]
        error=float(np.max(abs(vals[:2]-exact_target)))
        cutoff=float(np.max(abs(eigenvalues[0][:2]-vals[:2])))
        assert cutoff<2e-7,cutoff
        assert np.all(vals[:2]<=exact_target+2e-10)
        if previous is not None:assert error<previous
        previous=error
        out.append(dict(Lambda=strength,physical_eigenvalues=vals[:2].tolist(),
                        limiting_eigenvalues=exact_target.tolist(),first_excluded_eigenvalue=float(vals[2]),
                        max_error=error,normal_cutoff_comparison=cutoff,
                        effective_cutoff_comparison=target_comparison,
                        scope='Noncommuting physical matrices, two normal oscillators; increasing normal cutoff, no interval certificate'))
    return out


PAULI=[np.array([[0,1],[1,0]],complex),np.array([[0,-1j],[1j,0]],complex),np.diag([1.,-1.])]


def at_site(op,site,n):
    result=np.ones((1,1),complex)
    for i in range(n):result=np.kron(result,op if i==site else np.eye(2))
    return result


def full_spin_tests():
    out=[]
    lam=.61;omega1,omega2=.8,1.1;exchange=1.7
    for r in [1,2,3]:
        n=3*r;dim=2**n;eye=np.eye(dim)
        collective=[];numbers=[];penalty=np.zeros((dim,dim),complex)
        for block in range(3):
            operators=[[at_site(op,block*r+j,n) for j in range(r)] for op in PAULI]
            collective.append([sum(ops,np.zeros_like(penalty)) for ops in operators])
            numbers.append((r*eye-collective[-1][2])/2)
            for i in range(r):
                for j in range(i):
                    penalty+=exchange/(2*r)*(eye-sum((ops[i]@ops[j] for ops in operators),np.zeros_like(penalty)))
        generator=collective[0][1]@collective[1][0]@collective[2][0]/(2*r)**1.5
        unitary=la.expm(-1j*lam*generator)
        normal=unitary@numbers[0]@unitary.conj().T
        probe=at_site(PAULI[2],r,n)
        actual=la.norm(comm(normal,probe),2)
        expected=r*max(abs(np.sin(2*lam*c/(2*r)**1.5)) for c in range(-r,r+1,2))
        assert abs(actual-expected)<2e-11
        assert abs(la.norm(generator,2)-r**1.5/(2*np.sqrt(2)))<2e-11
        assert la.norm(comm(unitary,penalty))<2e-10
        base=numbers[0]/r+(omega1*numbers[1]+omega2*numbers[2])/r**2+penalty
        ham=unitary@base@unitary.conj().T
        vals=la.eigvalsh(ham)*r*r
        predicted=sorted(r*a+omega1*b+omega2*c for a,b,c in itertools.product(range(r+1),repeat=3))[:6]
        assert la.norm(vals[:6]-predicted)<3e-10
        pauli_coefficient=None
        if r==2:
            string=at_site(PAULI[2],0,n)
            for site in range(r,3*r):string=string@at_site(PAULI[0],site,n)
            pauli_coefficient=float(np.trace(string@normal).real/dim)
            assert abs(pauli_coefficient-(1-np.cos(lam))/8)<1e-12
        out.append(dict(block_size=r,full_dimension=dim,lambda_value=lam,
                        microscopic_commutator_norm=actual,exact_commutator_norm=expected,
                        unscaled_parent_budget_lower_bound=actual/2,
                        generator_optimal_budget=np.sqrt(r)/(2*np.sqrt(2)),
                        scaled_parent_budget_upper_bound=1+(omega1+omega2)/r,
                        low_physical_eigenvalues=vals[:6].tolist(),expected_eigenvalues=predicted,
                        five_qubit_coefficient=pauli_coefficient,exchange_gap=exchange))
    return out


def pauli_tests():
    out=[]
    for r,selected,lam in [(2,2,.61),(4,4,.9),(6,6,1.1)]:
        weights={c:0 for c in range(-r,r+1,2)}
        for j in range(selected+1):
            for l in range(r-selected+1):
                c=r-2*(j+l)
                weights[c]+=(-1)**j*math.comb(selected,j)*math.comb(r-selected,l)
        scale=2/(2*r)**1.5
        value=-.5*sum(wb*wc*np.cos(lam*scale*b*c) for b,wb in weights.items() for c,wc in weights.items())/2**(2*r)
        # Integer moments verify the leading coefficient without subtractive trigonometric cancellation.
        moment=sum(w*c**selected for c,w in weights.items())
        assert moment==2**r*math.factorial(selected)
        leading=-.5*(-1)**(selected//2)*math.factorial(selected)*scale**selected
        independently=-.5*(-1)**(selected//2)/math.factorial(selected)*scale**selected*moment**2/2**(2*r)
        assert abs(leading-independently)<1e-14 and abs(value)>1e-8
        out.append(dict(block_size=r,selected_per_control=selected,pauli_weight=2*selected+1,
                        lambda_value=lam,coefficient=value,leading_lambda_coefficient=leading))
    return out


def dressed_state(size,lam,spin_r=None,phase=1.):
    index=np.arange(1,size)
    amplitude=np.sqrt(index) if spin_r is None else np.sqrt(index*(1-(index-1)/spin_r))
    b=np.diag(amplitude,1)
    q=(b+b.T)/np.sqrt(2);p=(b-b.T)/(1j*np.sqrt(2))
    dp,vp=la.eigh(p);dq,vq=la.eigh(q)
    initial=np.zeros((size,size,size),complex)
    initial[0,0,0]=1/np.sqrt(2);initial[0,1,1]=phase/np.sqrt(2)
    coeff=np.einsum('ai,bj,ck,ijk->abc',vp.conj().T,vq.conj().T,vq.conj().T,initial,optimize=True)
    coeff*=np.exp(-1j*lam*dp[:,None,None]*dq[None,:,None]*dq[None,None,:])
    result=np.einsum('ia,jb,kc,abc->ijk',vp,vq,vq,coeff,optimize=True)
    return result,q


def spin_limit_tests():
    out=[]
    lam=.35;omega1,omega2=.8,1.1;time=.7
    reference,_=dressed_state(80,lam)
    larger,_=dressed_state(96,lam)
    padded=np.zeros_like(larger);padded[:80,:80,:80]=reference
    reference_difference=la.norm((larger-padded).ravel())
    assert reference_difference<2e-6,reference_difference
    reference=larger
    time_reference,_=dressed_state(96,lam,phase=np.exp(-1j*(omega1+omega2)*time))
    previous=None
    for r in [4,8,16,32,64]:
        state,q=dressed_state(r+1,lam,spin_r=r)
        overlap=np.vdot(reference[:r+1,:r+1,:r+1],state)
        difference=np.sqrt(max(0.,2-2*overlap.real))
        action=np.einsum('ij,jkl->ikl',q,state)
        response=float(np.vdot(state,action).real)
        evolved,_=dressed_state(r+1,lam,spin_r=r,phase=np.exp(-1j*(omega1+omega2)*time))
        overlap_time=np.vdot(time_reference[:r+1,:r+1,:r+1],evolved)
        time_difference=np.sqrt(max(0.,2-2*overlap_time.real))
        assert abs(la.norm(state.ravel())-1)<2e-12
        if previous is not None:assert difference<previous
        previous=difference
        out.append(dict(block_size=r,state_norm_difference=difference,response=response,
                        limiting_response=lam/2,physical_time=time,evolution_norm_difference=time_difference,
                        normal_gap_in_physical_units=r,reference_cutoff_comparison=reference_difference,
                        scope='Exact symmetric-spin unitary; canonical reference compared at two occupation cutoffs'))
    return out


def inverse_locality_tests():
    out=[]
    for side in [8,16,32,64]:
        frequency=2*np.pi*np.arange(side)/side
        ell=4*np.sin(frequency/2)**2
        symbol=np.zeros(side);symbol[1:]=1/ell[1:]
        column=np.fft.ifft(symbol).real
        lower=1/np.min(ell[1:]);row_sum=float(np.sum(abs(column)))
        residual=la.norm(np.roll(column,1)+np.roll(column,-1)-2*column+np.eye(side)[0]-1/side)
        assert row_sum>=lower-1e-11 and residual<1e-10
        out.append(dict(side=side,inverse_row_absolute_sum=row_sum,spectral_lower_bound=lower,
                        elliptic_residual=residual,scope='Periodic one-dimensional inverse; same small-momentum pole mechanism in higher dimensions'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report={'exact_identities':exact_identities(),'unitary_response':unitary_response_tests(),
            'covariant_oscillator':oscillator_tests(),'regulated_band':regulated_band_tests(),
            'full_spin':full_spin_tests(),
            'high_weight_pauli':pauli_tests(),'spin_limit':spin_limit_tests(),
            'inverse_locality':inverse_locality_tests()}
    paths=['COVARIANT_CONSTRAINT_TRANSPORT.md','scripts/covariant_constraint_transport_audit.py',
           'NONLINEAR_CONSTRAINT_DRESSING.md','scripts/nonlinear_constraint_dressing_audit.py',
           'data/nonlinear_constraint_dressing_audit.json',
           'HOLOMORPHIC_TENSOR_PHASE.md','data/holomorphic_tensor_phase_audit.json',
           'EINSTEIN_QUARTIC_CONSTRAINTS.md','TENSOR_VERTEX_SELECTION.md','SPATIAL_METRIC_VACUUM.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    report['scope']={
        'proved':'Covariant operator transport; response-order cancellation; exact commuting-source repair; microscopic strength and interaction-order tests; hierarchical three-block spin limit',
        'not_proved':['Finite-body local nonlinear tensor parent','Einstein clock algebra','interacting protected masslessness',
                      'physical Newton constant','joint continuum limit','TOE'],
        'warning':'A fully transported free Hamiltonian remains a free theory; the control is not gravitational self-interaction'}
    target=root/'data/covariant_constraint_transport_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    count=sum(len(report[key]) for key in ['unitary_response','covariant_oscillator','full_spin',
                                         'high_weight_pauli','spin_limit','inverse_locality','regulated_band'])
    print('PASS: exact identities and %d numerical cases'%count)
    print('Report:',target)
    print('Largest-spin response:',report['spin_limit'][-1]['response'],'limit:',report['spin_limit'][-1]['limiting_response'])


if __name__=='__main__':main()
