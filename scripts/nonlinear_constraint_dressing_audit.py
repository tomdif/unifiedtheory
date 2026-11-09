#!/usr/bin/env python3
"""Compatible nonlinear annihilation kernels and their normalized quantum response.

Finite matrix sources test operator ordering, not a full tensor field.
The oscillator limit has an independent analytic proof in the note.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from numpy.polynomial.hermite import hermgauss
import sympy as sy


RNG = np.random.default_rng(9112707)


def comm(a, b):
    return a @ b - b @ a


def hermitian(d, scale=1.0):
    a = RNG.normal(size=(d, d)) + 1j * RNG.normal(size=(d, d))
    a = (a + a.conj().T) / 2
    return a * scale / la.norm(a, 2)


def inverse_sqrt(a):
    vals, vecs = la.eigh(a)
    assert vals[0] > 0
    return (vecs / np.sqrt(vals)) @ vecs.conj().T


def exact_identities():
    x = sy.Matrix([[0, 1], [1, 0]])
    z = sy.diag(1, -1)
    y0, y1, h, lam = sy.symbols('y0 y1 h lambda', real=True, nonzero=True)
    sources = [x, z]
    ys = [y0, y1]
    a = [lam * s + lam**2 / (2*h) * sum(
        (ys[j] * comm(sources[j], s) for j in range(2)), sy.zeros(2))
         for s in sources]
    curvature = h*(a[1].diff(y0)-a[0].diff(y1))-comm(a[0], a[1])
    coefficient_two = curvature.applyfunc(lambda v: sy.expand(v).coeff(lam, 2))
    assert coefficient_two == sy.zeros(2)
    assert comm(x, z).det() == 4
    q, p, mu = sy.symbols('q p mu', real=True, positive=True)
    def poisson(f, g):
        return sy.diff(f,q)*sy.diff(g,p)-sy.diff(f,p)*sy.diff(g,q)
    geometric = sy.expand(h/(4*mu)*poisson(q*q, poisson(q*q,p*p/2)))
    assert geometric == h*q*q/mu
    t, v = sy.symbols('T V', real=True)
    scalar = -(7*t-v)*(t+v)/8
    assert sy.expand(scalar + (3*t+v)**2/10 - (t-3*v)**2/40) == 0
    return dict(second_order_flatness=True, naive_pauli_commutator_determinant=4,
                scalar_target=str(scalar), exact_geometric_potential=str(geometric),
                exact_oscillator_frequency='sqrt(omega^2+2*hbar*lambda^2/mu)',
                all_order_kernel='Omega exp(lambda*y.S/hbar) C^d',
                physical_map='J (J^dagger J)^(-1/2)')


def exact_tensor_correction():
    q0,qc,qs,p0,pc,ps,z,k=sy.symbols('q0 qc qs p0 pc ps z k',real=True)
    q=[q0,qc,qs];p=[p0,pc,ps]
    def poisson(a,b):
        return sy.expand(sum(sy.diff(a,x)*sy.diff(b,y)-sy.diff(a,y)*sy.diff(b,x)
                             for x,y in zip(q,p)))
    def average(a):
        return sy.simplify(sy.integrate(sy.expand_trig(sy.expand(a)),
                                       (z,0,2*sy.pi))/(2*sy.pi))
    e0=sy.Matrix([[0,0,1],[0,0,0],[1,0,0]])/sy.sqrt(2)
    diag=sy.diag(1,-1,0)
    h=q0*e0+(qc*sy.cos(z)+qs*sy.sin(z))*diag
    mom=p0*e0+(pc*sy.cos(z)+ps*sy.sin(z))*diag
    t=sy.trace(mom*mom);v=sy.trace((k*h.diff(z))**2)/4
    spatial=mom*h-h*mom
    f=[sy.expand(-((sy.trace(mom*k*h.diff(z)) if i==2 else 0)
                    +k*spatial[i,2].diff(z))/2) for i in range(3)]
    b=sy.expand(t+v);h2=average(b)
    ns=[(b-average(b))/(32*k*k),f[0]/(k*k),3*(f[2]-average(f[2]))/(16*k*k)]
    correction=sy.factor(average(sum(poisson(a,poisson(na,h2))
                                    for a,na in zip([b,f[0],f[2]],ns)))/4)
    target=(4*k*k*q0*q0+3*k*k*(qc*qc+qs*qs)+20*(pc*pc+ps*ps))/256
    assert sy.expand(correction-target)==0
    return dict(physical_pairs=3,free_hamiltonian=str(h2),correction_divided_by_hbar=str(correction),
                homogeneous_shear_coefficient='hbar*lambda^2*k^2/64',
                scope='Exact three-pair TT Galerkin source algebra; auxiliary constants removed; no full periodic Einstein solution')


def tensor_correction_tests():
    out=[]
    e0=np.array([[0,0,1],[0,0,0],[1,0,0]])/np.sqrt(2)
    diagonal=np.diag([1.,-1.,0.])
    symplectic=np.block([[np.zeros((3,3)),np.eye(3)],[-np.eye(3),np.zeros((3,3))]])
    def bracket(a,b):return a@symplectic@b-b@symplectic@a
    for k in [1,2,3,5]:
        n=6*k+1;z=2*np.pi*np.arange(n)/n
        def sources(state):
            q0,qc,qs,p0,pc,ps=state
            h=q0*e0+(qc*np.cos(k*z)+qs*np.sin(k*z))[:,None,None]*diagonal
            mom=p0*e0+(pc*np.cos(k*z)+ps*np.sin(k*z))[:,None,None]*diagonal
            dh=k*(-qc*np.sin(k*z)+qs*np.cos(k*z))[:,None,None]*diagonal
            ds=k*(-pc*np.sin(k*z)+ps*np.cos(k*z))[:,None,None]*diagonal
            b=np.sum(mom*mom,axis=(1,2))+np.sum(dh*dh,axis=(1,2))/4
            current=ds@h+mom@dh-dh@mom-h@ds
            f=-current[:,:,2]/2
            f[:,2]-=np.sum(mom*dh,axis=(1,2))/2
            return np.concatenate([b[:,None],f],axis=1)
        axes=np.eye(6);values=[sources(e) for e in axes]
        matrices=np.zeros((n,4,6,6))
        for i in range(6):
            matrices[:,:,i,i]=2*values[i]
            for j in range(i):
                cross=sources(axes[i]+axes[j])-values[i]-values[j]
                matrices[:,:,i,j]=cross;matrices[:,:,j,i]=cross
        wave=np.fft.fftfreq(n)*n
        multiplier=np.zeros(n);multiplier[1:]=1/wave[1:]**2
        solved=np.fft.ifft(np.fft.fft(matrices,axis=0)*multiplier[:,None,None,None],axis=0).real
        solved[:,0]/=8
        solved[:,3]*=.75
        h2=np.diag([0,k*k/2,k*k/2,2,2,2])
        correction=np.mean(np.sum(bracket(matrices,bracket(solved,h2)),axis=1),axis=0)/4
        expected=np.diag([k*k/32,3*k*k/128,3*k*k/128,0,5/32,5/32])
        error=la.norm(correction-expected)
        assert error<2e-11 and abs(correction[0,0]/2-k*k/64)<1e-12
        out.append(dict(wavenumber=k,grid_points=n,quadratic_hessian_error=error,
                        correction_hessian_diagonal=correction.diagonal().tolist(),
                        homogeneous_q_squared_coefficient=float(correction[0,0]/2),
                        hbar=1,scope='FFT inverse and canonical quadratic Hessians of actual restricted Einstein sources'))
    return out


def connection(y, sources, lam, hbar):
    exponent = lam/hbar * sum((t*s for t,s in zip(y,sources)),
                              np.zeros_like(sources[0]))
    t = la.expm(exponent)
    ti = la.expm(-exponent)
    a = [hbar*la.expm_frechet(exponent, lam*s/hbar, compute_expm=False) @ ti
         for s in sources]
    return t, a


def flatness_tests():
    out = []
    for d, m in [(2,2), (3,2), (4,3)]:
        sources = [hermitian(d) for _ in range(m)]
        y = RNG.normal(size=m)
        lam, hbar = .23, .8
        t, a = connection(y,sources,lam,hbar)
        step = 2e-5
        da = []
        for j in range(m):
            direction = np.eye(m)[j]*step
            ap = connection(y+direction,sources,lam,hbar)[1]
            am = connection(y-direction,sources,lam,hbar)[1]
            da.append([(ap[i]-am[i])/(2*step) for i in range(m)])
        residual = max(la.norm(hbar*(da[i][j]-da[j][i])-comm(a[i],a[j]))
                       for i in range(m) for j in range(m))
        naive = max(lam**2*la.norm(comm(si,sj)) for si in sources for sj in sources)
        assert residual < 2e-8 and naive > 1e-3
        # Differentiate the kernel numerically, independently of the Frechet connection.
        mat = RNG.normal(size=(m,m)); mat = mat@mat.T+np.eye(m)
        def kernel(z):
            return np.exp(-z@mat@z/(2*hbar))*connection(z,sources,lam,hbar)[0]
        psi = kernel(y)
        kres = []
        for j in range(m):
            direction = np.eye(m)[j]*step
            derivative = (kernel(y+direction)-kernel(y-direction))/(2*step)
            kres.append(la.norm(hbar*derivative+(mat@y)[j]*psi-a[j]@psi))
        assert max(kres) < 2e-8
        out.append(dict(physical_dimension=d,auxiliaries=m,flatness_residual=residual,
                        naive_curvature=naive,kernel_residual=max(kres)))
    return out


def integrate(sources, mat, lam, hbar, observables, order=18):
    """Normalized Gaussian integrals, including all noncommuting matrix factors."""
    m, d = len(sources), len(sources[0])
    vals, vecs = la.eigh(mat)
    transform = (vecs*np.sqrt(hbar/vals)) @ vecs.T
    nodes, weights = hermgauss(order)
    gram = np.zeros((d,d),complex)
    sums = {key:np.zeros((d,d),complex) for key in observables}
    for index in itertools.product(range(order),repeat=m):
        y = transform @ nodes[list(index)]
        weight = float(np.prod(weights[list(index)]))/np.pi**(m/2)
        exponent = lam/hbar * sum((v*s for v,s in zip(y,sources)),np.zeros((d,d),complex))
        t = la.expm(exponent)
        gram += weight*(t@t)
        for key, func in observables.items():
            sums[key] += weight*(t@func(y)@t)
    normalization = inverse_sqrt(gram)
    return gram, {key:normalization@v@normalization for key,v in sums.items()}


def response_tests():
    out = []
    for d, coupled in [(2,False),(3,True),(4,True)]:
        sources = [hermitian(d),hermitian(d)]
        mat = np.array([[1.3,.21 if coupled else 0],[.21 if coupled else 0,1.9]])
        inv = la.inv(mat); hbar=.7
        obs=hermitian(d); eye=np.eye(d)
        qc = -sum((inv[i,j]*comm(sources[i],comm(sources[j],obs))
                   for i in range(2) for j in range(2)),np.zeros((d,d),complex))/(4*hbar)
        gram2 = sum((inv[i,j]*sources[i]@sources[j] for i in range(2) for j in range(2)),
                    np.zeros((d,d),complex))/hbar
        mean1 = sum((inv[0,j]*sources[j] for j in range(2)),np.zeros((d,d),complex))
        mixed1 = sum((inv[0,j]*(sources[j]@obs+obs@sources[j])/2 for j in range(2)),
                     np.zeros((d,d),complex))
        second2 = sum((inv[0,i]*inv[1,j]*(sources[i]@sources[j]+sources[j]@sources[i])/2
                       for i in range(2) for j in range(2)),np.zeros((d,d),complex))
        errors=[]
        for lam in [.08,.04,.02]:
            gram, result = integrate(sources,mat,lam,hbar,
                  {'identity':lambda y:eye,'O':lambda y:obs,
                   'y0':lambda y:y[0]*eye,'y0O':lambda y:y[0]*obs,
                   'y0y1':lambda y:y[0]*y[1]*eye})
            assert la.norm(result['identity']-eye)<2e-12
            assert la.eigvalsh(gram)[0]>=1-1e-12
            err = dict(gram=la.norm(gram-eye-lam**2*gram2),
                       physical=la.norm(result['O']-obs-lam**2*qc),
                       mean=la.norm(result['y0']-lam*mean1),
                       mixed=la.norm(result['y0O']-lam*mixed1),
                       second=la.norm(result['y0y1']-hbar*inv[0,1]*eye/2-lam**2*second2))
            errors.append(err)
            out.append(dict(physical_dimension=d,coupled_covariance=coupled,lambda_value=lam,
                            gram_min_eigenvalue=float(la.eigvalsh(gram)[0]),errors=err))
        for key in errors[0]:
            expected=8 if key in ['mean','mixed'] else 16
            for a,b in zip(errors,errors[1:]):
                assert a[key]/b[key] > .85*expected, (d,key,a,b)
    return out


def quartic_tests():
    out=[]
    for d in [2,3]:
        h2=hermitian(d); h3=hermitian(d,.2); local4=hermitian(d,.15)
        t=hermitian(d); t=t@t
        v=hermitian(d); v=v@v
        a=7*t-v; b=t+v; f=hermitian(d)
        sources=[b,f]; ell=1.2; k=1.7; hbar=.8
        mat=np.diag([8*ell,k]); eye=np.eye(d)
        qquant=-(comm(b,comm(b,h2))/(8*ell)+comm(f,comm(f,h2))/k)/(4*hbar)
        target=local4-(a@b+b@a)/(16*ell)+2*f@f/k
        previous=None
        for lam in [.08,.04,.02]:
            def slow(y):
                return h2+lam*h3+lam**2*local4-lam*a*y[0]+(2*k*y[1]**2-hbar)*eye
            _, result=integrate(sources,mat,lam,hbar,
                        {'raw':slow,'counterterm':lambda y:-lam**2*qquant},order=20)
            predicted=h2+lam*h3+lam**2*(target+qquant)
            err=la.norm(result['raw']-predicted)
            corrected=la.norm(result['raw']+result['counterterm']-h2-lam*h3-lam**2*target)
            if previous is not None:
                assert previous/err>6, (previous,err)
            previous=err
            out.append(dict(physical_dimension=d,lambda_value=lam,raw_remainder=err,
                            counterterm_remainder=corrected,quantum_correction_norm=la.norm(qquant),
                            scope='Noncommuting matrix analogue of scalar and vector source ordering'))
    return out


def finite_spin_tests():
    out=[]
    pauli=[np.array([[0,1],[1,0]],complex),np.diag([1.,-1.])]
    # One symmetric two-level spin block of R cells for each auxiliary.
    for r in [2,3,5]:
        b=np.diag(np.sqrt(np.arange(1,r+1)*(1-(np.arange(1,r+1)-1)/r)),1)
        identity=np.eye(r+1)
        conditions=[np.kron(np.kron(b,identity),np.eye(2)),
                    np.kron(np.kron(identity,b),np.eye(2))]
        x=(np.kron(np.kron((b+b.T)/np.sqrt(2),identity),pauli[0])
           +np.kron(np.kron(identity,(b+b.T)/np.sqrt(2)),pauli[1]))
        original=sum((c.conj().T@c for c in conditions),np.zeros_like(x))
        eig0=la.eigvalsh(original); delta0=float(eig0[2])
        p=np.eye(len(x))[:,:2]
        for lam in [.1,.3]:
            t=la.expm(lam*x); ti=la.expm(-lam*x)
            dressed=[t@c@ti for c in conditions]
            h=sum((c.conj().T@c for c in dressed),np.zeros_like(x))
            spectrum=la.eigvalsh(h)
            embed=t@p@inverse_sqrt(p.conj().T@t@t@p)
            residual=max(la.norm(c@embed) for c in dressed)
            exact_bound=delta0/np.linalg.cond(t)**2
            norm_bound=delta0*np.exp(-4*abs(lam)*la.norm(x,2))
            assert np.sum(abs(spectrum)<1e-10)==2
            assert residual<1e-11 and la.norm(embed.conj().T@embed-np.eye(2))<1e-11
            assert spectrum[2]>=exact_bound-1e-11 and exact_bound>=norm_bound-1e-11
            out.append(dict(block_size=r,lambda_value=lam,dimension=len(x),kernel_dimension=2,
                            residual=residual,gap=float(spectrum[2]),condition_bound=exact_bound,
                            norm_bound=norm_bound))
    return out


def oscillator_matrix(nq,ny,lam,omega,mu,hbar,large):
    """Galerkin compression of the infinite polynomial, with extra output rows.

    Form q^4 before compressing. Multiplying already truncated q^2 would
    omit top-sector outputs and produce a different boundary Hamiltonian.
    """
    ext=nq+5
    aq=sp.diags(np.sqrt(np.arange(1,ext)),1,shape=(ext,ext),format='csr')
    freq=np.sqrt(omega**2+2*hbar*lam**2/mu)
    q=np.sqrt(hbar/(2*freq))*(aq+aq.T)
    p=1j*np.sqrt(hbar*freq/2)*(aq.T-aq)
    q2=(q@q)[:nq,:nq].tocsr()
    q4=(q@q@q@q)[:nq,:nq].tocsr()
    p2=(p@p)[:nq,:nq].tocsr()
    ay=sp.diags(np.sqrt(np.arange(1,ny)),1,shape=(ny,ny),format='csr')
    fast=(hbar*mu*sp.kron(sp.eye(nq),sp.diags(np.arange(ny)))
          -lam*np.sqrt(hbar*mu/2)*sp.kron(q2,ay+ay.T)
          +lam**2/2*sp.kron(q4,sp.eye(ny)))
    slow=sp.kron((p2+omega**2*q2)/2,sp.eye(ny))
    return (large*fast+slow).tocsc(),freq


def oscillator_tests():
    out=[]
    lam,omega,mu,hbar=.3,.7,1.2,1.
    last=None
    for large in [2.,8.,32.,128.]:
        results=[]
        for nq,ny in [(46,36),(58,48)]:
            mat,freq=oscillator_matrix(nq,ny,lam,omega,mu,hbar,large)
            vals,vecs=eigsh(mat,k=3,sigma=-.1,which='LM',tol=2e-12)
            indices=np.argsort(vals);vals=vals[indices];vecs=vecs[:,indices]
            residual=float(la.norm(mat@vecs-vecs*vals))
            assert residual<2e-8
            results.append((vals,residual))
        vals=results[-1][0]
        cutoff_difference=float(np.max(abs(results[0][0]-vals)))
        target=hbar*freq*(np.arange(3)+.5)
        error=float(np.max(abs(vals-target)))
        assert np.all(vals<=target+2e-6)
        assert cutoff_difference<3e-5,cutoff_difference
        if last is not None:assert error<last
        last=error
        out.append(dict(Lambda=large,lambda_value=lam,omega=omega,mu=mu,hbar=hbar,
                        eigenvalues=vals.tolist(),limiting_eigenvalues=target.tolist(),
                        max_error=error,cutoff_difference=cutoff_difference,
                        residual=results[-1][1],physical_cutoff=58,auxiliary_cutoff=48,
                        scope='Variational Galerkin spectra; cutoff difference is not an interval bound'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report={'exact_identities':exact_identities(),'exact_tensor_correction':exact_tensor_correction(),
            'flatness':flatness_tests(),'tensor_quantum_correction':tensor_correction_tests(),
            'normalized_response':response_tests(),'quartic_response':quartic_tests(),
            'finite_spin_dressing':finite_spin_tests(),'oscillator_limit':oscillator_tests()}
    paths=['NONLINEAR_CONSTRAINT_DRESSING.md','scripts/nonlinear_constraint_dressing_audit.py',
           'HOLOMORPHIC_TENSOR_PHASE.md','data/holomorphic_tensor_phase_audit.json',
           'EINSTEIN_QUARTIC_CONSTRAINTS.md','data/einstein_quartic_constraints_audit.json',
           'REDUCED_TENSOR_HAMILTONIAN.md','TENSOR_VERTEX_SELECTION.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    report['scope']={
        'proved':'Bounded-source compatible Gaussian kernel, normalized response, finite-spin similarity bound; untruncated scalar-control spectral limit',
        'conditional':'Einstein scalar/vector source ordering through coupling order two with supplied physical regulator and Hamiltonian',
        'not_proved':['Einstein clock algebra','uniform nonlinear spin locality','physical cutoff removal',
                      'protected graviton masslessness','physical Newton constant','joint continuum limit','TOE'],
        'numerics':'Noncommuting matrix controls and oscillator Galerkin checks; no full nonlinear 3D tensor diagonalization'}
    destination=root/'data/nonlinear_constraint_dressing_audit.json'
    destination.write_text(json.dumps(report,indent=2)+'\n')
    count=sum(len(report[key]) for key in ['flatness','normalized_response','quartic_response',
                                          'finite_spin_dressing','oscillator_limit','tensor_quantum_correction'])
    print('PASS: exact identities and %d numerical cases'%count)
    print('Report:',destination)
    print('Scalar-control largest-Lambda eigenvalues:',report['oscillator_limit'][-1]['eigenvalues'])
    print('Their limiting values:',report['oscillator_limit'][-1]['limiting_eigenvalues'])


if __name__=='__main__':
    main()
