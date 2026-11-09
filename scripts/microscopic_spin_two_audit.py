#!/usr/bin/env python3
"""Four-spin microscopic tensor seed and exact one-excitation dynamics."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp

import sympy as sy


def tensor_basis():
    result=[sy.diag(1,-1,0)/sy.sqrt(2), sy.diag(1,1,-2)/sy.sqrt(6)]
    for i,j in [(0,1),(1,2),(2,0)]:
        e=sy.zeros(3); e[i,j]=e[j,i]=1/sy.sqrt(2); result.append(e)
    return result


def exact_cell():
    single=[sy.Matrix([[0,1],[1,0]])/2,sy.Matrix([[0,-sy.I],[sy.I,0]])/2,sy.diag(1,-1)/2]
    spins=[]
    for site in range(4):
        rows=[]
        for component in single:
            factors=[sy.eye(2) for _ in range(4)]; factors[site]=component
            rows.append(sy.kronecker_product(*factors))
        spins.append(rows)
    aa=[spins[0][i]+spins[1][i] for i in range(3)]
    bb=[spins[2][i]+spins[3][i] for i in range(3)]
    total=[aa[i]+bb[i] for i in range(3)]
    square=lambda vector: sum((v*v for v in vector),sy.zeros(16))
    casimir=square(total)
    ptt=square(aa)*square(bb)/4
    p0=ptt*(casimir-2*sy.eye(16))*(casimir-6*sy.eye(16))/12
    p2=casimir*(casimir-2*sy.eye(16))/24
    p1=ptt-p0-p2
    bad=sy.eye(16)-ptt
    projectors=[p0,p2,p1,bad]
    assert [sy.trace(p) for p in projectors]==[1,5,3,7]
    for i,j in itertools.product(range(4),repeat=2):
        assert projectors[i]*projectors[j]==(projectors[i] if i==j else sy.zeros(16))
    assert sum(projectors,sy.zeros(16))==sy.eye(16)
    for p in projectors:
        for j in total: assert p*j-j*p==sy.zeros(16)
    plus=sy.Matrix([1,0,0,0]); zero=sy.Matrix([0,1,1,0])/sy.sqrt(2); minus=sy.Matrix([0,0,0,1])
    omega=(sy.kronecker_product(plus,minus)-sy.kronecker_product(zero,zero)+sy.kronecker_product(minus,plus))/sy.sqrt(3)
    assert p0==omega*omega.conjugate().T
    basis=tensor_basis()
    quadrupoles=[sum((e[i,j]*(aa[i]*aa[j]+aa[j]*aa[i])/2 for i in range(3) for j in range(3)),sy.zeros(16)) for e in basis]
    states=sy.Matrix.hstack(*[sy.simplify(sy.sqrt(3)*q*omega) for q in quadrupoles])
    assert sy.simplify(states.conjugate().T*states)==sy.eye(5)
    assert sy.simplify(casimir*states-6*states)==sy.zeros(16,5)
    creation=[sy.simplify(sy.sqrt(3)*p2*q*p0) for q in quadrupoles]
    annih=[c.conjugate().T for c in creation]
    for i,j in itertools.product(range(5),repeat=2):
        assert sy.simplify(annih[i]*creation[j]-(p0 if i==j else sy.zeros(16)))==sy.zeros(16)
        assert sy.simplify(creation[j]*annih[i]-states[:,j]*states[:,i].conjugate().T)==sy.zeros(16)
    assert sy.simplify(sum((c*b for c,b in zip(creation,annih)),sy.zeros(16))-p2)==sy.zeros(16)
    x=[c+b for c,b in zip(creation,annih)]
    for op in creation+annih+x:
        assert sy.simplify(op*(p1+bad))==sy.zeros(16)
        assert sy.simplify((p1+bad)*op)==sy.zeros(16)
    numeric=lambda a:np.array(a,dtype=complex)
    return dict(omega=numeric(omega).ravel(), states=numeric(states), projectors=list(map(numeric,projectors)),
                annih=list(map(numeric,annih)), x=list(map(numeric,x)), basis=list(map(numeric,basis))),dict(
        microscopic_spins=4, hilbert_dimension=16, projector_ranks=[1,5,3,7],
        pair_triplet_projector=True, vacuum_is_unique_pair_triplet_singlet=True,
        quintet_casimir=6, quadrupole_vacuum_gram='I_5/3', transition_pair_identities=25,
        higher_sectors_annihilated=True,
        scope='Exact local spin matrices and engineered projector Hamiltonian; physical spatial spin interpretation remains an input.')


def bond_and_chain(cell):
    p0,n,p1,bad=cell['projectors']
    bs=cell['annih']
    mu,M,K,hop=.2,1.1,1.6,.07
    onsite=mu*n+M*p1+K*bad
    spectrum=la.eigvalsh(onsite)
    assert np.max(abs(spectrum-np.sort([0]+[mu]*5+[M]*3+[K]*7)))<1e-12
    onsite_gap_residual=onsite-mu*(np.eye(16)-p0)
    assert np.min(la.eigvalsh(onsite_gap_residual))>-1e-12
    bond=np.kron(n,np.eye(16))+np.kron(np.eye(16),n)
    for b in bs: bond-=np.kron(b.conj().T,b)+np.kron(b,b.conj().T)
    eigen=la.eigvalsh(bond)
    assert min(eigen)>-1e-12 and abs(max(eigen)-2)<1e-12
    assert np.max(np.min(abs(eigen[:,None]-np.array([0,1,2])[None,:]),axis=1))<1e-12
    # Full three-cell, twelve-spin microscopic Hilbert space (dimension 4096).
    def embed(op,site,dimension=16,cells=3):
        factors=[sp.eye(dimension,format='csr',dtype=complex) for _ in range(cells)]
        factors[site]=sp.csr_matrix(op)
        result=factors[0]
        for factor in factors[1:]:result=sp.kron(result,factor,format='csr')
        return result
    h=sum((embed(onsite,r) for r in range(3)),sp.csr_matrix((4096,4096),dtype=complex))
    annih=[[embed(b,r) for b in bs] for r in range(3)]
    edges=[(0,1),(1,2),(2,0)]
    for r,s in edges:
        for alpha in range(5):
            difference=annih[r][alpha]-annih[s][alpha]
            h+=hop*(difference.conj().T@difference)
    vacuum=np.kron(np.kron(cell['omega'],cell['omega']),cell['omega'])
    assert la.norm(h@vacuum)<1e-12
    columns=[]
    for r in range(3):
        for alpha in range(5):
            factors=[cell['omega']]*3; factors[r]=cell['states'][:,alpha]
            columns.append(np.kron(np.kron(factors[0],factors[1]),factors[2]))
    embedding=np.column_stack(columns)
    assert la.norm(embedding.conj().T@embedding-np.eye(15))<1e-12
    lap=3*np.eye(3)-np.ones((3,3))
    one=np.kron(mu*np.eye(3)+hop*lap,np.eye(5))
    intertwining=float(la.norm(h@embedding-embedding@one))
    assert intertwining<1e-12
    uniform_quintet=embedding@np.kron(np.ones(3)/np.sqrt(3),np.eye(5)[:,0])
    gap_eigenstate_error=float(la.norm(h@uniform_quintet-mu*uniform_quintet))
    assert gap_eigenstate_error<1e-12
    total_number=sum((embed(n,r) for r in range(3)),sp.csr_matrix((4096,4096),dtype=complex))
    commutator=h@total_number-total_number@h
    assert sp.linalg.norm(commutator)<1e-11
    for r in range(3):
        inactive=embed(p1+bad,r)
        assert sp.linalg.norm(h@inactive-inactive@h)<1e-11
    propagation=[]
    for tau in [.1,1.,3.]:
        direct=la.expm(-tau*(embedding.conj().T@(h@embedding)))
        expected=np.kron(la.expm(-tau*(mu*np.eye(3)+hop*lap)),np.eye(5))
        error=float(la.norm(direct-expected))
        assert error<1e-12
        propagation.append(dict(euclidean_time=tau,error=error))
    return dict(mu=mu,triplet_gap=M,inactive_gap=K,hopping=hop,
                local_spectrum=spectrum.tolist(), bond_dimension=256,
                bond_spectrum_multiplicities={str(x):int(np.sum(abs(eigen-x)<1e-10)) for x in [0,1,2]},
                chain_cells=3, microscopic_hilbert_dimension=4096, one_excitation_dimension=15,
                gap_lower_bound_from_positive_terms=mu, gap_saturating_eigenstate_residual=gap_eigenstate_error,
                full_space_intertwining_residual=intertwining,
                one_excitation_eigenvalues=la.eigvalsh(one).tolist(), propagation_checks=propagation)


def collective_commutators():
    rows=[]
    for sites in [2,3,4]:
        basis=list(itertools.product(range(6),repeat=sites))
        number=np.array([sum(x!=0 for x in state) for state in basis])
        dimension=6**sites
        def embed(op,site):
            factors=[sp.eye(6,format='csr') for _ in range(sites)];factors[site]=sp.csr_matrix(op)
            out=factors[0]
            for f in factors[1:]:out=sp.kron(out,f,format='csr')
            return out
        local=[]
        for alpha in [0,1]:
            b=np.zeros((6,6));b[0,alpha+1]=1
            local.append([embed(b,r) for r in range(sites)])
        for k,l,alpha,beta in [(0,0,0,0),(0,1,0,0),(0,0,0,1)]:
            bk=sum((np.exp(-2j*np.pi*k*r/sites)*local[alpha][r] for r in range(sites)),sp.csr_matrix((dimension,dimension)))/np.sqrt(sites)
            bl=sum((np.exp(-2j*np.pi*l*r/sites)*local[beta][r] for r in range(sites)),sp.csr_matrix((dimension,dimension)))/np.sqrt(sites)
            error=bk@bl.conj().T-bl.conj().T@bk-(sp.eye(dimension) if k==l and alpha==beta else sp.csr_matrix((dimension,dimension)))
            predicted=sp.csr_matrix((dimension,dimension),dtype=complex)
            for r in range(sites):
                op=np.zeros((6,6));op[beta+1,alpha+1]=1
                if alpha==beta:op+=np.diag([0]+[1]*5)
                predicted-=np.exp(2j*np.pi*(l-k)*r/sites)*embed(op,r)/sites
            assert sp.linalg.norm(error-predicted)<1e-12
            for cutoff in [0,1,2]:
                mask=np.flatnonzero(number<=cutoff)
                norm=float(la.svdvals(error[mask,:][:,mask].toarray())[0])
                bound=2*cutoff/sites
                assert norm<=bound+1e-12
                if k==l and alpha==beta:assert abs(norm-bound)<1e-12
                rows.append(dict(cells=sites,occupation_cutoff=cutoff,momenta=[k,l],components=[alpha,beta],
                                 commutator_error=norm,uniform_bound=bound))
    return dict(rows=rows,all_matrix_identity_checks_passed=True,
                scope='Compressed commutators computed in the full finite active tensor product before projection; no full-Hilbert-space canonical commutator is claimed.')


def strain_coupling(cell):
    d=sy.Matrix(sy.symbols('dx dy dz',real=True))
    coeff=[(d.T*e*d)[0] for e in tensor_basis()]
    assert sy.expand(sum(c*c for c in coeff)-sy.Rational(2,3)*(d.dot(d))**2)==0
    rng=np.random.default_rng(6007)
    maximum=0.
    for vector in rng.normal(size=(50,3)):
        coefficients=[float(np.real(vector@e@vector)) for e in cell['basis']]
        operator=sum((c*x for c,x in zip(coefficients,cell['x'])),np.zeros((16,16),dtype=complex))
        predicted=np.sqrt(2/3)*np.dot(vector,vector)
        spectrum=la.eigvalsh(operator)
        error=float(np.max(abs(spectrum-np.array([-predicted]+[0.]*14+[predicted]))))
        maximum=max(maximum,error)
        assert error<1e-12
    # A small complete cubic torus independently checks central <= edge energy.
    length=5; coords=list(itertools.product(range(length),repeat=3));lookup={x:i for i,x in enumerate(coords)}
    central=np.zeros((3*length**3,length**3));lap=np.zeros((length**3,length**3))
    for row,x in enumerate(coords):
        for axis in range(3):
            plus=list(x);minus=list(x);plus[axis]=(plus[axis]+1)%length;minus[axis]=(minus[axis]-1)%length
            i,j=lookup[tuple(plus)],lookup[tuple(minus)]
            central[3*row+axis,i]=.5;central[3*row+axis,j]=-.5
            edge=np.eye(length**3)[i]-np.eye(length**3)[row];lap+=np.outer(edge,edge)
    minimum=float(la.eigvalsh(lap-central.T@central)[0])
    assert minimum>-1e-11
    kappa,gamma=.25,.02
    margin=kappa/4-abs(gamma)*np.sqrt(2/3)
    assert margin>0
    # The y-directed gradient excites the microscopic tensor from the vacuum.
    vector=np.array([0.,1.,0.])
    operator=sum((float(np.real(vector@e@vector))*x for e,x in zip(cell['basis'],cell['x'])),np.zeros((16,16),dtype=complex))
    norm=float(la.norm(operator@cell['omega']))
    assert abs(norm-np.sqrt(2/3))<1e-12
    return dict(exact_traceless_norm_identity=True,random_spin_tensor_spectra=50,
                maximum_star_spectrum_error=maximum,central_difference_vertices=length**3,
                minimum_edge_minus_central_eigenvalue=minimum,kappa=kappa,gamma=gamma,
                coupled_field_lower_stiffness=margin,
                old_switch_blind_gradient_quintet_amplitude=norm,
                scope='Direct operator lower bound for the explicit coupling to the supplied large-spin scalar field. Tensor pole persistence and a positive spin-history representation are not claimed.')


def band_scaling():
    hop=.07;mass=.2; rows=[]
    rng=np.random.default_rng(6117)
    momentum=rng.normal(size=(100,3))
    for a in [.2,.1,.05,.025]:
        exact=mass+4*hop*np.sum(np.sin(a*momentum/2)**2,axis=1)/a**2
        limit=mass+hop*np.sum(momentum**2,axis=1)
        bound=hop*a*a*np.sum(momentum**4,axis=1)/12
        errors=abs(exact-limit)
        assert np.all(errors<=bound+1e-12)
        rows.append(dict(spacing=a,maximum_error=float(max(errors)),maximum_error_to_bound=float(max(errors/bound))))
    return dict(polarizations=5,gapless_dynamic_exponent=2,scaled_mass=mass,hopping=hop,rows=rows)


def main():
    root=Path(__file__).resolve().parents[1]
    cell,algebra=exact_cell()
    report=dict(local_algebra=algebra,microscopic_propagation=bond_and_chain(cell),
                collective_commutators=collective_commutators(),strain_coupling=strain_coupling(cell),
                continuum_band=band_scaling())
    sources=['MICROSCOPIC_SPIN_TWO_SEED.md','scripts/microscopic_spin_two_audit.py',
             'UnifiedTheory/Audit/KFCausalMicroscopicSpinTwo.lean','BOND_TENSOR_CONSTRAINTS.md',
             'scripts/bond_tensor_audit.py','ENTANGLED_ACOUSTIC_BOUNDS.md',
             'COLLECTIVE_WAVE_SPACETIME.md','PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256']={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in sources}
    report['scope']=('Explicit four-spin-half cells with a singlet vacuum and selected quintet; local microscopic hopping, '
                     'exact five-polarization quadratic band, dilute collective commutator bound, and a stable scalar-strain coupling. '
                     'No emergent gravitational constraints, two-helicity linear pole, universal stress coupling, '
                     'physical spacetime selection, or Einstein gravity is proved.')
    (root/'data/microscopic_spin_two_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
