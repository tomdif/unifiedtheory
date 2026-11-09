#!/usr/bin/env python3
"""Exact compact tensor constraints and a separate linear wave benchmark."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from bond_tensor_audit import matrix_blocks


def stencil_symbols():
    w = sy.symbols('wx wy wz', nonzero=True)
    forward = [x-1 for x in w]
    backward = [1-1/x for x in w]
    lap = [w[i]+1/w[i]-2 for i in range(3)]
    g = sy.zeros(6, 3)
    for i in range(3):
        g[i, i] = 2*forward[i]
    pairs = [(0, 1), (1, 2), (2, 0)]
    for row, (i, j) in enumerate(pairs, 3):
        g[row, i] = forward[j]; g[row, j] = forward[i]
    b = sy.Matrix([[sum(lap[j] for j in range(3) if j != i)/w[i] for i in range(3)]
                   +[-2*backward[i]*backward[j] for i, j in pairs]])
    assert (b*g).applyfunc(sy.expand) == sy.zeros(1, 3)
    def extract(matrix):
        result = []
        for i, j in itertools.product(range(matrix.rows), range(matrix.cols)):
            for term in sy.Add.make_args(sy.expand(matrix[i, j])):
                if term == 0: continue
                powers = term.as_powers_dict()
                shift = tuple(int(powers.get(x, 0)) for x in w)
                coefficient = sy.simplify(term/sy.prod(x**power for x, power in zip(w, shift)))
                assert coefficient.is_Integer
                result.append((i, j, shift, int(coefficient)))
        return result
    gs, bs = extract(g), extract(b)
    # A column of G is an X check; a row of B is a Z check.
    x_support = [sum(j == direction for _, j, _, _ in gs) for direction in range(3)]
    z_support = len(bs)
    incidence = [sum(i == component for i, _, _, _ in gs)
                 +sum(j == component for _, j, _, _ in bs) for component in range(6)]
    assert x_support == [6, 6, 6] and z_support == 27
    assert max(incidence) == 8
    return (w, g, b, gs, bs), dict(
        exact_integer_BG_zero=True, x_check_supports=x_support, z_check_support=z_support,
        checks_per_tensor_component=incidence,
        maximum_stencil_l1_offset=max(sum(abs(x) for x in shift) for _, _, shift, _ in gs+bs),
        x_stencil=[dict(row=i,column=j,shift=list(s),coefficient=v) for i,j,s,v in gs],
        z_stencil=[dict(row=i,column=j,shift=list(s),coefficient=v) for i,j,s,v in bs])


def lattice_matrix(stencil, output_components, input_components, length):
    sites = list(itertools.product(range(length), repeat=3))
    lookup = {x:i for i,x in enumerate(sites)}; volume=len(sites)
    matrix = np.zeros((output_components*volume,input_components*volume), dtype=np.int64)
    for x in sites:
        for out, inp, shift, coefficient in stencil:
            y=tuple((x[i]+shift[i]) % length for i in range(3))
            matrix[out*volume+lookup[x],inp*volume+lookup[y]] += coefficient
    return matrix


def rank_mod(matrix, prime):
    a=matrix.copy() % prime; row=0
    for col in range(a.shape[1]):
        candidates=np.flatnonzero(a[row:,col])
        if not len(candidates): continue
        pivot=row+int(candidates[0]); a[[row,pivot]]=a[[pivot,row]]
        a[row]=(a[row]*pow(int(a[row,col]),-1,prime)) % prime
        below=np.flatnonzero(a[row+1:,col])+row+1
        if len(below):
            a[below]=(a[below]-a[below,col,None]*a[row]) % prime
        row+=1
        if row == a.shape[0]: break
    return row


def finite_field_checks(symbols):
    _,_,_,gs,bs=symbols;rows=[]
    cases=[(3,2),(3,4),(5,2),(5,3),(5,4),(7,2),(7,3),(7,4),(3,3)]
    matrices={}
    for prime,length in cases:
        if length not in matrices:
            g=lattice_matrix(gs,6,3,length);b=lattice_matrix(bs,1,6,length)
            assert np.max(abs(b@g)) == 0
            matrices[length]=(g,b)
        g,b=matrices[length];volume=length**3
        assert np.max(abs(b.T@np.ones(volume,dtype=np.int64))) == 0
        for direction in range(3):
            constant=np.zeros(3*volume,dtype=np.int64)
            constant[direction*volume:(direction+1)*volume]=1
            assert np.max(abs(g@constant)) == 0
        rg,rb=rank_mod(g,prime),rank_mod(b,prime)
        encoded=6*volume-rg-rb
        pair=np.zeros((volume,1),dtype=np.int64);pair[0]=1;pair[1]=-1
        augmented_rank=rank_mod(np.column_stack((b,pair)),prime)
        if length % prime:
            assert rg == 3*(volume-1) and rb == volume-1
            assert encoded == 2*volume+4
            assert augmented_rank == rb
        else:
            assert (prime,length,rg,rb,encoded)==(3,3,75,23,64)
            assert augmented_rank == rb+1
        rows.append(dict(prime=prime,length=length,vertices=volume,qudits=6*volume,
                         x_rank=rg,z_rank=rb,encoded_qudits=encoded,
                         coprime_fourier_hypothesis=bool(length % prime),
                         adjacent_scalar_pair_allowed=bool(augmented_rank == rb)))
    return dict(rows=rows,scope='Exact integer stencil composition and exact modular ranks, without constructing the exponentially large many-spin Hilbert space. Encoded qudits are degenerate states, not propagating graviton modes.')


def spin_embedding():
    # The total-spin-two quintet of four spin halves is the symmetric Dicke space.
    w=sy.zeros(16,5)
    for bitstring in range(16):
        occupation=bin(bitstring).count('1')
        w[bitstring,occupation]=1/sy.sqrt(math.comb(4,occupation))
    assert w.T*w == sy.eye(5)
    assert (w*w.T)**2 == w*w.T
    pauli=[sy.Matrix([[0,1],[1,0]]),sy.Matrix([[0,-sy.I],[sy.I,0]]),sy.diag(1,-1)]
    total=[]
    for axis in pauli:
        spin=sy.zeros(16)
        for site in range(4):
            spin+=sy.kronecker_product(*[axis/2 if j==site else sy.eye(2) for j in range(4)])
        total.append(spin)
    casimir=sum((s*s for s in total),sy.zeros(16))
    assert casimir*w == 6*w
    assert casimir*(casimir-2*sy.eye(16))/24 == w*w.T
    x=sy.zeros(5)
    for n in range(5): x[(n+1)%5,n]=1
    omega=sy.symbols('omega')
    z=sy.diag(*[omega**n for n in range(5)])
    cyclotomic=sum(omega**n for n in range(5))
    reduce=lambda v: sy.rem(sy.expand(v),cyclotomic,omega)
    assert (z*x-omega*x*z).applyfunc(reduce) == sy.zeros(5)
    assert x**5 == sy.eye(5)
    assert (z**5-sy.eye(5)).applyfunc(reduce) == sy.zeros(5)
    ww=np.array(w,dtype=float);pp=ww@ww.T;eye=np.eye(16)
    xx=ww@np.array(x,dtype=complex)@ww.T+(eye-pp)
    zz=ww@np.diag(np.exp(2j*np.pi*np.arange(5)/5))@ww.T+(eye-pp)
    sx=np.kron(xx,xx);sz=np.kron(zz,zz.conj().T);guard=np.kron(pp,pp)
    projector=lambda u: sum((np.linalg.matrix_power(u,r) for r in range(5)),np.zeros_like(u))/5
    hx=guard@(np.eye(256)-projector(sx));hz=guard@(np.eye(256)-projector(sz))
    guarded_error=float(la.norm(hx@hz-hz@hx,2))
    unguarded_error=float(la.norm(sx@sz-sz@sx,2))
    assert guarded_error < 1e-11 and unguarded_error > 1
    assert la.norm(hx@hx-hx) < 1e-11 and la.norm(hz@hz-hz) < 1e-11
    penalty,delta=1.7,.4
    ham=penalty*(np.kron(eye-pp,eye)+np.kron(eye,eye-pp))+delta*(hx+hz)
    eigen=la.eigvalsh(ham)
    expected=np.r_[np.zeros(1),np.full(8,delta),np.full(16,2*delta),
                   np.full(110,penalty),np.full(121,2*penalty)]
    spectrum_error=float(np.max(abs(eigen-expected)))
    assert spectrum_error < 1e-11
    return dict(exact_dicke_isometry=True,exact_spin_two_projector=True,exact_quintet_weyl_algebra=True,
                two_cell_dimension=256,guarded_check_commutator_norm=guarded_error,
                unguarded_extension_commutator_norm=unguarded_error,
                guarded_parent_spectrum_error=spectrum_error,
                spectrum=[dict(energy=e,multiplicity=n) for e,n in [(0,1),(delta,8),(2*delta,16),(penalty,110),(2*penalty,121)]],
                scope='Exact quintet embedding plus a full 256-state guarded-parent check. Guarding is necessary: identity extensions of Weyl operators do not preserve cancellations in partially inactive spin sectors.')


def lattice_wave_benchmark(symbols):
    w,g,b,_,_=symbols
    gfn=sy.lambdify(w,g,'numpy');bfn=sy.lambdify(w,b,'numpy')
    amplitude=np.diag([1.,1.,1.,np.sqrt(2),np.sqrt(2),np.sqrt(2)])
    inverse=la.inv(amplitude)
    offsets=np.array([[1,0,0],[0,1,0],[0,0,1],[.5,.5,0],[0,.5,.5],[.5,0,.5]])
    rows=[]
    for length in [3,4,5,8]:
        frequencies=2*np.pi*np.fft.fftfreq(length)
        residuals=[];ranks=[];physical=[];zero=0
        for k in itertools.product(frequencies,repeat=3):
            k=np.array(k);v=2*np.sin(k/2)
            if la.norm(v)<1e-12:
                zero+=1;continue
            kinetic,potential,div,scalar,_,_,_,tt=matrix_blocks(v)
            phases=np.diag(np.exp(1j*(offsets@k)))
            gp=np.asarray(gfn(*np.exp(1j*k)),dtype=complex)
            bp=np.asarray(bfn(*np.exp(1j*k)),dtype=complex)
            vector_phase=np.diag(np.exp(1j*k/2))
            predicted_g=inverse@phases@(2j*div.T)@vector_phase.conj().T
            predicted_b=scalar[None,:]@phases.conj().T@amplitude
            residue=max(la.norm(gp-predicted_g),la.norm(bp-predicted_b),la.norm(bp@gp))
            assert residue < 1e-10
            constraints=np.zeros((4,12),dtype=complex)
            constraints[:3,6:]=gp.conj().T;constraints[3,:6]=bp[0]
            rank=np.linalg.matrix_rank(constraints,tol=1e-10)
            assert rank==4
            _,vectors=la.eigh(tt);t=vectors[:,-2:]
            th=inverse@phases@t;tp=amplitude@phases@t
            kr=inverse@phases@kinetic@phases.conj().T@inverse
            vr=amplitude@phases@potential@phases.conj().T@amplitude
            assert la.norm(bp@th)<1e-10 and la.norm(gp.conj().T@tp)<1e-10
            assert la.norm(th.conj().T@tp-np.eye(2))<1e-10
            error=max(la.norm(tp.conj().T@kr@tp-np.eye(2)),
                      la.norm(th.conj().T@vr@th-np.dot(v,v)*np.eye(2)))
            assert error<1e-10
            residuals.append(float(residue));physical.append(float(error));ranks.append(rank)
        assert zero==1
        rows.append(dict(length=length,nonzero_momenta=len(ranks),zero_corners=zero,
                         maximum_staggered_symbol_error=max(residuals),
                         maximum_reduced_wave_error=max(physical),constraint_rank=4))
    return dict(rows=rows,scope='Separate continuous canonical Fierz-Pauli benchmark with the same stencils. Its nonzero-momentum quotient has two positive waves. No dynamical Hamiltonian on the finite-qudit code is derived, and homogeneous metric modes are excluded from the positive wave statement.')


def wave_stencil_locality():
    z=sy.symbols('zx zy zz',nonzero=True)
    v=sy.Matrix([(x-1/x)/sy.I for x in z]);v2=(v.T*v)[0]
    es=[sy.diag(*[int(j==i) for j in range(3)]) for i in range(3)]
    for i,j in [(0,1),(1,2),(2,0)]:
        e=sy.zeros(3);e[i,j]=e[j,i]=1;es.append(e)
    trace=sy.Matrix([sy.trace(e) for e in es])
    div=sy.Matrix.hstack(*[e*v for e in es])
    second=sy.Matrix([(v.T*e*v)[0] for e in es])
    gram=sy.diag(1,1,1,2,2,2)
    vp=v2*gram-v2*trace*trace.T-2*div.T*div+trace*second.T+second*trace.T
    kp=sy.diag(1,1,1,sy.Rational(1,2),sy.Rational(1,2),sy.Rational(1,2))-trace*trace.T/2
    phase=sy.diag(z[0]**2,z[1]**2,z[2]**2,z[0]*z[1],z[1]*z[2],z[2]*z[0])
    rows=[]
    for name,operator in [('kinetic',kp),('potential',vp)]:
        raw=phase*operator*phase.inv();offsets=[];terms=0
        for entry in raw:
            for term in sy.Add.make_args(sy.expand(entry)):
                if term==0: continue
                powers=term.as_powers_dict();exponents=[int(powers.get(x,0)) for x in z]
                assert all(n%2==0 for n in exponents)
                coefficient=sy.simplify(term/sy.prod(x**n for x,n in zip(z,exponents)))
                assert coefficient.is_Rational
                offsets.append(sum(abs(n//2) for n in exponents));terms+=1
        rows.append(dict(operator=name,laurent_terms=terms,maximum_integer_l1_offset=max(offsets)))
    return dict(rows=rows,integer_translation_powers_only=True,
                scope='Exact finite-range certificates for the separate continuous canonical benchmark; these energy forms are not added to the compact spin parent.')


def main():
    root=Path(__file__).resolve().parents[1]
    symbols,stencil=stencil_symbols()
    report=dict(stencils=stencil,finite_fields=finite_field_checks(symbols),
                spin_embedding=spin_embedding(),wave_benchmark=lattice_wave_benchmark(symbols),
                wave_stencil_locality=wave_stencil_locality())
    sources=['COMPACT_TENSOR_CONSTRAINTS.md','scripts/compact_tensor_constraint_audit.py',
             'EINSTEIN_MODEL_DECISION.md','SPIN_CLOCK_BRACKET.md','BOND_TENSOR_CONSTRAINTS.md',
             'scripts/bond_tensor_audit.py','MICROSCOPIC_SPIN_TWO_SEED.md','GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']='A newly engineered local finite-spin constraint parent with a uniform excitation-gap lower bound, and a separate continuous linear-wave benchmark. No propagating modes of the compact parent, nonlinear clock algebra, gravitational phase, or TOE are proved.'
    (root/'data/compact_tensor_constraint_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__': main()
