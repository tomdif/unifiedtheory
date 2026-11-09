#!/usr/bin/env python3
"""Protected compact dynamics and the limits of its smooth wave expansion."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from compact_tensor_constraint_audit import stencil_symbols, lattice_matrix
from bond_tensor_audit import matrix_blocks


def laurent_stencil(matrix, variables):
    result=[]
    for i,j in itertools.product(range(matrix.rows),range(matrix.cols)):
        for term in sy.Add.make_args(sy.expand(matrix[i,j])):
            if term==0: continue
            powers=term.as_powers_dict();shift=tuple(int(powers.get(x,0)) for x in variables)
            value=sy.simplify(term/sy.prod(x**n for x,n in zip(variables,shift)))
            assert value.is_Integer
            result.append((i,j,shift,int(value)))
    return result


def local_dynamics():
    original,_=stencil_symbols();w,g,b,_,_=original
    f=[x-1 for x in w];pairs=[(0,1),(1,2),(2,0)]
    components={frozenset(pair):i+3 for i,pair in enumerate(pairs)}
    curl=sy.zeros(9,6)
    for a,beta,m,n in itertools.product(range(3),repeat=4):
        sign=sy.LeviCivita(a,m,n)
        if not sign: continue
        row=3*a+beta
        if n==beta:
            for j in range(3):
                curl[row,j]+=sign*f[m]/w[j]*(2*int(j==beta)-1)
        else:
            curl[row,components[frozenset((n,beta))]]+=sign*f[m]/w[beta]
    cross=sy.Matrix([[0,-f[2],f[1]],[f[2],0,-f[0]],[-f[1],f[0],0]])
    es=[sy.diag(*[int(j==i) for j in range(3)]) for i in range(3)]
    for i,j in pairs:
        e=sy.zeros(3);e[i,j]=e[j,i]=1;es.append(e)
    curvature=sy.Matrix.hstack(*[sy.Matrix(list(cross*e*cross.T)) for e in es])
    star=lambda a:a.T.subs({x:1/x for x in w},simultaneous=True)
    assert (curl*star(b)).applyfunc(sy.expand)==sy.zeros(9,1)
    assert (curvature*g).applyfunc(sy.expand)==sy.zeros(9,3)
    cs,rs=laurent_stencil(curl,w),laurent_stencil(curvature,w)
    length,prime=3,5
    cm=lattice_matrix(cs,9,6,length);rm=lattice_matrix(rs,9,6,length)
    gm=lattice_matrix(original[3],6,3,length);bm=lattice_matrix(original[4],1,6,length)
    assert np.max(abs(bm@cm.T))==0 and np.max(abs(rm@gm))==0
    pairing=cm@rm.T
    position=np.argwhere(pairing%prime)[0]
    ci,ri=map(int,position);u,v=cm[ci],rm[ri];phase=int(u@v)%prime
    assert phase!=0
    def entries(vector):
        return [dict(index=int(i),coefficient=int(vector[i])) for i in np.flatnonzero(vector)]
    incidence_c=[sum(j==i for _,j,_,_ in cs) for i in range(6)]
    incidence_r=[sum(j==i for _,j,_,_ in rs) for i in range(6)]
    report=dict(exact_curl_scalar_commutation=True,exact_curvature_vector_commutation=True,
                curl_maximum_support=max(sum(i==row for i,_,_,_ in cs) for row in range(9)),
                curvature_maximum_support=max(sum(i==row for i,_,_,_ in rs) for row in range(9)),
                curl_incidence=incidence_c,curvature_incidence=incidence_r,
                maximum_l1_offset=max(sum(abs(t) for t in shift) for _,_,shift,_ in cs+rs),
                logical_pair=dict(length=length,prime=prime,curl_row=ci,curvature_row=ri,
                                  symplectic_phase=phase,x_pattern=entries(u),z_pattern=entries(v)),
                curl_stencil=[dict(row=i,column=j,shift=list(s),coefficient=t) for i,j,s,t in cs],
                curvature_stencil=[dict(row=i,column=j,shift=list(s),coefficient=t) for i,j,s,t in rs])
    return (w,curl,curvature,phase),report


def weyl(prime):
    x=np.zeros((prime,prime),dtype=complex)
    for n in range(prime): x[(n+1)%prime,n]=1
    z=np.diag(np.exp(2j*np.pi*np.arange(prime)/prime))
    return x,z


def logical_pair_dynamics(phase):
    x,z=weyl(5);z=np.linalg.matrix_power(z,phase)
    h=-.7*(x+x.conj().T)/2-1.1*(z+z.conj().T)/2
    comm=float(la.norm(h@z-z@h,2))
    initial=np.eye(5)[:,0]
    evolved=la.expm(-.8j*h)@initial
    assert comm>.1 and abs(evolved[0])**2<.99
    return dict(representation_dimension=5,commutator_norm=comm,
                time=.8,initial_return_probability=float(abs(evolved[0])**2),
                spectrum=la.eigvalsh(h).tolist(),
                scope='Exact dynamics of one local logical Weyl pair inside the large tensor code, using its five-dimensional irreducible representation. This does not measure a lattice wave dispersion.')


def absolute_value_checks():
    p=5;x,z=weyl(p);i=np.eye(p)
    kron=lambda a,b,c:np.kron(np.kron(a,b),c)
    sx=kron(x,x,i);sz=kron(z,z.conj().T,i)
    x0=kron(i,i,x);z0=kron(i,i,z)
    re=lambda a:(a+a.conj().T)/2
    dynamic=-.3*re(x0)-.8*re(sx@x0)-.4*re(z0)-1.1*re(sz@z0)
    rng=np.random.default_rng(9501);rows=[]
    for alpha,beta in itertools.product(range(p),repeat=2):
        for case in range(3):
            f=rng.normal(size=p)+1j*rng.normal(size=p);f/=la.norm(f)
            psi=np.zeros((p,p,p),dtype=complex)
            for n in range(p): psi[(n+beta)%p,n,:]=np.exp(-2j*np.pi*alpha*n/p)*f/np.sqrt(p)
            psi=psi.ravel();magnitude=abs(psi).reshape((p,)*3)
            after=np.fft.ifftn(abs(np.fft.fftn(magnitude,norm='ortho')),norm='ortho').ravel()
            error=max(la.norm(sx@after-after),la.norm(sz@after-after),abs(la.norm(after)-1))
            before=float(np.vdot(psi,dynamic@psi).real)
            finish=float(np.vdot(after,dynamic@after).real)
            assert error<1e-11 and finish<=before+1e-11
            rows.append(dict(alpha=alpha,beta=beta,case=case,energy_drop=before-finish,constraint_error=float(error)))
    # Independent exact syndrome blocks for the same three-qudit example.
    sector_rows=[]
    e0=float(la.eigvalsh(-1.1*re(x)-1.5*re(z))[0])
    for alpha,beta in itertools.product(range(p),repeat=2):
        block=-re((.3+.8*np.exp(2j*np.pi*alpha/p))*x)-re((.4+1.1*np.exp(2j*np.pi*beta/p))*z)
        ground=float(la.eigvalsh(block)[0])
        assert ground>=e0-1e-11
        sector_rows.append(dict(alpha=alpha,beta=beta,excess_dynamic_energy=ground-e0))
    return dict(state_tests=len(rows),maximum_constraint_error=max(r['constraint_error'] for r in rows),
                minimum_energy_drop=min(r['energy_drop'] for r in rows),syndrome_blocks=sector_rows,
                scope='Two successive basis absolute-value operations on 75 charged states and independent spectra of all 25 syndrome blocks. The all-volume comparison is proved analytically in the note.')


def guarded_strong_coupling_checks():
    p=5;d=p+1;x,z=weyl(p);identity=np.eye(d);active=np.diag([1.]*p+[0.])
    xb=la.block_diag(x,1);zb=la.block_diag(z,1)
    kron=lambda a,b,c:np.kron(np.kron(a,b),c)
    re=lambda a:(a+a.conj().T)/2
    sx=kron(xb,xb,identity);sz=kron(zb,zb.conj().T,identity)
    p12=kron(active,active,identity);p3=kron(identity,identity,active);pall=kron(active,active,active)
    project=lambda u:sum((np.linalg.matrix_power(u,r) for r in range(p)),np.zeros_like(u))/p
    hx=p12@(np.eye(d**3)-project(sx));hz=p12@(np.eye(d**3)-project(sz))
    inactive=kron(identity-active,identity,identity)+kron(identity,identity-active,identity)+kron(identity,identity,identity-active)
    x0=kron(identity,identity,xb);z0=kron(identity,identity,zb)
    dynamic=-.3*p3@re(x0)-.8*pall@re(sx@x0)-.4*p3@re(z0)-1.1*pall@re(sz@z0)
    code=np.zeros((d**3,p),dtype=complex)
    for n,t in itertools.product(range(p),repeat=2):code[(n*d+n)*d+t,t]=1/np.sqrt(p)
    code_project=code@code.conj().T
    charged=pall-code_project;illegal=np.eye(d**3)-pall
    charged_basis=la.eigh(charged)[1][:,-(p**3-p):]
    illegal_basis=la.eigh(illegal)[1][:,-(d**3-p**3):]
    delta,penalty=.7,1.3;rows=[]
    for strength in [.1,1.,10.,100.]:
        ham=penalty*inactive+delta*(hx+hz)+strength*dynamic
        assert la.norm(ham@code_project-code_project@ham)<1e-9
        ground=float(la.eigvalsh(code.conj().T@ham@code)[0])
        ec=float(la.eigvalsh(charged_basis.conj().T@ham@charged_basis)[0])
        ei=float(la.eigvalsh(illegal_basis.conj().T@ham@illegal_basis)[0])
        assert ec>=ground+delta-1e-8 and ei>=ground+penalty-1e-8
        rows.append(dict(strength=strength,ground_energy=ground,
                         charged_energy_margin=ec-ground,inactive_energy_margin=ei-ground))
    return dict(matrix_dimension=d**3,full_four_spin_dimension=16**3,
                rows=rows,charge_bound=delta,inactive_bound=penalty,
                scope='Each local inactive label has eleven identical copies in the full four-spin model; this 216-state block represents every active/inactive pattern. This toy has independent check relations, so its charge lower bound is Delta; the periodic tensor code instead has 2 Delta.')


def derivative_obstruction():
    k=sy.Matrix(sy.symbols('kx ky kz',real=True));v0=sy.symbols('v0:6')
    matrix=lambda c:sy.Matrix([[c[0],c[3],c[5]],[c[3],c[1],c[4]],[c[5],c[4],c[2]]])
    u=matrix(v0);identity=sy.expand((k.T*u*k)[0]-(k.T*k)[0]*sy.trace(u))
    equations=sy.Poly(identity,*k).coeffs()
    a0,_=sy.linear_eq_to_matrix(equations,v0)
    assert a0.rank()==6
    constant_z=[]
    for component in u*k:constant_z.extend(sy.Poly(component,*k).coeffs())
    az,_=sy.linear_eq_to_matrix(constant_z,v0)
    assert az.rank()==6
    coefficients=sy.symbols('c0:18')
    linear=matrix([sum(coefficients[3*i+j]*k[j] for j in range(3)) for i in range(6)])
    eq=[]
    for component in linear*k:eq.extend(sy.Poly(sy.expand(component),*k).coeffs())
    a1,_=sy.linear_eq_to_matrix(eq,coefficients)
    assert a1.rank()==18
    return dict(constant_X_kernel_dimension=6-int(a0.rank()),
                constant_Z_kernel_dimension=6-int(az.rank()),
                linear_Z_kernel_dimension=18-int(a1.rank()),
                scope='Exact coefficient elimination for analytic continuum-neutral local patterns: X starts at one derivative and Z at two. Modular-only patterns or singular coefficient limits are outside this statement.')


def cubic_expansion_checks(symbols):
    w,curl,curvature,_=symbols
    cf=sy.lambdify(w,curl,'numpy');rf=sy.lambdify(w,curvature,'numpy')
    amp=np.diag([1.,1.,1.,np.sqrt(2),np.sqrt(2),np.sqrt(2)])
    offsets=np.array([[1,0,0],[0,1,0],[0,0,1],[.5,.5,0],[0,.5,.5],[.5,0,.5]])
    rng=np.random.default_rng(9534);rows=[]
    for case in range(48):
        direction=rng.normal(size=3);direction/=la.norm(direction)
        for radius in [.3,.15,.075,.0375]:
            k=radius*direction;v=2*np.sin(k/2);v2=float(v@v)
            _,_,_,_,_,_,_,tt=matrix_blocks(v);t=la.eigh(tt)[1][:,-2:]
            phase=np.diag(np.exp(1j*(offsets@k)))
            th=la.solve(amp,phase@t);tp=amp@phase@t
            cp=np.asarray(cf(*np.exp(1j*k)),dtype=complex)@tp
            rq=np.asarray(rf(*np.exp(1j*k)),dtype=complex)@th
            kinetic=cp.conj().T@cp/4;potential=rq.conj().T@rq
            error=max(la.norm(kinetic-v2*np.eye(2)),la.norm(potential-v2*v2*np.eye(2)))
            assert error<1e-10
            frequencies=np.sqrt(np.maximum(0,la.eigvals(kinetic@potential).real))
            assert np.max(abs(frequencies-v2**1.5))<1e-9
            repaired=np.sqrt(np.maximum(0,la.eigvals((kinetic/v2)@(potential/v2)).real))
            assert np.max(abs(repaired-np.sqrt(v2)))<1e-9
            rows.append(dict(case=case,radius=radius,maximum_symbol_error=float(error),
                             frequency_over_radius=float(np.mean(frequencies)/radius),
                             frequency_over_radius_cubed=float(np.mean(frequencies)/radius**3),
                             nonlocal_repair_frequency_over_radius=float(np.mean(repaired)/radius)))
    return dict(cases=len(rows),maximum_symbol_error=max(r['maximum_symbol_error'] for r in rows),rows=rows,
                scope='The formal unwrapped quadratic expansion gives cubic dispersion. This is not a theorem that the fixed five-state quantum model is gapless or has this continuum limit.')


def main():
    root=Path(__file__).resolve().parents[1]
    symbols,local=local_dynamics()
    report=dict(local_operators=local,logical_pair=logical_pair_dynamics(symbols[3]),
                sector_comparison=absolute_value_checks(),guarded_dynamics=guarded_strong_coupling_checks(),
                derivative_obstruction=derivative_obstruction(),cubic_expansion=cubic_expansion_checks(symbols))
    sources=['COMPACT_TENSOR_DYNAMICS.md','scripts/compact_tensor_dynamics_audit.py',
             'COMPACT_TENSOR_CONSTRAINTS.md','scripts/compact_tensor_constraint_audit.py',
             'BOND_TENSOR_CONSTRAINTS.md','scripts/bond_tensor_audit.py',
             'EINSTEIN_MODEL_DECISION.md','GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']='Exact nontrivial local dynamics in the compact constraint space with a protected low-energy sector, plus an obstruction to a regular linear-wave expansion with the fixed linear gauges. Einstein gravity and the nonlinear constraint completion remain unproved.'
    (root/'data/compact_tensor_dynamics_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
