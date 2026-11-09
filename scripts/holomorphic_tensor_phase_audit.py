#!/usr/bin/env python3
"""Finite-spin annihilation constraints and the selected tensor quantum phase."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import scipy.sparse.linalg as sla
import sympy as sy

from compact_tensor_constraint_audit import stencil_symbols, lattice_matrix


RNG=np.random.default_rng(9112685)


def exact_bounds():
    n,R=sy.symbols('n R',positive=True)
    assert sy.simplify((R**((n-1)/2)*sy.sqrt(sy.gamma(R-n+2)/sy.gamma(R+1)))**2
                       /(R**(n/2)*sy.sqrt(sy.gamma(R-n+1)/sy.gamma(R+1)))**2
                       -(1-(n-1)/R))==0
    rg=4+4*sy.sqrt(2);rb=24+12*sy.sqrt(2)
    bc=sy.expand(3*rg*rg+rb*rb)
    assert bc==1008+672*sy.sqrt(2)
    for value in range(4):
        assert value*(value-1)*(value-2)>=sy.Rational(value**3,4)-2
    # For n>=4, each factor (n-1),(n-2) is at least n/2.
    x,a,nu=sy.symbols('x a nu',positive=True)
    assert sy.expand(nu*x*x/8-a*x+2*a*a/nu-nu*(x-4*a/nu)**2/8)==0
    return dict(exact_spin_similarity_ratio=True,falling_number_coercivity=True,
                cubic_absorption_square=True,vector_row_l1=str(rg),scalar_row_l1=str(rb),
                constraint_incidence_bound=str(bc),microscopic_time_scale='R^(-2)')


def symbol_functions(symbols):
    w,g,b,_,_=symbols
    wgt=np.diag([1,1,1,math.sqrt(2),math.sqrt(2),math.sqrt(2)])
    gf=sy.lambdify(w,g,'numpy');bf=sy.lambdify(w,b,'numpy')
    def evaluate(k):
        values=np.exp(1j*np.array(k))
        G=wgt@np.array(gf(*values),complex)
        B=np.array(bf(*values),complex)@la.inv(wgt)
        C=np.vstack([G.conj().T,B])
        return G,B,C,C.conj().T@C
    return evaluate


def symbol_checks(symbols):
    evaluate=symbol_functions(symbols);rows=[]
    for L in [2,3,4,7]:
        worst=0.;zeros=0;least=float('inf')
        axis=2*np.pi*np.fft.fftfreq(L)
        for k in itertools.product(axis,repeat=3):
            G,B,C,K=evaluate(k)
            ell=float(np.sum(4*np.sin(np.array(k)/2)**2))
            e=la.eigvalsh(K)
            expected=np.sort([0,0,2*ell,2*ell,4*ell,2*ell*ell])
            worst=max(worst,float(np.max(abs(e-expected))))
            assert la.norm(B@G)<2e-13
            if ell<1e-20:
                assert la.norm(K)<1e-12;zeros+=6
            else:
                assert np.sum(abs(e)<1e-8)==2;zeros+=2
                least=min(least,float(e[2]))
        assert worst<1e-10 and zeros==2*(L**3-1)+6
        rows.append(dict(length=L,one_particle_dimension=6*L**3,kernel_dimension=zeros,
                         maximum_symbol_error=worst,positive_gap=least))
    _,_,_,gs,bs=symbols
    L=5;V=L**3
    weights=np.repeat([1,1,1,math.sqrt(2),math.sqrt(2),math.sqrt(2)],V)
    G=weights[:,None]*lattice_matrix(gs,6,3,L)
    B=lattice_matrix(bs,1,6,L)/weights[None,:]
    C=np.vstack([G.T,B]);row_l1=np.sum(abs(C),axis=1)
    incidence=np.sum((abs(C).T@row_l1).reshape(6,V),axis=0)
    bound=1008+672*math.sqrt(2)
    assert np.max(abs(incidence-bound))<2e-10
    return dict(cases=rows,real_stencil_incidence=float(incidence.max()),
                scope='All momenta of the stated carriers, including homogeneous and Brillouin-corner modes; real-space incidence is checked before small-box aliasing.')


def real_constraint(symbols,L):
    _,_,_,gs,bs=symbols;V=L**3
    weights=np.repeat([1,1,1,math.sqrt(2),math.sqrt(2),math.sqrt(2)],V)
    G=weights[:,None]*lattice_matrix(gs,6,3,L)
    B=lattice_matrix(bs,1,6,L)/weights[None,:]
    order=np.array([a*V+x for x in range(V) for a in range(6)])
    return np.vstack([G.T,B])[:,order]


def particle_basis(m,n):
    return list(itertools.combinations_with_replacement(range(m),n))


def spin_similarity(states,R,d,V):
    values=[]
    for state in states:
        counts=np.bincount(np.array(state,dtype=int)//d,minlength=V)
        assert max(counts)<=R
        logvalue=-sum(math.log1p(-j/R) for count in counts for j in range(count))/2
        values.append(math.exp(logvalue))
    return np.array(values)


def constrained_annihilation(C,states,lower,R,d):
    lookup={state:i for i,state in enumerate(lower)}
    rows=[];cols=[];values=[];width=len(lower)
    for col,state in enumerate(states):
        blocks=np.bincount(np.array(state,dtype=int)//d,minlength=C.shape[1]//d)
        for mode in set(state):
            target=list(state);target.remove(mode)
            amplitude=math.sqrt(state.count(mode)*(1-(blocks[mode//d]-1)/R))
            for mu in np.flatnonzero(abs(C[:,mode])>1e-14):
                rows.append(mu*width+lookup[tuple(target)]);cols.append(col)
                values.append(C[mu,mode]*amplitude)
    return sp.csr_matrix((values,(rows,cols)),shape=(C.shape[0]*width,len(states)))


def two_particle_embedding(T,states):
    logical=particle_basis(T.shape[1],2)
    ii=np.array([state[0] for state in states]);jj=np.array([state[1] for state in states])
    result=[]
    for a,b in logical:
        result.append((T[ii,a]*T[jj,b]+T[ii,b]*T[jj,a])/np.sqrt((1+(ii==jj))*(1+(a==b))))
    result=np.array(result).T
    assert la.norm(result.T@result-np.eye(len(logical)))<2e-12
    return result


def finite_spin_kernels(symbols):
    C=real_constraint(symbols,2);K=C.T@C
    eig,Tfull=la.eigh(K);T=Tfull[:,eig<1e-9];delta=float(eig[eig>1e-9][0])
    assert T.shape==(48,20)
    states=particle_basis(48,2);lower=particle_basis(48,1)
    canonical=two_particle_embedding(T,states);rows=[]
    for R in [2,4,16]:
        A=constrained_annihilation(C,states,lower,R,6)
        s=spin_similarity(states,R,6,8);embedded=s[:,None]*canonical
        residual=float(la.norm(A@embedded))
        assert residual<4e-12
        eigen=la.eigvalsh((A.T@A).toarray())
        nullity=int(np.sum(abs(eigen)<1e-8));gap=float(eigen[nullity])
        bound=delta/float(max(s)**2)
        assert nullity==210 and gap>=bound-3e-10
        rows.append(dict(length=2,blocks=8,R=R,total_particles=2,full_sector_dimension=len(states),
                         lower_output_dimension=A.shape[0],exact_kernel_dimension=nullity,
                         kernel_residual=residual,positive_gap=gap,similarity_gap_bound=bound,
                         generic_note_gap_bound=delta*math.exp(-1/(R-1))))
        print('two-particle spin kernel',R,nullity,gap,flush=True)
    # Three-particle tests retain every lower-sector output, while sampling
    # kernel vectors rather than claiming a full 19600-dimensional spectrum.
    states=particle_basis(48,3);lower=particle_basis(48,2)
    samples=[]
    for R in [3,8,32]:
        f=T@RNG.normal(size=20);f/=la.norm(f)
        canonical=np.array([math.sqrt(math.factorial(3)/math.prod(math.factorial(state.count(i)) for i in set(state)))
                            *math.prod(f[i] for i in state) for state in states])
        assert abs(la.norm(canonical)-1)<2e-13
        s=spin_similarity(states,R,6,8);state=s*canonical
        squared_norm=float(state@state)
        block_probability=np.sum(f.reshape(8,6)**2,axis=1)
        pair=float(np.sum(block_probability**2));triple=float(np.sum(block_probability**3))
        predicted_norm=1+3*(pair-triple)/(R-1)+triple*(R*R/((R-1)*(R-2))-1)
        assert abs(squared_norm-predicted_norm)<2e-13
        state/=la.norm(state)
        A=constrained_annihilation(C,states,lower,R,6)
        residual=float(la.norm(A@state))
        assert residual<2e-12
        samples.append(dict(R=R,total_particles=3,full_sector_dimension=len(states),
                            lower_output_dimension=A.shape[0],kernel_residual=residual,
                            coherent_similarity_squared_norm=squared_norm,
                            independent_block_probability_norm=predicted_norm,
                            distance_from_undeformed_vector=float(la.norm(state-canonical))))
    return dict(cases=rows,scope='Complete active-symmetric two-particle sectors of the actual three-dimensional stencil. The theorem supplies full microscopic sector selection; the exponentially larger unrestricted spin space is not diagonalized.'),dict(cases=samples)


def normal_mode_separation():
    rows=[];U,r,g,Gamma=1.,.25,.3,1.
    for k in [np.array([.1,.2,.3]),np.array([np.pi,0,0])]:
        ell=float(np.sum(4*np.sin(k/2)**2));a=r+g*ell
        physical=math.sqrt(U*a)
        for R in [4,16,64]:
            lam=np.array([2*ell,2*ell,4*ell,2*ell*ell]);fast=Gamma*R*R*lam
            frequency=np.sqrt((fast+U)*(fast+a))
            # Stable evaluation avoids subtracting two large quantities.
            zero_point=(fast*(U+a)+U*a)/(2*(frequency+fast))
            excess=float(np.max(abs(zero_point-(U+a)/4)))
            rows.append(dict(momentum=k.tolist(),R=R,physical_frequency=physical,
                             surviving_nonzero_momentum_pairs=2,minimum_normal_frequency=float(min(frequency)),
                             normal_zero_point_limit_error=excess))
        assert rows[-1]['normal_zero_point_limit_error']<rows[-3]['normal_zero_point_limit_error']/100
    return dict(cases=rows,scope='Exact canonical strong-penalty normal modes, used as a comparison for the proved finite-spin limit. The interacting model has no proved protected massless spectrum.')


def projected_tensor_cubic(root,symbols):
    evaluate=symbol_functions(symbols)
    table=json.loads((root/'data/collective_gravity_coupling_audit.json').read_text())['einstein_cubic_density']
    coefficients=[(row['powers'],float(sy.N(sy.sympify(row['coefficient'])))) for row in table['cubic_polynomial']]
    shape=[np.diag([1,-1,0])/np.sqrt(2),np.diag([1,1,-2])/np.sqrt(6)]
    for i,j in [(0,1),(0,2),(1,2)]:
        e=np.zeros((3,3));e[i,j]=e[j,i]=1/np.sqrt(2);shape.append(e)
    shape=np.array(shape);cart=[]
    for i in range(3):
        e=np.zeros((3,3));e[i,i]=1;cart.append(e)
    for i,j in [(0,1),(1,2),(2,0)]:
        e=np.zeros((3,3));e[i,j]=e[j,i]=1/np.sqrt(2);cart.append(e)
    cart=np.array(cart);rows=[]
    for L in [5,7,9]:
        field=RNG.normal(size=(L,L,L,6));ft=np.fft.fftn(field,axes=(0,1,2))
        axis=2*np.pi*np.fft.fftfreq(L)
        worst=0.
        for pos in itertools.product(range(L),repeat=3):
            k=np.array([axis[i] for i in pos])
            if np.max(abs(k))>2*np.pi/L+1e-10 or la.norm(k)<1e-10:
                ft[pos]=0;continue
            G,B,C,K=evaluate(k)
            P=np.eye(6)-G@la.solve(G.conj().T@G,G.conj().T)-B.conj().T@B/(B@B.conj().T)[0,0]
            ft[pos]=P@ft[pos]
            worst=max(worst,float(la.norm(C@ft[pos])))
        value=np.fft.ifftn(ft,axes=(0,1,2))
        assert np.max(abs(value.imag))<2e-14
        field=value.real;field/=la.norm(field.ravel())
        tensor=np.einsum('...a,aij->...ij',field,cart)
        h=np.einsum('...ij,aij->...a',tensor,shape)
        derivatives=[(np.roll(h,-1,axis=i)-np.roll(h,1,axis=i))/2 for i in range(3)]
        variables=np.concatenate([h]+derivatives,axis=-1)
        density=np.zeros((L,L,L))
        for powers,coefficient in coefficients:
            product=np.ones((L,L,L))*coefficient
            for a,power in enumerate(powers):
                if power:product*=variables[...,a]**power
            density+=product
        cubic=float(density.sum());matrix_element=math.sqrt(3)*cubic/2
        assert abs(matrix_element)>1e-8
        block_probability=np.sum(field*field,axis=-1)
        pair=float(np.sum(block_probability**2));triple=float(np.sum(block_probability**3))
        finite=[]
        for R in [3,8,32]:
            squared_norm=1+3*(pair-triple)/(R-1)+triple*(R*R/((R-1)*(R-2))-1)
            finite.append(dict(R=R,normalized_spin_kernel_matrix_element_per_chi=matrix_element/math.sqrt(squared_norm)))
        rows.append(dict(length=L,profile_norm=float(la.norm(field.ravel())),
                         constraint_fourier_residual_before_normalization=worst,
                         homogeneous_mode_removed=True,classical_cubic=cubic,
                         vacuum_to_three_particle_matrix_element_per_chi=matrix_element,
                         exact_finite_spin_matrix_elements=finite))
    cstar=3*float(sy.N(sy.sympify(table['exact_coefficient_l1'])))
    return dict(cases=rows,cubic_monomials=len(coefficients),uniform_incidence_bound=cstar,
                scope='Actual supplied tracefree cubic extension on normalized nonzero-momentum kernel profiles. Staggered lattice symmetry is not claimed to give exact nonlinear diffeomorphism covariance.')


def occupation_vectors(m,cutoff):
    states=[]
    for n in range(cutoff+1):
        for state in particle_basis(m,n):
            states.append(tuple(np.bincount(state,minlength=m)))
    return states


def finite_operators(m,d,R,cutoff):
    states=[state for state in occupation_vectors(m,cutoff)
            if R is None or max(sum(state[i:i+d]) for i in range(0,m,d))<=R]
    lookup={state:i for i,state in enumerate(states)};ann=[]
    for mode in range(m):
        row=[];col=[];val=[]
        for j,state in enumerate(states):
            if not state[mode]:continue
            target=list(state);target[mode]-=1
            number=sum(state[(mode//d)*d:(mode//d+1)*d])
            factor=1 if R is None else 1-(number-1)/R
            row.append(lookup[tuple(target)]);col.append(j);val.append(math.sqrt(state[mode]*factor))
        ann.append(sp.csr_matrix((val,(row,col)),shape=(len(states),)*2))
    return states,ann


def normal_cubic(ann,labels):
    result=sp.csr_matrix(ann[0].shape)
    for creation in itertools.product([0,1],repeat=3):
        factors=[ann[label].T for label,bit in zip(labels,creation) if bit]
        factors += [ann[label] for label,bit in zip(labels,creation) if not bit]
        result+=factors[0]@factors[1]@factors[2]
    return result/(2*math.sqrt(2))


def smallest(matrix,below):
    value,vector=sla.eigsh(matrix,k=1,sigma=below,which='LM',tol=2e-12,
                          v0=RNG.normal(size=matrix.shape[0]))
    vector=vector[:,0];value=float(value[0])
    residual=float(la.norm(matrix@vector-value*vector))
    assert residual<3e-8
    return value,vector,residual


def cutoff_enclosure(H,states,cutoff,K0,nu,blocks):
    chosen=np.flatnonzero(np.sum(states,axis=1)<=cutoff)
    other=np.flatnonzero(np.sum(states,axis=1)>cutoff)
    A=H[chosen][:,chosen].tocsc()
    upper,vector,residual=smallest(A,-K0*blocks-1)
    if not len(other):return upper,upper,vector,residual,chosen,0.
    coupling=H[other][:,chosen].tocsr()
    tail=nu*(cutoff+1)**3/(8*blocks**2)-K0*blocks
    assert tail>upper
    norm_squared=float(abs(coupling).sum(axis=0).max()*abs(coupling).sum(axis=1).max())
    schur=A-(coupling.T@coupling)/(tail-upper)
    below=-K0*blocks-norm_squared/(tail-upper)-1
    lower,_,residual2=smallest(schur.tocsc(),below)
    assert lower<=upper+2e-10
    return lower,upper,vector,max(residual,residual2),chosen,tail


def small_interacting_model():
    U,r,g,chi,nu,Gamma=1.,.4,.2,.004,.1,1.
    cstar=3.;a3=4*math.sqrt(3)*chi*cstar;b3=36*chi*cstar
    K0=2*nu+2*a3*a3/nu+b3
    cutoff=12
    # The exact projected comparison has two physical oscillators. Its
    # normal vacua contribute (U+r+g)/2; its local sextics compress to
    # nu*N(N-1)(N-2)/4. This is a two-flavor diagnostic, not a GR lattice.
    logical,aa=finite_operators(2,2,None,cutoff+3)
    Q=[(a+a.T)/math.sqrt(2) for a in aa];P=[(a-a.T)/math.sqrt(2) for a in aa]
    F=sp.eye(len(logical),format='csr')*((U+r+g)/2)
    for mode in range(2):F+=(r+2*g*mode)/2*(Q[mode]@Q[mode])-U/2*(P[mode]@P[mode])
    number=np.sum(logical,axis=1)
    F+=chi/math.sqrt(2)*normal_cubic(aa,[0,1,1])+sp.diags(nu*number*(number-1)*(number-2)/4)
    target_low,target_high,target_vector,target_residual,target_chosen,_=cutoff_enclosure(F,logical,cutoff,K0,nu,2)
    rows=[]
    for R in [4,8,16,32,64]:
        full_cutoff=min(cutoff+3,2*R)
        states,ann=finite_operators(4,2,R,full_cutoff)
        Q=[(a+a.T)/math.sqrt(2) for a in ann];P=[(a-a.T)/math.sqrt(2) for a in ann]
        slow=sp.csr_matrix((len(states),)*2)
        for mode in range(4):slow+=r/2*(Q[mode]@Q[mode])-U/2*(P[mode]@P[mode])
        for mode in range(2):
            diff=Q[mode]-Q[mode+2];slow+=g/2*(diff@diff)
        for x in range(2):
            number=np.sum(np.array(states)[:,2*x:2*x+2],axis=1)
            slow+=sp.diags(nu*number*(number-1)*(number-2))
            slow+=chi*normal_cubic(ann,[2*x,2*x+1,2*x+1])
        normal=[(ann[0]-ann[2])/math.sqrt(2),(ann[1]+ann[3])/math.sqrt(2)]
        D=sum((a.T@a for a in normal),sp.csr_matrix(slow.shape))
        H=(Gamma*R*R*D+slow).tocsr()
        lower,upper,state,residual,chosen,tail=cutoff_enclosure(H,states,cutoff,K0,nu,2)
        dark=float(state@(D[chosen][:,chosen]@state))
        rows.append(dict(R=R,total_occupation_cutoff=cutoff,retained_dimension=len(chosen),
                         full_output_dimension=len(states),ground_energy_lower_estimate=lower,
                         ground_energy_upper_estimate=upper,cutoff_interval_width=max(0.,upper-lower),
                         analytical_complement_lower_bound=tail,slow_target_energy=target_high,
                         distance_from_target_energy=abs(upper-target_high),
                         constraint_energy=dark,eigensolver_residual=residual,
                         full_two_block_space_retained=bool(2*R<=cutoff)))
        print('nonlinear phase',R,upper,'target',target_high,'cutoff width',upper-lower,flush=True)
    assert rows[-1]['distance_from_target_energy']<rows[0]['distance_from_target_energy']/8
    assert rows[-1]['constraint_energy']<rows[0]['constraint_energy']/100
    assert max(row['cutoff_interval_width'] for row in rows)<2e-7
    return dict(cases=rows,target_energy_lower_estimate=target_low,target_energy_upper_estimate=target_high,
                target_eigensolver_residual=target_residual,chi=chi,nu=nu,uniform_coercivity_constant=K0,
                scope='Two blocks with two excitation flavors and two retained canonical modes. The R=4 case retains its entire collective Hilbert space. Other cases use all output rows through cutoff+3 and a Schur lower bound from uniform number coercivity. Floating-point eigenvalues are diagnostics, not interval-arithmetic certificates. This is not a full three-dimensional interacting gravity spectrum.')


def main():
    root=Path(__file__).resolve().parents[1]
    symbols,exact_stencil=stencil_symbols()
    report=dict(exact_bounds=exact_bounds(),exact_stencil=exact_stencil,symbols=symbol_checks(symbols))
    report['finite_spin_kernels'],report['three_particle_kernels']=finite_spin_kernels(symbols)
    report['normal_mode_separation']=normal_mode_separation()
    report['projected_tensor_cubic']=projected_tensor_cubic(root,symbols)
    report['small_interacting_model']=small_interacting_model()
    sources=['HOLOMORPHIC_TENSOR_PHASE.md','scripts/holomorphic_tensor_phase_audit.py',
             'COMPACT_TENSOR_CONSTRAINTS.md','scripts/compact_tensor_constraint_audit.py',
             'TENSOR_VERTEX_SELECTION.md','data/tensor_vertex_selection_audit.json',
             'COLLECTIVE_GRAVITY_COUPLING.md','data/collective_gravity_coupling_audit.json',
             'SPIN_BLOCK_WAVE_PARENT.md','EINSTEIN_QUARTIC_CONSTRAINTS.md',
             'COMPACT_CONSTRAINT_NORMALIZER.md','PREPOTENTIAL_LATTICE_BRIDGE.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']=('An engineered local annihilation-constraint parent on finite spin blocks selects '
                     'two tensor polarizations per nonzero momentum. Exact kernel embeddings and number '
                     'bounds prove a fixed-volume quantum spectral and evolution limit, with a surviving '
                     'supplied normally ordered cubic under slow-clock scaling. Six homogeneous modes '
                     'are retained. Nonlinear Einstein constraints, the Newton quartic, protected '
                     'interacting masslessness, physical G, a joint continuum limit and TOE remain unproved.')
    target=root/'data/holomorphic_tensor_phase_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    counts={key:len(value['cases']) for key,value in report.items() if isinstance(value,dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target),cases=counts,total_cases=sum(counts.values()),scope=report['scope']),indent=2))


if __name__=='__main__':main()
