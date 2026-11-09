#!/usr/bin/env python3
"""Collective interaction scaling and conditional Einstein vertex lift.

This does not construct gravitational constraints or select an Einstein phase.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
from scipy.special import gammaln
import sympy as sy

from spin_block_wave_parent_audit import (
    collective, embed_local, lowest, maximum, microscopic, occupations, onsite)


D = 6
RNG = np.random.default_rng(20260912)


def ground(matrix):
    if matrix.shape[0] < 5:
        e, v = la.eigh(matrix.toarray())
        return float(e[0]), v[:, 0]
    e, v, _ = lowest(matrix)
    return float(e[0]), v[:, 0]


def point_maps():
    rows = []
    for d in [1, 2, 3, 6]:
        q = sy.symbols('q:'+str(d))
        monomials = [q[j]*q[k] for j in range(d) for k in range(j, d)]
        coefficients = sy.symbols('c:'+str(d*len(monomials)))
        f = sy.Matrix([sum(coefficients[i*len(monomials)+j]*m for j,m in enumerate(monomials))
                       for i in range(d)])
        symmetric = f.jacobian(q)+f.jacobian(q).T
        equations = [sy.expand(symmetric[i,j]).coeff(q[k])
                     for i in range(d) for j in range(i,d) for k in range(d)]
        matrix, _ = sy.linear_eq_to_matrix(equations, coefficients)
        rank = matrix.rank()
        assert rank == len(coefficients)
        rows.append(dict(coordinates=d, quadratic_map_coefficients=len(coefficients),
                         kinetic_matching_rank=rank, kernel_dimension=0))
    q,p,w,c = sy.symbols('q p w c', nonzero=True, real=True)
    bracket = lambda f,g: sy.diff(f,q)*sy.diff(g,p)-sy.diff(f,p)*sy.diff(g,q)
    h2=(p*p+w*w*q*q)/2
    generator=c*q*q*p/w**2+2*c*p**3/(3*w**4)
    h3=sy.expand(bracket(h2,generator))
    h4=sy.expand(bracket(h3,generator)/2)
    assert sy.simplify(h3-c*q**3) == 0
    assert sy.simplify(h4-3*c*c*q**4/(2*w*w)-3*c*c*q*q*p*p/w**4) == 0
    # The inverse Lie map removes both terms through quartic order exactly.
    remainder=sy.expand(h4-bracket(h3,generator)+bracket(bracket(h2,generator),generator)/2)
    assert remainder == 0
    N,Q,r,beta,R,lam = sy.symbols('N Q r beta R lam', positive=True)
    # Scalar coefficients of the anticommutator are audited separately below.
    square=r/4*(Q-2*sy.sqrt(2)*beta*N/(r*sy.sqrt(R)))**2
    lhs=r*Q**2/2-sy.sqrt(2)*beta*N*Q/sy.sqrt(R)+lam*N*N/R
    rhs=r*Q**2/4+square+(lam-2*beta**2/r)*N*N/R
    assert sy.simplify(lhs-rhs) == 0
    U,g,s=sy.symbols('U g s',positive=True)
    b=(U/g)**sy.Rational(1,4);v=sy.sqrt(U*g)
    assert sy.simplify(U/b**2-v)==0 and sy.simplify(g*b**2-v)==0
    assert sy.simplify((s*g)*b**3/v-s*b)==0
    x=sy.symbols('x',real=True)
    assert sy.expand(1-x+x*x-sy.Rational(3,4)-(x-sy.Rational(1,2))**2)==0
    return dict(cases=rows, momentum_dependent_cubic_positive_control=dict(
        generator=str(generator), cubic=str(h3), induced_quartic=str(h4),
        inverse_Lie_cancellation=True,
        scope='A standalone oscillator illustrating coordinate-induced vertices; not the non-invariant compact Einstein profile.'),
        odd_parent_square_coefficients=True, physical_wave_and_cubic_normalization=True,
        higher_order_guard_coercivity_identity=True)


def thin_collective(R, cutoff=6):
    states=occupations(D,cutoff)
    lookup={v:i for i,v in enumerate(states)}
    qs=[]
    for a in range(D):
        rows,cols,values=[],[],[]
        for j,v in enumerate(states):
            if v[a]:
                w=list(v);w[a]-=1
                factor=1. if R is None else 1-(sum(v)-1)/R
                rows.append(lookup[tuple(w)]);cols.append(j)
                values.append(math.sqrt(v[a]*factor))
        b=sp.csr_matrix((values,(rows,cols)),shape=(len(states),)*2)
        qs.append((b+b.T)/math.sqrt(2))
    ns=np.array([sum(v) for v in states])
    return states,qs,sp.diags(ns),ns


def core_scaling():
    states,qa,n,ns=thin_collective(None)
    inputs=np.flatnonzero(ns<=3)
    beta=.3
    M=3
    error_constant=beta/2*((2*M+1)*math.sqrt(M+1)*M+(2*M-1)*math.sqrt(M)*(M-1))
    limit=-beta/math.sqrt(2)*(n@qa[0]+qa[0]@n)
    rows=[]
    for R in [8,16,32,64,128,256]:
        _,q,n,_=thin_collective(R)
        odd=-beta/math.sqrt(2*R)*(n@q[0]+q[0]@n)
        error=float(la.norm((math.sqrt(R)*odd-limit)[:,inputs].toarray(),2))
        cubic=odd+beta/math.sqrt(2*R)*q[0]
        one=states.index((1,0,0,0,0,0));two=states.index((2,0,0,0,0,0))
        extracted=-float(cubic[two,one])/math.sqrt(2*(1-1/R))
        assert abs(extracted-beta/math.sqrt(R)) < 2e-15
        assert error*R <= error_constant+1e-12
        rows.append(dict(R=R, input_cutoff=3, retained_output_cutoff=6,
                         rescaled_odd_full_output_error=error, R_times_error=R*error,
                         analytical_error_constant=error_constant,
                         extracted_normal_ordered_cubic=extracted,
                         expected_cubic=beta/math.sqrt(R)))
    return dict(cases=rows,scope='Full output of fixed occupation inputs; neither an operator-norm limit on the whole block nor a joint volume limit.')


def creation_scaling():
    rows=[]
    for p in [2,3,4]:
        for R in [8,16,32,64,128,256]:
            n=np.arange(R)
            raising=sp.diags(np.sqrt((n+1)*(R-n)),-1,shape=(R+1,R+1),format='csr')
            power=sp.eye(R+1,format='csr')
            for _ in range(p): power=raising@power
            actual=float(power[p,0])/R**(p-1)
            expected=math.sqrt(math.factorial(p))*R**(1-p/2)*math.sqrt(math.prod(1-j/R for j in range(p)))
            budget=p*math.prod((R-j)/R for j in range(1,p))
            assert abs(actual-expected)<3e-14 and budget<=p
            rows.append(dict(R=R, interaction_order=p, vacuum_to_p_amplitude=actual,
                             predicted_amplitude=expected, rescaled_amplitude=actual*R**(p/2-1),
                             asymptotic_rescaled_amplitude=math.sqrt(math.factorial(p)),
                             summed_per_cell_norm_budget=budget))
    return dict(cases=rows,scope='Exact p-cell raising interactions exhibit the sharp quadratic, cubic and quartic powers. The general fixed-order theorem is analytical.')


def higher_order_chart():
    rows=[]
    U,r,lam=1.,.25,.25
    c=min(U,r);alpha=c*(D-1)/2
    for R in [2,4,8,16,32,64,128,256]:
        candidates=[]
        for ell in range(R+1):
            ns=np.arange(ell,R+1,2,dtype=float)
            diag=(U+r)/4*(2*ns*(1-ns/R)+D-(D-1)*ns/R)+alpha*ns/R+lam*ns**3/R**2
            n=ns[:-1]
            off=(r-U)/(4*R)*np.sqrt((R-n)*(R-n-1)*(n-ell+2)*(n+ell+D))
            if len(ns)==1: energy=diag[0];vector=np.ones(1)
            else:
                e,v=la.eigh_tridiagonal(diag,off,select='i',select_range=(0,0))
                energy=e[0];vector=v[:,0]
            candidates.append((float(energy),ell,ns,vector))
        energy,ell,ns,vector=min(candidates,key=lambda v:v[0])
        assert ell==0
        if vector[0]<0:vector=-vector
        pairs=ns/2;t=1/3
        gaussian=(1-t*t)**1.5*np.sqrt((pairs+1)*(pairs+2)/2)*t**pairs
        distance=math.sqrt(max(0.,2-2*float(vector@gaussian)))
        mean=float((vector*vector)@ns)
        assert energy>=.75*c*mean+D*c/2-1e-10
        # Exact expansion in commuting microscopic excitation projectors.
        N=np.arange(R+1,dtype=float)
        cubic_projector_sum=N+3*N*(N-1)+N*(N-1)*(N-2)
        assert np.array_equal(cubic_projector_sum,N**3)
        per_cell_budget=alpha/R+lam*(3*R*R-3*R+1)/R**2
        assert per_cell_budget<=alpha+3*lam
        rows.append(dict(R=R,lambda_sextic=lam,alpha_number_counterterm=alpha,
                         angular_sectors_checked=R+1,ground_energy=energy,gaussian_energy=1.5,
                         mean_occupation=mean,full_gaussian_state_distance=distance,
                         guard_per_cell_norm_budget=per_cell_budget,
                         guard_normal_ordered_quartic_coefficient=3*lam/R**2))
    assert rows[-1]['full_gaussian_state_distance']<.04
    return dict(cases=rows,scope='A diagonal three-cell guard preserves the previous sector-selection proof and avoids a guard quartic at order 1/R. It does not establish selection after adding the Einstein cubic.')


def odd_micro_spectra():
    rows=[]
    for R,V,qcell in [(2,1,7),(3,1,7),(4,1,7),(2,2,7),(2,1,16)]:
        U,r,g,lam,beta,Delta,delta=1.,.25,.1,1.5,.3,.4,6.
        amax=r+g*(V-1);J0=(U+amax)/2+.05;J=J0+Delta
        qs,ps,ns,cs,t,inactive=microscopic(R,V,qcell)
        dim=t.shape[0];zero=sp.csr_matrix((dim,dim))
        wave=zero.copy();chart=zero.copy();odd=zero.copy()
        for x in range(V):
            for qa,pa in zip(qs[x],ps[x]): wave+=r/2*(qa@qa)-U/2*(pa@pa)
            chart+=lam/R*(ns[x]@ns[x])
            odd-=beta/math.sqrt(2*R)*(ns[x]@qs[x][0]+qs[x][0]@ns[x])
        if V==2:
            for a in range(D):
                diff=qs[0][a]-qs[1][a];wave+=g/2*(diff@diff)
        ctotal=sum(cs,zero.copy())
        h0=wave+chart+odd+J0/R*ctotal
        h=h0+Delta/R*ctotal+sp.diags(delta*inactive)
        offdiag=h0-sp.diags(h0.diagonal());offdiag.eliminate_zeros()
        assert offdiag.data.max()<=1e-13
        energy,vector=ground(h)
        hc=(t.T@h@t).tocsr();ec,_=ground(hc)
        projection=t@t.T
        leakage=float(la.norm(vector-projection@vector))
        assert abs(energy-ec)<2e-9 and leakage<1e-8
        assert maximum(h@t-t@hc)<3e-12
        lift=2*float(abs(h).sum(axis=1).max())+10
        excluded,_=ground(h+lift*projection)
        repair=J+1.5*(U+amax)
        assert excluded-energy>=min(Delta,delta-repair)-1e-8
        inactive_gap=None
        if qcell>7:
            inds=np.flatnonzero(inactive)
            e_inactive,_=ground(h.tocsr()[inds][:,inds])
            inactive_gap=e_inactive-energy
            assert inactive_gap>=delta-repair-1e-8
        number=sum(ns,zero.copy())
        c=min(U,r/2)
        assert lam-2*beta**2/r>=c*(D+1)/2
        coercivity=hc-c*(t.T@number@t)-D*c*V/2*sp.eye(hc.shape[0])
        coercivity_min,_=ground(coercivity)
        assert coercivity_min>=-1e-10
        parity=sp.diags((-1.)**number.diagonal().astype(int))
        parity_break=maximum(h@parity-parity@h)
        assert parity_break>.01
        rows.append(dict(R=R,blocks=V,cell_dimension=qcell,full_dimension=dim,beta=beta,
                         ground_energy=energy,collective_energy=ec,ground_leakage=leakage,
                         excluded_gap=excluded-energy,uniform_excluded_gap_bound=min(Delta,delta-repair),
                         inactive_gap=inactive_gap,coercivity_minimum=coercivity_min,
                         parity_commutator_maximum=parity_break))
        print('odd microscopic',R,V,qcell,'gap',excluded-energy,flush=True)
    return dict(cases=rows,scope='An internal-rotation-invariant scalar parity-breaking example preserves selection; its vertex is not asserted to be the Einstein tensor vertex.')


def odd_radial_matrix(R,ell,beta,U=1.,r=.25,lam=1.5):
    states=[(m,t) for t in range(ell,R+1,2) for m in range(R-t+1)]
    index={v:i for i,v in enumerate(states)}
    rows=[];cols=[];values=[]
    def edge(i,v,value):
        j=index[v];rows.extend([i,j]);cols.extend([j,i]);values.extend([value,value])
    for i,(m,t) in enumerate(states):
        N=m+t
        diag=(U+r)/4*(2*N*(1-N/R)+D-(D-1)*N/R)+lam*N*N/R
        rows.append(i);cols.append(i);values.append(diag)
        if N+2<=R:
            common=(r-U)/(4*R)*math.sqrt((R-N)*(R-N-1))
            edge(i,(m+2,t),common*math.sqrt((m+1)*(m+2)))
            edge(i,(m,t+2),common*math.sqrt((t-ell+2)*(t+ell+5)))
        if N+1<=R:
            edge(i,(m+1,t),-beta/(2*math.sqrt(R))*(2*N+1)*math.sqrt((m+1)*(1-N/R)))
    matrix=sp.csr_matrix((values,(rows,cols)),shape=(len(states),)*2)
    return states,matrix


def angular_multiplicity(ell):
    return math.comb(ell+4,4)-(math.comb(ell+2,4) if ell>=2 else 0)


def odd_radial_checks():
    cross=[];convergence=[]
    for R in [2,4]:
        _,q,p,n=collective(R)
        number=sp.diags(n);beta=.3
        h=onsite(q,p,n,R,1.,.25,1.5)-beta/math.sqrt(2*R)*(number@q[0]+q[0]@number)
        full=la.eigvalsh(h.toarray());predicted=[]
        for ell in range(R+1):
            _,matrix=odd_radial_matrix(R,ell,beta)
            predicted.extend(np.repeat(la.eigvalsh(matrix.toarray()),angular_multiplicity(ell)))
        error=float(np.max(np.abs(full-np.sort(predicted))))
        assert error<3e-12 and len(predicted)==math.comb(R+D,D)
        cross.append(dict(R=R,dimension=len(full),complete_spectrum_error=error))
    for beta in [.15,.3]:
        for R in [4,8,16,32,64]:
            candidates=[]
            for ell in range(R+1):
                states,matrix=odd_radial_matrix(R,ell,beta)
                energy,vector=ground(matrix)
                candidates.append((energy,ell,states,vector))
            energy,ell,states,vector=min(candidates,key=lambda v:v[0])
            assert ell==0
            if vector[0]<0: vector=-vector
            target=np.zeros(len(states));qmean=0.
            index={v:i for i,v in enumerate(states)}
            t=1/3
            for i,(m,nperp) in enumerate(states):
                if m%2==0:
                    j=m//2;k=nperp//2
                    weight=(gammaln(.5+j)-gammaln(.5)-gammaln(j+1)
                            +gammaln(2.5+k)-gammaln(2.5)-gammaln(k+1))/2
                    target[i]=(1-t*t)**1.5*math.exp(weight)*t**(j+k)
                if m+nperp<R:
                    j=index[(m+1,nperp)]
                    qmean+=math.sqrt(2*(m+1)*(1-(m+nperp)/R))*vector[i]*vector[j]
            distance=math.sqrt(max(0.,2-2*float(vector@target)))
            number=float(sum((m+n)*v*v for (m,n),v in zip(states,vector)))
            assert qmean>0
            convergence.append(dict(R=R,beta=beta,angular_sectors_checked=R+1,
                                    ground_angular_sector=ell,radial_dimension=len(states),ground_energy=energy,
                                    gaussian_energy=1.5,mean_total_occupation=number,
                                    mean_eta_coordinate=qmean,full_gaussian_state_distance=distance))
            print('odd radial',R,beta,'distance',distance,flush=True)
    for beta in [.15,.3]:
        group=[v for v in convergence if v['beta']==beta]
        assert group[-1]['full_gaussian_state_distance']<group[0]['full_gaussian_state_distance']
    return dict(cases=cross),dict(cases=convergence,scope='Every O(5) angular sector is checked at each R; the ground-state convergence theorem remains at fixed volume and positive regulator.')


def weyl3(a,b,c):
    return (a@b@c+a@c@b+b@a@c+b@c@a+c@a@b+c@b@a)/6


def cubic_lift():
    rows=[]
    for R in [2,3]:
        qs,_,_,_,t,_=microscopic(R,1,7)
        q=qs[0]
        X=[]
        for a in [0,1]:
            xcell=sp.csr_matrix(([1.,1.],([0,a+1],[a+1,0])),shape=(7,7))
            X.append([embed_local(xcell,j,R,7) for j in range(R)])
        expanded=sp.csr_matrix(q[0].shape)
        for i,j,k in itertools.product(range(R),repeat=3):
            expanded+=weyl3(X[0][i],X[1][j],X[1][k])/(2*math.sqrt(2)*R*R)
        target=weyl3(q[0],q[1],q[1])/math.sqrt(R)
        error=maximum(expanded-target)
        assert error<1e-13 and maximum(expanded-expanded.T)<1e-13
        _,cq,_,_=collective(R)
        ct=weyl3(cq[0],cq[1],cq[1])/math.sqrt(R)
        full_output=maximum(expanded@t-t@ct)
        assert full_output<2e-13
        rows.append(dict(R=R,full_dimension=t.shape[0],microscopic_expansion_error=error,
                         collective_full_output_error=full_output,
                         maximum_cells_per_term=3,per_cell_norm_sum_upper_bound=3/(2*math.sqrt(2))))
    return dict(cases=rows,scope='An exact noncommuting cubic monomial tests the general Weyl lift used for every monomial of the Einstein cubic density.')


def cubic_density():
    hvars=sy.symbols('h:5');dvars=sy.symbols('d:15');variables=hvars+dvars
    basis=[sy.diag(1,-1,0)/sy.sqrt(2),sy.diag(1,1,-2)/sy.sqrt(6)]
    for i,j in [(0,1),(0,2),(1,2)]:
        b=sy.zeros(3);b[i,j]=b[j,i]=1/sy.sqrt(2);basis.append(b)
    h=sum((v*b for v,b in zip(hvars,basis)),sy.zeros(3))
    dh=[sum((dvars[5*i+a]*basis[a] for a in range(5)),sy.zeros(3)) for i in range(3)]
    def connection(derivatives):
        return [[[ (derivatives[i][k,j]+derivatives[j][k,i]-derivatives[k][i,j])/2
                   for j in range(3)] for i in range(3)] for k in range(3)]
    g1=connection(dh);c2=connection([v*h+h*v for v in dh])
    g2=[[[sy.expand(c2[k][i][j]/2-sum(h[k,l]*g1[l][i][j] for l in range(3)))
           for j in range(3)] for i in range(3)] for k in range(3)]
    density=sy.expand(-2*sum(2*int(i==j)*g1[k][i][l]*g2[l][j][k]
                                 -h[i,j]*g1[k][i][l]*g1[l][j][k]
                                 for i,j,k,l in itertools.product(range(3),repeat=4)))
    polynomial=sy.Poly(density,*variables)
    terms=polynomial.terms()
    assert all(sum(powers)==3 and sum(powers[:5])==1 for powers,_ in terms)
    evaluator=sy.lambdify(variables,density,'numpy',cse=True)
    numeric_basis=np.array([np.array(b,float) for b in basis])
    # Generate first jets satisfying the flat TT divergence conditions.
    divergence=np.array([[numeric_basis[a,i,j] for i in range(3) for a in range(5)] for j in range(3)])
    kernel=la.null_space(divergence)
    rows=[]
    for case in range(3):
        hv=RNG.normal(size=5)/4;dv=kernel@(RNG.normal(size=kernel.shape[1])/4)
        hm=np.einsum('a,aij->ij',hv,numeric_basis)
        dm=np.einsum('ka,aij->kij',dv.reshape(3,5),numeric_basis)
        exact=float(evaluator(*hv,*dv))
        def bulk(epsilon):
            de=np.array([la.expm_frechet(epsilon*hm,epsilon*v,compute_expm=False) for v in dm])
            inverse=la.expm(-epsilon*hm)
            lower=np.array([[[ (de[i,k,j]+de[j,k,i]-de[k,i,j])/2 for j in range(3)]
                              for i in range(3)] for k in range(3)])
            gamma=np.einsum('kl,lij->kij',inverse,lower)
            return -2*float(np.einsum('ij,kil,ljk->',inverse,gamma,gamma))
        errors=[]
        for eps in [.04,.02,.01]:
            numerical=(bulk(eps)-bulk(-eps))/(2*eps**3)
            error=abs(numerical-exact);errors.append(error)
            rows.append(dict(jet=case,epsilon=eps,exact_cubic_density=exact,
                             exponential_metric_extraction=numerical,error=error))
        assert errors[-1]<errors[0]/10 and errors[-1]<2e-5
    return dict(cases=rows,variables=list(map(str,variables)),monomial_count=len(terms),
                exact_coefficient_l1=str(sy.simplify(sum(abs(c) for _,c in terms))),
                cubic_polynomial=[dict(powers=list(p),coefficient=str(c)) for p,c in terms],
                scope='Local integrated-curvature cubic density in a traceless frame; finite jets do not impose or solve the full gravitational constraints.')


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(point_maps=point_maps(),core_scaling=core_scaling(),creation_scaling=creation_scaling(),
                odd_micro_spectra=odd_micro_spectra())
    report['odd_radial_crosscheck'],report['odd_radial_convergence']=odd_radial_checks()
    report['cubic_lift']=cubic_lift()
    report['einstein_cubic_density']=cubic_density()
    report['higher_order_chart']=higher_order_chart()
    report['matching_relation']=dict(G_match='sigma^2 a^2/(32 pi R) = s^2 sqrt(U/g) a^2/(32 pi R)',
        cubic_coefficient_condition='chi = s g',
        assumptions='v=sqrt(Ug), b=(U/g)^(1/4), H_phys=H_lat/(a v), Qhat=Q/b=a phi, h=s Q/sqrt(R), sigma=s b, and the supplied Einstein normalization.',
        not_established='An actual Newton coupling, area entropy law, coarse-graining map or selected gravitational phase.')
    sources=['COLLECTIVE_GRAVITY_COUPLING.md','scripts/collective_gravity_coupling_audit.py',
             'SPIN_BLOCK_WAVE_PARENT.md','scripts/spin_block_wave_parent_audit.py',
             'scripts/microscopic_spin_two_audit.py','REDUCED_TENSOR_HAMILTONIAN.md',
             'CANONICAL_METRIC_RECONSTRUCTION.md','SPATIAL_METRIC_VACUUM.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']=('Regular finite-order collective interactions have cubic and quartic coefficients '
                     'of order R^-1/2 and R^-1. A parity-breaking two-cell example preserves vacuum '
                     'selection yet has the same fixed-volume Gaussian limit. The supplied Einstein '
                     'cubic has an exact bounded-strength three-cell Weyl lift; a higher-order '
                     'guard avoids fixing a leading quartic. Selection and '
                     'physical constraints for that lift are unproved. Point cotangent maps cannot '
                     'supply its pure potential cubic. A conditional G matching relation motivates '
                     'coordinated coarse scaling; it is not a physical G derivation or TOE.')
    target=root/'data/collective_gravity_coupling_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    counts={k:len(v['cases']) for k,v in report.items() if isinstance(v,dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target),cases=counts,total_cases=sum(counts.values()),
                          source_references=len(sources),scope=report['scope']),indent=2))


if __name__=='__main__':
    main()
