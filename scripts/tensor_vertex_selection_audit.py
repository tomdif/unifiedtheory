#!/usr/bin/env python3
"""Sign-independent selection of symmetric blocks with a tensor cubic.

The note proves the uniform bounds; finite cases test their ingredients.
"""
import functools
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy

from spin_block_wave_parent_audit import (
    collective, embed_local, lowest, maximum, microscopic, occupations, partitions)
from collective_gravity_coupling_audit import weyl3


RNG=np.random.default_rng(20260913)


@functools.lru_cache(None)
def compositions(q,n):
    if q==1:return ((n,),)
    return tuple((i,)+v for i in range(n+1) for v in compositions(q-1,n-i))


def multinomial(v):
    return math.factorial(sum(v))//math.prod(math.factorial(n) for n in v)


@functools.lru_cache(None)
def symmetric_isometry(q,R):
    states=compositions(q,R);index={v:i for i,v in enumerate(states)}
    digits=np.array(np.unravel_index(np.arange(q**R),(q,)*R)).T if R else np.empty((1,0),int)
    out=np.zeros((q**R,len(states)))
    for j,v in enumerate(digits):
        n=tuple(np.bincount(v,minlength=q));out[j,index[n]]=1/math.sqrt(multinomial(n))
    return out


@functools.lru_cache(None)
def trace_kraus(q,l,p):
    ins=compositions(q,l);outs=compositions(q,p);rests=compositions(q,l-p)
    lookup={v:i for i,v in enumerate(ins)}
    result=[]
    for rest in rests:
        a=np.zeros((len(outs),len(ins)))
        for row,v in enumerate(outs):
            n=tuple(x+y for x,y in zip(v,rest))
            a[row,lookup[n]]=math.sqrt(multinomial(v)*multinomial(rest)/multinomial(n))
        result.append(a)
    return tuple(result)


def channel_from_kraus(kraus):
    return sum((np.einsum('ai,bj->abij',k,k.conj()) for k in kraus))


def choi(channel):
    out,_,inn,_=channel.shape
    return channel.transpose(2,0,3,1).reshape(inn*out,inn*out)


@functools.lru_cache(None)
def measure_prepare(q,l,p):
    ins=compositions(q,l);outs=compositions(q,p)
    out=np.zeros((len(outs),len(outs),len(ins),len(ins)))
    d_l=math.comb(l+q-1,q-1)
    scale=d_l*math.factorial(q-1)/math.factorial(l+p+q-1)
    for i,n in enumerate(ins):
        for j,m in enumerate(ins):
            for a,u in enumerate(outs):
                total=tuple(mv+uv for mv,uv in zip(m,u))
                target=tuple(tv-nv for tv,nv in zip(total,n))
                if min(target)<0:continue
                try:b=outs.index(target)
                except ValueError:continue
                pref=math.sqrt(multinomial(n)*multinomial(m)*multinomial(u)*multinomial(target))
                out[a,b,i,j]=scale*pref*math.prod(math.factorial(v) for v in total)
    return out


def channel_checks():
    rows=[]
    for q,l,p in [(2,2,1),(2,3,2),(2,5,3),(2,8,2),(3,3,1),(3,4,2),(3,5,3),(7,2,1)]:
        direct=measure_prepare(q,l,p)
        trace=channel_from_kraus(trace_kraus(q,l,p))
        mixture=np.zeros_like(direct);weights=[]
        for s in range(p+1):
            weight=sy.Rational(math.comb(l,s)*math.comb(p+q-1,p-s),math.comb(l+p+q-1,p))
            weights.append(weight)
            reduction=trace_kraus(q,l,s)
            d_s=math.comb(s+q-1,q-1);d_p=math.comb(p+q-1,q-1)
            clones=[math.sqrt(d_s/d_p)*k.T for k in trace_kraus(q,p,s)]
            composition=channel_from_kraus([a@b for a in clones for b in reduction])
            mixture+=float(weight)*composition
        assert sum(weights)==1
        error=float(np.max(np.abs(direct-mixture)))
        assert error<3e-14
        w=float(weights[-1]);difference=choi(direct-w*trace)
        minimum=float(la.eigvalsh(difference)[0])
        trace_error=float(la.norm(np.einsum('aaij->ij',direct)-np.eye(direct.shape[2])))
        assert minimum>=-3e-13 and trace_error<2e-13
        entangled_error=float(np.sum(np.abs(la.eigvalsh(choi(direct-trace))))/direct.shape[2])
        assert entangled_error<=2*(1-w)+1e-12
        rows.append(dict(cell_dimension=q,input_copies=l,output_copies=p,
                         exact_partial_trace_weight=str(weights[-1]),identity_error=error,
                         CP_remainder_minimum=minimum,trace_preservation_error=trace_error,
                         maximally_entangled_input_error=entangled_error,diamond_bound=2*(1-w)))
    return dict(cases=rows,scope='Independent coherent-state moments and cloning decomposition, including complete Choi matrices. The analytical diamond bound retains arbitrary external entanglement.')


@functools.lru_cache(None)
def permutation_matrix(q,permutation):
    R=len(permutation);dim=q**R
    digits=np.array(np.unravel_index(np.arange(dim),(q,)*R)).T
    target=np.ravel_multi_index(digits[:,permutation].T,(q,)*R)
    return sp.csr_matrix((np.ones(dim),(target,np.arange(dim))),shape=(dim,dim))


def group_average(q,R,groups,antisymmetric=False):
    result=sp.eye(q**R,format='csr')
    for group in groups:
        average=sp.csr_matrix(result.shape)
        for order in itertools.permutations(group):
            perm=list(range(R))
            for original,new in zip(group,order):perm[original]=new
            inversions=sum(order[i]>order[j] for i in range(len(order)) for j in range(i+1,len(order)))
            sign=(-1)**inversions if antisymmetric else 1
            average+=sign*permutation_matrix(q,tuple(perm))/math.factorial(len(group))
        result=average@result
    return result


def representation_dimension(q,part):
    padded=part+(0,)*(q-len(part))
    answer=sy.Integer(1)
    for i in range(q):
        for j in range(i+1,q):answer*=sy.Rational(padded[i]-padded[j]+j-i,j-i)
    return int(answer)


@functools.lru_cache(None)
def young_isometry(q,part):
    R=sum(part)
    if len(part)==1:return symmetric_isometry(q,R)
    offsets=np.cumsum([0]+list(part))
    rows=[tuple(range(offsets[i],offsets[i+1])) for i in range(len(part))]
    columns=[tuple(offsets[i]+j for i in range(len(part)) if part[i]>j) for j in range(part[0])]
    y=group_average(q,R,rows)@group_average(q,R,columns,True)
    u,s,_=la.svd(y.toarray(),full_matrices=False)
    rank=int(np.sum(s>1e-10))
    assert rank==representation_dimension(q,part)
    return u[:,:rank]


def exchange_operator(q,R):
    identity=sp.eye(q**R,format='csr');c=sp.csr_matrix(identity.shape)
    for i,j in itertools.combinations(range(R),2):
        perm=list(range(R));perm[i],perm[j]=perm[j],perm[i]
        c+=identity-permutation_matrix(q,tuple(perm))
    return c


def young_checks():
    rows=[]
    cases=[(2,p) for p in [(3,),(2,1),(4,),(3,1),(2,2)]]
    cases += [(3,p) for p in [(4,),(3,1),(2,2),(2,1,1)]]
    cases += [(7,p) for p in [(3,),(2,1),(1,1,1)]]
    for q,part in cases:
        R=sum(part);l=part[0];m=R-l
        v=young_isometry(q,part)
        first=group_average(q,R,[tuple(range(l))])
        symmetry_error=float(la.norm(first@v-v))
        c=exchange_operator(q,R)
        eigen=R*(R-1)/2-sum(n*(n-2*i+1) for i,n in enumerate(part,1))/2
        eigen_error=float(la.norm(c@v-eigen*v))
        collective_error=0.
        for a,b in [(0,0),(0,1),(1,0)]:
            unit=sp.csr_matrix(([1.],([a],[b])),shape=(q,q))
            t=sum((embed_local(unit,j,R,q) for j in range(R)),sp.csr_matrix(c.shape))
            image=t@v
            collective_error=max(collective_error,float(la.norm(image-v@(v.T@image))))
        assert max(symmetry_error,eigen_error,collective_error)<2e-12
        assert eigen/R>=m/2
        rows.append(dict(cell_dimension=q,partition=part,R=R,first_row=l,defect=m,
                         representation_dimension=v.shape[1],first_row_symmetry_error=symmetry_error,
                         exchange_eigenvalue=eigen,exchange_eigen_error=eigen_error,
                         collective_invariance_error=collective_error))
    return dict(cases=rows,scope='Row-last Young images explicitly retain the same collective representation inside Sym^(R-m) tensor m extra cells.')


def large_block_entangled_rounding():
    rows=[]
    for R in [8,16,32,64,128]:
        l=R-1;dim=l
        # Exact lower-spin Clebsch--Gordan embedding of partition (R-1,1).
        embedding=np.zeros((l+1,2,dim))
        for j in range(dim):
            embedding[j+1,0,j]=-math.sqrt((j+1)/(l+1))
            embedding[j,1,j]=math.sqrt((l-j)/(l+1))
        # compositions(2,l) is ordered by occupation of label 0, opposite n_down.
        embedding=embedding[::-1]
        # Use two-cell outputs: the one-cell map happens to match exactly
        # for this lower-spin irrep after coherent-state estimation.
        s1=symmetric_isometry(2,1);s2=symmetric_isometry(2,2)
        one=channel_from_kraus(trace_kraus(2,l,1))
        one=np.einsum('au,bv,uvnm->abnm',s1,s1,one,optimize=True)
        cross=np.einsum('abnm,nci,mdj->acbdij',one,embedding,embedding,optimize=True).reshape(4,4,dim,dim)
        swap=permutation_matrix(2,(1,0)).toarray()
        cross=(cross+np.einsum('au,bv,uvij->abij',swap,swap,cross,optimize=True))/2
        good=channel_from_kraus(trace_kraus(2,l,2))
        good=np.einsum('abnm,nti,mtj->abij',good,embedding,embedding,optimize=True)
        good=np.einsum('au,bv,uvij->abij',s2,s2,good,optimize=True)
        measured=np.einsum('abnm,nti,mtj->abij',measure_prepare(2,l,2),embedding,embedding,optimize=True)
        measured=np.einsum('au,bv,uvij->abij',s2,s2,measured,optimize=True)
        original=(R-2)/R*good+2/R*cross
        error=float(np.sum(np.abs(la.eigvalsh(choi(measured-original))))/dim)
        bound=4/R+2*(1-math.comb(l,2)/math.comb(l+3,2))
        assert error<=bound+1e-12
        rows.append(dict(R=R,partition=[R-1,1],ancilla_dimension=dim,
                         maximally_entangled_local_error=error,R_times_error=R*error,
                         channel_comparison_bound=bound))
    return dict(cases=rows,scope='Two-cell marginals with a full irrep-dimensional entangled reference. This tests actual 1/R decay, not only a bound exceeding two.')


def rounding_channel(q,part):
    R=sum(part);l=part[0];m=R-l
    embedding=young_isometry(q,part);dout=math.comb(R+q-1,q-1)
    if not m:return np.einsum('ai,bj->abij',np.eye(dout),np.eye(dout))
    first=symmetric_isometry(q,l)
    coordinates=np.einsum('an,atj->ntj',first,embedding.reshape(q**l,q**m,-1))
    channel=measure_prepare(q,l,R)
    out=np.einsum('abnm,nti,mtj->abij',channel,coordinates,coordinates.conj(),optimize=True)
    assert la.norm(np.einsum('aaij->ij',out)-np.eye(embedding.shape[1]))<3e-13
    return out


def entangled_energy_rounding():
    rows=[];spectra=[]
    R=3;k=3;B=1.64;Delta=.4
    for q in [2,3]:
        local=[]
        x=np.zeros((q,q),complex);x[0,1]=x[1,0]=1
        y=np.zeros((q,q),complex);y[0,1]=-1j;y[1,0]=1j
        z=np.diag([1,-1]+[0]*(q-2)).astype(complex)
        if q==3:
            x[1,2]=x[2,1]=.6
            y[0,2]=-.4j;y[2,0]=.4j
            z[2,2]=.35
            x/=la.norm(x,2);y/=la.norm(y,2)
        for a in [x,y,z]:
            local.append(sum((embed_local(sp.csr_matrix(a),j,R,q) for j in range(R)),sp.csr_matrix((q**R,)*2)))
        I=sp.eye(q**R,format='csr')
        S=[[sp.kron(a,I,format='csr') for a in local],[sp.kron(I,a,format='csr') for a in local]]
        sx,sy0,sz=S[0];tx,ty,tz=S[1]
        F=(.13*sx+.17*tz+.2/R*(sz@sz)+.05/R*(sx@sy0+sy0@sx)
           +.3/R*(sx@ty)+.2/R**2*weyl3(sz,sx,ty)+.07/R**2*(sx@sx@sx+tz@tz@tz)).tocsr()
        assert maximum(F-F.conj().T)<1e-13
        sym=symmetric_isometry(q,R);isometry=sp.csr_matrix(np.kron(sym,sym))
        Fs=(isometry.T@F@isometry).toarray()
        for left,right in [((3,),(3,)),((2,1),(3,)),((3,),(2,1)),((2,1),(2,1))]:
            e1=young_isometry(q,left);e2=young_isometry(q,right)
            state=RNG.normal(size=e1.shape[1]*e2.shape[1])+1j*RNG.normal(size=e1.shape[1]*e2.shape[1])
            state/=la.norm(state)
            full=np.kron(e1,e2)@state
            original=float(np.vdot(full,F@full).real)
            rho=np.outer(state,state.conj()).reshape(e1.shape[1],e2.shape[1],e1.shape[1],e2.shape[1])
            rounded=np.einsum('abij,cdkl,ikjl->acbd',rounding_channel(q,left),rounding_channel(q,right),rho,optimize=True)
            rounded=rounded.reshape(Fs.shape)
            positivity=float(la.eigvalsh(rounded)[0])
            assert abs(np.trace(rounded)-1)<4e-13 and positivity>-3e-13
            after=float(np.trace(rounded@Fs).real)
            defect=2*R-left[0]-right[0];C=4*k*(k+q)
            bound=C*B*defect
            assert abs(after-original)<=bound+1e-11
            rows.append(dict(cell_dimension=q,left_partition=left,right_partition=right,
                             defect_sum=defect,original_energy=original,rounded_energy=after,
                             energy_change=after-original,uniform_energy_change_bound=bound,
                             rounded_density_minimum=positivity))
        C=4*k*(k+q);J=2*(C*B+Delta)
        exchange=exchange_operator(q,R)
        exchange=sp.kron(exchange,I)+sp.kron(I,exchange)
        H=F+J/R*exchange
        e,v,_=lowest(H);es=la.eigvalsh(Fs)[0]
        projector=isometry@isometry.T
        lift=2*float(abs(H).sum(axis=1).max())+10
        excluded,_,_=lowest(H+lift*projector)
        assert abs(e[0]-es)<2e-8
        assert excluded[0]-e[0]>=Delta-1e-8
        spectra.append(dict(cell_dimension=q,R=R,blocks=2,full_dimension=H.shape[0],
                            per_cell_budget_bound=B,J=J,ground_energy=float(e[0]),
                            collective_ground_energy=float(es),excluded_gap=float(excluded[0]-e[0]),
                            analytical_gap=Delta,ground_projection_error=float(la.norm(v-projector@v))))
    return dict(cases=rows,scope='The state is entangled between complete collective irreps; only defective blocks are measured and replaced.'),dict(cases=spectra)


def scalar_bounds():
    rows=[]
    for q in [2,3,7]:
        for R in [2,4,8,16,32]:
            k=3;C=4*k*(k+q);worst=0.;minimum_exchange_margin=float('inf');count=0
            for part in partitions(R,slots=q):
                l=part[0];m=R-l
                if not m:continue
                count+=1
                eigen=R*(R-1)/2-sum(n*(n-2*i+1) for i,n in enumerate(part,1))/2
                minimum_exchange_margin=min(minimum_exchange_margin,eigen/R-m/2)
                for p in range(1,min(k,R)+1):
                    if l<p:error=2.
                    else:
                        w=math.comb(l,p)/math.comb(l+p+q-1,p)
                        error=min(2.,2*p*m/R+2*(1-w))
                    worst=max(worst,error*R/m)
                    assert error<=C*m/R+1e-13
            assert minimum_exchange_margin>=0
            rows.append(dict(cell_dimension=q,R=R,partitions_checked=count,
                             maximum_rescaled_local_error_bound=worst,theorem_constant=C,
                             minimum_exchange_defect_margin=minimum_exchange_margin))
    # Scalar Young bound used to absorb the cubic with a three-cell guard.
    t=sy.symbols('t',nonnegative=True)
    polynomial=sy.Rational(27,4)*t**4-t+sy.Rational(1,4)
    factor=sy.factor(polynomial)
    assert factor==(3*t-1)**2*(3*t*t+2*t+1)/4
    return dict(cases=rows,cubic_absorption_factorization=str(factor))


def tensor_patch_coefficients(root):
    previous=json.loads((root/'data/collective_gravity_coupling_audit.json').read_text())
    terms=[]
    for row in previous['einstein_cubic_density']['cubic_polynomial']:
        powers=row['powers']
        if any(powers[10:]):continue
        h=[i for i,n in enumerate(powers[:5]) for _ in range(n)]
        derivative=[i for i,n in enumerate(powers[5:10]) for _ in range(n)]
        assert len(h)==1 and len(derivative)==2
        coefficient=float(sy.N(sy.sympify(row['coefficient'])))/4
        for center in [0,1]:
            terms.append((coefficient,[(center,h[0]+1),(1-center,derivative[0]+1),(1-center,derivative[1]+1)]))
    cstar=max(sum(abs(c)*sum(x==center for x,a in labels) for c,labels in terms) for center in [0,1])
    return terms,cstar


def tensor_parent(root):
    terms,cstar=tensor_patch_coefficients(root)
    rows=[]
    U,r,g,Delta=1.,.25,.1,.4
    c=min(U,r);alpha=c*5/2
    chi=c/(16*math.sqrt(3)*cstar)
    a3=4*math.sqrt(3)*abs(chi)*cstar;b3=36*abs(chi)*cstar
    lam=c+27*a3**4/(4*c**3)
    amax=r+6*g
    B=4.5*(U+amax)+3*g*6+alpha+3*lam+abs(chi)*cstar/(2*math.sqrt(2))
    C=4*3*(3+7);J=2*(C*B+Delta);delta=J+2*B+Delta
    for R,qcell in [(1,7),(2,7),(2,8)]:
        qs,ps,ns,cs,isometry,inactive=microscopic(R,2,qcell)
        dim=isometry.shape[0];zero=sp.csr_matrix((dim,dim))
        F=zero.copy();cubic=zero.copy();number=zero.copy()
        for x in range(2):
            number+=ns[x]
            # Five boundary neighbors are fixed to zero; the sixth is the
            # other site of the patch. The cubic uses the same zero exterior.
            for qa,pa in zip(qs[x],ps[x]):F+=(r+5*g)/2*(qa@qa)-U/2*(pa@pa)
            F+=alpha/R*ns[x]+lam/R**2*(ns[x]@ns[x]@ns[x])
        for a in range(6):
            diff=qs[0][a]-qs[1][a];F+=g/2*(diff@diff)
        for coefficient,labels in terms:
            cubic+=coefficient*weyl3(*(qs[x][a] for x,a in labels))/math.sqrt(R)
        F+=chi*cubic
        exchange=sum(cs,zero.copy())
        H=(F+J/R*exchange+sp.diags(delta*inactive)).tocsr()
        Hs=(isometry.T@H@isometry).tocsr()
        e,v,residual=lowest(H);es,_,_=lowest(Hs)
        projection=isometry@isometry.T
        assert abs(e[0]-es[0])<3e-8
        leakage=float(la.norm(v-projection@v))
        assert leakage<1e-7
        excluded_gap=None;inactive_gap=None
        if dim>isometry.shape[1]:
            lift=2*float(abs(H).sum(axis=1).max())+10
            excluded,_,_=lowest(H+lift*projection)
            excluded_gap=float(excluded[0]-e[0])
            assert excluded_gap>=Delta-2e-7
        if qcell>7:
            inds=np.flatnonzero(inactive)
            ei,_,_=lowest(H[inds][:,inds]);inactive_gap=float(ei[0]-e[0])
            assert inactive_gap>=delta-J-2*B-2e-7
        nonconstant=H-sp.diags(H.diagonal());nonconstant.eliminate_zeros()
        largest_positive=float(nonconstant.data.max())
        assert largest_positive>1e-6
        collective_number=isometry.T@number@isometry
        bound=.5*c*collective_number+(6*c-b3*2/math.sqrt(R))*sp.eye(Hs.shape[0])
        coercivity,_,_=lowest(Hs-bound)
        assert coercivity[0]>=-1e-8
        commutator=maximum(H@isometry-isometry@Hs)
        assert commutator<1e-9
        rows.append(dict(R=R,blocks=2,cell_basis_dimension=qcell,full_test_dimension=dim,
                         collective_dimension=isometry.shape[1],ground_energy=float(e[0]),
                         collective_ground_energy=float(es[0]),excluded_gap=excluded_gap,
                         inactive_gap=inactive_gap,analytical_gap=Delta,ground_projection_error=leakage,
                         eigensolver_residual=residual,largest_positive_offdiagonal=largest_positive,
                         occupation_bound_minimum=float(coercivity[0]),collective_invariance_error=commutator,
                         minimum_cubic_entry=float(cubic.data.min()),maximum_cubic_entry=float(cubic.data.max())))
        print('tensor parent',R,qcell,'ground',e[0],'excluded gap',excluded_gap,flush=True)
    return dict(cases=rows,cubic_monomials=len(terms),c_star=cstar,chi=chi,lambda_guard=lam,
                alpha_counterterm=alpha,a3=a3,b3=b3,per_cell_F_budget=B,J=J,inactive_penalty=delta,
                scope='The actual traceless Einstein cubic extension on a two-site Dirichlet finite-difference patch. This patch is not a physical TT reduction. q=8 exactly collapses nine identical inactive levels to one representative, retaining every inactive-pattern energy but not its multiplicity.')


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(channel_checks=channel_checks(),young_checks=young_checks(),
                large_block_entangled_rounding=large_block_entangled_rounding(),scalar_bounds=scalar_bounds())
    report['entangled_energy_rounding'],report['complex_parent_spectra']=entangled_energy_rounding()
    report['tensor_parent']=tensor_parent(root)
    sources=['TENSOR_VERTEX_SELECTION.md','scripts/tensor_vertex_selection_audit.py',
             'COLLECTIVE_GRAVITY_COUPLING.md','scripts/collective_gravity_coupling_audit.py',
             'data/collective_gravity_coupling_audit.json','SPIN_BLOCK_WAVE_PARENT.md',
             'scripts/spin_block_wave_parent_audit.py','scripts/microscopic_spin_two_audit.py',
             'REDUCED_TENSOR_HAMILTONIAN.md','SPATIAL_METRIC_VACUUM.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']=('For a block-permutation-invariant k-cell Hamiltonian of bounded per-cell norm sum, '
                     'a sign-independent rounding argument selects symmetric ground sectors with '
                     'exchange strength independent of block size and volume. Applied to the actual '
                     'supplied tensor cubic with a three-cell guard, it proves occupation control '
                     'and the fixed-volume Gaussian limit. A two-helicity gravitational constraint '
                     'phase, Einstein quartic, nonzero physical coupling limit and TOE remain unproved.')
    target=root/'data/tensor_vertex_selection_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    counts={k:len(v['cases']) for k,v in report.items() if isinstance(v,dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target),cases=counts,total_cases=sum(counts.values()),
                          source_references=len(sources),scope=report['scope']),indent=2))


if __name__=='__main__':main()
