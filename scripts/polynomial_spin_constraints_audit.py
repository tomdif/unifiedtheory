#!/usr/bin/env python3
"""Polynomial spin-coherent parent, quantum limit, and noncommuting source energy."""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
import sympy as sy

from covariant_constraint_transport_audit import at_site, PAULI


RNG=np.random.default_rng(9112721)


def comm(a,b):return a@b-b@a


def block(r):
    n=np.arange(r+1)
    b=np.diag(np.sqrt(n[1:]*(1-(n[1:]-1)/r)),1)
    return b,np.diag(n),np.diag(1-2*n/r),(b+b.T)/np.sqrt(2)


def coherent(r,alpha):
    alpha=np.asarray(alpha)
    t=alpha/np.sqrt(r)
    value=np.exp(-r*np.log1p(t*t)/2)
    values=[value]
    for n in range(r):
        value=value*t*np.sqrt((r-n)/(n+1))
        values.append(value)
    return np.stack(values,axis=0)


def exact_identities():
    t=sy.symbols('t',real=True)
    for r in [1,2,3,4]:
        b=sy.zeros(r+1)
        for n in range(1,r+1):b[n-1,n]=sy.sqrt(sy.Rational(n*(r-n+1),r))
        z=sy.diag(*[1-sy.Rational(2*n,r) for n in range(r+1)])
        c=b-sy.sqrt(r)*t*z-t*t*b.T
        phi=sy.Matrix([sy.sqrt(sy.binomial(r,n))*t**n for n in range(r+1)])
        assert (c*phi).applyfunc(sy.simplify)==sy.zeros(r+1,1)
    w1,w2,a,b=sy.symbols('w1 w2 a b',positive=True)
    optimum=(w1*a+w2*b)/(w1+w2)
    assert sy.simplify(w1*(optimum-a)**2+w2*(optimum-b)**2-w1*w2*(a-b)**2/(w1+w2))==0
    q0,qc,qs,p0,pc,ps,k,hbar=sy.symbols('q0 qc qs p0 pc ps k hbar',real=True)
    qs_all=[q0,qc,qs];ps_all=[p0,pc,ps]
    def poisson(a,b):
        return sy.expand(sum(sy.diff(a,q)*sy.diff(b,p)-sy.diff(a,p)*sy.diff(b,q)
                             for q,p in zip(qs_all,ps_all)))
    scalar=(pc**2-ps**2+k**2*(qs**2-qc**2)/4)/sy.sqrt(2)
    vector=k*(q0*pc-p0*qc)/4
    bracket=sy.factor(poisson(scalar,vector))
    expected=k*p0*pc/(2*sy.sqrt(2))-k**3*q0*qc/(8*sy.sqrt(2))
    assert sy.expand(bracket-expected)==0
    assert sy.expand(poisson(scalar,bracket)-k*k*vector/2)==0
    classical=hbar*bracket**2/(4*33*k*k)
    point=sy.simplify(classical.subs({q0:1,qc:1,qs:0,p0:0,pc:0,ps:0}))
    assert point==hbar*k**4/16896
    return dict(exact_coherent_recurrences=True,weighted_least_squares=True,
                Einstein_source_bracket=str(bracket),nonterminating_double_bracket='(k^2/2)f',
                selected_quartic_symbol=str(point),source_weights=['32 k^2','k^2'],
                scope='Specified three-pair TT source truncation; exact quadratic Weyl bracket, not full Einstein dynamics')


def coherent_tests():
    out=[]
    for r in [1,2,5,12]:
        b,n,z,q=block(r)
        for alpha in [.3,1.,3.]:
            c=b-alpha*z-alpha*alpha*b.T/r
            state=coherent(r,alpha)
            actual=la.eigvalsh(c.T@c)
            expected=np.sort((1+alpha*alpha/r)**2*np.arange(r+1)*(1-(np.arange(r+1)-1)/r))
            error=la.norm(actual-expected)
            residual=la.norm(c@state)
            probability=alpha*alpha/(r+alpha*alpha)
            third=r*probability+3*r*(r-1)*probability**2+r*(r-1)*(r-2)*probability**3
            measured=float(state@(n@n@n)@state)
            assert error<3e-10 and residual<3e-12 and abs(state@state-1)<2e-12
            assert abs(measured-third)<2e-10
            out.append(dict(block_size=r,alpha=alpha,kernel_residual=residual,spectrum_error=error,
                            normal_gap=float(actual[1]),exact_gap=(1+alpha*alpha/r)**2,
                            normal_third_moment=measured,poisson_upper_bound=alpha**6+3*alpha**4+alpha**2))
    return out


def budget_tests():
    out=[];lam=.35;nu=.2
    a=abs(lam)/(2*np.sqrt(2));b=lam*lam/8
    bound=2*(1+a+b)*(1+a+2*b)
    for r in [1,2,3,5]:
        monomials=[]
        for i in range(r):monomials.append((1/np.sqrt(r),{(0,i)}))
        for i,j,k in itertools.product(range(r),repeat=3):
            monomials.append((a/r**2,{(0,i),(1,j),(2,k)}))
        for i,j,jj,k,kk in itertools.product(range(r),repeat=5):
            monomials.append((b/r**3.5,{(0,i),(1,j),(1,jj),(2,k),(2,kk)}))
        total=sum(weight for weight,_ in monomials)
        per_cell={(block,cell):0. for block in range(3) for cell in range(r)}
        for weight,support in monomials:
            for cell in support:per_cell[cell]+=weight
        # Sum over all ordered pairs whose union contains this cell.
        per_cell_d={cell:(2*total*v-v*v)/r**2 for cell,v in per_cell.items()}
        actual=max(per_cell_d.values())
        assert actual<=bound+1e-11 and max(len(s) for _,s in monomials)<=5
        out.append(dict(block_size=r,c_monomials=len(monomials),normal_term_support_bound=10,
                        scaled_D_budget=actual,uniform_D_budget=bound,
                        total_parent_budget=bound+1+3*nu,
                        scope='Conservative absolute-monomial norm sums, including repeated microscopic indices'))
    return out


def dicke_embedding(r):
    result=np.zeros((2**r,r+1))
    for bits in range(2**r):
        n=bin(bits).count('1')
        result[bits,n]=1/np.sqrt(math.comb(r,n))
    return result


def full_spin_tests():
    out=[];lam=.35;nu=.2;delta=1.
    a=abs(lam)/(2*np.sqrt(2));b=lam*lam/8
    budget=2*(1+a+b)*(1+a+2*b)+1+3*nu
    exchange=2*(480*budget+delta)
    lower=np.array([[0,1],[0,0]],complex)
    for r in [1,2,3]:
        ncell=3*r;dim=2**ncell;eye=np.eye(dim)
        numbers=[];quadratures=[];penalty=np.zeros((dim,dim),complex)
        for blockid in range(3):
            ops=[[at_site(op,blockid*r+j,ncell) for j in range(r)] for op in PAULI]
            sums=[sum(v,np.zeros_like(penalty)) for v in ops]
            numbers.append((r*eye-sums[2])/2)
            quadratures.append(sums[0]/np.sqrt(2*r))
            for i in range(r):
                for j in range(i):
                    penalty+=exchange/(2*r)*(eye-sum((v[i]@v[j] for v in ops),np.zeros_like(penalty)))
        b0=sum((at_site(lower,j,ncell) for j in range(r)),np.zeros_like(penalty))/np.sqrt(r)
        alpha=lam*quadratures[1]@quadratures[2]/np.sqrt(2)
        z0=eye-2*numbers[0]/r
        c=b0-alpha@z0-alpha@alpha@b0.conj().T/r
        fast=c.conj().T@c
        slow=numbers[1]+numbers[2]+nu*numbers[0]@numbers[0]@numbers[0]
        h=fast/r**2+slow/r**3+penalty
        single=dicke_embedding(r);embed=np.kron(np.kron(single,single),single)
        hsym=embed.conj().T@h@embed
        symmetric_ground=float(la.eigh(hsym,eigvals_only=True,subset_by_index=[0,0])[0])
        ground=float(la.eigh(h,eigvals_only=True,subset_by_index=[0,0])[0])
        leak=la.norm(h@embed-embed@hsym)
        assert abs(ground-symmetric_ground)<3e-9 and leak<3e-8
        excluded=None
        if r>1:
            other=la.null_space(embed.conj().T)
            excluded=float(la.eigh(other.conj().T@h@other,eigvals_only=True,subset_by_index=[0,0])[0]-ground)
            assert excluded>=delta-1e-8
        fast_sym=embed.conj().T@fast@embed
        vals=la.eigvalsh(fast_sym)
        kernel=int(np.sum(abs(vals)<1e-10))
        assert kernel==(r+1)**2 and vals[kernel]>=1-1e-10
        out.append(dict(block_size=r,full_dimension=dim,symmetric_dimension=(r+1)**3,
                        kernel_dimension=kernel,normal_gap=float(vals[kernel]),
                        physical_ground_energy=ground*r**3,excluded_sector_gap=excluded,
                        required_excluded_gap=delta,exchange=exchange,sector_leakage=leak))
    return out


def canonical_effective(n,lam,nu):
    ext=n+7
    a=sp.diags(np.sqrt(np.arange(1,ext)),1,shape=(ext,ext),format='csr')
    q=(a+a.T)/np.sqrt(2)
    q2=q@q;q4=q2@q2;q6=q4@q2
    q2=q2[:n,:n];q4=q4[:n,:n];q6=q6[:n,:n]
    identity=sp.eye(n);number=sp.diags(np.arange(n))
    return (sp.kron(number,identity)+sp.kron(identity,number)
            +lam**2/4*(sp.kron(q2,identity)+sp.kron(identity,q2))
            +nu*(lam**6/8*sp.kron(q6,q6)+3*lam**4/4*sp.kron(q4,q4)
                 +lam**2/2*sp.kron(q2,q2))).tocsc()


def mixed_control(r,lam,nu):
    b,n,z,q=block(r);size=r+1
    values,vectors=la.eigh(q)
    number=vectors.T@n@vectors
    number[abs(number)<1e-10]=0
    # In this eigenbasis N is tridiagonal (phases depend on eigensolver choices).
    assert la.norm(number-np.diag(np.diag(number))-np.diag(np.diag(number,1),1)
                   -np.diag(np.diag(number,-1),-1))<1e-9
    number=sp.csr_matrix(number);identity=sp.eye(size)
    physical=(sp.kron(number,identity)+sp.kron(identity,number)).tocsr()
    alpha=(lam/np.sqrt(2)*values[:,None]*values[None,:]).ravel()
    iphys=sp.eye(size*size)
    c=(sp.kron(sp.csr_matrix(b),iphys)-sp.kron(sp.csr_matrix(z),sp.diags(alpha))
       -sp.kron(sp.csr_matrix(b.T/r),sp.diags(alpha*alpha))).tocsr()
    fast=c.T@c
    slow=sp.kron(identity,physical)+nu*sp.kron(sp.diags(np.arange(size)**3),iphys)
    h=(r*fast+slow).tocsc()
    coo=physical.tocoo();angles=np.arctan(alpha/np.sqrt(r))
    overlap=np.cos(angles[coo.row]-angles[coo.col])**r
    compressed=sp.coo_matrix((coo.data*overlap,(coo.row,coo.col)),shape=physical.shape).tocsr()
    probability=alpha*alpha/(r+alpha*alpha)
    third=r*probability+3*r*(r-1)*probability**2+r*(r-1)*(r-2)*probability**3
    compressed=(compressed+nu*sp.diags(third)).tocsc()
    return h,fast,compressed


def control_limit_tests():
    out=[];lam=.35;nu=.2
    references=[]
    for n in [26,36]:
        mat=canonical_effective(n,lam,nu)
        vals=eigsh(mat,k=3,sigma=-.1,which='LM',tol=2e-12,return_eigenvectors=False)
        references.append(np.sort(vals))
    target=references[-1];reference_error=float(np.max(abs(references[0]-target)))
    assert reference_error<2e-8,reference_error
    previous=None
    for r in [4,8,12,20,28]:
        h,fast,compressed=mixed_control(r,lam,nu)
        vals,vecs=eigsh(h,k=3,sigma=-.1,which='LM',tol=2e-11,v0=RNG.normal(size=h.shape[0]))
        indices=np.argsort(vals);vals=vals[indices];vecs=vecs[:,indices]
        residual=la.norm(h@vecs-vecs*vals)
        kernel_vals=np.sort(eigsh(compressed,k=3,sigma=-.1,which='LM',tol=2e-12,return_eigenvectors=False))
        fast_ground=float(vecs[:,0]@(fast@vecs[:,0]))
        error=float(np.max(abs(vals-target)))
        assert residual<5e-7 and np.all(vals<=kernel_vals+2e-9)
        assert fast_ground<=vals[0]/r+1e-10
        if previous is not None:assert error<previous
        previous=error
        out.append(dict(block_size=r,full_symmetric_dimension=h.shape[0],eigenvalues=vals.tolist(),
                        kernel_compression_eigenvalues=kernel_vals.tolist(),limiting_eigenvalues=target.tolist(),
                        max_error=error,ground_fast_expectation=fast_ground,residual=residual,
                        canonical_cutoff_comparison=reference_error,
                        scope='Full three-spin-block symmetric spectrum, not a global-particle truncation; canonical cutoff comparison is not an interval bound'))
    return out


def noncommuting_model(r,sources,weights,lam,repair=False):
    b,n,z,q=block(r);s=r+1;d=len(sources[0]);ia=np.eye(s)
    bs=[np.kron(b,ia),np.kron(ia,b)]
    zs=[np.kron(z,ia),np.kron(ia,z)]
    conditions=[];c0=[];c1=[];c2=[]
    for i in range(2):
        zero=np.kron(bs[i],np.eye(d))
        one=-np.kron(zs[i],sources[i])
        two=np.asarray(-np.kron(bs[i].T,sources[i]@sources[i])/r,dtype=complex)
        if repair:
            j=1-i
            two+=weights[j]/sum(weights)*np.kron(zs[i]@bs[j].T,comm(sources[i],sources[j]))
        conditions.append(zero+lam*one+lam*lam*two)
        c0.append(zero);c1.append(one);c2.append(two)
    h=sum((w*c.conj().T@c for w,c in zip(weights,conditions)),np.zeros_like(conditions[0]))
    coefficient=comm(c0[0],c2[1])+comm(c1[0],c1[1])+comm(c2[0],c0[1])
    return h,float(la.norm(coefficient))


def effective_band(h,d):
    vals,vecs=la.eigh(h,subset_by_index=[0,d])
    overlap=vecs[:d,:d]
    gram=overlap@overlap.conj().T
    eig,v=la.eigh(gram)
    inverse=(v/np.sqrt(eig))@v.conj().T
    result=inverse@((overlap*vals[:d])@overlap.conj().T)@inverse
    return result,vals


def source_curvature_tests():
    out=[]
    sx,sy,sz=PAULI
    sources=[la.block_diag(sx,2*sx),la.block_diag(sz,sz)]
    for r,weights in [(1,[1.,1.]),(3,[1.,1.]),(8,[1.,1.]),(3,[1.,2.3])]:
        bracket=comm(*sources)
        target=weights[0]*weights[1]/sum(weights)*(bracket.conj().T@bracket)
        previous=None;previous_repaired=None
        for lam in [.06,.03,.015]:
            h,defect=noncommuting_model(r,sources,weights,lam)
            band,vals=effective_band(h,4)
            repaired,zero_defect=noncommuting_model(r,sources,weights,lam,repair=True)
            repaired_vals=la.eigh(repaired,eigvals_only=True,subset_by_index=[0,3])
            error=la.norm(band/lam**4-target)
            assert vals[0]>0 and defect>1 and zero_defect<3e-12
            assert np.max(repaired_vals)<.2*np.max(vals[:4])
            if previous is not None:assert previous/error>3.4,(r,weights,previous,error)
            repaired_size=float(np.max(abs(repaired_vals)))
            if r>1 and previous_repaired is not None:
                assert previous_repaired/repaired_size>55.,(r,weights,previous_repaired,repaired_size)
            previous=error
            previous_repaired=repaired_size
            out.append(dict(block_size=r,normal_weights=weights,lambda_value=lam,
                            band_eigenvalues=vals[:4].tolist(),scaled_band_eigenvalues=(vals[:4]/lam**4).tolist(),
                            target_curvature_eigenvalues=la.eigvalsh(target).tolist(),
                            effective_coefficient_error=error,first_excluded_energy=float(vals[4]),
                            repaired_band_eigenvalues=repaired_vals.tolist(),
                            uncorrected_order_two_commutator_norm=defect,
                            repaired_order_two_commutator_norm=zero_defect,
                            scope='Bounded four-dimensional source space; exact complete two-normal-block matrices'))
    return out


def main():
    root=Path(__file__).resolve().parents[1]
    report={'exact_identities':exact_identities(),'coherent_kernels':coherent_tests(),
            'microscopic_budgets':budget_tests(),'full_spin_selection':full_spin_tests(),
            'control_quantum_limit':control_limit_tests(),'source_curvature':source_curvature_tests()}
    paths=['POLYNOMIAL_SPIN_CONSTRAINTS.md','scripts/polynomial_spin_constraints_audit.py',
           'COVARIANT_CONSTRAINT_TRANSPORT.md','scripts/covariant_constraint_transport_audit.py',
           'data/covariant_constraint_transport_audit.json','NONLINEAR_CONSTRAINT_DRESSING.md',
           'data/nonlinear_constraint_dressing_audit.json','TENSOR_VERTEX_SELECTION.md',
           'HOLOMORPHIC_TENSOR_PHASE.md','EINSTEIN_QUARTIC_CONSTRAINTS.md']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    report['scope']={
        'proved':'Fixed-ten-qubit commuting-source nonlinear control with bounded strength and a three-block quantum limit; R-independent fourth-order source-curvature energy',
        'not_proved':['All-order compatible Einstein sources','covariant finite-body tensor parent','Einstein clock algebra',
                      'physical Newton constant','joint spatial continuum','TOE'],
        'warning':'The control keeps a geometric mass term and an added stabilizing interaction; neither is a derived Einstein model'}
    target=root/'data/polynomial_spin_constraints_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    count=sum(len(report[key]) for key in ['coherent_kernels','microscopic_budgets','full_spin_selection',
                                         'control_quantum_limit','source_curvature'])
    print('PASS: exact identities and %d numerical cases'%count)
    print('Report:',target)
    print('Largest-block control eigenvalues:',report['control_quantum_limit'][-1]['eigenvalues'])
    print('Limiting eigenvalues:',report['control_quantum_limit'][-1]['limiting_eigenvalues'])


if __name__=='__main__':main()
