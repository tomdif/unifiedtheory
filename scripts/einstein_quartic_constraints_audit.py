#!/usr/bin/env python3
"""Conditional Einstein quartic localization, source brackets and Dirac flow."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.sparse.linalg import LinearOperator, cg
import sympy as sy

from reduced_tensor_hamiltonian_audit import christoffel_lower, contraction


RNG = np.random.default_rng(9112684)


def symplectic(n):
    return np.block([[np.zeros((n,n)),np.eye(n)],[-np.eye(n),np.zeros((n,n))]])


def exact_identities():
    t,v,u,n,l=sy.symbols('T V u n l', real=True)
    target=-(7*t-v)*(t+v)/8
    assert sy.expand(target+(3*t+v)**2/10-(t-3*v)**2/40)==0
    matrix=sy.Matrix([[-sy.Rational(7,8),-sy.Rational(3,8)],
                      [-sy.Rational(3,8),sy.Rational(1,8)]])
    assert matrix.eigenvals()=={-1:1,sy.Rational(1,4):1}
    saddle=8*n*l*u-(7*t-v)*u-n*(t+v)
    solution=sy.solve([sy.diff(saddle,u),sy.diff(saddle,n)],[u,n])
    assert sy.factor(saddle.subs(solution)-target/l)==0
    assert sy.factor(-solution[u]-solution[n]+t/l)==0
    z=sy.symbols('z',real=True)
    h=2*sy.cos(z);s=sy.sqrt(3)*sy.sin(z)
    source=sy.expand(s*s-3*sy.diff(h,z)**2/4)
    assert sy.simplify(source)==0
    gauss=sy.integrate(-3*s*sy.diff(h,z)*sy.diff(sy.sin(2*z),z),(z,0,2*sy.pi))/(2*sy.pi)
    assert gauss==-3*sy.sqrt(3)

    def project(k,a):
        k=sy.Matrix(k)
        P=sy.eye(3)-k*k.T/k.dot(k)
        return P*a*P-P*sy.trace(P*a)/2

    p,q,kn,km=[sy.Matrix(k) for k in [(0,0,1),(1,0,0),(0,1,0),(1,1,1)]]
    hp=sy.diag(1,-1,0);sq=sy.diag(0,1,-1)
    actual=sy.S.Zero;unreduced=sy.S.Zero;terms=0
    for signs in itertools.product([-1,1],repeat=4):
        pp,qq,nn,mm=[a*b for a,b in zip(signs,[p,q,kn,km])]
        if pp+qq+nn+mm!=sy.zeros(3,1):continue
        actual+=sy.trace(sq*(pp.dot(pp+nn)*project(pp+nn,hp)
                              -pp.dot(pp+mm)*project(pp+mm,hp)))/16
        unreduced+=pp.dot(nn-mm)*sy.trace(sq*hp)/16
        terms+=1
    assert actual==0 and unreduced==-sy.Rational(1,8) and terms==2
    ell,d=sy.symbols('ell d',positive=True)
    eps=sy.Matrix([[0,1],[-1,0]])
    C=sy.BlockMatrix([[sy.zeros(2),-ell*sy.eye(2)],[ell*sy.eye(2),d*eps]]).as_explicit()
    w=sy.symbols('w',real=True)
    polynomial=sy.factor((C-sy.I*w*sy.eye(4)).det())
    assert sy.expand(polynomial-((w*w-ell*ell)**2-d*d*w*w))==0
    return dict(source_matrix_eigenvalues=['-1','1/4'],source_square_decomposition=True,
                scalar_saddle_solution={str(k):str(value) for k,value in solution.items()},
                quadratic_lapse='-N T',gauss_source_identically_zero=True,
                gauss_bracket_on_constraint=str(gauss),TT_lapse_bracket=str(actual),
                incorrectly_unprojected_bracket=str(unreduced),
                two_source_normal_frequency_polynomial=str(polynomial))


class Fourier:
    def __init__(self,n):
        self.n=n
        axis=np.fft.fftfreq(n)*n
        self.k=np.stack(np.meshgrid(axis,axis,axis,indexing='ij'),axis=-1)
        self.k2=np.sum(self.k*self.k,axis=-1)
        self.safe=self.k2.copy();self.safe[0,0,0]=1
        self.P=np.eye(3)-self.k[..., :,None]*self.k[...,None,:]/self.safe[...,None,None]
        self.P[0,0,0]=0

    def derivative(self,a,i):
        multiplier=self.k[...,i].reshape(self.k2.shape+(1,)*(a.ndim-3))
        return np.fft.ifftn(1j*multiplier*np.fft.fftn(a,axes=(0,1,2)),axes=(0,1,2)).real

    def laplacian(self,a):
        return -sum(self.derivative(self.derivative(a,i),i) for i in range(3))

    def mean_zero(self,a):
        return a-np.mean(a,axis=(0,1,2),keepdims=True)

    def newton(self,a):
        ft=np.fft.fftn(a,axes=(0,1,2))/self.safe.reshape(self.k2.shape+(1,)*(a.ndim-3))
        ft[0,0,0]=0
        return np.fft.ifftn(ft,axes=(0,1,2)).real

    def tt(self,a):
        ft=np.fft.fftn(a,axes=(0,1,2))
        projected=self.P@ft@self.P
        projected-=self.P*np.trace(projected,axis1=-2,axis2=-1)[...,None,None]/2
        return np.fft.ifftn(projected,axes=(0,1,2)).real

    def field(self):
        a=RNG.normal(size=self.k2.shape+(3,3))
        a=(a+a.swapaxes(-1,-2))/2
        ft=np.fft.fftn(a,axes=(0,1,2))
        ft[np.any(abs(self.k)>1.01,axis=-1)]=0
        a=self.tt(np.fft.ifftn(ft,axes=(0,1,2)).real)
        return a/np.sqrt(np.mean(np.sum(a*a,axis=(-2,-1))))

    def longitudinal(self,a):
        gradient=np.stack([self.derivative(a,i) for i in range(3)],axis=-2)
        div=np.trace(gradient,axis1=-2,axis2=-1)
        return gradient+gradient.swapaxes(-1,-2)-2*div[...,None,None]*np.eye(3)/3

    def vector_operator(self,a):
        div=sum(self.derivative(a[...,i],i) for i in range(3))
        return self.laplacian(a)-np.stack([self.derivative(div,i) for i in range(3)],axis=-1)/3

    def vector_inverse(self,a):
        ft=np.fft.fftn(a,axes=(0,1,2))
        ft-=self.k*np.sum(self.k*ft,axis=-1)[...,None]/(4*self.safe[...,None])
        ft/=self.safe[...,None];ft[0,0,0]=0
        return np.fft.ifftn(ft,axes=(0,1,2)).real

    def iterative(self,a,vector=False):
        shape=a.shape;size=a.size
        apply=self.vector_operator if vector else self.laplacian
        def matvec(x):
            value=x.reshape(shape)
            # Add identity only on constants, while explicitly removing the
            # source mean. This makes the auxiliary solve strictly positive.
            return (apply(value)+np.mean(value,axis=(0,1,2),keepdims=True)).ravel()
        operator=LinearOperator((size,size),matvec=matvec,dtype=float)
        result,status=cg(operator,self.mean_zero(a).ravel(),rtol=2e-12,atol=1e-13,maxiter=200)
        assert status==0
        return result.reshape(shape)


def densities(grid,h,s):
    dh=np.stack([grid.derivative(h,i) for i in range(3)],axis=-3)
    T=np.sum(s*s,axis=(-2,-1));V=np.sum(dh*dh,axis=(-3,-2,-1))/4
    comm=s@h-h@s
    current=np.stack([np.sum(s*dh[...,i,:,:],axis=(-2,-1)) for i in range(3)],axis=-1)
    row_div=sum(grid.derivative(comm[..., :,j],j) for j in range(3))
    f=-(current+row_div)/2
    return T,V,f,dh


def curvature_bulk(h,dh):
    one=np.broadcast_to(np.eye(3),h.shape);h2=h@h
    dh2=dh@h[...,None,:,:]+h[...,None,:,:]@dh
    dh3=dh@h2[...,None,:,:]+h[...,None,:,:]@dh@h[...,None,:,:]+h2[...,None,:,:]@dh
    g1=christoffel_lower(dh)
    g2=christoffel_lower(dh2)/2-np.einsum('...kl,...lij->...kij',h,g1)
    g3=(christoffel_lower(dh3)/6-np.einsum('...kl,...lij->...kij',h,christoffel_lower(dh2))/2
        +np.einsum('...kl,...lij->...kij',h2,g1)/2)
    return (2*contraction(one,g1,g3)+contraction(one,g2,g2)
            -2*contraction(h,g1,g2)+contraction(h2,g1,g1)/2)


def field_localization():
    rows=[]
    for n,case in itertools.product([9,11],range(3)):
        grid=Fourier(n);h=grid.field();s=grid.field()
        if case==1:s*=0
        if case==2:h*=0
        T,V,f,dh=densities(grid,h,s);A=7*T-V;B=T+V
        u=grid.newton(B)/8;multiplier=grid.newton(A)/8;W=grid.vector_inverse(f)
        u_cg=grid.iterative(B)/8;n_cg=grid.iterative(A)/8;W_cg=grid.iterative(f,True)
        solve_error=max(float(np.max(abs(u-u_cg))),float(np.max(abs(multiplier-n_cg))),
                        float(np.max(abs(W-W_cg))))
        assert solve_error<2e-11
        scalar=-float(np.mean(A*grid.newton(B)))/8
        split=-float(np.mean((3*T+V)*grid.newton(3*T+V)))/10
        split+=float(np.mean((T-3*V)*grid.newton(T-3*V)))/40
        assert abs(scalar-split)<2e-13
        comm=h@s-s@h
        local=-float(np.mean(np.sum(comm*comm,axis=(-2,-1))))/12-float(np.mean(curvature_bulk(h,dh)))
        LW=grid.longitudinal(W)
        vector=float(np.mean(np.sum(LW*LW,axis=(-2,-1))))
        vector_kernel=2*float(np.mean(np.sum(f*grid.vector_inverse(f),axis=-1)))
        assert abs(vector-vector_kernel)<2e-13
        local_scalar=float(np.mean(-A*u_cg+n_cg*(8*grid.laplacian(u_cg)-grid.mean_zero(B))))
        vmult=-4*W_cg
        local_vector=float(np.mean(np.sum(grid.longitudinal(W_cg)**2,axis=(-2,-1))
                             +np.sum(vmult*(grid.vector_operator(W_cg)-grid.mean_zero(f)),axis=-1)))
        direct=local+scalar+vector;localized=local+local_scalar+local_vector
        assert abs(direct-localized)<3e-12
        assert np.max(abs(-u-multiplier+grid.newton(T)))<2e-14
        direction_h=grid.field();direction_s=grid.field()
        grad_s=grid.tt(-s*(7*grid.newton(B)+grid.newton(A))[...,None,None]/4)
        grad_h=grid.tt(sum(grid.derivative((grid.newton(A)-grid.newton(B))[...,None,None]
                                         *dh[...,i,:,:],i) for i in range(3))/16)
        gradient=float(np.mean(np.sum(grad_h*direction_h+grad_s*direction_s,axis=(-2,-1))))
        frozen_s=grid.tt(-14*s*u[...,None,None])
        frozen_h=grid.tt(-sum(grid.derivative(u[...,None,None]*dh[...,i,:,:],i) for i in range(3))/2)
        frozen_gradient=float(np.mean(np.sum(frozen_h*direction_h+frozen_s*direction_s,axis=(-2,-1))))
        def scalar_energy(hh,ss):
            t,v,_,_=densities(grid,hh,ss)
            return -float(np.mean((7*t-v)*grid.newton(t+v)))/8
        step=2e-5
        difference=(scalar_energy(h+step*direction_h,s+step*direction_s)
                    -scalar_energy(h-step*direction_h,s-step*direction_s))/(2*step)
        force_error=abs(difference-gradient)
        assert force_error<2e-9
        # The vector source response is checked independently by varying its
        # bilinear expression, then comparing with a solved finite difference.
        _,_,df1,_=densities(grid,direction_h,s)
        _,_,df2,_=densities(grid,h,direction_s)
        df=df1+df2
        vector_gradient=4*float(np.mean(np.sum(W*df,axis=-1)))
        def vector_energy(hh,ss):
            _,_,ff,_=densities(grid,hh,ss)
            ww=grid.vector_inverse(ff)
            return float(np.mean(np.sum(grid.longitudinal(ww)**2,axis=(-2,-1))))
        vector_difference=(vector_energy(h+step*direction_h,s+step*direction_s)
                           -vector_energy(h-step*direction_h,s-step*direction_s))/(2*step)
        assert abs(vector_difference-vector_gradient)<2e-9
        rows.append(dict(grid_per_axis=n,case=['mixed','gradient_only','momentum_only'][case],
                         elliptic_solve_error=solve_error,scalar_energy=scalar,vector_energy=vector,
                         complete_quartic=direct,localized_quartic=localized,
                         scalar_force_error=force_error,frozen_response_force_error=abs(frozen_gradient-gradient),
                         vector_force_error=abs(vector_difference-vector_gradient),
                         constant_conformal_source_removed=float(np.mean(B))))
    assert min(row['frozen_response_force_error'] for row in rows)>1e-5
    return dict(cases=rows,scope='Band-limited TT fields; periodic elliptic inverses remove source constants. These are coefficient/variation checks, not full periodic or asymptotically flat Einstein solutions.')


def projected_brackets():
    rows=[]
    for n in [9,11,13]:
        grid=Fourier(n)
        x,y,z=np.meshgrid(*(2*np.pi*np.arange(n)/n for _ in range(3)),indexing='ij')
        examples=[(2*np.cos(z)[...,None,None]*np.diag([1,-1,0])/np.sqrt(2),
                   np.sqrt(3)*np.sin(z)[...,None,None]*np.diag([1,-1,0])/np.sqrt(2),
                   np.ones_like(z),np.sin(2*z),-3.,-3*np.sqrt(3)),
                  (np.cos(z)[...,None,None]*np.diag([1,-1,0]),
                   np.cos(x)[...,None,None]*np.diag([0,1,-1]),
                   np.cos(y),np.cos(x+y+z),1.,0.)]
        for case,(h,s,N,M,ab,expected) in enumerate(examples):
            dh=[grid.derivative(h,i) for i in range(3)]
            dm=sum(grid.derivative(M[...,None,None]*dh[i],i) for i in range(3))
            dn=sum(grid.derivative(N[...,None,None]*dh[i],i) for i in range(3))
            actual=ab*float(np.mean(np.sum(s*(N[...,None,None]*grid.tt(dm)
                                             -M[...,None,None]*grid.tt(dn)),axis=(-2,-1))))
            unreduced=ab*float(np.mean(sum(np.sum(s*dh[i],axis=(-2,-1))
                                  *(N*grid.derivative(M,i)-M*grid.derivative(N,i)) for i in range(3))))
            assert abs(actual-expected)<2e-13
            if case==0:
                T,V,_,_=densities(grid,h,s)
                assert np.max(abs(T-3*V))<3e-13
            else:assert abs(unreduced+1/8)<2e-14
            rows.append(dict(grid_per_axis=n,case=case,TT_bracket=actual,
                             unprojected_current_expression=unreduced,exact_expected=expected))
    return dict(cases=rows)


def dirac_flows():
    rows=[]
    for d,a in [(2,2),(2,4),(3,4),(4,6)]:
        omega=symplectic(d);z=.3*RNG.normal(size=2*d)
        raw=RNG.normal(size=(a,a));L=raw@raw.T+np.eye(a)
        raw=RNG.normal(size=(a,a));energy_matrix=raw@raw.T+np.eye(a)
        source_matrices=RNG.normal(size=(a,2*d,2*d));source_matrices=(source_matrices+source_matrices.swapaxes(-1,-2))/2
        coupling_matrices=RNG.normal(size=(a,2*d,2*d));coupling_matrices=(coupling_matrices+coupling_matrices.swapaxes(-1,-2))/2
        Jf=np.einsum('aij,j->ai',source_matrices,z)
        Ja=np.einsum('aij,j->ai',coupling_matrices,z)
        f=Jf@z/2;coupling=Ja@z/2;y=la.solve(L,f)
        total=la.block_diag(omega,symplectic(a))
        constraint_jacobian=np.block([[np.zeros((a,2*d)),np.zeros((a,a)),np.eye(a)],
                                      [-Jf,L,np.zeros((a,a))]])
        C=constraint_jacobian@total@constraint_jacobian.T
        D=Jf@omega@Jf.T;inverse=la.inv(L)
        expected_inverse=np.block([[inverse@D@inverse.T,inverse],[-inverse.T,np.zeros((a,a))]])
        assert la.norm(la.inv(C)-expected_inverse)<2e-12
        reduced=total-total@constraint_jacobian.T@la.solve(C,constraint_jacobian@total)
        assert la.norm(reduced[:2*d,:2*d]-omega)<2e-13
        h0_gradient=z+.4*z**3
        off_gradient=np.r_[h0_gradient-Ja.T@y,energy_matrix@y-coupling,np.zeros(a)]
        physical_gradient=h0_gradient-Ja.T@y+Jf.T@la.solve(L.T,energy_matrix@y-coupling)
        full_flow=reduced@off_gradient;physical_flow=omega@physical_gradient
        expected_flow=np.r_[physical_flow,la.solve(L,Jf@physical_flow),np.zeros(a)]
        flow_error=float(la.norm(full_flow-expected_flow))
        assert flow_error<3e-12
        assert la.norm(constraint_jacobian@full_flow)<3e-12
        assert la.norm(D)>1e-3
        rows.append(dict(physical_pairs=d,auxiliary_pairs=a,source_bracket_norm=float(la.norm(D)),
                         reduced_poisson_error=float(la.norm(reduced[:2*d,:2*d]-omega)),
                         full_Dirac_flow_error=flow_error,
                         frozen_auxiliary_flow_error=float(la.norm(omega@off_gradient[:2*d]-physical_flow))))
    return dict(cases=rows,scope='All auxiliary and physical components of the Dirac Hamiltonian vector field are checked for quadratic noncommuting sources; auxiliary momenta vanish and coordinates follow their constraints.')


def quantum_normal_modes():
    rows=[]
    # One physical pair (q,p), two auxiliary pairs in coordinates (a,b,pa,pb).
    # f=(gq,gp), ell=1. This is an exactly quadratic canonical model.
    omega=la.block_diag(symplectic(1),symplectic(2))
    for g in [.1,.4,1.,2.]:
        M=np.array([[0,0,0,0,1,0],[0,0,0,0,0,1],
                    [-g,0,1,0,0,0],[0,-g,0,1,0,0]],float)
        C=M@omega@M.T
        frequencies=la.eigvalsh(1j*C)[2:]
        d=g*g;expected=np.array([(np.sqrt(d*d+4)-d)/2,(np.sqrt(d*d+4)+d)/2])
        assert la.norm(frequencies-expected)<2e-14
        flow=omega@M.T@M
        eigen=la.eigvals(flow)
        nonzero=np.sort(np.imag(eigen)[np.imag(eigen)>1e-8])
        assert la.norm(nonzero-expected)<2e-13
        null=la.null_space(M)
        # The two-dimensional zero space is symplectic, retaining one pair.
        assert np.linalg.matrix_rank(null.T@omega@null,tol=1e-10)==2
        rows.append(dict(source_strength=g,source_bracket=d,normal_frequencies=frequencies.tolist(),
                         surviving_physical_pairs=1,ground_energy_per_penalty_hbar=float(frequencies.sum()/2),
                         ground_energy_above_commuting_reference=float(frequencies.sum()/2-1)))
    return dict(cases=rows,scope='Exact quadratic linear-source model. Field-dependent tangent frequencies for nonlinear Einstein sources are only a diagnostic, not a proved nonlinear quantum reduction.')


def main():
    root=Path(__file__).resolve().parents[1]
    report=dict(exact=exact_identities(),field_localization=field_localization(),
                projected_brackets=projected_brackets(),dirac_flows=dirac_flows(),
                quantum_normal_modes=quantum_normal_modes())
    sources=['EINSTEIN_QUARTIC_CONSTRAINTS.md','scripts/einstein_quartic_constraints_audit.py',
             'REDUCED_TENSOR_HAMILTONIAN.md','scripts/reduced_tensor_hamiltonian_audit.py',
             'CONSTRAINED_MEDIATOR_TEST.md','GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
             'TENSOR_VERTEX_SELECTION.md','data/tensor_vertex_selection_audit.json',
             'CANONICAL_METRIC_RECONSTRUCTION.md','scripts/canonical_metric_reconstruction_audit.py']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope']=('A supplied Einstein quartic has a classical local constrained realization preserving '
                     'the assumed TT brackets, energy and forces; its scalar multiplier matches the '
                     'quadratic maximal lapse. Stable quadratic elimination and an independent Abelian '
                     'source Gauss law fail. The microscopic two-helicity constraint phase, quantum '
                     'Einstein dynamics, physical nonzero-G limit and TOE remain unproved.')
    target=root/'data/einstein_quartic_constraints_audit.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    counts={k:len(value['cases']) for k,value in report.items() if isinstance(value,dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target),cases=counts,total_cases=sum(counts.values()),scope=report['scope']),indent=2))


if __name__=='__main__':main()
