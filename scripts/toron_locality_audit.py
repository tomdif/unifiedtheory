#!/usr/bin/env python3
"""Flat-holonomy locality and weak fluctuations about arbitrary flat references.

Analytic gap/seam bounds are documented separately; float64 scans are diagnostics.
No interacting compact quotient or continuum limit is certified here.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import numpy as np
import sympy as s
from compact_measure_holonomy_audit import CLIFFORD, FlatFamily
from radial_measure_audit import RectangularOverlap, SPECIES, density, curvature
from overlap_chirality_audit import GAMMA, GAMMA5, equal
from local_cohomology_audit import jacobian_resolvent, gradient
from second_cohomology_audit import DoubleComplex, density_hessian
from chiral_measure_audit import inverse_sqrt


def exact_checks():
    gs = [s.I*GAMMA5*g for g in GAMMA]+[GAMMA5]
    # The even-resolvent numerator for a first derivative contains one or
    # three Clifford matrices. Each such spin trace vanishes, even at p != p'.
    assert all(a.trace() == 0 for a in gs)
    assert all((a*b*c).trace() == 0 for a in gs for b in gs for c in gs)
    t = s.symbols('t', real=True)
    left, right, vertex = gs[0]+2*gs[4], gs[1]-gs[3], gs[2]+s.I*gs[4]
    numerator = (s.I*t*s.eye(4)+left)*vertex*(s.I*t*s.eye(4)+right)
    numerator += (-s.I*t*s.eye(4)+left)*vertex*(-s.I*t*s.eye(4)+right)
    equal(numerator, 2*(left*vertex*right-t*t*vertex))
    assert s.expand(numerator.trace()) == 0
    return dict(arithmetic='exact SymPy', first_density_derivative_zero_at_all_flat_references=True,
                one_and_three_clifford_traces_zero=True, even_resolvent_numerator=True)


def local_hessian(length, theta, charge, count=48):
    """One density Hessian entry from small spin blocks of Fourier resolvents.

    No dense (4V)^2 matrix: only resolvents between the density and four
    edge endpoints are evaluated. The directions are distinct, so H_ef=0.
    Integer coordinates are retained to give the antiperiodic wrap signs.
    """
    lengths = (length,)*4
    family = FlatFamily(lengths, True)
    momenta = family.momenta
    k = momenta-charge*np.asarray(theta)/length
    coefficients = np.column_stack((np.sin(k), 3-np.cos(k).sum(axis=1)))
    radii2 = np.sum(coefficients**2, axis=1)
    sites = [np.array(x) for x in [(0,0,0,0), (0,0,1,0), (-1,0,1,0),
                                  (0,0,0,1), (0,-1,0,1)]]
    displacements = list({tuple(x-y) for x in sites for y in sites})
    phases = np.exp(1j*np.array(displacements)@momenta.T)/family.n
    lookup = {d:j for j,d in enumerate(displacements)}
    pair = np.array([[lookup[tuple(x-y)] for y in sites] for x in sites])
    spin = np.concatenate((np.eye(4, dtype=complex)[None], CLIFFORD))
    he = []
    for mu in [0,1]:
        plus = (np.eye(4)+np.array(GAMMA[mu], complex))/2
        he.append(-1j*charge*np.exp(1j*charge*theta[mu]/length)*np.array(GAMMA5, complex)@plus)
    edges = [[(1,2,he[0]), (2,1,he[0].conj().T)],
             [(3,4,he[1]), (4,3,he[1].conj().T)]]
    nodes, weights = np.polynomial.legendre.leggauss(count)
    value = 0.
    for u,w in zip((nodes+1)/2,weights/2):
        angle = np.pi*u/2
        t, dt = np.tan(angle), np.pi/2/np.cos(angle)**2
        scalars = -np.column_stack((np.full(family.n,1j*t),coefficients))/(t*t+radii2)[:,None]
        blocks = np.einsum('da,aij->dij', phases@scalars, spin)[pair]
        term = 0j
        for first,second in [edges,edges[::-1]]:
            for h1,t1,v1 in first:
                for h2,t2,v2 in second:
                    term += np.trace(blocks[0,h1]@v1@blocks[t1,h2]@v2@blocks[t2,0])
        value += -charge/np.pi*w*dt*term.real
    return float(value)


def local_scan():
    theta = np.array([.37,-.29,.43,.61])
    # Independent comparison with the actual position-space projector Hessian.
    length=3
    model=RectangularOverlap((length,)*4)
    lookup={tuple(x):i for i,x in enumerate(model.geom.sites)}
    e,f=np.zeros((4,model.n)),np.zeros((4,model.n))
    e[0,lookup[(0,0,1,0)]]=1
    f[1,lookup[(0,0,0,1)]]=1
    a=np.broadcast_to((theta/length)[:,None],e.shape)
    sp=model.operator(np.exp(1j*a),6)
    _,_,mixed=model.projector_jet(np.exp(1j*a),6,sp,e,f)
    dense=6*np.diag(mixed).real.reshape(4,model.n).sum(axis=0)[0]
    fourier=local_hessian(length,theta,6)
    assert abs(dense-fourier)<2e-12,(dense,fourier)
    rows=[]
    for length in [2,3,4,6,8,12,16]:
        base=local_hessian(length,np.zeros(4),1)
        terms=[dict(charge=q,multiplicity=m,value=local_hessian(length,theta,q))
               for _,q,m in SPECIES]
        summed=sum(r['multiplicity']*r['value'] for r in terms)
        discrepancy=max(abs(r['value']/r['charge']**3-base) for r in terms)
        rows.append(dict(length=length,zero_toron_charge_one=base,
                         anomaly_free_sum=summed,maximum_normalized_toron_change=discrepancy,
                         species=terms))
        print('local Hessian',length,summed,discrepancy,flush=True)
    assert abs(rows[-1]['zero_toron_charge_one'])>1e-8
    assert rows[-1]['maximum_normalized_toron_change'] < rows[2]['maximum_normalized_toron_change']/100
    assert abs(rows[-1]['anomaly_free_sum']) < abs(rows[2]['anomaly_free_sum'])/100
    refine=local_hessian(16,theta,6,64)
    assert abs(refine-rows[-1]['species'][-1]['value'])<1e-12
    return dict(dense_projector_comparison_error=float(abs(dense-fourier)),rows=rows,
                largest_charge_quadrature_refinement_error=abs(refine-rows[-1]['species'][-1]['value']),
                scope='One fixed local Hessian entry; volume-independent exponential bounds are analytic')


def seam_check():
    length=4
    model=RectangularOverlap((length,)*4)
    theta=np.array([.37,-.29,.43,.61])
    a=np.random.default_rng(2026091004).uniform(-.018,.018,(4,model.n))
    sites=np.array(model.geom.sites)
    centered=(sites+length//2)%length-length//2
    chi=-np.sum(centered*theta/length,axis=1)
    cuts=np.array([(1-(centered[:,mu]-centered[tail,mu]))/length
                   for mu,tail in enumerate(model.geom.previous)])
    assert np.array_equal(cuts,cuts.astype(int))
    uniform=a+(theta/length)[:,None]
    seam=a+theta[:,None]*cuts
    gauge=np.tile(np.exp(6j*chi),4)
    hu=model.kernel(np.exp(1j*uniform),6)
    hs=model.kernel(np.exp(1j*seam),6)
    covariance=float(np.linalg.norm(hs-gauge[:,None]*hu*gauge.conjugate()[None,:]))
    difference=hs-model.kernel(np.exp(1j*a),6)
    allowed=np.zeros((model.n,model.n),bool)
    endpoints=[]
    for mu,tail in enumerate(model.geom.previous):
        for head in np.flatnonzero(cuts[mu]):
            allowed[head,tail[head]]=True
            allowed[tail[head],head]=True
            endpoints.extend([head,tail[head]])
    forbidden=float(np.linalg.norm(difference[~np.tile(allowed,(4,4))]))
    seam_distance=int(np.abs(centered[endpoints]).max(axis=1).min())
    assert covariance<1e-11 and forbidden==0
    assert seam_distance>=length//2-1
    return dict(length=length,charge=6,weak_fluctuation_max=float(abs(a).max()),
                covariance_error=covariance,difference_off_seam=forbidden,
                minimum_seam_endpoint_distance=seam_distance,
                changed_link_count=int(np.count_nonzero(cuts)))


def weak_jets(model,theta,a,field_nodes=4,resolvent_nodes=32):
    """The previous descent with contraction b(theta)+t*a, keeping all remainders."""
    c=DoubleComplex(model.lengths)
    smap=c.phi_map()
    n,e=model.n,4*model.n
    base=np.broadcast_to((np.asarray(theta)/model.lengths)[:,None],a.shape)
    j1,j1w=np.zeros((n,e)),np.zeros((n,e))
    j2,j2w=np.zeros((6*n,e)),np.zeros((6*n,e))
    avg=np.zeros(n)
    min_gap=np.inf
    nodes,weights=np.polynomial.legendre.leggauss(field_nodes)
    for t,w in zip((nodes+1)/2,weights/2):
        for _,q,m in SPECIES:
            jac,sp=jacobian_resolvent(model,base+t*a,q,resolvent_nodes)
            hess=density_hessian(model,base+t*a,q,resolvent_nodes)
            mapped=smap@hess.reshape(n*e,e)
            j1+=m*w*jac
            j1w+=m*w*(1-t)*jac
            j2+=m*w*(1-t)*mapped
            j2w+=m*w*(1-t)**2/2*mapped
            avg+=m*w*density(model,sp['p'],q)
            min_gap=min(min_gap,sp['gap'])
        print('weak toron node',float(t),flush=True)
    anomaly=sum(m*density(model,model.operator(np.exp(1j*(base+a)),q)['p'],q) for _,q,m in SPECIES)
    radial_error=float(np.linalg.norm(j2@a.ravel()-smap@j1.ravel()))
    weighted_error=float(np.linalg.norm(j2w@a.ravel()-smap@j1w.ravel()))
    assert max(radial_error,weighted_error)<1e-9
    h,raw=c.finish(a,j1,j2,anomaly)
    hw,weighted=c.finish(a,j1w,j2w,avg)
    return dict(current=h,weighted_current=hw,phase=-float(a.ravel()@hw),anomaly=anomaly,
                average_density=avg,audit=dict(minimum_kernel_gap=min_gap,radial_identity_error=radial_error,
                weighted_identity_error=weighted_error,phase=-float(a.ravel()@hw),
                anomaly_norm=float(np.linalg.norm(anomaly)),unweighted=raw,weighted=weighted))


def weak_checks():
    model=RectangularOverlap((2,)*4)
    theta=np.array([.37,-.29,.43,.61])
    a=np.random.default_rng(2026091002).uniform(-.018,.018,(4,model.n))
    original=weak_jets(model,theta,a)
    periodic=weak_jets(model,theta+2*np.pi*np.array([0,0,0,1]),a)
    omega=np.random.default_rng(2026091003).uniform(-1,1,model.n)
    transformed=weak_jets(model,theta,a+gradient(model,omega))
    periodic_error=float(np.linalg.norm(original['current']-periodic['current']))
    gauge_error=float(np.linalg.norm(original['current']-transformed['current']))
    phase_error=abs(transformed['phase']-original['phase']+float(omega@original['average_density']))
    assert max(periodic_error,gauge_error,phase_error)<1e-9
    base=np.broadcast_to((theta/2)[:,None],a.shape)
    first=[]
    for _,q,m in SPECIES:
        jac,sp=jacobian_resolvent(model,base,q)
        first.append(dict(charge=q,jacobian_norm=float(np.linalg.norm(jac)),
                          density_norm=float(np.linalg.norm(density(model,sp['p'],q)))))
    assert max(r['jacobian_norm'] for r in first)<1e-11
    return dict(theta=theta.tolist(),original=original['audit'],
                periodic_current_error=periodic_error,gauge_current_error=gauge_error,
                finite_gauge_phase_error=phase_error,flat_reference_first_jets=first,
                scope='Weak-potential charts parametrized by torons, including gauge orbits; quotient descent remains separate')


def mixed_connection_check():
    """Varying the flat reference needs int F(a,delta b), without a t factor."""
    model=RectangularOverlap((2,)*4)
    family=FlatFamily(model.lengths,True)
    theta=np.array([.37,-.29,.43,.61])
    a=np.random.default_rng(2026091002).uniform(-.018,.018,(4,model.n))
    q=6
    base=np.broadcast_to((theta/2)[:,None],a.shape)
    direction=np.zeros_like(a);direction[0]=.5
    nodes,weights=np.polynomial.legendre.leggauss(8)
    predicted=0.
    for t,w in zip((nodes+1)/2,weights/2):
        links=np.exp(1j*(base+t*a));sp=model.operator(links,q)
        pa=model.projector_derivative(links,q,sp,a)
        pb=model.projector_derivative(links,q,sp,direction)
        predicted+=w*curvature(sp['p'],pa,pb)
    fourier=np.exp(1j*np.array(model.geom.sites)@family.momenta.T)/np.sqrt(model.n)
    transform=np.kron(np.eye(4),fourier)
    def transported(point,steps):
        paired=family.paired_frame(family.blocks(point,q)[1])
        frame=np.zeros((4*model.n,2*model.n),complex)
        for k in range(model.n):
            frame[np.ix_(np.arange(4)*model.n+k,[2*k,2*k+1])]=paired[k]
        frame=transform@frame
        b=np.broadcast_to((point/2)[:,None],a.shape)
        for k in range(1,steps+1):
            sp=model.operator(np.exp(1j*(b+k/steps*a)),q)
            factor,_=inverse_sqrt(frame.conj().T@sp['p']@frame)
            frame=sp['p']@frame@factor
        return frame
    rows=[]
    delta=2e-4
    for steps in [32,64,128]:
        dt=np.array([delta,0,0,0])
        minus,plus=transported(theta-dt,steps),transported(theta+dt,steps)
        phase,_=np.linalg.slogdet(minus.conj().T@plus)
        actual=-float(np.angle(phase))/(2*delta)
        rows.append(dict(steps=steps,connection=actual,error=abs(actual-predicted)))
    assert abs(predicted)>1e-8
    assert rows[-1]['error']<1e-8
    return dict(charge=q,theta_direction=0,predicted_curvature_transgression=predicted,
                finite_difference_step=delta,transport=rows,
                scope='Reference-direction component of radial connection; adding dC preserves mixed curvature')


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=['scan','weak','all'],default='all')
    args=parser.parse_args()
    result=dict(exact=exact_checks(),seam=seam_check(),mixed_connection=mixed_connection_check())
    if args.part in ['scan','all']: result['local_scan']=local_scan()
    if args.part in ['weak','all']: result['weak_charts']=weak_checks()
    root=Path(__file__).resolve().parents[1]
    paths=['scripts/toron_locality_audit.py','scripts/compact_measure_holonomy_audit.py',
           'scripts/second_cohomology_audit.py','scripts/local_cohomology_audit.py',
           'scripts/radial_measure_audit.py','scripts/overlap_chirality_audit.py',
           'UnifiedTheory/Audit/KFCausalToronLocality.lean','TORON_WEAK_CHART_EXTENSION.md']
    result['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    output=root/('data/toron_locality_'+('audit' if args.part=='all' else args.part)+'.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
