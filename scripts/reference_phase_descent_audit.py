#!/usr/bin/env python3
"""Explicit curvature transitions between descriptions of the same real potential.

The canonical determinant phase is constructed, not set equal by assertion.
Uniform locality after this new phase adjustment remains a separate obligation.
"""
import hashlib
import json
from pathlib import Path
import numpy as np

from radial_measure_audit import RectangularOverlap, SPECIES, curvature
from compact_measure_holonomy_audit import FlatFamily
from chiral_measure_audit import inverse_sqrt
from toron_locality_audit import weak_jets
from local_cohomology_audit import gradient


def example():
    model=RectangularOverlap((2,)*4)
    theta=np.array([.37,-.29,.43,.61])
    a=np.random.default_rng(2026091005).uniform(-.010,.010,(4,model.n))
    a-=a.mean(axis=1)[:,None]
    shifts=[np.zeros(4),np.array([.004,-.003,.002,.001]),np.array([-.002,.003,-.004,.002])]
    refs=[theta+np.array(model.lengths)*r for r in shifts]
    fluctuations=[a-r[:,None] for r in shifts]
    physical=theta[:,None]/np.array(model.lengths)[:,None]+a
    for ref,field in zip(refs,fluctuations):
        assert np.linalg.norm(ref[:,None]/np.array(model.lengths)[:,None]+field-physical)<1e-14
        assert abs(field).max()<.018
        canonical=ref+np.array(model.lengths)*field.mean(axis=1)
        assert np.linalg.norm(canonical-theta)<1e-14
    return model,refs,fluctuations


def reference_frame(model,theta,q):
    family=FlatFamily(model.lengths,True)
    paired=family.paired_frame(family.blocks(theta,q)[1])
    frame=np.zeros((4*model.n,2*model.n),complex)
    for k in range(model.n):
        frame[np.ix_(np.arange(4)*model.n+k,[2*k,2*k+1])]=paired[k]
    fourier=np.exp(1j*np.array(model.geom.sites)@family.momenta.T)/np.sqrt(model.n)
    return np.kron(np.eye(4),fourier)@frame


def radial_frame(model,theta,a,q,steps):
    frame=reference_frame(model,theta,q)
    base=(theta/np.array(model.lengths))[:,None]
    for k in range(1,steps+1):
        sp=model.operator(np.exp(1j*(base+k/steps*a)),q)
        factor,_=inverse_sqrt(frame.conj().T@sp['p']@frame)
        frame=sp['p']@frame@factor
    return frame


def triangle_flux(model,theta,a,next_theta,count=8):
    """Integral of the radial connection along the fixed-potential fibre.

    U(s,t)=B_i+s*r+t*(a_i-s*r), r=(B_j-B_i).
    The t=1 edge collapses to the shared physical field.
    """
    base=(theta/np.array(model.lengths))[:,None]
    r=np.broadcast_to(((next_theta-theta)/np.array(model.lengths))[:,None],a.shape)
    nodes,weights=np.polynomial.legendre.leggauss(count)
    value=0.
    minimum_gap=np.inf
    for u,wu in zip((nodes+1)/2,weights/2):
        field=a-u*r
        for t,wt in zip((nodes+1)/2,weights/2):
            links=np.exp(1j*(base+u*r+t*field))
            for _,q,m in SPECIES:
                sp=model.operator(links,q)
                pa=model.projector_derivative(links,q,sp,field)
                pr=model.projector_derivative(links,q,sp,r)
                value+=m*wu*wt*(1-t)*curvature(sp['p'],pa,pr)
                minimum_gap=min(minimum_gap,sp['gap'])
    return float(value),minimum_gap


def raw_checks():
    model,refs,fields=example()
    pairs=[(0,1),(1,2),(0,2)]
    flux={pair:triangle_flux(model,refs[pair[0]],fields[pair[0]],refs[pair[1]])[0]
          for pair in pairs}
    cocycle=abs(flux[(0,1)]+flux[(1,2)]-flux[(0,2)])
    refined,_=triangle_flux(model,refs[0],fields[0],refs[1],12)
    assert cocycle<1e-12 and abs(refined-flux[(0,1)])<1e-12
    rows=[]
    for steps in [32,64,128]:
        frames={q:[radial_frame(model,ref,a,q,steps) for ref,a in zip(refs,fields)]
                for _,q,_ in SPECIES}
        transitions={}
        for i,j in pairs:
            result=1.+0j
            for _,q,m in SPECIES:
                phase,_=np.linalg.slogdet(frames[q][i].conj().T@frames[q][j])
                result*=phase**m
            error=abs(result-np.exp(-1j*flux[(i,j)]))
            assert error<1e-9
            transitions[(i,j)]=result
            rows.append(dict(steps=steps,source=i,target=j,flux=flux[(i,j)],
                             raw_overlap_phase=float(np.angle(result)),error=float(error)))
        assert abs(transitions[(0,1)]*transitions[(1,2)]-transitions[(0,2)])<1e-11
    assert max(abs(v) for v in flux.values())>1e-9
    assert max(row['error'] for row in rows if row['steps']==128)<1e-10
    return dict(curvature_fluxes=[dict(source=i,target=j,value=flux[(i,j)]) for i,j in pairs],
                additive_flux_cocycle_error=cocycle,quadrature_refinement_error=abs(refined-flux[(0,1)]),
                direct_frames=rows)


def corrected_checks(raw):
    model,refs,fields=example()
    jets=[weak_jets(model,ref,a) for ref,a in zip(refs,fields)]
    corrections=[row['phase'] for row in jets]
    flux={(r['source'],r['target']):r['value'] for r in raw['curvature_fluxes']}
    flux[(0,0)]=0.
    f=[flux[(0,i)]+corrections[i]-corrections[0] for i in range(3)]
    rows=[]
    for row in raw['direct_frames']:
        i,j=row['source'],row['target']
        corrected=np.exp(1j*(row['raw_overlap_phase']+corrections[i]-corrections[j]))
        predicted=np.exp(-1j*(flux[(i,j)]+corrections[j]-corrections[i]))
        # Multiplying determinant section i by exp(i*f_i) fixes its phase.
        descended=corrected*np.exp(1j*(f[j]-f[i]))
        rows.append(dict(steps=row['steps'],source=i,target=j,
                         corrected_overlap_phase=float(np.angle(corrected)),
                         predicted_transition_error=float(abs(corrected-predicted)),
                         descended_transition_error=float(abs(descended-1))))
    assert max(abs(r['corrected_overlap_phase']) for r in rows)>1e-10
    assert max(r['descended_transition_error'] for r in rows if r['steps']==128)<1e-10
    # The triangle's gauge change cancels the endpoint corrections' gauge change.
    omega=np.random.default_rng(2026091006).uniform(-1,1,model.n)
    gauge=gradient(model,omega)
    gauge_flux,_=triangle_flux(model,refs[0],fields[0]+gauge,refs[1])
    expected_delta=float(omega@(jets[1]['average_density']-jets[0]['average_density']))
    flux_gauge_error=abs(gauge_flux-flux[(0,1)]-expected_delta)
    gauged=[weak_jets(model,refs[i],fields[i]+gauge) for i in [0,1]]
    gauge_f=gauge_flux+gauged[1]['phase']-gauged[0]['phase']
    gauge_phase_error=abs(gauge_f-f[1])
    assert max(flux_gauge_error,gauge_phase_error)<1e-10
    return dict(references=[r.tolist() for r in refs],scalar_corrections=corrections,
                canonical_adjustments=f,transitions=rows,
                triangle_gauge_change_error=flux_gauge_error,
                canonical_adjustment_gauge_error=gauge_phase_error,
                original_ward_errors=[r['audit']['unweighted']['ward_error'] for r in jets],
                scope='Exact analytic phase descent for equal real potentials; uniform locality of the new adjustment not certified')


def main():
    raw=raw_checks()
    print('raw transition checks complete',flush=True)
    result=dict(raw=raw,corrected=corrected_checks(raw))
    root=Path(__file__).resolve().parents[1]
    paths=['scripts/reference_phase_descent_audit.py','scripts/toron_locality_audit.py',
           'scripts/compact_measure_holonomy_audit.py','scripts/second_cohomology_audit.py',
           'scripts/local_cohomology_audit.py','scripts/radial_measure_audit.py',
           'scripts/chiral_measure_audit.py','UnifiedTheory/Audit/KFCausalReferencePhaseDescent.lean',
           'REFERENCE_PHASE_DESCENT.md']
    result['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    (root/'data/reference_phase_descent_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
