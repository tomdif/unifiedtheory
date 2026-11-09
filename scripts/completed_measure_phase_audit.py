#!/usr/bin/env python3
"""Corrected chiral basis phase and a separate Dirac-zero-mode control."""
import hashlib
import json
from pathlib import Path
import numpy as np
from radial_measure_audit import RectangularOverlap, SPECIES, density, positive_current
from chiral_measure_audit import inverse_sqrt
from local_cohomology_audit import jacobian_resolvent
from second_cohomology_audit import DoubleComplex, density_hessian


def phase_check(correction):
    model=RectangularOverlap((2,)*4)
    a=np.random.default_rng(2026090906).uniform(-.018,.018,(4,model.n))
    free=model.operator(np.ones_like(a,dtype=complex),1)
    initial=free['v']
    b0=model.eye[:,np.diag(model.geom.g5).real>0]
    reference,_=np.linalg.slogdet(b0.conj().T@free['d']@initial)
    nodes,weights=np.polynomial.legendre.leggauss(8)
    radial=sum(m*sum(w/2*positive_current(model,np.exp(1j*(t+1)/2*a),q,a)
                      for t,w in zip(nodes,weights)) for _,q,m in SPECIES)
    rank=initial.shape[1]*sum(m for _,_,m in SPECIES)
    rows=[]
    for count in [64,128]:
        value=0.
        for _,q,m in SPECIES:
            frame=initial.copy()
            for k in range(1,count+1):
                sp=model.operator(np.exp(1j*k/count*a),q)
                factor,_=inverse_sqrt(frame.conj().T@sp['p']@frame)
                frame=sp['p']@frame@factor
            # i Tr(V^dag dV) gains +dC, while det(B^dag D V) gains exp(-iC).
            corrected=frame*np.exp(-1j*correction/rank)
            phase,_=np.linalg.slogdet(b0.conj().T@sp['d']@corrected)
            value+=m*float(np.angle(phase*reference.conjugate()))
        error=abs(value-(radial-correction))
        assert error<1e-9
        rows.append(dict(steps=count,corrected_relative_determinant_phase=value,
                         error_against_integrated_derivative=error))
    assert rows[-1]['error_against_integrated_derivative']<1e-10
    assert abs(radial-correction)>100*rows[-1]['error_against_integrated_derivative']
    return dict(radial_relative_phase=float(radial),scalar_correction=correction,
                predicted_corrected_relative_phase=float(radial-correction),
                complete_frame_rank=rank,direct_frames=rows,
                scope='Nonconstant finite determinant phase; not continuum equivalence')


def zero_mode_check():
    model=RectangularOverlap((2,)*4,antiperiodic=False)
    a=np.zeros((4,model.n))
    sp=model.operator(np.ones_like(a,dtype=complex),1)
    constant=np.kron(np.eye(4),np.ones((model.n,1))/np.sqrt(model.n))
    zero_error=float(np.linalg.norm(sp['d']@constant))
    assert zero_error<1e-12
    assert sp['gap']>.99
    jac,_=jacobian_resolvent(model,a,1,32)
    hessian=density_hessian(model,a,1,32)
    assert np.isfinite(hessian).all()
    c=DoubleComplex(model.lengths)
    # At zero field, first and second anomaly derivatives scale as q^2 and q^3.
    j1=sum(m*q**2 for _,q,m in SPECIES)*jac
    j2=.5*sum(m*q**3 for _,q,m in SPECIES)*(c.phi_map()@hessian.reshape(4*model.n**2,4*model.n))
    anomaly=sum(m*q for _,q,m in SPECIES)*density(model,sp['p'],1)
    current,audit=c.finish(a,j1,j2,anomaly)
    assert np.linalg.norm(current)==0
    return dict(lengths=model.lengths,boundary='periodic in every direction',
                constant_spinor_dirac_residual=zero_error,kernel_gap=sp['gap'],
                current_norm=float(np.linalg.norm(current)),ward_error=audit['ward_error'],
                scope='Current defined at free Dirac zero modes; determinant phase undefined there')


def main():
    root=Path(__file__).resolve().parents[1]
    report_path=root/'data/second_cohomology_audit.json'
    source_report=json.loads(report_path.read_text())
    sources=['scripts/completed_measure_phase_audit.py','scripts/second_cohomology_audit.py',
             'scripts/local_cohomology_audit.py','scripts/radial_measure_audit.py',
             'scripts/positive_measure_audit.py','scripts/gauge_dressed_measure_audit.py',
             'scripts/chiral_measure_audit.py','scripts/overlap_chirality_audit.py',
             'data/second_cohomology_audit.json']
    report=dict(arithmetic='Float64 independent direct-frame refinement; no interval certificate',
                determinant_phase=phase_check(source_report['phase']),zero_modes=zero_mode_check(),
                source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources})
    out=root/'data/completed_measure_phase_audit.json'
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':
    main()
