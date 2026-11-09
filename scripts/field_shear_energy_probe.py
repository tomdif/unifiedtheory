#!/usr/bin/env python3
"""Test the weighted field-shear square against the original Hamiltonian energy.

Run: python3 scripts/field_shear_energy_probe.py --output PATH
Requires NumPy and SciPy. This is floating-point evidence, not a Lean proof.

The single coherent input has seed [R,0,0,0,0,0]. Its displacement lies in
the first transverse pair, absent from the physical field q2+q3+q4. The
actual energy and responses are charge averaged at time 0, with all three
couplings equal to 1. Transverse Gaussian integration is analytic through
completion of the square and exact-degree polynomial Hermite rules. Clock
and charge integrals are numerical. Logarithmic weights prevent overflow
for displaced states whose unnormalized exponential output is enormous.

G0/G1 are mean(norm(D^3 J(Phi^p T U(theta) f))^2), p=1,2, divided by energy.
The density term in J=-i*h*(velocity dot grad+1) is retained, as is the
field derivative. The graph is the actual operator from
KFCausalCoherentFieldShearGraph and KFCausalFieldShearHardy, not Phi^p Jg.
The existing probe supplies only its inverse clock chart and independent
comparisons; its files and the Lean audit hash chain remain unchanged.

No finite scan proves an unbounded ratio, a global obstruction, clock
escape, or a physical theory of everything.
"""
import argparse
import hashlib
import json
from pathlib import Path
import matter_energy_gram_probe as old
import numpy as np
from numpy.polynomial.hermite import hermgauss
from numpy.polynomial.legendre import leggauss
from scipy.special import logsumexp
import itertools
import time


def hermite_cloud(H, order=5):
    nodes, weights = hermgauss(order)
    ids = np.array(list(itertools.product(range(order), repeat=len(H))))
    transform = np.linalg.inv(np.linalg.cholesky(H).T)
    return nodes[ids]@transform.T, np.prod(weights[ids], axis=1)/np.pi**(len(H)/2)


def pair_moments(alpha, r, b):
    """Mean and squared modulus of the first-pair logarithmic derivative.

    For Gaussian X=mu+Y with covariance sigma2*I, A=c*|X|^2+l*X.
    Its centered linear and quadratic parts have zero covariance.
    """
    H = 2*alpha*(r*r).real
    if H <= 0:
        raise ValueError('Shifted first-pair Gaussian is not positive.')
    sigma2 = .5/H
    B = b*r
    mu = B.real/H
    coeff = -alpha*r*r
    linear = B/2
    mean = np.sum(linear*mu,axis=-1)+coeff*(np.sum(mu*mu,axis=-1)+2*sigma2)
    centered = linear+2*coeff*mu
    second = np.abs(mean)**2+sigma2*np.sum(np.abs(centered)**2,axis=-1)+4*abs(coeff)**2*sigma2**2
    return mean, second


def rest_moments(widths, L, flow, H, power):
    q, qw = hermite_cloud(H[2:,2:])
    F = q.sum(axis=1)
    Q = q[:,:2].sum(axis=1)
    Lq = q@L[2:,2:].T
    LVq = q@(L@flow)[2:,2:].T
    Brest = -2*np.sum(widths[2:]*Lq*LVq,axis=1)
    fpower = F**power
    derivative = power*1.5*F**(power-1)*Q
    prest = fpower*(1+Brest)+derivative
    return dict(moment=np.dot(qw,fpower**2),
                cross=np.dot(qw,fpower*prest),
                restnorm=np.dot(qw,np.abs(prest)**2),
                bare_shear=np.dot(qw,fpower**2*Brest),
                correction=np.dot(qw,fpower*derivative),
                derivative_sq=np.dot(qw,derivative**2))


def forms(R, eps=1., h=.3, a=1., ns=160, nt=64, left=-12., right=4.):
    if not np.isfinite([R,eps,h,a,left,right]).all():
        raise ValueError('Parameters must be finite.')
    if not (eps > 0 and a > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
        raise ValueError('Require epsilon>0, a>0, 0<abs(h)<=2*pi*epsilon/3.')
    if ns < 16 or nt < 8 or not left < right:
        raise ValueError('Invalid quadrature settings.')
    theta = 2*np.pi*np.arange(nt)/nt
    alpha = 1/(2*abs(h))
    widths = np.array([1., 1., 1., 1., 1/32])*alpha
    v = 2*np.pi*h*R*np.cos(theta)
    phase = -R*np.sin(theta)
    b = np.zeros((nt,5), complex)
    b[:,0] = (-2*alpha*v+2j*np.pi*phase)/np.sqrt(2)
    b[:,1] = (2*alpha*v+2j*np.pi*phase)/np.sqrt(2)
    logamp = -alpha*v*v
    H0 = 2*np.diag(widths)
    V0 = .5*np.linalg.inv(H0)
    mu0 = b.real/2/widths
    logZ0 = 2.5*np.log(np.pi)-.5*np.linalg.slogdet(H0)[1]+np.sum(b.real*mu0,axis=1)+2*logamp
    kinetic = np.zeros(nt)
    for vdir in np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]]):
        row = -2*widths*vdir
        kinetic += h*h*(np.abs(b@vdir+mu0@row)**2+row@V0@row)
    flow = np.eye(5)/2
    flow[4,:] = [0,0,1,1,0]
    nodes, weights = leggauss(ns)
    nodes = left+(nodes+1)*(right-left)/2
    weights *= (right-left)/2/nt
    shifted_logs, initial_logs = [], []
    vals = {name:[] for name in ['field','quartic','vacuum','G0','G1','R0','R1','direct0','direct1','C0','C1','H0','H1']}
    inputs = {name:[] for name in ['norm','static']}
    angle_error = 0.
    for s,ds in zip(nodes,weights):
        C = np.exp(s)+eps
        D = eps/C
        chart = np.exp(s)+eps*s
        z = old.inverse_shift(s,eps,h)
        if not (h*z.imag < 0 and abs(z.imag) <= abs(h)/(2*eps)+2e-13):
            raise FloatingPointError('Inverse clock chart left the physical strip.')
        delta = z-s
        r = np.exp(delta/2)
        L = np.eye(5,dtype=complex)*r
        L[4,4] = 1
        L[4,2:4] = 2*(r-1)
        H = 2*(L.T@np.diag(widths)@L).real
        assert np.linalg.eigvalsh(H)[0] > 0
        B = b[:,:2]*r
        mu = B.real/H[0,0]
        logZ = 2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+np.sum(B.real*mu,axis=1)+2*logamp
        angle_error = max(angle_error, float(np.ptp(logZ)))
        shifted_logs.append(np.log(ds)+np.log(C)-2*s-2*a*(chart**2-h*h/4)+logZ)
        initial_logs.append(np.log(ds)+2*np.log(C)-2*s-2*a*chart**2+logZ0)
        inputs['norm'].append(np.ones(nt))
        inputs['static'].append(.5*(C+kinetic/C))
        meanA, secondA = pair_moments(alpha,r,b[:,:2])
        physical = eps/(np.exp(z)+eps)
        m = (D-physical)/eps
        direct = 2*(np.exp(z)/(2*(np.exp(z)+eps)**2)-1/(np.exp(z)+eps)-2*a*(chart-.5j*h)).real
        vals['vacuum'].append(np.ones(nt))
        for p in [1,2]:
            rest = rest_moments(widths,L,flow,H,p)
            moment, cross, restnorm = (rest[key] for key in ['moment','cross','restnorm'])
            graph = h*h*(secondA*moment+2*np.real(meanA.conj()*cross)+restnorm)
            if np.min(graph) < 0:
                raise FloatingPointError('Negative squared graph norm; no result accepted.')
            rate = (physical*(1-physical)).real/eps*moment+2*np.real(m*(moment*(1+meanA)+rest['bare_shear']))
            correction = 2*m.real*rest['correction']
            vals['field' if p==1 else 'quartic'].append(np.full(nt,moment))
            vals[f'G{p-1}'].append(D**6*graph)
            vals[f'R{p-1}'].append(rate)
            vals[f'direct{p-1}'].append(np.full(nt,direct*moment))
            vals[f'C{p-1}'].append(np.full(nt,correction))
            vals[f'H{p-1}'].append(np.full(nt,D**5*(1-D)*rest['derivative_sq']))
    ls = np.concatenate(shifted_logs)
    li = np.concatenate(initial_logs)
    vals = {k:np.concatenate(v) for k,v in vals.items()}
    inputs = {k:np.concatenate(v) for k,v in inputs.items()}
    growing = .5*vals['field']+.25*vals['quartic']+vals['vacuum']
    logenergy = logsumexp(np.concatenate([ls+np.log(growing),li+np.log(inputs['static'])]))
    shifted_weights = np.exp(ls-logenergy)
    initial_weights = np.exp(li-logenergy)
    out = {k:float(np.dot(shifted_weights,v)) for k,v in vals.items()}
    out.update({k:float(np.dot(initial_weights,v)) for k,v in inputs.items()})
    out['log_energy'] = float(logenergy)
    out['matter'] = .5*out['R0']+.25*out['R1']
    out['graph'] = .5*out['G0']+.25*out['G1']
    out['angle_log_density_spread'] = angle_error
    out['log_norm_over_energy'] = float(logsumexp(li)-logenergy)
    out['log_static_over_energy'] = float(logsumexp(li+np.log(inputs['static']))-logenergy)
    assert all(np.isfinite(x) for x in out.values())
    assert abs(out['static']+.5*out['field']+.25*out['quartic']+out['vacuum']-1)<1e-10
    # A zero floating ratio at very large displacement is not a zero form.
    # Preserve its finite logarithm and explicitly mark lost representability.
    out['underflowed_input_ratios'] = [key for key in ['norm','static'] if out[key]==0.]
    return out


def independent_shear_check():
    """Check the split moment formula against a full 5D polynomial integral.

    A separate finite-difference evaluation uses the actual real shear flow
    and wavefunction, checking both the density and field derivative terms.
    """
    moment_errors, derivative_errors = [], []
    for h, R in itertools.product([.3,-.3],[.7,8.,64.,128.]):
        alpha = 1/(2*abs(h))
        widths = np.array([1.,1.,1.,1.,1/32])*alpha
        # Compute source coefficients without ever exponentiating the tiny
        # translation amplitude, which cancels in normalized moments.
        v = 2*np.pi*h*R*np.cos(.61)
        phase = -R*np.sin(.61)
        b = np.array([(-2*alpha*v+2j*np.pi*phase)/np.sqrt(2),
                      (2*alpha*v+2j*np.pi*phase)/np.sqrt(2),0,0,0])
        for s in [-2.,-.3,1.]:
            r = np.exp((old.inverse_shift(s,1.,h)-s)/2)
            L = np.eye(5,dtype=complex)*r
            L[4,4] = 1
            L[4,2:4] = 2*(r-1)
            flow = np.eye(5)/2
            flow[4,:] = [0,0,1,1,0]
            H = 2*(L.T@np.diag(widths)@L).real
            B = b@L
            mu = np.linalg.solve(H,B.real)
            cloud, weights = hermite_cloud(H)
            cloud += mu
            first, second = pair_moments(alpha,r,b[:2])
            for p in [1,2]:
                F = cloud[:,2:].sum(axis=1)
                velocity = cloud@flow.T
                Fprime = p*F**(p-1)*velocity[:,2:].sum(axis=1)
                Lq = cloud@L.T
                gradient = B-2*(Lq*widths)@L
                polynomial = F**p*(1+np.sum(gradient*velocity,axis=1))+Fprime
                direct = h*h*np.dot(weights,np.abs(polynomial)**2)
                rest = rest_moments(widths,L,flow,H,p)
                split = h*h*(second*rest['moment']+2*np.real(first.conjugate()*rest['cross'])+rest['restnorm'])
                moment_errors.append(float(abs(direct-split)/max(abs(direct),abs(split))))
                if R != .7:
                    continue
                # Five-point derivative of exp(t)*Phi(flow_t q)^p*g(flow_t q)/g(q).
                q = mu+np.array([.11,-.17,.23,-.07,.19])
                lq = L@q
                exponent0 = -np.dot(widths,lq*lq)+np.dot(b,lq)
                def amplitude(t):
                    rt = np.exp(t/2)
                    qt = rt*q.copy()
                    qt[4] = q[4]+2*(rt-1)*(q[2]+q[3])
                    lqt = L@qt
                    exponent = -np.dot(widths,lqt*lqt)+np.dot(b,lqt)
                    return np.exp(t+exponent-exponent0)*qt[2:].sum()**p
                step = 1e-4
                derivative = (amplitude(-2*step)-8*amplitude(-step)+8*amplitude(step)-amplitude(2*step))/(12*step)
                velocity = flow@q
                gradient = B-2*(widths*lq)@L
                expected = q[2:].sum()**p*(1+np.dot(gradient,velocity))+p*q[2:].sum()**(p-1)*velocity[2:].sum()
                derivative_errors.append(float(abs(derivative-expected)/max(1.,abs(expected))))
    if max(moment_errors)>2e-12 or max(derivative_errors)>2e-8:
        raise AssertionError(('Independent shear calculation failed',moment_errors,derivative_errors))
    return dict(graph_test_displacements=[.7,8.,64.,128.],hbar_values=[.3,-.3],
                clock_values=[-2.,-.3,1.],charge_angle=.61,
                finite_difference_displacement=.7,
                full_five_dimensional_graph_relative_errors=moment_errors,
                real_flow_derivative_relative_errors=derivative_errors)


def comparison_check():
    errors = []
    setting = dict(ns=96,nt=32,left=-10.,right=4.)
    names = ['norm','field','quartic','vacuum','R0','R1','C0','C1','H0','H1','direct0','direct1']
    for R in [0.,.7,2.]:
        previous = old.forms([[R,0,0,0,0,0]],**setting)
        current = forms(R,**setting)
        energy = previous['energy'][0,0].real
        errors.append({k:abs(current[k]-previous[k][0,0].real/energy) for k in names})
    if max(max(e.values()) for e in errors)>2e-10:
        raise AssertionError(('Existing independent probe disagrees',errors))
    return dict(seeds=[0.,.7,2.],quadrature=setting,energy_scaled_comparison_errors=errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    np.seterr(over='raise',invalid='raise',divide='raise')
    checks = {'shear':independent_shear_check(),'previous_probe':comparison_check()}
    print('Independent shear, real-flow derivative and existing-energy checks passed.',flush=True)
    displacements = [0.,.5,1.,2.,4.,8.,16.,32.,64.,128.]
    parameters = dict(eps=1.,h=.3,a=1.)
    settings = [dict(ns=160,nt=64,left=-12.,right=4.),
                dict(ns=240,nt=96,left=-14.,right=4.5)]
    runs = []
    for setting in settings:
        start = time.monotonic()
        values = [dict(R=R,**forms(R,**parameters,**setting)) for R in displacements]
        for value in values:
            error = max(abs(value[f'R{i}']-value[f'direct{i}'])/max(1.,abs(value[f'R{i}'])) for i in [0,1])
            if error>2e-8:
                raise AssertionError(('Direct and shear responses disagree',value['R'],error))
        runs.append(dict(quadrature=setting,seconds=time.monotonic()-start,values=values))
        print(json.dumps(runs[-1]),flush=True)
    changes = []
    for first, second in zip(runs[0]['values'],runs[1]['values']):
        assert first['underflowed_input_ratios'] == second['underflowed_input_ratios']
        diff = {k:abs(first[k]-second[k])/max(1.,abs(second[k])) for k in first if k not in ['R','angle_log_density_spread','underflowed_input_ratios']}
        changes.append(dict(R=first['R'],relative_or_absolute_changes=diff))
    if max(max(v['relative_or_absolute_changes'].values()) for v in changes)>2e-7:
        raise AssertionError(('Quadrature refinement failed',changes))
    root = Path(__file__).resolve().parents[1]
    files = ['scripts/field_shear_energy_probe.py','scripts/matter_energy_gram_probe.py',
             'data/matter_energy_gram_probe.json','data/field_shear_hardy_audit.json']
    report = dict(kind='Exploratory floating-point quadrature; not a proof',
                  parameters=parameters,time=0.,mass2=1.,quartic=1.,vacuum=1.,
                  seed_recipe='[R,0,0,0,0,0] in coordinates [u0,u1,r0,r1,r2,r3]',
                  normalization='Every form is divided by the actual charge-averaged energy of the same state; log_energy is the unnormalized energy logarithm. Underflowed input ratios are explicitly flagged, with finite logarithms retained; their printed floating zero does not mean a zero form.',
                  graph_recipe='G0=mean(||D^3 J(Phi T U(theta) f)||^2)/E; G1 uses Phi^2; graph=G0/2+G1/4.',
                  source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files},
                  checks=checks,runs=runs,refinement=changes,
                  limitations=['No certified clock-tail or quadrature-error enclosure.',
                               'Large finite ratios do not prove asymptotic divergence or exclude every possible affine energy bound.',
                               'Positivity on this single-seed family does not prove a lower bound on the entire coherent span.',
                               'No common form core, evolution identity, quantum clock escape, model change or physical TOE is established.'])
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(args.output,flush=True)
    else:
        print(json.dumps(report,indent=2,allow_nan=False))


if __name__ == '__main__':
    main()
