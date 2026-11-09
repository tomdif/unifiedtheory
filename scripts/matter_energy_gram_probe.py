#!/usr/bin/env python3
"""Numerical stress test of the remaining quantum matter energy estimate.

Run: python3 scripts/matter_energy_gram_probe.py --grid 7 --output PATH
Requires NumPy and SciPy. This is NOT a Lean audit or a certified quadrature.

The five transverse integrals are analytic Gaussian moments, including every
complex cross term. Only clock and charge-angle integrals use quadrature.
Energy is the actual eight-factor form at t=0 and mass2=quartic=vacuum=1.
Two independent expressions for each matter response are compared: the weak
pairing with T B f and the previously proved shear-commutator expression.

Seed coordinates are [u0,u1,r0,r1,r2,r3]. The initial field polynomial is
q4 + (3 exp(-Delta/2)-2)(q2+q3), not the unweighted initial interpolation.
Source formulas: KFCausalClockFloorCoherentSources, CoherentSpectral,
KFCausalTransportedInitialAssembly and KFCausalFieldEigenpolynomials.
Operator formulas: KFCausalClockFloorCommonDomain, PhysicalEnergyFactors,
KFCausalCoherentMatterWeakResponse, ClockFloorPureClockVacuumCommutator.

Fixed finite-subspace extrema and convergence checks cannot establish a
state-uniform inequality, an infinite-domain obstruction, or a physical TOE.
No rank truncation, finite coefficient cutoff theorem, or interval-error
certificate is silently substituted for such a statement.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.linalg import eigh
from numpy.polynomial.legendre import leggauss
from numpy.polynomial.hermite import hermgauss
from functools import lru_cache


def inverse_shift(s, eps, h):
    z = complex(s, -h/(2*(np.exp(s)+eps)))
    target = np.exp(s)+eps*s-0.5j*h
    for _ in range(30):
        step=(np.exp(z)+eps*z-target)/(np.exp(z)+eps)
        z-=step
        if abs(step)<2e-15: break
    assert abs(np.exp(z)+eps*z-target)<2e-12
    return z


def sources(k, theta, h):
    k=np.array(k,dtype=float,copy=True)
    ct,st=np.cos(theta),np.sin(theta)
    for u,v in [(0,3),(1,4)]:
        x,y=k[:,u].copy(),k[:,v].copy()
        k[:,u]=ct*x+st*y
        k[:,v]=-st*x+ct*y
    alpha=1/(2*abs(h)); v=(2*np.pi*h)*k[:,:2]
    b=np.zeros((len(k),5),complex)
    for j in range(2):
        b[:,2*j]=(-2*alpha*v[:,j]+2j*np.pi*k[:,3+j])/np.sqrt(2)
        b[:,2*j+1]=(2*alpha*v[:,j]+2j*np.pi*k[:,3+j])/np.sqrt(2)
    b[:,4]=2j*np.pi*k[:,5]
    amp=np.exp(-alpha*np.sum(v*v,axis=1))
    return b,amp,2*np.pi*k[:,2]


def gaussian_gram(b, amp, widths, L):
    A=L.T@np.diag(widths)@L
    H=2*A.real
    assert np.linalg.eigvalsh(H)[0]>0
    V=0.5*np.linalg.inv(H)
    B=b@L
    lin=B.conj()[:,None,:]+B[None,:,:]
    mean=np.einsum('...i,ij->...j',lin,V)
    Z=np.pi**2.5/np.sqrt(np.linalg.det(H))*np.exp(0.5*np.sum(lin*mean,axis=-1))
    Z*=amp.conj()[:,None]*amp[None,:]
    @lru_cache(None)
    def calc(rs):
        if not rs: return np.ones(Z.shape,complex)
        row=np.asarray(rs[0]); tail=rs[1:]
        result=np.einsum('...i,i->...',mean,row)*calc(tail)
        for j,other in enumerate(tail):
            result=result+(row@V@other)*calc(tail[:j]+tail[j+1:])
        return result
    def moment(*rows):
        return calc(tuple(tuple(row) for row in rows))
    return Z,mean,V,moment


def forms(k, eps=1., h=.3, a=1., nt=48, ns=64, left=-8., right=3.):
    k=np.asarray(k,float); n=len(k)
    if k.shape != (n,6) or n == 0 or not np.isfinite(k).all():
        raise ValueError('Expected a nonempty finite array of six-coordinate seeds.')
    if not (eps > 0 and a > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
        raise ValueError('Require epsilon>0, a>0, 0<abs(h)<=2*pi*epsilon/3.')
    if nt < 8 or ns < 16 or not left < right:
        raise ValueError('Invalid quadrature settings.')
    names=['norm','energy','base','vacuum','A0','A1','H0','H1','B0','B1','E0','E1','R0','R1','L0','L1','C0','C1','field','quartic','direct0','direct1']
    out={name:np.zeros((n,n),complex) for name in names}
    widths=np.array([1.,1.,1.,1.,1/32])/(2*abs(h))
    Q=np.array([0.,0.,1.,1.,0.]); F=Q.copy();F[4]=1
    flow=np.eye(5)/2; flow[4,:]=Q
    vs=np.array([[1,1,0,0,0],[0,0,1,1,1],[1,-1,0,0,0],[0,0,1,-1,0]],float)
    nodes,weights=leggauss(ns); nodes=left+(nodes+1)*(right-left)/2;weights*= (right-left)/2
    for theta in 2*np.pi*np.arange(nt)/nt:
        b,amp,p=sources(k,theta,h)
        Z0,mu0,V0,m0=gaussian_gram(b,amp,widths,np.eye(5))
        kinetic=np.zeros_like(Z0)
        for v in vs:
            row=-2*widths*v
            constant=b@v
            means=constant[None,:]+np.einsum('...i,i->...',mu0,row)
            leftmeans=constant.conj()[:,None]+np.einsum('...i,i->...',mu0,row)
            kinetic+=h*h*Z0*(leftmeans*means+row@V0@row)
        for s,ds in zip(nodes,weights/nt):
            C=np.exp(s)+eps; D=eps/C; chart=np.exp(s)+eps*s
            z=inverse_shift(s,eps,h); delta=z-s; r=np.exp(delta/2)
            L=np.eye(5,dtype=complex)*r;L[4,4]=1;L[4,2:4]=2*(r-1)
            phase=np.exp(1j*p*s)
            fclock=C*np.exp(-s-a*chart*chart)
            pairf=fclock*fclock*phase.conj()[:,None]*phase[None,:]
            ashift=np.sqrt(C)*np.exp(-s-a*(chart-.5j*h)**2)*np.exp(1j*p*z)
            pair1=ashift.conj()[:,None]*ashift[None,:]
            pair0=np.exp(-2*delta.real)*pair1
            Z1,mu1,V1,m1=gaussian_gram(b,amp,widths,L)
            P=(3*np.exp(-delta/2)-2)*Q.astype(complex);P[4]=1
            physical=eps/(np.exp(z)+eps)
            c=1j*delta/h
            w2=eps*physical.imag/(2*h)
            rho=w2/c.real
            assert -1e-12<=rho<=eps/4+1e-12
            vacuum=pair1*Z1
            field=vacuum*m1(F,F)
            quartic=vacuum*m1(F,F,F,F)
            initial0=pair0*Z0*m0(P.conj(),P)
            initial1=pair0*Z0*m0(P.conj(),P.conj(),P,P)
            rates=[]; longitudinal=[]; corrections=[]
            B=b@L
            LV=L@flow
            for power in [1,2]:
                rows=[F]*(2*power)
                derivative=m1(*rows).copy()
                for j in range(5):
                    derivative+=B[None,:,j]*m1(*rows,flow[j])
                    derivative-=2*widths[j]*m1(*rows,L[j],LV[j])
                J=-1j*h*vacuum*derivative
                m=(D-physical)/eps
                longitudinal.append((physical*(1-physical)).real/eps*vacuum*m1(*rows))
                rates.append(longitudinal[-1]-(2/h)*(m*J-(m*J).conj().T)/(2j))
                corrections.append(2*m.real*power*1.5*vacuum*m1(*([F]*(2*power-1)),Q))
            Cz=np.exp(z)+eps
            Bclock=-1j*h*(np.exp(z)/(2*Cz*Cz)-1/Cz-2*a*(chart-.5j*h)+1j*p/Cz)
            direct=[]
            for power in [1,2]:
                pairB=vacuum*m1(*([F]*(2*power)))*Bclock[None,:]
                direct.append((-2/h)*(pairB-pairB.conj().T)/(2j))
            values={
                'norm':pairf*Z0,
                'R0':rates[0],'R1':rates[1],
                'direct0':direct[0],'direct1':direct[1],
                'L0':longitudinal[0],'L1':longitudinal[1],
                'C0':corrections[0],'C1':corrections[1],
                'field':field,'quartic':quartic,
                'energy':.5*pairf*(C*Z0+kinetic/C)+.5*field+.25*quartic+vacuum,
                'base':pair0*Z0,'vacuum':vacuum,
                'A0':initial0,'A1':initial1,
                'H0':D**5*(1-D)*2.25*vacuum*m1(Q,Q),
                'H1':D**5*(1-D)*9*vacuum*m1(F,F,Q,Q),
                'B0':rho*initial0,'B1':rho*initial1,
                'E0':rho*field,'E1':rho*quartic,
            }
            for name,v in values.items(): out[name]+=ds*v
    for name,v in out.items():
        if not np.isfinite(v).all():
            raise FloatingPointError(f'{name}: non-finite quadrature; no result accepted.')
        err=np.linalg.norm(v-v.conj().T)/max(1.,np.linalg.norm(v))
        assert err<2e-12,(name,err)
        out[name]=(v+v.conj().T)/2
    return out


def whitening(energy, relative_floor=1e-10):
    """Whiten the complete finite subspace; refuse an unresolved small mode."""
    scales = np.sqrt(np.real(np.diag(energy)))
    if not np.isfinite(scales).all() or np.any(scales <= 0):
        raise ValueError('Nonpositive/nonfinite energy diagonal.')
    normalized = energy/scales[:,None]/scales[None,:]
    ev, vectors = eigh(normalized)
    if ev[0] <= relative_floor*ev[-1]:
        raise ValueError('Energy Gram is insufficiently conditioned; no rank truncation used.')
    W = vectors/np.sqrt(ev)[None,:]/scales[:,None]
    residual = np.linalg.norm(W.conj().T@energy@W-np.eye(len(energy)),2)
    return W, {
        'dimension': len(energy),
        'normalized_energy_min_eigenvalue': float(ev[0]),
        'normalized_energy_condition': float(ev[-1]/ev[0]),
        'whitening_residual': float(residual),
        'rank_truncated': False,
    }


def extreme(M, W, smallest=False):
    compressed = W.conj().T@M@W
    ev, vectors = eigh((compressed+compressed.conj().T)/2)
    index = 0 if smallest else -1
    return float(ev[index]), W@vectors[:,index]


def value(M, v):
    return float(np.real(np.vdot(v,M@v)))


def summarize(f, h, eps):
    W, info = whitening(f['energy'])
    beta = 800*np.exp(4*np.pi/3)*h**4/eps**5
    terminal = .5*f['H0']+.25*f['H1']
    coarse = (.5*f['A0']+.25*f['A1'])/(2*eps)+beta*terminal
    sharp = 2/eps**2*(.5*(f['B0']-f['E0'])+.25*(f['B1']-f['E1']))+beta*terminal
    response = .5*f['R0']+.25*f['R1']
    difference = f['A1']-f['quartic']
    eigenvalue, witness = extreme(difference,W)
    info.update({
        'max_initial_quartic_minus_final_over_energy': eigenvalue,
        'min_signed_matter_response_over_energy': extreme(response,W,smallest=True)[0],
        'max_coarse_loss_over_energy': extreme(coarse,W)[0],
        'max_sharp_loss_over_energy': extreme(sharp,W)[0],
        'max_initial_quartic_over_energy': extreme(f['A1'],W)[0],
        'max_terminal_quartic_correction_over_energy': extreme(f['H1'],W)[0],
        'min_vacuum_minus_base_over_energy': extreme(f['vacuum']-f['base'],W,smallest=True)[0],
        'direct_response_relative_errors': [
            float(np.linalg.norm(f['R'+str(i)]-f['direct'+str(i)])/np.linalg.norm(f['R'+str(i)]))
            for i in range(2)],
        'minimum_positive_form_eigenvalue_over_energy': min(
            extreme(f[name],W,smallest=True)[0]
            for name in ['norm','vacuum','base','field','quartic','A0','A1','H0','H1']),
    })
    return info, witness, W


def independent_gaussian_check():
    """Compare Wick contractions with direct five-dimensional Hermite quadrature.

    The quadrature evaluates the original wavefunctions and their complex
    superposition, independently of the mean/covariance moment recursion.
    """
    rng = np.random.default_rng(734210)
    widths = np.array([1.,1.2,.9,1.1,.4])
    b = .12*(rng.normal(size=(3,5))+1j*rng.normal(size=(3,5)))
    amp = np.array([1.+.2j,.7-.1j,-.4+.3j])
    L = np.eye(5,dtype=complex)
    L[0,1] = .07j
    L[4,2] = .04+.03j
    Z, _, _, moment = gaussian_gram(b,amp,widths,L)
    H = 2*(L.T@np.diag(widths)@L).real
    transform = np.linalg.inv(np.linalg.cholesky(H).T)
    nodes, weights = hermgauss(12)
    ids = np.array(list(itertools.product(range(12), repeat=5)))
    q = nodes[ids]@transform.T
    quadrature_weights = np.prod(weights[ids],axis=1)*np.linalg.det(transform)
    B = b@L
    row = np.array([.3,-.2,.5,.4,.7])
    coefficients = np.array([1.+.3j,-.4+.7j,.2-.5j])
    # The common e^{-q^T H q} factor is already in the Hermite weights.
    modulations = np.exp(q@B.T)*amp[None,:]
    squared = np.abs(modulations@coefficients)**2
    errors = []
    for degree in [0,2,4,6]:
        direct = np.dot(quadrature_weights,squared*(q@row)**degree)
        analytic = value(Z*moment(*([row]*degree)),coefficients)
        errors.append(float(abs(direct-analytic)/max(abs(direct),abs(analytic))))
    if max(errors) > 2e-11:
        raise AssertionError(('Independent Gaussian moment check failed',errors))
    seeds = .2*rng.normal(size=(4,6))
    widths = np.array([1.,1.,1.,1.,1/32])/.6
    b0, a0, _ = sources(seeds,0,.3)
    reference = gaussian_gram(b0,a0,widths,np.eye(5))[0]
    charge_errors = []
    for theta in [.19,.73,2.1]:
        bt, at, _ = sources(seeds,theta,.3)
        gram = gaussian_gram(bt,at,widths,np.eye(5))[0]
        charge_errors.append(float(np.linalg.norm(gram-reference)/np.linalg.norm(reference)))
    if max(charge_errors) > 2e-12:
        raise AssertionError(('Charge inner-product invariance failed',charge_errors))
    return {'independent_gaussian_moment_relative_errors': errors,
            'charge_gram_relative_errors': charge_errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--grid',type=int,default=5)
    parser.add_argument('--epsilon',type=float,default=1.)
    parser.add_argument('--hbar',type=float,default=.3)
    parser.add_argument('--a',type=float,default=1.)
    parser.add_argument('--ns',type=int,default=96)
    parser.add_argument('--nt',type=int,default=64)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    if not 2 <= args.grid <= 7:
        parser.error('Use grid sizes 2 through 7; larger grids need a precision study.')
    # Float overflow must stop a run, never masquerade as an inequality result.
    np.seterr(over='raise',invalid='raise',divide='raise')
    checks = independent_gaussian_check()
    print('Independent five-dimensional quadrature and charge checks passed.',flush=True)
    seeds = np.array([[0,x,0,0,0,y] for x in np.linspace(-.35,.35,args.grid)
                      for y in np.linspace(-.25,.25,args.grid)])
    parameters = {'eps':args.epsilon,'h':args.hbar,'a':args.a}
    settings = [dict(ns=args.ns,nt=args.nt,left=-9.,right=3.5),
                dict(ns=(3*args.ns+1)//2,nt=(3*args.nt+1)//2,left=-10.,right=4.)]
    runs = []
    matrices = []
    witnesses = []
    for setting in settings:
        start = time.monotonic()
        f = forms(seeds,**parameters,**setting)
        result, witness, W = summarize(f,args.hbar,args.epsilon)
        if max(result['direct_response_relative_errors']) > 2e-8:
            raise AssertionError('Independent response formulas disagree; refine the quadrature.')
        if result['min_vacuum_minus_base_over_energy'] < -2e-7:
            raise AssertionError('Quadrature contradicts the proved unweighted comparison.')
        if result['minimum_positive_form_eigenvalue_over_energy'] < -2e-7:
            raise AssertionError('A positive Gram form failed the numerical positivity check.')
        matrices.append(f)
        witnesses.append(witness)
        runs.append({'quadrature':setting,'seconds':time.monotonic()-start,**result})
        print(json.dumps(runs[-1]),flush=True)
    # Evaluate the same first-run witness against refined, independently summed
    # matrices, rather than comparing separately optimized eigenvalues alone.
    fixed = witnesses[0]
    fixed /= np.max(np.abs(fixed))
    evaluations = []
    for f in matrices:
        energy = value(f['energy'],fixed)
        evaluations.append({
            'energy':energy,
            'initial_quartic_cost':value(f['A1'],fixed),
            'final_quartic_cost':value(f['quartic'],fixed),
            'difference_over_energy':value(f['A1']-f['quartic'],fixed)/energy,
            'signed_matter_response_over_energy':value(.5*f['R0']+.25*f['R1'],fixed)/energy,
        })
    W, _ = whitening(matrices[-1]['energy'])
    convergence = {}
    for name in matrices[0]:
        delta = W.conj().T@(matrices[0][name]-matrices[1][name])@W
        convergence[name] = float(np.linalg.norm(delta,2))
    if max(convergence.values()) > 2e-6:
        raise AssertionError(('Energy-scaled refinement failed',convergence))
    root = Path(__file__).resolve().parents[1]
    audit = root/'data/initial_norm_energy_audit.json'
    report = {
        'kind':'exploratory floating-point quadrature; not a proof',
        'parameters':parameters,
        'time':0.,'mass2':1.,'quartic':1.,'vacuum':1.,
        'seed_coordinates':['u0','u1','r0','r1','r2','r3'],
        'seeds':seeds.tolist(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'previous_lean_audit_sha256':hashlib.sha256(audit.read_bytes()).hexdigest(),
        'checks':checks,'runs':runs,
        'energy_scaled_refinement_matrix_norms':convergence,
        'fixed_witness_coefficients_real_imag':[[float(z.real),float(z.imag)] for z in fixed],
        'fixed_witness_evaluations':evaluations,
        'limitations':[
            'Clock tails and quadrature errors have no certified interval enclosure.',
            'The seed coordinates and coefficients are floating-point numbers.',
            'A positive initial-minus-final difference is a numerical candidate counterexample only.',
            'Positive response on these subspaces does not prove positivity on the coherent span.',
            'No state-uniform lower energy bound, model change, or physical TOE is established.',
        ],
    }
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
        print(args.output,flush=True)
    else:
        print(json.dumps(report,indent=2,allow_nan=False),flush=True)


if __name__ == '__main__':
    main()

