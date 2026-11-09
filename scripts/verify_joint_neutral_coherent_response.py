#!/usr/bin/env python3
"""Independently recompute selected coupled-kernel witnesses at high precision.

This checks floating diagnostics, not a Lean theorem or an interval bound.
The high-precision derivative is taken through a fresh complex clock solve
and a Gaussian-moment recurrence, independently of the producer's analytic
derivative. It verifies a finite candidate Rayleigh quotient, not a uniform
constant or coverage of arbitrary polynomials and Hamiltonian evolution.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import mpmath as mp
import numpy as np


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unpack(value):
    return np.asarray(value['real'])+1j*np.asarray(value['imag'])


def number(x):
    return mp.mpf(str(x))


def complex_numbers(value):
    return [mp.mpc(number(a),number(b)) for a,b in zip(value['real'],value['imag'])]


def clock(eps,h,s):
    target=mp.exp(s)+eps*s-mp.j*h/2
    guess=s-mp.j*h/(2*(mp.exp(s)+eps))
    z=mp.findroot(lambda x:mp.exp(x)+eps*x-target,guess)
    assert abs(mp.exp(z)+eps*z-target)<mp.mpf('1e-65')
    return mp.exp((z-s)/2)


def moments(mean,variance):
    result=[mp.mpf(1),mean]
    for k in range(2,5):
        result.append(mean*result[-1]+(k-1)*variance*result[-2])
    return result


def kernel(alpha,beta,wi,wj,bi,bj,r):
    a=alpha*(mp.conj(r)**2/wi+r**2/wj)/2
    b=alpha*(mp.conj(r)**2*wi+r**2*wj)/2
    c=b-8*beta*mp.im(r)**2
    assert min(mp.re(a),mp.re(b),mp.re(c),beta)>0
    dx=mp.conj(bi)+bj
    dy=2*mp.j*mp.im(r)*(bj-mp.conj(bi))
    mx=dx/(4*beta);my=dy/(2*c)
    Mx=moments(mx,1/(4*beta));My=moments(my,1/(2*c))
    L=3-2*mp.re(r)
    def field_moment(k):
        return sum(math.comb(k,j)*L**(k-j)*Mx[j]*My[k-j] for j in range(k+1))
    factor=1+field_moment(2)/2+field_moment(4)/4
    normalization=-(mp.re(bi)**2+mp.re(bj)**2)/(4*beta)
    gaussian=mp.pi/(4*a)*mp.sqrt(mp.pi/b)*mp.sqrt(mp.pi/c)*mp.sqrt(mp.pi/(2*beta))
    return gaussian*mp.exp(dx**2/(8*beta)+dy**2/(4*c)+normalization)*factor


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    report=json.loads(args.report.read_text())
    assert all(digest(root/p)==h for p,h in report['source_sha256'].items())
    parent=report['parent_report']
    assert parent['sha256']=='047e2d5021bd9db56d086d4bde86c593bfd113751493caf4cfc70ba778c35598'
    assert digest(root/parent['path'])==parent['sha256']
    assert report['rank_truncation'] is False and report['conditioning_floor']==1e-9
    assert report['test_count']==len(report['records'])==900
    assert report['rejected_cases']==sum(bool(item.get('rejected_condition')) for item in report['records'])
    valid=[v for v in report['records'] if not v.get('rejected_condition')]
    for v in valid:
        assert v['alpha']==1/(2*abs(v['h'])) and v['beta']==v['alpha']/32
        assert v['epsilon']>0 and abs(v['h'])<=math.pi*v['epsilon']/3
        assert v['condition']<1e9 and v['hermitian_error']<1e-10 and v['eigen_residual']<1e-10
    winner=report['largest_observed'];p=winner['parameters']
    assert winner['result']['max_slope']==max(v['max_slope'] for v in valid)
    K=unpack(winner['gram']);D=unpack(winner['derivative']);coeff=unpack(winner['coefficients'])
    E=float(np.vdot(coeff,K@coeff).real);rate=float(np.vdot(coeff,D@coeff).real)
    assert E>0 and abs(rate/E-winner['result']['max_slope'])<2e-8
    mp.mp.dps=80
    eps,h,s=map(number,[p['epsilon'],p['h'],p['s']])
    alpha,beta=map(number,[p['alpha'],p['beta']])
    widths=list(map(number,winner['widths']))
    sources=complex_numbers(winner['sources']);c=complex_numbers(winner['coefficients'])
    def energy(t):
        r=clock(eps,h,t);value=mp.mpf(0)
        for i in range(len(c)):
            diag=kernel(alpha,beta,widths[i],widths[i],sources[i],sources[i],r)
            assert abs(mp.im(diag))<mp.mpf('1e-65')
            value+=abs(c[i])**2*mp.re(diag)
            for j in range(i+1,len(c)):
                value+=2*mp.re(mp.conj(c[i])*c[j]*kernel(alpha,beta,widths[i],widths[j],sources[i],sources[j],r))
        return value
    e=energy(s);d=mp.diff(energy,s);assert e>0
    ratio=d/e
    energy_error=float(abs(e-number(E))/e)
    slope_error=float(abs(ratio-number(winner['result']['max_slope'])))
    assert energy_error<2e-7 and slope_error<2e-8
    print('High precision finite witness:',mp.nstr(ratio,22),flush=True)
    o=report['radial_obstruction_profile']
    z=clock(mp.mpf(1),-mp.mpf(1)/64,mp.mpf(0))
    source=4+mp.j*((mp.mpf(2)/3)/(2*mp.im(z)))
    # Freeze the source at s=0 when differentiating the actual clock curve.
    def obstruction(t):
        return mp.re(kernel(mp.mpf(32),mp.mpf(1),mp.mpf(1),mp.mpf(1),source,source,
                            clock(mp.mpf(1),-mp.mpf(1)/64,t)))
    oe=obstruction(mp.mpf(0));od=mp.diff(obstruction,mp.mpf(0));oratio=od/oe
    obstruction_error=float(abs(oratio-number(o['logarithmic_derivative'])))
    assert oe>0 and oratio<0 and obstruction_error<2e-12
    print('High precision radial-obstruction profile full slice slope:',mp.nstr(oratio,22),flush=True)
    result=dict(report_sha256=digest(args.report),source_sha256=report['source_sha256'],
                mpmath_precision=80,verified_finite_candidate_slope=mp.nstr(ratio,50),
                energy_relative_error=energy_error,slope_absolute_error=slope_error,
                radial_obstruction_profile_slope=mp.nstr(oratio,50),obstruction_slope_absolute_error=obstruction_error,
                scope=__doc__,passed=True)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('Independent finite diagnostic verification passed; no uniform bound or counterexample certified.')


if __name__=='__main__':
    main()
