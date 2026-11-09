#!/usr/bin/env python3
"""Exhaustive finite-basis checks for the centered homotopy locality proof.

Exact bounded int64 arithmetic: coefficients, support, and contraction.
This checks the stated finite volumes, not the infinite-volume theorem.
"""
import hashlib
import itertools
import json
from pathlib import Path
import numpy as np
from local_cohomology_audit import CubicalTorus, pack, unpack


def check(length):
    torus=CubicalTorus((length,)*4)
    sites=list(itertools.product(range(length),repeat=4))
    n=len(sites)
    reports=[]
    for center in [(0,)*4,(length//2,)*4]:
        radius=np.array([max(min((x[k]-center[k])%length,
                                (center[k]-x[k])%length) for k in range(4)) for x in sites])
        for degree in range(5):
            count=len(torus.cells[degree])*n
            out_count=len(torus.cells.get(degree+1,[]))*n
            row_sum=np.zeros(out_count,dtype=np.int64)
            maximum_coefficient=0
            for column in range(count):
                vector=np.zeros(count,dtype=np.int64)
                vector[column]=1
                chain=unpack(torus,vector,degree)
                hchain=torus.homotopy(chain,center)
                filled=pack(hchain)
                if out_count:
                    assert np.all(np.abs(filled)<=1)
                    maximum_coefficient=max(maximum_coefficient,int(np.max(np.abs(filled))))
                    nz=np.flatnonzero(filled)
                    assert np.all(radius[nz%n]<=radius[column%n])
                    row_sum+=np.abs(filled)
                dh=torus.boundary(hchain)
                hd=torus.homotopy(torus.boundary(chain),center)
                projection=torus.project(chain,center)
                for cell in chain:
                    assert np.array_equal(dh.get(cell,0)+hd.get(cell,0),chain[cell]-projection[cell])
            max_row_sum=int(row_sum.max()) if out_count else 0
            assert max_row_sum<=16*n
            reports.append(dict(center=center,degree=degree,basis_vectors=count,
                                maximum_coefficient=maximum_coefficient,
                                maximum_absolute_row_sum=max_row_sum,
                                coefficient_bound=1,row_sum_bound=16*n,
                                centered_box_preserved=True,contraction_exact=True))
    print('All bases and centered supports pass at length',length,flush=True)
    return dict(length=length,checks=reports)


def main():
    rows=[check(length) for length in [3,4]]
    root=Path(__file__).resolve().parents[1]
    sources=['scripts/cohomology_locality_audit.py','scripts/local_cohomology_audit.py',
             'scripts/radial_measure_audit.py','scripts/positive_measure_audit.py',
             'scripts/gauge_dressed_measure_audit.py','scripts/chiral_measure_audit.py',
             'scripts/overlap_chirality_audit.py']
    result=dict(arithmetic='Exact bounded int64, no overflow',
                scope='Exhaustive finite-basis controls; the uniform locality theorem is analytic',
                volumes=rows,source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources})
    out=root/'data/cohomology_locality_audit.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('Wrote',out,flush=True)


if __name__=='__main__':
    main()
