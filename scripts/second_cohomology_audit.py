#!/usr/bin/env python3
"""Second cubical descent and exact finite-volume Ward completion.

No harmonic term is discarded. The final finite residual is explicitly
solved; locality requires quantitative control of that residual.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import scipy.sparse as sparse
import numpy as np
from local_cohomology_audit import (CubicalTorus, pack, unpack, divergence,
    field_strength, gradient, descend, jacobian_resolvent,
    RectangularOverlap, base_field, density, SPECIES, GAMMA5, radial_current)

def density_hessian(model,a,q,count=24):
    sp=model.operator(np.exp(1j*a),q);v=sp['vectors'];ev=sp['values'];n=model.n
    nodes,weights=np.polynomial.legendre.leggauss(count)
    out=np.zeros((n,4*n,4*n))
    for u,w in zip((nodes+1)/2,weights/2):
        angle=np.pi*u/2;t=np.tan(angle);dt=np.pi/2/np.cos(angle)**2
        r=(v/(1j*t-ev))@v.conj().T
        b=r.reshape(4,n,4,n).transpose(1,3,0,2)
        he=[];tails=[]
        for mu in range(4):
            phase=model.boundary[mu]*np.exp(1j*q*a[mu])
            he.extend(-1j*q*phase[:,None,None]*(np.array(GAMMA5,complex)@model.geom.plus[mu])[None,:,:])
            tails.extend(model.geom.previous[mu])
        he=np.array(he);heads=np.tile(np.arange(n),4);tails=np.array(tails);het=he.conj().transpose(0,2,1)
        # dR[k,x,y,a,d] = R[x,head] H'_k R[tail,y] + conjugate edge.
        dr=np.einsum('xkab,kbc,kycd->kxyad',b[:,heads],he,b[tails],optimize=True)
        dr+=np.einsum('xkab,kbc,kycd->kxyad',b[:,tails],het,b[heads],optimize=True)
        for mu in range(4):
            tail=model.geom.previous[mu];hh=he[mu*n:(mu+1)*n];hht=het[mu*n:(mu+1)*n]
            term=np.einsum('kxjab,jbc,jxca->xjk',dr,hh,b[tail],optimize=True)
            term+=np.einsum('xjab,jbc,kjxca->xjk',b,hh,dr[:,tail],optimize=True)
            term+=np.einsum('kxjab,jbc,jxca->xjk',dr[:,:,tail],hht,b,optimize=True)
            term+=np.einsum('xjab,jbc,kjxca->xjk',b[:,tail],hht,dr,optimize=True)
            # H'' along one phase twice: +iq times head-tail H', adjoint on reverse.
            h2=1j*q*hh;h2t=h2.conj().transpose(0,2,1)
            diag=np.einsum('xjab,jbc,jxca->xj',b,h2,b[tail],optimize=True)
            diag+=np.einsum('xjab,jbc,jxca->xj',b[:,tail],h2t,b,optimize=True)
            for j in range(n):term[:,j,mu*n+j]+=diag[:,j]
            out[:,mu*n:(mu+1)*n,:]+=-q/np.pi*w*dt*term.real
    return out


class DoubleComplex:
    """Two commuting cubical boundaries; each homotopy uses the other anchor."""
    def __init__(self, lengths):
        self.torus = CubicalTorus(lengths)
        self.sites = list(itertools.product(*(range(n) for n in lengths)))
        self.n = len(self.sites)
        self.sizes = {k: len(v)*self.n for k, v in self.torus.cells.items()}
        self.boundaries = {k: self.boundary_matrix(k) for k in range(1, 5)}

    def boundary_matrix(self, degree):
        torus = self.torus
        index = {cell: i for i, cell in enumerate(torus.cells[degree-1])}
        lookup = {x: i for i, x in enumerate(self.sites)}
        rows, cols, values = [], [], []
        for c, cell in enumerate(torus.cells[degree]):
            for x, site in enumerate(self.sites):
                for position, mu in enumerate(cell):
                    face = cell[:position]+cell[position+1:]
                    tail = list(site)
                    tail[mu] = (tail[mu]-1) % torus.lengths[mu]
                    rows.extend([index[face]*self.n+x,
                                 index[face]*self.n+lookup[tuple(tail)]])
                    cols.extend([c*self.n+x]*2)
                    values.extend([(-1)**position, -(-1)**position])
        return sparse.csr_matrix((values, (rows, cols)),
                                 shape=(self.sizes[degree-1], self.sizes[degree]))

    def hx(self, matrix, degree):
        answer = np.zeros((self.sizes[degree+1], matrix.shape[1]))
        for column in range(matrix.shape[1]):
            if np.any(matrix[:, column]):
                answer[:, column] = pack(self.torus.homotopy(
                    unpack(self.torus, matrix[:, column], degree), self.sites[column % self.n]))
        return answer

    def hy(self, matrix, degree):
        return self.hx(matrix.T, degree).T

    def dx(self, matrix, degree):
        return self.boundaries[degree]@matrix

    def dy(self, matrix, degree):
        return (self.boundaries[degree]@matrix.T).T

    def phi_map(self):
        """Phi = S vec(j); used to contract the actual density Hessian."""
        edges, faces = self.sizes[1], self.sizes[2]
        result = np.zeros((faces, self.n*edges))
        eye = np.eye(edges)
        for x, center in enumerate(self.sites):
            for e in range(edges):
                result[:, x*edges+e] = pack(self.torus.homotopy(
                    unpack(self.torus, eye[e], 1), center))
        return result

    def second_descent(self, j):
        """Exact J = dx dy L + dx Q + K, with the diagonal top-form retained.

        J has bidegree (2,1). T:(3,1), U:(4,0), V:(4,1), W:(3,1),
        L:(3,2). The diagonal M, and the K/S/Q remainders, are never zeroed.
        """
        t = self.hx(j, 2)
        k = j-self.dx(t, 3)
        dyt = self.dy(t, 1)
        u = self.hx(dyt, 3)
        s = dyt-self.dx(u, 4)
        g = u.sum(axis=1)
        m = np.diag(g)
        v = self.hy(u-m, 0)
        w = t-self.dx(v, 4)
        ell = self.hy(w, 1)
        q = w-self.dy(ell, 2)
        reconstructed = self.dx(self.dy(ell, 2), 3)+self.dx(q, 3)+k
        identities = dict(
            factorization_error=float(np.linalg.norm(j-reconstructed)),
            top_centering_error=float(np.linalg.norm(self.dy(v, 1)-(u-m))),
            cycle_remainder_error=float(np.linalg.norm(self.dy(w, 1)-s-self.dx(m, 4))),
            top_gradient_error=float(np.linalg.norm(self.dx(g[:, None], 4)+s.sum(axis=1)[:, None])))
        assert max(identities.values()) < 1e-10
        return ell, dict(**identities, k_norm=float(np.linalg.norm(k)),
                         s_norm=float(np.linalg.norm(s)), q_norm=float(np.linalg.norm(q)),
                         top_diagonal_norm=float(np.linalg.norm(g)),
                         input_x_boundary=float(np.linalg.norm(self.dx(j, 2))),
                         input_y_boundary=float(np.linalg.norm(self.dy(j, 1))))

    def cap_current(self, three_form, curvature):
        """Pointwise <d t,F> = div cap(t,F), when the Bianchi identity holds."""
        t = unpack(self.torus, three_form, 3)
        f = unpack(self.torus, curvature, 2)
        out = self.torus.zero(1)
        for cell, a in t.items():
            for position, mu in enumerate(cell):
                face = cell[:position]+cell[position+1:]
                out[(mu,)] += (-1)**position*a*np.roll(f[face], 1, axis=mu)
        return pack(out)

    def finite_primitive(self, residual):
        """Average all anchors: exact divergence and translation covariance.

        Each summation acts on a volume-small residual, and averaging keeps
        the same absolute row-sum bound as any one summation.
        """
        source=unpack(self.torus,residual,0)
        answer=np.zeros(self.sizes[1])
        for center in self.sites:
            answer+=pack(self.torus.homotopy(source,center))
        return answer/self.n

    def finish(self, potential, j_first, j_second, actual_density):
        first = descend(self.torus, j_first, potential)
        ell, audit = self.second_descent(j_second)
        f = field_strength(self.torus, potential)
        t = ell@f
        second = self.cap_current(t, f)
        phi_div = self.dx(t[:, None], 3).ravel()
        paired = (phi_div*f).reshape(6, self.n).sum(axis=0)
        cap_error = float(np.linalg.norm(divergence(self.torus, second)-paired))
        phi_remainder = first['phi']-phi_div
        expected = (phi_remainder*f).reshape(6, self.n).sum(axis=0)+first['winding']
        residual = actual_density-divergence(self.torus, first['h']+second)
        finite = self.finite_primitive(residual)
        full = first['h']+second+finite
        ward_error = float(np.linalg.norm(divergence(self.torus, full)-actual_density))
        assert cap_error < 1e-11
        assert ward_error < 1e-10
        return full, dict(first_current_norm=float(np.linalg.norm(first['h'])),
                          second_current_norm=float(np.linalg.norm(second)),
                          residual_norm=float(np.linalg.norm(residual)),
                          residual_total=float(residual.sum()),
                          finite_completion_norm=float(np.linalg.norm(finite)),
                          ward_error=ward_error, bianchi_cap_error=cap_error,
                          residual_formula_error=float(np.linalg.norm(residual-expected)),
                          second_descent=audit)


def integrated_jets(model, a, field_nodes=4, resolvent_nodes=32):
    """Unweighted and phase-weighted first and second density kernels.

    j2 = S int (1-t) a''(tA) dt;
    j2w = S int (1-t)^2/2 a''(tA) dt. The latter already integrates
    the two field-strength factors in the scalar phase correction.
    """
    complex_ = DoubleComplex(model.lengths)
    smap = complex_.phi_map()
    n, e = model.n, 4*model.n
    j1, j1w = np.zeros((n,e)), np.zeros((n,e))
    j2, j2w = np.zeros((6*n,e)), np.zeros((6*n,e))
    avg = np.zeros(n)
    minimum_gap = np.inf
    nodes, weights = np.polynomial.legendre.leggauss(field_nodes)
    for t, weight in zip((nodes+1)/2, weights/2):
        for _, charge, multiplicity in SPECIES:
            jac, sp = jacobian_resolvent(model, t*a, charge, resolvent_nodes)
            hess = density_hessian(model, t*a, charge, resolvent_nodes)
            phijac = smap@hess.reshape(n*e,e)
            j1 += multiplicity*weight*jac
            j1w += multiplicity*weight*(1-t)*jac
            j2 += multiplicity*weight*(1-t)*phijac
            j2w += multiplicity*weight*(1-t)**2/2*phijac
            avg += multiplicity*weight*density(model, sp['p'], charge)
            minimum_gap = min(minimum_gap, sp['gap'])
        print('field node', float(t), 'done', flush=True)
    anomaly = sum(m*density(model, model.operator(np.exp(1j*a), q)['p'], q)
                  for _, q, m in SPECIES)
    phi = smap@j1.ravel()
    phiw = smap@j1w.ravel()
    phi_error = float(np.linalg.norm(j2@a.ravel()-phi))
    phiw_error = float(np.linalg.norm(j2w@a.ravel()-phiw))
    assert phi_error < 1e-10
    assert phiw_error < 1e-10
    h, raw = complex_.finish(a, j1, j2, anomaly)
    hw, weighted = complex_.finish(a, j1w, j2w, avg)
    return dict(current=h, weighted_current=hw, phase=-float(a.ravel()@hw),
                anomaly=anomaly, average_density=avg,
                audit=dict(lengths=model.lengths, field_nodes=field_nodes,
                           resolvent_nodes=resolvent_nodes, sampled_kernel_gap=minimum_gap,
                           second_radial_identity_error=phi_error,
                           weighted_second_radial_identity_error=phiw_error,
                           anomaly_norm=float(np.linalg.norm(anomaly)),
                           first_and_second=raw, phase_weighted=weighted))


def hessian_checks():
    model=RectangularOverlap((2,)*4)
    a=base_field(model)
    rng=np.random.default_rng(31)
    e,f=[rng.normal(size=a.shape) for _ in range(2)]
    sp=model.operator(np.exp(1j*a),6)
    _,_,dp=model.projector_jet(np.exp(1j*a),6,sp,e,f)
    exact=6*np.diag(dp).real.reshape(4,model.n).sum(axis=0)
    rows=[]
    for count in [24,32]:
        hess=density_hessian(model,a,6,count)
        result=np.einsum('xjk,j,k->x',hess,e.ravel(),f.ravel())
        rows.append(dict(nodes=count,error=float(np.linalg.norm(result-exact)),
                         mixed_symmetry_error=float(np.linalg.norm(hess-hess.transpose(0,2,1)))))
    assert rows[-1]['error'] < 1e-10
    free=np.zeros_like(a)
    base_hessian=density_hessian(model,free,1,32)
    free_charge_checks=[]
    for charge in [-4,6]:
        actual=density_hessian(model,free,charge,32)
        error=float(np.linalg.norm(actual-charge**3*base_hessian))
        assert error < 1e-10
        free_charge_checks.append(dict(charge=charge,error=error))
    cubic_sum=sum(m*q**3 for _,q,m in SPECIES)
    assert cubic_sum==0
    free_jac,_=jacobian_resolvent(model,free,1,32)
    assert np.linalg.norm(free_jac)<1e-12
    return dict(reference_norm=float(np.linalg.norm(exact)), quadrature=rows,
                free_charge_scaling=free_charge_checks,cubic_charge_sum=cubic_sum,
                free_first_derivative_norm=float(np.linalg.norm(free_jac)))


def algebra_checks():
    rows=[]
    for lengths in [(2,2,2,2),(3,3,3,3)]:
        c=DoubleComplex(lengths)
        rng=np.random.default_rng(45)
        j=rng.integers(-2,3,size=(6*c.n,4*c.n)).astype(float)
        _, checks=c.second_descent(j)
        assert max(checks[x] for x in ['factorization_error','top_centering_error',
                                      'cycle_remainder_error','top_gradient_error']) == 0
        a=rng.integers(-3,4,size=(4,c.n))
        f=field_strength(c.torus,a)
        t=rng.integers(-3,4,size=4*c.n)
        current=c.cap_current(t,f)
        paired=((c.boundaries[3]@t)*f).reshape(6,c.n).sum(axis=0)
        assert np.array_equal(divergence(c.torus,current),paired)
        source=rng.integers(-4,5,size=c.n).astype(float)
        source[0]-=source.sum()
        base=c.finite_primitive(source).reshape(4,*lengths)
        for mu in range(4):
            shifted=np.roll(source.reshape(lengths),1,axis=mu).ravel()
            actual=c.finite_primitive(shifted).reshape(4,*lengths)
            expected=np.roll(base,1,axis=mu+1)
            assert np.linalg.norm(actual-expected)<1e-12
        assert np.linalg.norm(divergence(c.torus,base.ravel())-source)<1e-12
        rows.append(dict(lengths=lengths,exact_integer_identities=True,
                         averaged_finite_solver_translation_checked=True))
    return rows


def synthetic_class_checks():
    """Distinguish a local divergence from the nonzero F wedge F class.

    Every operation is on small integer-valued arrays stored exactly in
    float64. Sparse boundaries avoid cubic dense matrix products.
    """
    rows=[]
    for length in [3,4,5]:
        c=DoubleComplex((length,)*4)
        n=c.n
        face_index={cell:i for i,cell in enumerate(c.torus.cells[2])}
        lookup={x:i for i,x in enumerate(c.sites)}
        local=sparse.csr_matrix((np.ones(n),(np.arange(n),
                                face_index[(1,2)]*n+np.arange(n))),shape=(4*n,6*n))
        jlocal=(c.boundaries[3]@local@c.boundaries[2].T).toarray()
        ell, finite=c.second_descent(jlocal)
        error=float(np.linalg.norm(jlocal-c.dx(c.dy(ell,2),3)))
        star_rows,star_cols,values=[],[],[]
        for cell in c.torus.cells[2]:
            complement=tuple(mu for mu in range(4) if mu not in cell)
            permutation=cell+complement
            sign=(-1)**sum(permutation[i]>permutation[j] for i in range(4) for j in range(i+1,4))
            for x,site in enumerate(c.sites):
                tail=tuple((value-1)%length if mu in cell else value for mu,value in enumerate(site))
                star_rows.append(face_index[cell]*n+x)
                star_cols.append(face_index[complement]*n+lookup[tail])
                values.append(sign)
        star=sparse.csr_matrix((values,(star_rows,star_cols)),shape=(6*n,6*n))
        jtop=(star@c.boundaries[2].T).toarray()
        ell, top=c.second_descent(jtop)
        top_error=float(np.linalg.norm(jtop-c.dx(c.dy(ell,2),3)))
        row=dict(length=length,local_divergence_remainder=error,
                 local_diagonal_norm=finite['top_diagonal_norm'],
                 topological_remainder=top_error,top_diagonal_norm=top['top_diagonal_norm'],
                 top_x_boundary=top['input_x_boundary'],top_y_boundary=top['input_y_boundary'])
        assert top['input_x_boundary']==0
        assert top['input_y_boundary']==0
        if length>=4:
            assert error==0
            assert finite['top_diagonal_norm']==0
            assert top_error>0
            assert top['top_diagonal_norm']==length**2
        rows.append(row)
        print('synthetic',row,flush=True)
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('data/second_cohomology_audit.json'))
    parser.add_argument('--skip-gauge-check',action='store_true')
    args=parser.parse_args()
    report=dict(scope='Second descent and exact finite Ward completion; locality of final residual requires its own bound',
                algebra_checks=algebra_checks(), hessian_checks=hessian_checks(),
                synthetic_classes=synthetic_class_checks())
    model=RectangularOverlap((2,)*4)
    a=np.random.default_rng(2026090906).uniform(-.018,.018,(4,model.n))
    base=integrated_jets(model,a)
    report['base']=base['audit']
    report['phase']=base['phase']
    if not args.skip_gauge_check:
        omega=np.random.default_rng(2026090907).uniform(-2,2,model.n)
        bomega=gradient(model,omega)
        shifted=integrated_jets(model,a+bomega)
        jrad=sum(m*radial_current(model,a,q,bomega,count=8)['current'] for _,q,m in SPECIES)
        shift=shifted['phase']-base['phase']
        expected=-float(omega@base['average_density'])
        corrected=jrad+float(omega@base['anomaly'])+shift
        checks=dict(current_gauge_error=float(np.linalg.norm(base['current']-shifted['current'])),
                    phase_change=shift,predicted_phase_change=expected,
                    phase_change_error=abs(shift-expected), corrected_ward_error=abs(corrected))
        assert checks['current_gauge_error'] < 1e-10
        assert checks['phase_change_error'] < 1e-10
        assert checks['corrected_ward_error'] < 1e-10
        report['gauge_and_phase']=checks
    refined=integrated_jets(model,a,field_nodes=6)
    report['quadrature_refinement']=dict(
        current_error=float(np.linalg.norm(base['current']-refined['current'])),
        weighted_current_error=float(np.linalg.norm(base['weighted_current']-refined['weighted_current'])),
        phase_error=abs(base['phase']-refined['phase']),
        refined_audit=refined['audit'])
    assert report['quadrature_refinement']['current_error'] < 1e-10
    assert report['quadrature_refinement']['phase_error'] < 1e-12
    report['arithmetic']='Float64 diagnostics; integer-valued cubical controls stay exactly representable; not interval certification'
    root=Path(__file__).resolve().parents[1]
    sources=['scripts/second_cohomology_audit.py','scripts/local_cohomology_audit.py',
             'scripts/radial_measure_audit.py','scripts/positive_measure_audit.py',
             'scripts/gauge_dressed_measure_audit.py','scripts/chiral_measure_audit.py',
             'scripts/overlap_chirality_audit.py','UnifiedTheory/Audit/KFCausalSecondCohomology.lean']
    report['source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest()
                             for p in sources if (root/p).exists()}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':
    main()
