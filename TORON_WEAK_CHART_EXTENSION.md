# Weak-field descent around every flat holonomy

Date: 2026-09-10

The nonzero flat-holonomy Hessian in
[COMPACT_MEASURE_HOLONOMY.md](COMPACT_MEASURE_HOLONOMY.md) is now controlled
by a finite-volume locality argument. A gauge transformation places the
holonomy on seams far from the density site. A closed resolvent chain that
detects the change must reach a seam and return. The uniform Wilson gap
then gives exponential suppression in lattice size.

This extends the existing gauge-invariant Ward primitive and scalar phase
correction to weak fluctuations about **every flat reference**, periodically
in the four holonomy angles. The construction retains all finite-volume
terms. Its locality argument is analytic, with nine supporting Lean results
and independent operator checks; it is not a fully formalized theorem.

The parameter space still has redundant descriptions of a physical link
field. Descending the complete connection to that physical field space,
with locality and all intended symmetries, remains a further obligation.
This does not complete the compact interacting measure, non-Abelian theory,
physical continuum, or TOE.

## 1. Domain and the flat first jet

Work on `L^4` tori, with the repository's periodic or antiperiodic-time
fermion boundary condition, supplied integer charges `|q|<=6`, and

\[
B_\mu(\theta)=\theta_\mu/L,\qquad
U(\theta,A)=\exp[i(B(\theta)+A)],\qquad
\|A\|_\infty\le\epsilon<1/24.
\]

Here `theta` is a four-vector of angles. The free gap is at least one for
every flat reference, so `H_q(B(theta)+tA)` has gap
`h0=1-24 epsilon>0` uniformly in `theta` and `0<=t<=1`.
The index is zero along this contraction. The physical Dirac gap is unused.
Gauge orbits of these bounded representatives are included by covariance.

Write the anomaly as `rho_q=q tr_spin(P_q-Pbar)(x,x)`, and let primes denote
derivatives in arbitrary individual link-potential directions. At every flat
reference,

\[
\rho_q(B)=0,\qquad \rho_q'(B)=0.
\]

For the first equality, every momentum block of `P_q(B)` has trace two.
For the second, the free `H(p)` and every momentum-matrix element of a
single link vertex lie in the complex span of the five Clifford generators.
Their traces and all triple traces vanish. In the paired resolvent integral,
the spin numerator for the first derivative is

\[
(it+H_p)V_{pp'}(it+H_{p'})+
(-it+H_p)V_{pp'}(-it+H_{p'})
=2(H_pV_{pp'}H_{p'}-t^2V_{pp'}).
\]

Its trace is zero, including when `p != p'`; denominators are even in `t`.
Fourier transformation therefore gives zero first density derivative for
every site and every link direction. This is stronger than vanishing of
derivatives restricted to the flat submanifold. Exact spin traces and
independent dense Jacobians check the argument.

## 2. Move the holonomy to a distant seam

Fix a density site `x`. Choose each periodic coordinate `y_mu(z)` as the
integer representative centered on `x_mu`. On an edge,

\[
y_\mu(z)-y_\mu(z-\hat\mu)=1-L c_\mu(z),
\qquad c_\mu(z)\in\{0,1\}.
\]

The gauge phase `chi(z)=-sum_mu theta_mu y_mu(z)/L` transforms
`B(theta)+A` to `A+theta_mu c_mu` on direction `mu`. Hence the transformed
Wilson kernel equals `H_q(A)` away from four seams. Their edge endpoints
are at maximum-coordinate distance at least `ceil(L/2)-1 >= L/2-1` from `x`.
The fermion boundary signs are retained on both sides of this identity.

Both kernels have the gap `h0`: the seam kernel is unitarily equivalent to
the original uniform-holonomy kernel. A large seam phase does not spoil this
argument. No small-norm expansion in the seam perturbation is used.

Let `R_theta=(it-H_seam)^(-1)` and `R_0=(it-H_q(A))^(-1)`. Exactly,

\[
R_\theta-R_0=R_\theta(H_{\rm seam}-H_q(A))R_0.
\]

Use the previous weighted-resolvent bound with
`alpha=log(1+h0/8)>0`:

\[
\|R_t(z,w)\|\le
2(h_0^2+t^2)^{-1/2}e^{-\alpha d_1(z,w)}.
\]

An anomaly derivative is a finite sum of closed chains of resolvents and
edge vertices. Telescope the difference between the seam and zero-holonomy
chains. Every term has either the displayed resolvent difference or a
changed differentiated vertex. In both cases the closed chain visits a
seam. The total distance travelled by its resolvents is at least
`L-O(m+1)` for fixed field-derivative order `m`: the chain must go from `x`
to the seam and return, with only finitely many unit edges supplied by its
vertices. This statement also covers derivatives whose specified edges
already lie on a seam.

Summing seam locations contributes a polynomial in `L`; each fixed-order
resolvent integral is convergent. For `m=0`, taking the difference already
introduces two resolvents and makes the integral convergent. Thus, for
each fixed `m`, uniformly in `theta`, bounded `A`, `x`, and all derivative
edges,

\[
\left|\rho_q^{(m)}(B(\theta)+A)-\rho_q^{(m)}(A)\right|
\le C_m(1+L)^{p_m}e^{-\beta L},\qquad \beta>0.
\tag{1}
\]

Constants depend on the fixed derivative order, charges, and gap, not the
volume or holonomy. One may decrease the exponent, for example to
`beta=alpha/4`, to absorb fixed endpoint conventions. Fixed orders of
`theta` differentiation obey the same type of estimate: in the seam gauge,
each such derivative inserts a bounded seam vertex. Additional seam sums
only alter the polynomial. The gauge transformation is held fixed for field
derivatives; scalar gauge invariance justifies choosing its center separately
for each density coefficient being bounded.

Equation (1) applies at **weak interacting fields**, not just at `A=0`.
It is the main input for the extension below. The finite scan tests one
coefficient and does not by itself prove this uniform estimate.

## 3. The nonzero Hessian is retained and controlled

At `theta=0`, the summed second derivative vanishes by the supplied cubic
charge cancellation. At nonzero holonomy it need not vanish, but

\[
\sum_q m_q\rho_q''(B(\theta))
=\sum_q m_q\bigl[\rho_q''(B(\theta))-\rho_q''(0)\bigr]
\]

is exponentially small in volume in the sense of (1). The old exact-zero
argument is replaced by a quantitative bound. This does not remove the
single-charge anomaly: its zero-holonomy quadratic coefficient can remain
nonzero as `L` grows.

Run exactly the previous first and second cubical descents, replacing their
radial path `tA` by `B(theta)+tA`. In particular,

\[
j_{1,\theta}=\int_0^1\rho'(B+tA)\,dt,\qquad
J_{2,\theta}=S\int_0^1(1-t)\rho''(B+tA)\,dt.
\]

The flat first-jet result gives the exact identities
`rho(B+A)=j1_theta A` and `S vec(j1_theta)=J2_theta A`.
The same Bianchi cap product and averaged finite primitive therefore give

\[
h_\theta=h_{1,\theta}+h_{2,\theta}+\bar H_0R_{{\rm fin},\theta},
\qquad B_{\rm grad}^{T}h_\theta=\rho(B(\theta)+A).
\tag{2}
\]

Here `B_grad` is the discrete gradient, distinct from the flat potential
`B(theta)`. Every retained remainder and the true finite density are used
in the executable; none is projected to zero to force a test to pass.

There are two ways to see why the old locality proof survives. First, its
top coefficient now starts at a volume-small value `g_theta(0)`. The old
distant-derivative estimate implies
`|g_theta(A)| <= |g_theta(0)| + sum_e |A_e| sup_t |partial_e g_theta(tA)|`,
which remains volume-small. Exact zero at the base was stronger than needed.

More directly, (1) bounds the differences of **all** input density kernels
between the new and old descents. The implemented homotopies and finite
solver have polynomial row bounds, all orientations are finite, and the
explicit field-strength factors are bounded. Every fixed field derivative
of `h_theta(A)-h_0(A)` is consequently volume-small. The earlier proof gives
uniform spatial locality for `h_0`. Absorbing the polynomial and using
`d_1(x,y)<=2L` turns the new remainder into a spatial exponential bound.
This proves locality of (2) in fluctuation directions, uniform in the flat
reference, with the same growing-four-torus scope as the original proof.

## 4. Phase correction, periodicity, and the missing reference component

The scalar correction is still

\[
C_\theta(A)=-\int_0^1\langle A,h_\theta(tA)\rangle\,dt.
\]

Its weighted kernels use `(1-t)` for the first derivative and
`(1-t)^2/2` for the second. The corrected fluctuation Ward equation and
finite gauge phase change hold exactly as before:

\[
C_\theta(A+B_{\rm grad}\omega)-C_\theta(A)
=-\left\langle\omega,\int_0^1\rho(B(\theta)+tA)\,dt\right\rangle.
\]

Shifting `theta -> theta+2pi n` is the same fixed winding gauge
transformation along the entire radial path. The density kernels are
invariant, so `h_theta` and `C_theta` are exactly periodic in `theta`.
The previous paired determinant orientation supplies the compatible flat
reference phase. This glues these particular holonomy identifications.

Allowing the reference itself to vary requires a further component of the
connection. Let `F_U(eta,zeta)=i Tr P[P'_eta,P'_zeta]`, summed over species.
The radial frame based on the horizontal flat determinant section has

\[
\mathcal L_{\rm rad}(\delta\theta,\delta A)
=\int_0^1F_{B(\theta)+tA}
       \bigl(A,\delta B+t\delta A\bigr)\,dt,
\qquad \delta B_\mu=\delta\theta_\mu/L.
\tag{3}
\]

This follows by pulling the curvature back through the contraction and
integrating its radial component; the base determinant connection is zero.
The `delta B` term has **no factor of t**. Omitting it would fail when the
flat reference moves. Adding the full differential `dC_theta` preserves
curvature, including mixed reference/fluctuation components. Direct Kato
frame transport checks the nonzero reference component of (3).

The remaining redundancy is more general than integer winding. The pairs
`(theta,A)` and `(theta+delta,A-delta/L)` represent the same link field.
This work does not prove that the completed connection descends through
that redundancy with local transition phases. A canonical decomposition,
its response under arbitrary link variations, and the required lattice
symmetries must still be supplied or their effects rigorously cancelled.
Equations (2)–(3) are a construction on the parametrized weak charts, not a
finished measure on the physical compact field space. Nonzero flux sectors
and the non-Abelian/physical continuum obligations also remain open.

## 5. Evidence and formal boundary

The new Fourier evaluator computes selected density Hessian coefficients
using only small spin resolvent blocks between the density site and four
edge endpoints. It avoids a dense `(4V)^2` matrix. On `3^4`, it agrees with
the independent dense projector Hessian to `1.41e-16`. It retains the
antiperiodic wrap signs by using integer displacements rather than dropping
them modulo the lattice size.

For the fixed probe and angles recorded in the script:

| L | Summed hypercharge Hessian coefficient | Largest change after division by q^3 |
| ---: | ---: | ---: |
| 4 | -2.69252e-3 | 2.68410e-5 |
| 8 | -4.86248e-5 | 4.33963e-7 |
| 12 | -1.25829e-6 | 1.10991e-8 |
| 16 | -4.20810e-8 | 3.68601e-10 |

At `L=16`, the zero-toron charge-one coefficient is `8.11772e-5`.
The charge-six resolvent quadrature changes by about `6.94e-18` when
increased from 48 to 64 nodes. These are finite numerical diagnostics of
the decay mechanism; no exponent is inferred solely by fitting this table.

On a seeded weak `2^4` field about nonzero holonomy, the full Ward residual
is `5.56e-14`, current periodicity error `7.27e-14`, gauge covariance error
`6.81e-14`, and finite gauge phase error `2.23e-14`. The scalar correction
is nonzero, about `-1.61888e-6`. The top diagonal and finite residual are
substantial on this small volume and are explicitly retained.
The reference component in (3) is about `3.60378e-5`; 32, 64, and 128
transport steps give errors `4.04e-10`, `1.03e-10`, and `2.70e-11`.

The nine Lean results prove the inverse-kernel difference, even resolvent
numerator, uniform-to-seam edge identity, closed-chain distance and
exponential implications, subtraction of the common charge reference and
its bound, transport from a small base, and the two terms in (3).
The analytic spectral estimates, actual cubical operators, and differential
bundle construction are not wholly formalized by these lemmas.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/toron_locality_audit.py
lake env lean UnifiedTheory/Audit/KFCausalToronLocality.lean
lake build
```

Run Lean commands sequentially with other Lean jobs in this repository.
The combined report is `data/toron_locality_audit.json`, with source hashes.
The `--part scan` and `--part weak` modes provide smaller diagnostics.

This work builds on the established finite-volume Abelian measure program,
not a new claim of its existence. Lüscher's
[original construction](https://arxiv.org/abs/hep-lat/9811032) separates local
current conditions from global phase compatibility; sections 10–11 address
loop phases and finite-volume corrections. The seam comparison here is
applied to this repository's explicit overlap descent. Its remaining
quotient and symmetry obligations cannot be replaced by citing that result.
