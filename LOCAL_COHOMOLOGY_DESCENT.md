# A gauge-invariant first descent for the overlap measure

Follow-up: [the second descent and finite Ward completion](SECOND_COHOMOLOGY_COMPLETION.md)
now supply the full primitive on the bounded weak Abelian chart. Its
analytic locality proof controls the finite residual on uniformly growing
tori; global compact-chart and sector assembly remain open. The first-step
remainders described below are retained throughout that construction.

The repo now constructs a **gauge-invariant part** of the missing anomaly
primitive from the actual four-dimensional overlap operator. Its divergence
and scalar phase correction are checked against that operator. The result is
an exact decomposition into a constructed divergence, a field-strength term,
and an explicit torus winding term. The last two terms remain nonzero.
This is progress on the chiral measure supplier, not a completed measure or TOE.

This implements the first descent in established Abelian lattice cohomology.
The relevant precedents are [Lüscher, section 6](https://arxiv.org/html/hep-lat/9808021v2),
the [finite-volume treatment by Kadoh, Kikukawa, and Nakayama](https://arxiv.org/html/hep-lat/0309022v2),
and the [numerical construction by Kadoh and Kikukawa](https://arxiv.org/html/hep-lat/0401025v2).
The contribution here is a concrete supplier, independently controlled
computation, and scoped formal audit within this repo. It is not a new
classification theorem for gauge anomalies.

## 1. The problem carried forward

The [radial current](RADIAL_MEASURE_RECONSTRUCTION.md) has the required
projector curvature and a locality estimate using only the Wilson gap.
It retains a nonconstant determinant phase and stays defined when the
physical Dirac operator has zero modes. Its gauge contraction is

\[
 J_{\rm rad}(A)[B\omega]
 =-\langle\omega,a(A)\rangle+
   \left\langle\omega,\int_0^1a(tA)\,dt\right\rangle.
\]

Here an edge is labeled by its head x and direction mu, with tail x-mu;
\(B\omega\) is the head-minus-tail gauge gradient. All five supplied
left-handed charge blocks are included, with q=6Y and multiplicities
\((q,m)=(1,6),(-4,3),(2,3),(-3,2),(6,1)\). Non-Abelian backgrounds are the
identity. The density is

\[
 a(A,x)=\sum_{q,m}m q\,\operatorname{tr}_{\rm spin}
       (P_q(A)-P_+)(x,x).
\]

The previous local pair-flux primitive was not gauge invariant. The new
construction starts from the **scalar invariant density's link derivative**:

\[
 j(x,e;A)=\int_0^1\left.
      \frac{\partial a(X,x)}{\partial X_e}\right|_{X=tA}\,dt.
\]

On the weak, zero-flux potential chart, a(0)=0. The fundamental theorem of
calculus and constant index along the gapped path give

\[
 a(A)=j(A)A,\qquad j(A)B=0,\qquad \mathbf1^Tj(A)=0.
\]

The first zero follows from gauge invariance; the second follows from
\(\sum_x a(A,x)=0\). Also \(j(A+B\omega)=j(A)\): at every t, the two
arguments differ by the gauge transformation t omega, and differentiation
with respect to an individual Abelian link commutes with that translation.
The Lean theorem `radial_link_derivative_gauge` proves this derivative
inheritance as a function identity. The actual density's invariance follows
from the overlap projector's gauge covariance. No moving-frame term occurs
in this scalar derivative.

## 2. A periodic contraction with its harmonic part retained

Use cubical k-chains with increasing direction lists I. Their boundary is

\[
 (\partial f)_{I\setminus\mu}(x)\mathrel{+}=
 (-1)^{\operatorname{position}(\mu,I)}[f_I(x)-f_I(x+\mu)].
\]

Thus \(\partial_1=B^T\), \(\partial_2=C^T\), and the curvature is

\[
 F_{\mu\nu}(x)=(CA)_{\mu\nu}(x)
 =\nabla^-_\mu A_\nu(x)-\nabla^-_\nu A_\mu(x),\qquad CB=0.
\]

This fixes the sign and face-anchor conventions explicitly; antisymmetric
faces are stored only for mu<nu, so no factor 1/2 is needed.

For each coordinate choose an anchor c and a cut opposite c on the circle.
On 0-chains, \(P_0f\) places the total at c. On 1-chains, \(P_1u\) is the
constant chain whose value is u at the cut. Define h on 0-chains to be the
negative strict prefix of \(f-P_0f\), starting with zero at the cut. Then

\[
 \partial h=1-P_0,\qquad h\partial=1-P_1.
\]

The last edge closes because \(f-P_0f\) has zero sum. A constant winding
cycle survives as P1; it is not assigned a fictitious filling. Tensoring the
one-dimensional contractions with the usual graded signs yields

\[
 H=\sum_\mu P^{(0)}\cdots P^{(\mu-1)}h^{(\mu)},\qquad
 \partial H+H\partial=1-\Pi,\quad \Pi=\prod_\mu P^{(\mu)}.
\]

The cross terms cancel by graded anticommutation; the remaining terms
\(P^{(0)}\cdots P^{(\mu-1)}(1-P^{(\mu)})\) telescope to 1-Pi.
The executable checks this identity, in every degree through dimension
four, with bounded exact integer chains. Lean proves the one-dimensional
prefix, boundary, support, and periodic closure identities and the abstract
chain-contraction consequences. The complete tensor implementation is not
itself extracted from or fully formalized in Lean.

## 3. The actual divergence component

Apply H to each row j(x,.) with center **x**, obtaining theta(x,face).
Retain \(r(x,.)=\Pi_xj(x,.)\). Since each row is a cycle,

\[
 j=\theta C+r.
\]

For each face f with its own anchor z(f), let

\[
 \Phi_f=\sum_x\theta_{xf},\qquad
 M_{xf}=\delta_{x,z(f)}\Phi_f,\qquad \eta=\theta-M.
\]

Each column of eta has zero sum. Apply H again, now to that column as a
0-chain centered at **z(f)**. This constructs tau with \(B^T\tau=\eta\).
The edge current \(h=\tau F\) then satisfies

\[
 \boxed{a(A)=B^Th(A)+R(A),\qquad R(A)=M(A)F(A)+r(A)A.}
\]

Every geometry operator is field independent. Thus h is gauge invariant
because j and F are invariant. The winding piece is also invariant:
\(rB=0\). No inverse physical Dirac operator, gauge fixing, or common
spatial root enters this construction. The matrix identity, the anchored
column sums, and the supplied invariance implications are Lean-checked.
The cubical construction supplies the matrices numerically and analytically;
the formal matrix theorem alone does not assert their existence or locality.

A useful diagnostic for the next descent is

\[
 (\mathbf1^T\theta)C=-\mathbf1^Tr.
\]

Consequently Phi is not generally co-closed on a finite torus. Ignoring r
would give a false premise for the next cohomological step. The executable
records both the nonzero co-closedness defect and the residual in this exact
finite-volume equation.

## 4. Locality and the finite-size qualification

The homotopies use the density/face location as center, not one fixed root
for the whole lattice. On a source supported in a box about its center and
away from the opposite cuts, the anchored prefix and tensor projections
stay in that box. Prefix sums outside it vanish because their source has
zero total in that coordinate. Exact tests fill a translated elementary
plaquette loop with one face at each of three increasing volumes. A
noncontractible cycle is independently checked to survive in Pi.

The usual extension to exponentially decaying kernels sums compact support
shells; the finite sums introduce polynomial factors in the shell radius.
Together with a uniform Wilson gap, this is the route to locality of h
and its field derivatives. A full quantitative bound for this implemented
four-dimensional current, including its finite-volume terms, has not yet
been completed or formalized here. The support tests do not replace it.

The retained winding flux samples j at the opposite cut and sums over
transverse coordinates. If a supplied row bound is
\(|j(x,e)|\le K e^{-d(x,e)/\rho}\), then on an L^d torus a loop coefficient
is bounded by

\[
 L^{d-1}K e^{-(\lfloor L/2\rfloor-1)/\rho}.
\]

The subtraction of one allows for the edge's tail endpoint. Repeating this
coefficient around all d loops gives a row l1 bound at most
\(dL^d K e^{-(\lfloor L/2\rfloor-1)/\rho}\). Lean proves the finite-sum
absolute-value bound used here; the exponential hypothesis comes from a
separate spectral locality estimate. This is small only when the lattice
lengths are large relative to rho. Growing time with the other lengths
fixed at two does not justify dropping these fluxes.

The fixed coordinate order can also distinguish lattice directions.
Restoring all desired lattice symmetries is a further condition on a
completed supplier; it is not asserted by this first implementation.

## 5. Its scalar phase correction and exact residual

The physical divergence convention in the radial reconstruction is
\(\operatorname{div}_{\rm phys}k=-B^Tk\). Set k_h=-h, so its divergence is
\(B^Th=a-R\). The corresponding real phase correction is

\[
 C_h(A)=-\int_0^1 A^T h(tA)\,dt.
\]

Let L denote the two linear homotopies and anchoring operations that send
j to tau. Because F(tA)=tF(A), changing the order of the two finite-interval
integrals gives a single weighted density derivative integral:

\[
 j_w(A)=\int_0^1(1-u)a'(uA)\,du,\quad
 h_w(A)=(Lj_w(A))F(A),\quad C_h(A)=-A^Th_w(A).
\]

This avoids nested numerical integration. In particular,

\[
 j_wA=\int_0^1a(tA)\,dt,\qquad
 C_h(A+B\omega)-C_h(A)=-\omega^TB^Th_w(A).
\]

For \(J_{\rm partial}=J_{\rm rad}+dC_h\), the remaining Ward defect is
exactly \(\omega^TR_w\), where R_w is the same first descent applied to
j_w. Since the correction is the derivative of a smooth real scalar on
the chart, its curl and integrals around closed chart loops vanish.
This preserves the radial curvature and loop phases. It does not make the
remaining Ward defect zero or establish transitions between compact-field
charts and topological sectors.

## 6. Computation and checks

The new [executable](scripts/local_cohomology_audit.py) obtains **all** link
derivatives from the Wilson resolvent. For \(R_t=(it-H_W)^{-1}\),

\[
 P'=-\frac1{2\pi}\int_0^\infty
   (R_tH'_WR_t+R_t^\dagger H'_WR_t^\dagger)\,dt.
\]

Each link derivative of H_W has only the edge block and its adjoint.
Contracting four-spin blocks of R_t evaluates the complete Jacobian without
one eigensolve per edge. Gauss integration follows t=tan(pi u/2). A
separate spectral divided-difference derivative controls the answer.
Both formulations divide only across the Wilson gap. The field path uses
six Gauss nodes, with eight-node and higher-resolvent-order checks on the
small volume. Independent random potentials at every site have absolute
value at most 0.018. The elementary weak-field estimate supplies a kernel
gap of at least \(1-4\cdot6\cdot0.018=0.568\) throughout the path, including
between quadrature nodes. Measured gaps are reported separately.

The generated [report](data/local_cohomology_audit.json) separates exact
integer checks from float64 diagnostics and records source hashes. On
2^4 sites:

- The resolvent Jacobian agrees with the independent spectral derivative
  within about 2.5e-15 in Frobenius norm.
- The full density norm is about 1.598e-6; the first-descent reconstruction
  error is about 1.6e-16, while the separate fundamental-theorem error is
  about 2.9e-14.
- Under a real gauge transformation with site angles between -2 and 2,
  h changes by about 3.1e-16. Links may cross their principal logarithm;
  the test uses the real potential chart and its gauge translates.
- The scalar correction is about -2.009e-9. Its finite gauge-change
  formula agrees within about 2.3e-16; quadrature refinement changes it
  by about 1.7e-18.
- The corrected Ward defect agrees with the predicted remaining terms
  within about 3.7e-14.

The 3^4-site check also passes: its density norm is about 3.217e-6,
its retained remainder norm is about 6.261e-6, and its decomposition error
is about 3.1e-16. The separate fundamental-theorem error is about 9.9e-14.
Its Phi co-closedness defect has norm about 9.257e-5; including the winding
term restores the equation to about 3.3e-14. These small, deterministically generated
finite volumes are not a locality fit or a continuum extrapolation.

**This is not a norm-reduction algorithm.** On this test the remainder norm
is about 2.585e-6, larger than the original 1.598e-6 density norm. In the
specified gauge direction, the Ward defect changes from about -2.51e-8 to
-8.48e-8. Those values are nonzero and far above the controlled numerical
error. The purpose of this step is to identify a gauge-invariant divergence
and the structured next obstruction, not to minimize the defect in one step.

## 7. Obligation passed to the second descent

The [second-descent follow-up](SECOND_COHOMOLOGY_COMPLETION.md) processes
the remaining Phi F term and its modified
co-closedness equation. The four-dimensional F wedge F class carries the
usual cubic charge sum; the supplied spectrum has sum(m q^3)=0. That
cancellation alone is not an explicit primitive for the higher-order local
remainder. The torus fluxes and Wilson-line dependence must be treated
alongside the next descent, rather than silently discarded. A resulting
full current must have a quantitative locality bound, the desired lattice
symmetries, and compatible phase assembly across the intended sectors.

This work supplies a gauge-invariant component and exposes the exact
remaining finite-volume equation. It does not derive the spectrum,
continuous gauge dynamics, spacetime geometry, GR, a physical continuum
limit, or independent empirical predictions. Those remain requirements
of the proposed TOE.

Reproduce the audits with sequential Lean/Lake processes:

```sh
lake env lean UnifiedTheory/Audit/KFCausalLocalCohomology.lean
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/local_cohomology_audit.py --output data/local_cohomology_audit.json
lake build
```

The [formal module](UnifiedTheory/Audit/KFCausalLocalCohomology.lean)
audits 17 results. All 8,922 integrated build jobs pass, with no warnings
from the new module. Its printed axioms are limited to `propext`,
`Classical.choice`, and `Quot.sound` where needed. The executable passes
with runtime warnings treated as errors, and all seven recorded source
hashes match the final files. `git diff --check` passes. Existing warnings
elsewhere in the repository remain outside this change.
