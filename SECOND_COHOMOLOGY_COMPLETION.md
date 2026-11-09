# Second descent and a finite chiral Ward completion

The anomaly primitive is now explicit on the bounded, zero-flux Abelian
potential chart. The construction performs the second cubical descent,
retains every finite-volume remainder, and solves the final zero-total
remainder by a finite summation averaged over all anchors. With physical current k=-h it gives

\[
 -B^T k=a,\qquad k(A+B\omega)=k(A).
\]

Adding its scalar phase derivative to the radial measure current removes
the Ward defect while preserving curvature and closed chart-loop phases.
The finite identities are formalized and tested on the actual overlap
operator. Section 5 gives the separate analytic locality argument for
uniformly growing four-dimensional tori. That argument is not fully
formalized in Lean or a numerical continuum certificate.

This completes a **weak-chart measure-current construction**, with supplied
hypercharges and background geometry. It does not assemble all compact-field
charts and topological sectors, introduce non-Abelian dynamics, derive a
physical continuum theory, or complete the proposed TOE.

The guiding precedent is [Abelian local cohomology](https://arxiv.org/html/hep-lat/9808021v2).
Its [finite-lattice extension](https://arxiv.org/html/hep-lat/0309022v2)
explains why winding and Wilson-line effects must be retained. The new
executable implements a double-complex factorization and an explicit
finite remainder, with independent matrix and topological controls. No
claim of a new anomaly-classification theorem is intended. All field
orders are retained; the free-field Hessian cancellation controls the
topological term rather than truncating the density expansion.

## 1. Input and the second integrated derivative

Use the [first descent's conventions](LOCAL_COHOMOLOGY_DESCENT.md):
\(\partial_1=B^T\), \(\partial_2=C^T\), \(F=CA\), and increasing
orientation lists with no duplicate antisymmetric components. That step
constructed

\[
 a=B^Th_1+\langle\Phi,F\rangle_{\rm site}+r_1A,
 \qquad \partial_2\Phi=-\sum_xr_1(x,\cdot).
\]

Let S be the fixed linear map taking the integrated density Jacobian to
Phi. Charge conjugation makes the density even in A, so Phi(0)=0. Define

\[
 J(A)=\int_0^1\Phi'(tA)\,dt
     =S\int_0^1(1-t)a''(tA)\,dt.
\]

Then \(\Phi=JA\). J has bidegree (2,1): a two-cell in its first variable
and an edge in its second. It is gauge invariant, its second-variable
boundary vanishes, and its first-variable boundary is the explicitly
retained winding derivative. The one-dimensional change of integration
order above avoids nested field quadrature.

The full density Hessian is computed from two variations of
\(R_t=(it-H_W)^{-1}\): its integrand contains
\(RH'_eRH'_fR+RH'_fRH'_eR+RH''_{ef}R\), together with the adjoint-resolvent
contribution. The last term is nonzero when both derivatives act on the
same link. All link pairs are contracted from four-spin blocks. Independent
spectral projector jets check this implementation, including repeated
same-sign eigenvalues.

## 2. The double-complex factorization

Write x and y for the two boundary variables. They commute because they
act on different tensor factors. Every H below is the periodic homotopy
already constructed in the first descent, centered at the other variable's
head site. Define

\[
 \begin{aligned}
 T&=H_xJ,& K&=J-\partial_xT,\\
 U&=H_x\partial_yT,& S_1&=\partial_yT-\partial_xU,\\
 g(x)&=\sum_yU(x,y),&M(x,y)&=\delta_{xy}g(x),\\
 V&=H_y(U-M),&W&=T-\partial_xV,\\
 \mathcal L&=H_yW,&Q&=W-\partial_y\mathcal L.
 \end{aligned}
\]

The bidegrees are T=(3,1), U=(4,0), V=(4,1), W=(3,1), and L=(3,2).
In particular, U has just one first-variable orientation in four dimensions.
The diagonal M is essential: U-M has zero sum in y, which makes
\(\partial_yV=U-M\) exact on the torus. No harmonic term is set to zero.

Using only the boundary-square identities gives

\[
 \boxed{J=\partial_x\partial_y\mathcal L+\partial_xQ+K},
 \qquad \partial_yW=S_1+\partial_xM,
 \qquad \partial_xg=-\sum_yS_1.
\]

These identities hold even for input J which is not a cycle. The
[Lean module](UnifiedTheory/Audit/KFCausalSecondCohomology.lean) proves
them as finite matrix identities. The executable also checks them with
integer-valued inputs in dimensions 2^4 and 3^4; these controls stay exactly
representable in float64. The particular centered homotopies are an
executable/analytic supplier, not Lean-generated code.

Contracting the second variable with A gives

\[
 \Phi=\partial_x t+E_2,\qquad
 t=\mathcal L F,\qquad E_2=(\partial_xQ+K)A.
\]

The three-form t is gauge invariant: its kernel and F are invariant.
E2 remains explicitly computable. It is not assumed to vanish.

## 3. The Bianchi identity supplies a current

Multiplication by F requires a lattice product rule with shifted arguments.
For each increasing triple I and mu in I, define

\[
 (h_2)_\mu(x)\mathrel{+}=
 (-1)^{\operatorname{position}(\mu,I)}
 t_I(x)F_{I\setminus\mu}(x-\hat\mu).
\]

Then

\[
 \langle\partial_3t,F\rangle_{\rm site}-B^Th_2
   =\sum_I t_I(x)(dF)_I(x)=0.
\]

The final equality is the exact Bianchi identity for F=CA. Both the product
rule and its Bianchi consequence are formalized. Random integer potentials
and three-forms check the complete periodic implementation independently.
Thus, with

\[
 R_{\rm fin}=a-B^T(h_1+h_2)
            =\langle E_2,F\rangle_{\rm site}+r_1A,
\]

one has \(\sum_xR_{\rm fin}=0\), because the overlap index is constant and
zero on the chart. The final summation is explicitly averaged over every anchor,
Hbar_0=(1/volume) sum_c H_0,c. This removes an arbitrary preferred origin:
translation permutes the summands. On a zero-total source every summand
has the same divergence, so the average retains the exact equation.
The final finite summation h_fin=Hbar_0 R_fin solves
\(B^Th_{\rm fin}=R_{\rm fin}\). Hence

\[
 h=h_1+h_2+h_{\rm fin},\qquad B^Th=a.
\]

R_fin is a gauge-invariant scalar, so its field-independent finite
summation is also invariant. This finite completion alone would work even
for a nonlocal current or anomalous spectrum. The following locality
argument is therefore indispensable.

## 4. The charge cancellation appears in the top diagonal

At the free field, H_W is charge independent and its first and second link
variations scale as q and q^2. Including the density's prefactor q gives

\[
 a_q''(0)=q^3 a_1''(0).
\]

For the supplied left-handed spectrum,

\[
 \sum m q^3=6-192+24-54+216=0.
\]

Consequently J(0)=0 and **g(0)=0**, since all the subsequent geometry maps
are linear. No continuum normalization of the anomaly coefficient needs
to be guessed to establish this cancellation. The previous formal charge
identity supplies the arithmetic; independent negative- and positive-charge
Hessian calculations check the scaling on the actual operator.

The synthetic controls distinguish this cancellation from simply hiding a
topological class in the finite solver:

| Cubic length L | Local-divergence kernel: remaining norm | F wedge F kernel: top-diagonal norm |
| ---: | ---: | ---: |
| 3 | 0 | 9 |
| 4 | 0 | 16 |
| 5 | 0 | 25 |

The first input is J=partial_3 L_local C and has a known strictly local
primitive. The second is the closed kernel J=star_shift C, with
\((\star_{\rm shift}F)_{\mu\nu}(x)=\epsilon_{\mu\nu\rho\sigma}
F_{\rho\sigma}(x-\hat\mu-\hat\nu)\) for the complementary increasing pair.
Its diagonal has magnitude one per site: its norm is sqrt(volume)=L^2.
The algorithm retains that class at every tested size. No finite-volume
Ward solve by itself certifies anomaly cancellation.

## 5. Analytic locality argument and its scope

Consider L^4 tori with the same specified fermion spin structure and real
potentials satisfying |A_e|<=epsilon, with 24 epsilon<1. All five supplied
charges have |q|<=6. The free Wilson gap is at least one, so throughout the
radial path a uniform lower bound is

\[
 h_W\ge h_0=1-24\epsilon>0.
\]

For epsilon=0.018 this is 0.568. Physical Dirac eigenvalues may vanish;
no inverse physical Dirac operator occurs in this construction. The
following estimates concern fixed orders of field differentiation, with
constants independent of L and of the potential in this bounded chart.
They are analytic estimates, separate from the finite numerical checks.

### 5.1 Spectral input

Conjugate the Wilson kernel by the exponential of distance from a site.
For a weight exponent alpha, its nearest-neighbor change has norm at most
4(exp(alpha)-1). Taking alpha=log(1+h0/8) bounds that change by h0/2.
The resolvent identity therefore gives the matrix-element estimate

\[
 \|R_t(x,y)\|\le
 \frac{2e^{-\alpha d_1(x,y)}}{\sqrt{h_0^2+t^2}}.
\]

Each derivative of H_W is supported on the relevant edge and has a bound
depending only on its derivative order and |q|<=6. A derivative of the
projector is a finite sum of chains of these resolvents and edge insertions.
Its closed chain visits the density site and every differentiated edge.
The t integral is absolutely convergent once at least one derivative is
present. Thus, for every fixed m>=1, the density derivative obeys

\[
 |a^{(m)}(x;e_1,\ldots,e_m)|
 \le C_m e^{-\alpha\max_i d_\infty(x,e_i)}.
\]

Edge endpoints change C_m, not the volume-independent exponent. The
charge sum, radial integrations, and their extra powers of t preserve
these bounds. This supplies the local derivative kernel entering S and J.

### 5.2 Bounds for the actual centered homotopy

In the implemented one-dimensional strict prefix, each input coefficient
is 0, +1, or -1. Tensoring the projections retains that property for each
pair of oriented cells. A nonzero H matrix entry can connect an input and
output only if the output's maximum coordinate distance from the chosen
center is no larger than the input's. These facts follow directly from
the prefix formula: subtracting the sum at the center cancels the prefix
outside the interval between the input and the center. The opposite cut
never enlarges that centered coordinate box. The independent
[locality audit](scripts/cohomology_locality_audit.py) checks all 10,784
basis vectors at two centers on the 3^4 and 4^4 tori, with exact bounded
integer arithmetic; coefficient bounds, support, and the full contraction
identity pass on every basis vector. They also hold for the
periodic projections; a positive-degree projection samples an opposite cut.

There are at most 16 orientations in four dimensions. A conservative
absolute row-sum bound for H is 16 L^4. More usefully, for a centered input
bounded by C exp(-mu max(distance,R)), its output at radius r is bounded by

\[
 16C\,Z_4(\mu/3)e^{-\mu(r+R)/3},\qquad
 Z_4(s)=\sum_{z\in\mathbb Z^4}e^{-s\|z\|_\infty}
 \le\left(\frac{1+e^{-s/4}}{1-e^{-s/4}}\right)^4.
\]

Indeed, a contributing input has radius at least r, and
max(distance,R)>=(distance+r+R)/3. This proves a volume-independent
locality transfer for H. Swapping the two kernel anchors loses at most
a further factor two in the exponent by the triangle inequality. Summing
one local kernel variable loses at most a factor two by the same lattice
sum bound. A boundary difference only shifts an anchor by one lattice
step. These finite transfer rules apply also after any fixed number of
field derivatives.

Consequently all the kernels J,T,U,V,W,L and the local field g have uniform
exponential derivative bounds. The diagonal subtraction M is local since
g is local. There are finitely many transfers in the displayed formulas;
iterating the explicit rules yields a positive common exponent mu. No
fit to numerical volume data or physical Dirac gap is used here.

### 5.3 Bounding every retained remainder

Call an array volume-small if all its fixed-order field derivatives satisfy
C_m(1+L)^{p_m} exp(-beta L), for some beta>0 and volume-independent
constants. Finite sums, boundaries, products with bounded potentials, and
H preserve this class because their absolute row sums grow polynomially.
A positive-degree harmonic projection of a local centered kernel is
volume-small: it samples an input at distance at least floor(L/2)-1.

The first-descent winding r1 is therefore volume-small. The identity for
partial_2 Phi in section 1 shows that partial_x J is volume-small too,
while partial_y J=0 exactly. The homotopy identities now give

\[
 K=\Pi_xJ+H_x\partial_xJ,
\]

so K is volume-small. Similarly,

\[
 S_1=\Pi_x\partial_yT+H_x\partial_x\partial_yT,
 \qquad\partial_x\partial_yT=-\partial_yK,
\]

makes S1 volume-small. No commutation of a boundary with a moving-center
homotopy is assumed here; the stated identities use the actual remainders.

The only remaining issue is M. For any differentiated edge e, choose a
site z at distance at least floor(L/2)-1 from e. Locality bounds
|partial_e g(z)| exponentially in L. Moving from z to any x takes at most
2L nearest-neighbor steps. Since partial_x g=-sum_y S1, the difference
between partial_e g(x) and partial_e g(z) is bounded by a polynomial times
exp(-beta L). The same argument works for higher mixed derivatives by
choosing z far from one of their differentiated edges. Thus every positive
field derivative of g is volume-small. Finally,

\[
 g(A)-g(0)=\int_0^1\sum_e A_e\partial_e g(tA)\,dt,
\]

and the previously established g(0)=0 show that g itself, and hence M,
is volume-small. This is exactly where the cubic charge cancellation
is used; it fails for the synthetic nonzero anomaly class.

Now

\[
 Q=\Pi_yW+H_y\partial_yW,
 \qquad \partial_yW=S_1+\partial_xM,
\]

shows that Q is volume-small. It follows successively that E2, R_fin,
and h_fin are volume-small, including all fixed-order field derivatives.
This controls the actual final summation, rather than assuming that an
arbitrary zero-total source has a local inverse.

### 5.4 From a volume bound to spatial locality

Polynomial volume factors do not defeat exponential suppression. For
x>=0 the formalized estimate is

\[
 x^p e^{-x}\le 2^p p!\,e^{-x/2}.
\]

On an L^4 torus any two site anchors have d1<=2L. Therefore a bound
C(1+L)^p exp(-beta L) gives a volume-independent exponential bound in
their separation, after reducing the rate. The finite summation of
R_fin thus has local field responses despite involving the whole torus.
The same holds for h1+h2 by the centered-kernel transfer estimates.
Finally, differentiating the scalar phase requires summing a local
response against bounded A; the lattice sum estimate controls that last
sum as well. The corrected measure current consequently has a uniform
exponentially decaying two-link response on this family.

The resulting constants are conservative and have not been optimized or
numerically evaluated. Lean verifies the finite-sum, distant-representative,
and polynomial/exponential implications, **not this entire spectral and
cubical-locality proof**. This conclusion is restricted to bounded weak
potentials on uniformly growing tori. It does not establish the previously
tested thin-torus limit, arbitrary admissible compact sectors, or a
non-Abelian measure.

## 6. Scalar phase and reproducible checks

Let h_w=int_0^1 h(tA) dt and C(A)=-A^T h_w. The first-descent weighted
Jacobian remains int_0^1(1-t)a'(tA)dt. Because the second current contains
two field strengths, its already-integrated kernel is instead

\[
 J_w=S\int_0^1\frac{(1-t)^2}{2}a''(tA)\,dt.
\]

The executable uses this weight, not nested integrations. The final
weighted residual is completed against the independently integrated actual
density. Gauge invariance of h gives

\[
 C(A+B\omega)-C(A)=-\omega^T\int_0^1a(tA)\,dt,
\]

which cancels the radial Ward defect. As an exact differential of a smooth
real scalar on the chart, dC has zero curl and zero closed-loop integral.
It preserves the radial curvature and loop phases; it does not force the
whole Weyl determinant to be positive. If the full radial Kato frame has
rank N, the explicit corrected frame is V_corr=V_rad exp(-iC/N). Its
connection gains +dC, and its Weyl determinant gains exp(-iC). The
[direct-frame audit](scripts/completed_measure_phase_audit.py) checks this
sign and retains a nonconstant phase. A separate periodic free-field test
checks the current at Dirac zero modes, where the determinant's argument
itself is undefined.

The [executable](scripts/second_cohomology_audit.py) and its generated
[report](data/second_cohomology_audit.json) record the actual operator's
Hessian controls, finite identities, nonzero remaining terms, final Ward
error, large-gauge phase change, and independent field-quadrature refinement.
The report contains source hashes. Float64 checks are not interval proofs.

The complete overlap test uses 2^4 sites with independently generated
link potentials bounded by 0.018. The density norm is about 1.598e-6.
Before the final finite correction the residual norm is about 3.720e-6;
it has not become small at this tiny volume. After the correction:

| Check | Measured error |
| --- | ---: |
| Full divergence/Ward equation | 3.2e-15 |
| Current under a large real gauge transformation | 7.2e-14 |
| Finite scalar phase-change formula | 2.0e-14 |
| Corrected radial Ward contraction | 1.2e-14 |
| Scalar phase under 4-to-6-node refinement | 1.7e-15 |
| Hessian versus independent spectral jet | 3.5e-14 |

The scalar correction is about 3.129e-9. Independent radial basis
transports retain a corrected determinant phase about -1.04346e-8;
64-to-128-step refinement controls that comparison. On the separately
tested free periodic lattice the Wilson gap is one, four constant spinors
have Dirac residual about 3.6e-15, and the completed current is defined and
zero. The whole-torus summation is also checked for translation covariance.
The growing-volume locality conclusion comes from section 5.



```sh
lake env lean UnifiedTheory/Audit/KFCausalSecondCohomology.lean
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/second_cohomology_audit.py --output data/second_cohomology_audit.json
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/cohomology_locality_audit.py
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/completed_measure_phase_audit.py
lake build
```

Run Lean/Lake processes sequentially for this repository. All 8,923
integrated build jobs pass, with no warnings from the new formal module.
Its 11 printed results use only `propext`, `Classical.choice`, and
`Quot.sound` where needed. All three new executables pass with runtime
warnings treated as errors. Their eight, seven, and nine recorded source
hashes respectively match the final files; `git diff --check` passes.
Existing warnings elsewhere in the repository are outside this change.
