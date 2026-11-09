# Exact scalar relabeling identities and the missing gravitational symmetry

Date: 2026-09-10

This stage constructs an exact Gaussian relabeling completion of the
whole scalar regulator. Its nonlinear contact vertex cancels the bubble
along every redundant direction. The transformed matrix stays positive
and exponentially local, with explicit positive finite-range approximants
and volume-independent coefficient bounds at fixed lattice spacing.

The completion does **not** repair the Einstein mismatch. Applied to an
arbitrary strain model, it leaves that model's entire effective action
unchanged. Thus the failed all-direction response in
[the isotropic regulator](ISOTROPIC_TENSOR_REGULATOR.md) survives even
though the added relabeling variables have exact Ward identities. This is
a concrete counterexample to treating formal source invariance alone as
evidence of emergent gravity.

A second result identifies why the natural lattice generators are not
already a microscopic diffeomorphism algebra. On an odd periodic cubic
graph with V sites, their unrestricted Lie closure is so(V). On smooth
band-limited data they instead approximate the continuum spatial bracket
with an explicit second-order bound. A high-frequency input shows that
this is not convergence in full-space operator norm.

These are analytical matrix and spatial-generator results with executable
checks. They do not prove a gravitational phase, the normal clock bracket,
Einstein dynamics, or a TOE. No new Lean theorem is claimed.

## 1. The full Gaussian source, including its contact terms

Let M be any real positive definite finite scalar matrix. For example,

\[
 M=m^2I+\sum_{i=1}^d(2I-T_i-T_i^{-1}),\qquad m>0,
\]

on a periodic cubic graph with lattice spacing one. A static spatial
calculation also applies separately to each Euclidean frequency block
M plus a scalar multiple of I. Set

\[
 D_i=(T_i-T_i^{-1})/2,\qquad
 R(\xi)=\tfrac12\sum_i(\Xi_iD_i+D_i\Xi_i),
 \quad \Xi_i=\operatorname{diag}(\xi_i).
\]

For real displacement samples, \(R^T=-R\). The continuum expression
approximated by this generator is the action on a scalar half-density,
\(R_c(\xi)=\xi^i\partial_i+\tfrac12\partial_i\xi^i\). The
half-density convention makes the action skew-adjoint with respect to
the fixed coordinate inner product. It does not make R a derivation
on ordinary scalar products.

Define the complete source path

\[
 U(t)=e^{tR},\qquad M(t)=U(t)^TMU(t)=e^{-tR}Me^{tR}.
\]

Orthogonality proves positivity, equality of spectra, and

\[
 \Gamma(t)=\tfrac12\log\det M(t)=\tfrac12\log\det M.
\]

There is no measure Jacobian: \(\det U=1\). The Gaussian integral is
exactly related to the original one by the field change \(\phi=U\psi\).
Every term in M is transformed, including the ultraviolet regulator.

The first and second vertices are

\[
 V=[M,R],\qquad W=[[M,R],R].
\]

Differentiating the determinant gives

\[
 \Gamma'(0)=\tfrac12\operatorname{Tr}(M^{-1}V)=0,
\]
\[
 \Gamma''(0)=\tfrac12\operatorname{Tr}(M^{-1}W)
 -\tfrac12\operatorname{Tr}(M^{-1}VM^{-1}V)=0.                 \tag{1}
\]

The second trace is nonnegative before its minus sign, since it is the
trace of \((M^{-1/2}VM^{-1/2})^2\). It is generally nonzero. The first
trace is the required contact contribution and cancels it exactly.
Keeping only the linear vertex would misidentify a nonzero response
along a direction that is exactly a field redefinition in this model.

Equation (1) is also a direct cyclic-trace identity; it does not require
a large-volume limit, perturbative approximation to the scalar integral,
or mass counterterm. For two generators R,S and the path
\(e^{-(tR+uS)}Me^{tR+uS}\), the mixed contact is

\[
 W_{RS}=\tfrac12\{[[M,R],S]+[[M,S],R]\},
\]

and the mixed version of (1) vanishes. Higher contact vertices follow
from the convergent commutator expansion. All identities in this
section concern the newly supplied redundant source family, not the
old six-component strain vertex by itself.

For a time-independent spatial U, the entire free scalar transfer
construction is transported by the canonical rotation of both Q and P.
Thus its positivity is preserved. Arbitrary transformations mixing time
slices require a separate reflection-positivity analysis; positivity of
a Euclidean matrix alone would not establish that property.

## 2. Locality and positive finite-range approximations

For graph distance d(x,y), define the weighted row norm

\[
 \|A\|_\alpha=\sup_x\sum_y|A_{xy}|e^{\alpha d(x,y)}.
\]

The triangle inequality for graph distance makes this norm
submultiplicative. If \(\max_{i,x}|\xi_i(x)|\leq\Xi\), then at unit
spacing

\[
 \|R\|_\alpha\leq\rho e^\alpha,\quad \rho=d\Xi,
 \qquad \|M\|_\alpha\leq m^2+2d(1+e^\alpha).
\]

The exponential series therefore proves

\[
 \|M(t)\|_\alpha\leq
 [m^2+2d(1+e^\alpha)]e^{2|t|\rho e^\alpha}.                 \tag{2}
\]

This is exponential coefficient locality, uniformly in the number of
sites for fixed bounded displacement and finite t. The nth nested
commutator has range at most n+1. In particular V has range at most two
and W at most three, so the first Ward cancellation has local vertices.

A truncation preserving positivity is obtained by approximating U before
forming the congruence:

\[
 S_r(t)=\sum_{n=0}^r\frac{t^nR^n}{n!},\qquad
 M_r(t)=S_r(t)^TMS_r(t).
\]

Because R is skew and its absolute row/column sums are bounded by rho,
\(\|R\|_2\leq\rho\). The standard exponential-series remainder gives

\[
 \|S_r-U\|_2\leq\delta_r:=
 e^{|t|\rho}\frac{(|t|\rho)^{r+1}}{(r+1)!}.
\]

Consequently

\[
 \|M_r-M(t)\|_2\leq(m^2+4d)(2\delta_r+\delta_r^2).
\]

The range of \(M_r\) is at most \(2r+1\). It is nonnegative for all r;
when \(\delta_r<1\), the stronger bound

\[
 M_r\geq m^2(1-\delta_r)^2 I>0
\]

follows from the smallest singular value of \(S_r\). These are uniform
finite-volume matrix statements. Exact finite-amplitude Ward invariance
belongs to U; a finite polynomial is an approximation to that identity.

Restoring spacing a changes the elementary generator bound to
\(\rho=d\Xi/a\). Thus (2) is not a bound uniform in refinement in lattice
distance. Nor is it a bounded-operator-norm locality theorem for the
unbounded Q,P field Hamiltonian or for interacting microscopic spins.

## 3. Why this exact completion cannot fix the old tensor response

Let \(M[h]\) be any positive seed strain model, and add U as above:

\[
 \widetilde M[h,U]=U^TM[h]U.
\]

Then, for every h in its positive domain,

\[
 \widetilde\Gamma[h,U]=\tfrac12\log\det\widetilde M[h,U]
 =\tfrac12\log\det M[h]=\Gamma[h].                         \tag{3}
\]

The new U derivatives and their mixed h derivatives vanish, but **all h
derivatives are unchanged**. Applied to the earlier isotropic source,
this retains its six-component temporal response and its failed
all-direction TT ratios. The extra Ward identities do not remove those
old strain variables. One can fix U=I and recover the original theory
exactly. Allowing U to vary introduces redundant coordinates and a gauge
volume, not gravitational dynamics for the original h.

This establishes a useful necessary distinction for the research program:
the symmetry must act on the candidate metric and matter so that its
physical constraint reduction changes the relevant strain dynamics.
Adding independent variables that merely rename the old theory does not
meet that requirement. The present completion has neither new curvature
degrees of freedom nor a derived normal-deformation constraint.

The broader distinction has a continuum precedent: parametrized free
field theory can describe flat-spacetime matter on arbitrary foliations
while using diffeomorphism-invariant variables. See
[Varadarajan's treatment of parametrized field theory](https://journals.aps.org/prd/abstract/10.1103/PhysRevD.75.044018).
The finite matrix construction here is our explicit Gaussian diagnostic;
it does not import that paper's quantization results.

## 4. The finite algebra does not already act as spatial diffeomorphisms

At a finite set of sites, the pointwise scalar algebra is \(\mathbb R^V\).
Every derivation of this algebra vanishes. Indeed its coordinate
idempotents satisfy \(e_x^2=e_x\); a derivation D would require

\[
 D e_x=2e_x D e_x.
\]

At x the equality forces the x component to zero, and at every other
site it forces the other components to zero. The idempotents span the
algebra. This simple statement uses the ordinary pointwise product and
does not exclude continuum limits or other products/algebras.

The equivalent issue in the half-density representation concerns how R
acts on multiplication operators. In the continuum,
\([R_c(\xi),F_f]=F_{\xi\cdot\nabla f}\). On the finite lattice,

\[
 [R,F_f]_{xy}=R_{xy}(f_y-f_x).
\]

If this commutator were diagonal for every f, every off-diagonal entry
of R would vanish. A real skew diagonal R is zero. Thus no nonzero
generator of this form preserves the fixed diagonal algebra as an
infinitesimal spatial-coordinate action. Orthogonal conjugation instead
transports that algebra to another matrix algebra.

Related lattice product-rule obstructions, under more general product,
translation, and locality assumptions, are proved by
[Kato, Sakamoto, and So](https://arxiv.org/abs/0803.3121).
Our finite-idempotent argument is narrower and elementary; it is not a
new no-go theorem for all emergent gravity or all finite-spin models.

There is also an exact result for the particular R family. On an odd
one-dimensional cycle of N sites, the coefficient on edge (x,x+1) is

\[
 R(\xi)_{x,x+1}=(\xi_x+\xi_{x+1})/4.
\]

The map \(I+T\) is invertible: its determinant is two for odd N. Thus
linear combinations of the R generators isolate every neighboring
skew rotation \(E_{x,x+1}\). For three distinct vertices,

\[
 [E_{xy},E_{yz}]=E_{xz},\qquad E_{xy}=|x\rangle\langle y|-|y\rangle\langle x|.
\]

Connectivity then generates every skew matrix. The same proof applies
on a periodic cubic graph of odd side length: invert \(I+T_i\) on
each coordinate cycle to isolate all graph edges, and use paths to
generate all pairs. The unrestricted Lie closure is therefore
\(\mathfrak{so}(V)\), of dimension \(V(V-1)/2\). It generally exceeds
the original dV sampled vector-field parameters. Reconstruction of an
isolated edge can use a displacement supported around a full cycle;
this is a Lie-span statement, not a locality bound on that inverse map.

The audit verifies closure by exact arithmetic modulo 101 on four odd
cycles and a two-dimensional odd torus. Full modular rank supplies a
lower bound on real rank, and the skew dimension supplies the upper
bound. The general graph argument supplies the theorem beyond these
finite checks.

## 5. A controlled smooth bracket still exists

Failure of the unrestricted finite-site algebra does not exclude an
approximate spatial algebra on a physically selected smooth sector.
This distinction can be quantified explicitly in one dimension.

For spacing a, \(\xi=e^{ikx}\) and \(f=e^{iqx}\), the centered
half-density generator has coefficient

\[
 R_a(\xi)f=r_a(k,q)e^{i(k+q)x},\qquad
 r_a(k,q)=\frac{i}{2a}[\sin(aq)+\sin(a(q+k))].
\]

Its continuum coefficient is \(r_0(k,q)=i(q+k/2)\). The continuum
vector bracket is \([\xi,\eta]=i(\ell-k)e^{i(k+\ell)x}\).
The exact full-output bracket defect for a single mode is

\[
 \mathcal E_a(k,\ell,q)=r_a(\ell,q)r_a(k,q+\ell)
 -r_a(k,q)r_a(\ell,q+k)-i(\ell-k)r_a(k+\ell,q).             \tag{4}
\]

For \(|k|,|\ell|,|q|\leq K\), the inequality
\(|\sin z-z|\leq|z|^3/6\) proves

\[
 |\mathcal E_a(k,\ell,q)|\leq\frac{103}{6}a^2K^4.         \tag{5}
\]

For completeness, a base vertex error is at most \(3a^2K^3/4\);
a shifted vertex error is at most \(35a^2K^3/12\). The corresponding
vertex magnitudes are bounded by \(3K/2\) and \(5K/2\). Subtracting
the two products in (4) from their continuum values costs at most
\(25a^2K^4/2\). The final bracket vertex costs at most
\(14a^2K^4/3\); their sum is (5). The continuum expression cancels
identically.

For general band-limited inputs, summing Fourier coefficients gives the
pointwise full-output estimate

\[
 \|([R_a(\xi),R_a(\eta)]-R_a([\xi,\eta]))f\|_\infty
 \leq\frac{103}{6}a^2K^4
 \|\widehat\xi\|_1\|\widehat\eta\|_1\|\widehat f\|_1.
\]

Taking \(3K<\pi/a\) also avoids output aliasing. This is a specified
spatial smooth-sector result; no projection discards the generated
output mode. The audit checks (4) against direct sampled matrix action
on refining grids and checks (5) on eighty mode triples.

There is no analogous unrestricted operator-norm convergence. Choose
\(k=0\), \(\ell=1\), and \(q=\pi/(2a)\), available on a circle of
length \(2\pi\) when the number of sites is divisible by four. Then

\[
 a|\mathcal E_a(0,1,\pi/(2a))|
 =\cos^2(a/2)\left[1+\frac{1-\cos a}{a}\right]\longrightarrow1.
\]

The full-space defect therefore grows like \(1/a\) on this ultraviolet
input, despite fixed smooth displacement modes. Complex Fourier modes
are used to display the calculation; decomposing into real and imaginary
parts cannot make all corresponding real-generator defects converge.

For the fixed smooth triple \((k,\ell,q)=(1,2,3)\), measured errors
at 64, 128, 256, and 512 sites are approximately 0.39624, 0.10335,
0.02611, and 0.006545. The finest refinement ratios approach four.
For the ultraviolet example, a times the error is approximately 1.0465,
1.0239, 1.0121, and 1.0061. These numerical values support the exact
formulas and are not interval certificates.

## 6. Revised criterion for a microscopic Einstein construction

There are now two distinct checks. Exact identities along a field-basis
orbit can be implemented with local contact vertices and a controlled
positive completion. Equation (3) proves that such identities can coexist
with every previously failed strain observable. To infer gravity, the
symmetry must constrain those physical observables themselves.

The smooth bracket estimate is useful but insufficient for the induced
action: the earlier tensor kinetic coefficients integrate ultraviolet
scalar modes, precisely where the smooth estimate does not control the
algebra. A microscopic construction must therefore establish the required
identities for the coarse effective action, including regulator, measure,
and contact contributions. Restricting only the external wavelength
cannot silently discard internal ultraviolet contributions.

The next viable target is a selected collective sector where spatial and
normal generators act jointly on the actual geometry and matter,
eliminate the unwanted strain components, and retain physical curvature
excitations with a common cone. The normal bracket must still produce
the metric-dependent spatial displacement in
[the conditional Einstein benchmark](GRAVITY_FROM_CLOCK_CONSTRAINTS.md).
Neither the arbitrary matrix Lie algebra nor the purely spatial smooth
limit above supplies it. A different collective limit, observable algebra,
or microscopic carrier may evade these particular restrictions; none is
proved here to realize the required phase.

The scalar relabeling calculation is consequently a regression test for
false gravitational completions and a derivation of the missing contact
structure. It preserves the full TOE objective while leaving the central
physical, dynamical, and continuum obligations open.

## 7. Reproduction and scope

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/microscopic_metric_ward_audit.py
```

The audit contains rational Ward identities, six finite point-algebra
checks, eight finite-amplitude matrix cases through 125 sites, nine
locality/positive-approximation cases, five modular Lie-closure cases,
eighty mode-bound checks, and four full-output refinement comparisons.
It verifies the unchanged finite strain determinant as well as the
unchanged strain Hessian. The report is
`data/microscopic_metric_ward_audit.json`, with eight source hashes.
Earlier sources and reports are unchanged. No Lean source is changed.
