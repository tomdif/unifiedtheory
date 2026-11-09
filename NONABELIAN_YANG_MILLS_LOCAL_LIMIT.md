# Nonlinear nonabelian refinement: a local Yang–Mills heat theorem

Date: 2026-11-09

We extend the previous refinement program to the actual nonabelian
Yang–Mills heat equation, in DeTurck gauge, on the unit two-torus. The
finite models are exact Fourier–Galerkin cutoffs of that equation. Quadratic
derivative commutators and cubic double commutators are retained.

For sufficiently regular initial SU(m) connection data we prove a common
positive existence time, bounds independent of the cutoff, uniqueness,
positive-time smoothness, and convergence of the entire cutoff sequence.
Parallel transport and normalized Wilson traces converge with an explicit
error estimate. A spatially homogeneous SU(2) solution exhibits nonzero
curvature and genuinely nonlinear motion even when all spatial derivatives
vanish.

**Scope.** This theorem is local in time and uses regular connection data.
It does not extend the abelian rough-data theorem unchanged. The discretization
is a spectral method in a specified gauge, not the nearest-neighbor compact
Wilson lattice action. The full proof below is analytic; the accompanying
Lean file checks stated ingredients. These are applications of established
parabolic methods, with no claim of mathematical novelty.

## 1. Use the actual nonlinear equation

Let A=A1 dx1+A2 dx2 with periodic anti-Hermitian trace-free m-by-m matrices.
Write [X,Y]=XY-YX, D_j X=partial_j X+[A_j,X], and

\[
 F_{ji}=\partial_j A_i-\partial_i A_j+[A_j,A_i].
\]

Yang–Mills heat is partial_t A_i=sum_j D_j F_ji. Its strictly parabolic
DeTurck form adds D_i div A. Expanding by the Leibniz rule gives

\[
 \partial_t A_i=\Delta A_i+\mathcal N_i(A),\qquad
 \mathcal N_i(A)=\sum_{j=1}^2\left(
 2[A_j,\partial_j A_i]-[A_j,\partial_i A_j]
       +[A_j,[A_j,A_i]]\right).
 \tag{1}
\]

The mixed second derivatives cancel between D_j F_ji and D_i div A.
The terms [partial_j A_j,A_i]+[A_i,partial_j A_j] cancel as well. This
derives (1) from the Yang–Mills equation; no new reaction term is introduced.

To remove the DeTurck term, solve at each spatial point

\[
 \partial_t g=g\,\operatorname{div}A,\quad g(0,x)=I,\qquad
 B_i=gA_ig^{-1}-(\partial_i g)g^{-1}.
 \tag{2}
\]

Since div A is anti-Hermitian and trace free, g remains in SU(m). Set
eta=(partial_t g)g^{-1}=g(div A)g^{-1}. Direct differentiation gives
partial_t B_i=g(partial_t A_i)g^{-1}-D_i^B eta, which cancels the added term.
Thus B solves Yang–Mills heat on the same interval. This is a time-dependent
gauge equivalence, not an assertion that (1) is itself invariant under every
position-dependent, time-independent gauge transformation.

## 2. A norm with explicit, cutoff-independent constants

For integer r>=0 use the weighted Fourier norm

\[
 \|a\|_{\mathcal W_r}=\sum_{k\in\mathbb Z^2}(1+|k_1|+|k_2|)^r
                                  \|\widehat a(k)\|_{\rm op},
 \quad \|A\|_r=\|A_1\|_{\mathcal W_r}+\|A_2\|_{\mathcal W_r}.
 \tag{3}
\]

Fourier coefficients are complex matrices; their conjugate symmetry encodes
anti-Hermiticity of A(x). All matrix norms here are operator norms, not the
entrywise maximum norm. Put w(k)=1+|k1|+|k2|. Since w(k+l)<=w(k)w(l), convolution
and submultiplicativity give, with no dimension-dependent constant,

\[
 \|ab\|_{\mathcal W_r}\le\|a\|_{\mathcal W_r}\|b\|_{\mathcal W_r},\quad
 \|[a,b]\|_{\mathcal W_r}\le2\|a\|_{\mathcal W_r}\|b\|_{\mathcal W_r},\quad
 \|\partial_j a\|_{\mathcal W_{r-1}}\le2\pi\|a\|_{\mathcal W_r}.
 \tag{4}
\]

In particular W_r embeds in C^r for integer r. Define, for R>=0,

\[
 b(R)=16\pi R^2+4R^3,\qquad l(R)=32\pi R+12R^2.
 \tag{5}
\]

For r>=1 and ||A||_r,||C||_r<=R, (4) yields

\[
 \|\mathcal N(A)\|_{r-1}\le b(R),\qquad
 \|\mathcal N(A)-\mathcal N(C)\|_{r-1}\le l(R)\|A-C\|_r.
 \tag{6}
\]

Here are the constants explicitly. If a_i=||A_i||_r, the first quadratic
term sums to at most 8pi(sum a_i)^2 and the second to at most 8pi sum a_i^2.
Their total is at most 16pi R^2. The cubic term is at most
4(sum a_i)(sum a_j^2)<=4R^3. The associated bilinear map has bound 16pi and
the trilinear map bound 4; expanding the difference of their diagonal values
gives 32pi R+12R^2. These estimates use the noncommutative products exactly.

Let S(t)=exp(t Delta). Its Fourier multiplier is exp(-4pi^2|k|_2^2 t), so
||S(t)||_(W_r->W_r)<=1 and, for t>0,

\[
 \|S(t)f\|_r\le(1+t^{-1/2})\|f\|_{r-1},\qquad
 K(T):=\int_0^T(1+t^{-1/2})dt=T+2\sqrt T.
 \tag{7}
\]

For example, |k|_1<=sqrt(2)|k|_2 and u exp(-u^2)<=1 show
w(k)exp(-4pi^2|k|_2^2t)<=1+sqrt(2)/(2pi sqrt(t))<=1+t^(-1/2).
The integrability of this singularity is what controls the derivative in
the nonlinear term.

## 3. Define the finite models and prove their common lifespan

Fix integers s>=2 and p>=1, q=s+p, and initial data A0 in W_q with the
SU(m) reality and trace conditions. Let a0=||A0||_q. If a0=0, all solutions
are identically zero. Otherwise put R=2a0 and choose the explicit positive time

\[
 T=\left(\sqrt{1+\frac1{2l(R)}}-1\right)^2.
 \tag{8}
\]

Then K(T)l(R)=1/2. Also b(R)<=R l(R)/2, so K(T)b(R)<=R/4.
This time is conservative; no optimal lifespan is asserted.
One can replace a0 by any positive upper bound for ||A0||_q throughout;
the same conclusions hold with the resulting R and T. This is convenient
when using a computable bound for matrix Fourier coefficients.

Let P_N retain frequencies |k|_infinity<=N. It is contractive in every W_r,
commutes with S(t), and preserves the required matrix reality conditions.
Our finite-dimensional nonlinear model is

\[
 \partial_t A_N=\Delta A_N+P_N\mathcal N(A_N),\qquad A_N(0)=P_N A_0.
 \tag{9}
\]

All products in (9) are exact Fourier convolutions before projection. An
aliased product on an insufficiently padded grid is a different ODE.

On the closed radius-R ball in C([0,T];W_q), define the Duhamel maps

\[
 \Phi(A)(t)=S(t)A_0+\int_0^tS(t-u)\mathcal N(A(u))\,du,
\]

and Phi_N by inserting P_N on the initial datum and the nonlinearity.
Equations (6)-(8) show both

\[
 \|\Phi(A)\|_{C_TW_q},\ \|\Phi_N(A)\|_{C_TW_q}
       \le a_0+K(T)b(R)\le3R/4,
\]

and a contraction constant at most K(T)l(R)=1/2. The integrable bound (7)
also proves the integrals are continuous in W_q, including at t=0.
The Banach fixed-point theorem therefore produces a continuum solution A
and every finite-cutoff solution A_N on the same interval, with

\[
 \sup_{0\le t\le T}\|A(t)\|_q\le R,\qquad
 \sup_N\sup_{0\le t\le T}\|A_N(t)\|_q\le R.
 \tag{10}
\]

Anti-Hermiticity and trace-freeness are preserved by derivatives, heat flow,
commutators, projection, and the fixed-point limit. For each N, the mild
solution agrees with the usual solution of the finite polynomial ODE (9).

Uniqueness is not restricted to an arbitrarily chosen small ball. Two
C([0,T];W_q) solutions have a finite joint norm bound. Divide time into
intervals small enough that K(delta)l(that bound)<1, and apply the difference
estimate on each interval with their common initial value. Induction over
the intervals identifies the solutions. The same argument works in W_s.

## 4. Full-sequence convergence with an explicit rate

Projection tails obey, for r>=0,

\[
 \|(I-P_N)f\|_r\le(N+1)^{-p}\|f\|_{r+p}.
 \tag{11}
\]

Outside the cutoff at least one integer frequency has magnitude N+1, so
w(k)>=N+2; the weaker N+1 bound in (11) is sufficient.
Subtract the two mild equations in W_s. Apply (6) to the difference of the
nonlinearities, and (11) to A0 in W_q and N(A) in W_(q-1). With
e_N=sup_(t<=T)||A_N(t)-A(t)||_s, this gives

\[
 e_N\le(N+1)^{-p}[a_0+K(T)b(R)]+K(T)l(R)e_N.
\]

Absorb the last term using K(T)l(R)<=1/2:

\[
 \boxed{e_N\le E_N:=2(N+1)^{-p}[a_0+K(T)b(R)]\le\tfrac32R(N+1)^{-p}.}
 \tag{12}
\]

Thus the entire sequence converges, with no subsequence selection. The limit
is already identified uniquely by (1) and A0. This estimate is for exact
Galerkin solutions; an additional time-discretization error must be included
when integrating the finite ODE numerically.

The same contraction argument gives stability under perturbing initial data
in W_s, with factor at most 2, provided the common W_q bounds and time are
chosen as above for both data sets. Uncontrolled high-frequency initialization
is not silently covered by that hypothesis.

## 5. Curvature and regularity now follow from the equations

With s>=2, define

\[
 M=2\pi R+2R^2,\qquad L=2\pi M.
\]

Using (4) and (10), both continuum and all cutoff curvatures satisfy

\[
 \|F_{12}(A_N(t))\|_\infty,\ \|F_{12}(A(t))\|_\infty\le M,
 \qquad \|\partial_j F_{12}\|_\infty\le L.
 \tag{13}
\]

Indeed ||F12||_(W_(s-1))<=2pi R+2R^2, and one more derivative costs 2pi.
These bounds are derived from a common lifespan estimate for the actual
nonlinear dynamics. They are not imposed as assumptions on evolved curvature.
Similarly,

\[
 \|F_{12}(A_N)-F_{12}(A)\|_\infty\le(2\pi+4R)E_N.
 \tag{14}
\]

The solutions are smooth for positive time. To justify the upgrade, split
the mild equation at an earlier positive time. Heat smoothing gains any
number of derivatives on the term separated from the current time. In the
remaining integral, N loses one derivative, while heat gains 1+alpha with
singularity (t-u)^(-(1+alpha)/2), integrable for 0<alpha<1. This gives a gain
of alpha derivatives on intervals bounded away from zero. Iterating, using
fractional versions of the same weighted norm and product inequality, gives
all spatial derivatives; (1) then gives time derivatives. Projection is
contractive at each step, so the corresponding positive-time bounds can be
chosen uniformly in N. No smoothness at time zero beyond A0's stated norm is
asserted.

## 6. Reconstruct finite SU(m) links and control observables

For example sample a square grid with h_N=1/(2N+1). Assign each edge the
exact parallel transport of A_N along that edge. In the head-to-tail
convention used in the earlier notes, along a parametrized path gamma it is
the solution U'=U sum_i A_(N,i)(gamma) dot gamma_i, U(0)=I. Since the
coefficient is anti-Hermitian and trace-free, every link lies in SU(m).
This is an explicit finite-mode model with group-valued readouts; the links
are not asserted to obey a separate local Wilson-action flow.

For any piecewise C1 path of total coordinate length
ell_1=integral(|dot gamma_1|+|dot gamma_2|), variation of parameters and
unitarity give

\[
 \boxed{\sup_{0\le t\le T}
 \|W_{A_N(t)}(\gamma)-W_{A(t)}(\gamma)\|_{\rm op}\le\ell_1(\gamma)E_N.}
 \tag{15}
\]

To see this directly, differentiate U_N U^{-1}; the derivative is
U_N(a_N-a)U^{-1}, whose norm is at most ||a_N-a||. Integrate and use unitary
invariance of the norm. The bound is uniform over paths of bounded length,
including grid paths, backtracking, and closed loops. Because
|tr X|/m<=||X||_op, normalized Wilson traces satisfy the same estimate.

Here the connection itself is a finite-mode unknown, so this direct bound
is stronger than first estimating plaquettes and then reconstructing an
axial connection. The curvature controls in (13) provide the previously
missing geometric regularity as well.

Gauge qualification matters: P_N does not commute with arbitrary
position-dependent gauge transformations. Equation (9) is defined in
DeTurck gauge; constant conjugations do commute with it. Exact link readouts
transform correctly under any post-applied vertex gauge. The continuum
limit is gauge-equivalent to Yang–Mills heat by (2), and its Wilson traces are
gauge invariant. This is not a proof that the finite spectral ODE is locally
gauge equivariant.

## 7. An exact nonlinear SU(2) solution and a sign check

Identify su(2) with imaginary quaternions e1,e2,e3 satisfying
[e1,e2]=2e3 and cyclic permutations. Let A1=a(t)e1, A2=a(t)e2, spatially
constant. Then the derivative terms vanish but the cubic terms do not:

\[
 [A_2,[A_2,A_1]]=-4a^3e_1,\qquad
 [A_1,[A_1,A_2]]=-4a^3e_2.
\]

The exact solution for any a_*>0 is

\[
 a(t)=\frac{a_*}{\sqrt{1+8a_*^2t}},\qquad a'=-4a^3,
 \quad F_{12}=2a(t)^2 e_3\ne0.
 \tag{16}
\]

Thus noncommutativity changes the dynamics even at zero spatial frequency.
Dropping the cubic commutator would incorrectly leave this field constant.
The squared curvature norm is 4a^4; its half-energy has derivative -32a^6.
This solution exists globally, but it is a special family and does not
upgrade the general local theorem to a global theorem.

## 8. Literature, formalization, and validation

The equation and local parabolic theory are established. Primary references
checked for this work include:

- Chandra, Chevyrev, Hairer, and Shen,
  [Langevin dynamic for the 2D Yang–Mills measure](https://www.numdam.org/item/10.1007/s10240-022-00132-0.pdf),
  which gives the DeTurck formulation and its gauge interpretation.
- [Norm inflation for a non-linear heat equation with Gaussian initial conditions](https://link.springer.com/article/10.1007/s40072-023-00317-6),
  which explicitly displays the deterministic DeTurck–Yang–Mills nonlinearity
  and discusses its local solution theory. Its rough-data issues are not
  bypassed by our regular-data hypothesis.

Our contribution here is a self-contained quantitative implementation of this
restricted program in the repository, not a priority claim for the theorem.
Global nonlinear control, rough curvature initialization comparable to the
abelian case, and a local compact-link discretization are separate extensions.

The accompanying Lean module checks commutator estimates, exact algebraic
identities and the SU(2) witness, together with scalar inequalities used in
the contraction argument. The weighted Fourier Banach-space construction,
fixed-point assembly, gauge-removal ODE, and full convergence theorem are
analytic proofs here, not a complete Lean formalization.

The numerical audit uses exact dealiased Fourier projection for nonlinear
products, independently checks convolution at small cutoff, compares the
homogeneous solution with (16), checks constant SU(2) conjugation symmetry,
and measures inhomogeneous cutoff convergence and transport errors. Time
integration and the higher-cutoff reference are numerical approximations;
their observed errors are not substituted for (12).

### Reproducible results

Files:

- [Supporting Lean proofs](UnifiedTheory/LayerA/NonabelianYangMillsLocal.lean)
- [Every-theorem axiom audit](scripts/CheckNonabelianYangMillsLocal.lean)
- [Executable numerical audit](scripts/nonabelian_yang_mills_local_audit.py)
- [Numerical results](data/nonabelian_yang_mills_local_audit.json)
- [Verification manifest](data/nonabelian_yang_mills_local_verification.json)

The module contains 18 supporting theorems, including the actual derivative
identity for (16). The numerical audit passed 64 exact rational algebra
checks, an independent 54-coefficient convolution comparison, constant
SU(2) conjugation and Lie-algebra reality checks, and 20 path comparisons.
The homogeneous nonlinear solution's maximum error across 21 time samples
on [0,1] was 5.53e-13 or less. Its half-energy fell from 0.4802 to about
0.0198377; the evolution with commutators removed would leave it constant.

The inhomogeneous test uses s=2, p=2 and the conservative initial W_4 upper
bound 0.168040219. The guaranteed time from (8) is about 5.02524e-5.
With an N=8 numerical reference, the sampled maximum W_2 error upper
estimates were:

| Cutoff N | Error upper estimate against N=8 |
| --- | ---: |
| 1 | 4.64483e-4 |
| 2 | 8.47952e-5 |
| 3 | 2.55360e-5 |
| 4 | 9.05645e-6 |
| 6 | 3.40845e-12 |

These sampled maxima include the initial time. The initial field has modes
only through cutoff 6, explaining the sharp improvement there; the table
does not measure an asymptotic continuum convergence order. Matrix Fourier
norms are bounded using the sum of the absolute quaternion coefficients,
which is valid for complex coefficients as well. The higher-cutoff reference
has its own analytic error E_8. Ordinary floating-point evaluation of the
bound formulas is not an interval certificate.

The inhomogeneous trajectory also differs from the linear heat trajectory
by about 6.43e-7 in the computed W_2 upper metric at the final time. Changing
both integration tolerance and maximum step size changed sampled solutions
by less than 1.4e-17 in that metric. This is a time-integration diagnostic,
not a rigorous error enclosure. Transport calculations use midpoint
piecewise-constant coefficients with a separate analytic quadrature budget;
their largest observed change on doubling the quadrature resolution was
2.66e-8. General discrete Yang–Mills energy monotonicity is not claimed for
the projected ODE.

Run from the repository root, in this order:

```sh
lake build UnifiedTheory.LayerA.NonabelianYangMillsLocal
lake env lean scripts/CheckNonabelianYangMillsLocal.lean
python3 scripts/nonabelian_yang_mills_local_audit.py
```

The manifest records the targeted build, all-theorem axiom audit, numerical
checks, and SHA-256 hashes. The analytic argument in this note remains the
source of the full local convergence theorem; the partial formalization and
floating-point experiments do not independently certify that entire theorem.
