# Fermions remove the leading scalar obstruction, but leave a non-Einstein term

Date: 2026-09-10

Adding a specified first-order fermion determinant to eight real scalars
cancels the fourth-power cutoff shape response found in
[the scalar-only matrix benchmark](GEOMETRIC_SPECTRAL_INDUCTION.md).
The complete determinant then has quadratic cutoff growth and the
Einstein sign near the round product-sphere background. No spectral
window has been discarded to obtain this improvement.

The remaining term can be computed analytically. Its shape dependence
fails a necessary higher-variation identity of the Einstein functional.
A constant nonminimal scalar curvature coupling cannot repair the
whole function. The result therefore revises the scalar-only assessment:
fermionic balance is a viable cancellation mechanism in this benchmark,
but it does not yet produce Einstein dynamics.

The field content, Euclidean matrix geometry, and operator choices are
supplied. The positive finite fermion determinant is not a proof of
Lorentzian reconstruction. No supersymmetry, microscopic protection of
the cancellation, local finite-spin phase, gravitational constraint
algebra, recovered Standard Model, or TOE is established. No new Lean
theorem is claimed.

## 1. A first-order fermion operator on the same matrix geometry

Let N=L+1 be the matrix size of each fuzzy sphere, with spin
\(j=(N-1)/2\). On its two-component matrix spinors define

\[
 D_N=I+\sum_{a=1}^3\sigma_a\operatorname{ad}(J_a).
\]

Angular-momentum addition gives the exact spectrum

\[
 +(\ell+1)\quad\hbox{with multiplicity }2\ell+2,
 \qquad -\ell\quad\hbox{with multiplicity }2\ell,
 \qquad 0\leq\ell\leq N-1.
\]

The second branch has zero multiplicity at ell=0. There are 2N^2
spinor components and no zero eigenvalues. The positive top branch is
unpaired on a single finite sphere. The standard spin-one-half spectrum
is reviewed, for example, in section 4 of
[Digal and Padmanabhan](https://arxiv.org/abs/1004.3252).
Only that spectrum is used here; no higher-spin statistics proposal
from that literature is assumed.

For the product, introduce one auxiliary two-component factor and set

\[
 Q=\tau_1\otimes(D_N/r_1)\otimes I
   +\tau_2\otimes I\otimes(D_N/r_2).
\]

The two sphere factors commute, while the tau matrices anticommute, so

\[
 Q^2=I_\tau\otimes[(D_N/r_1)^2\otimes I
                              +I\otimes(D_N/r_2)^2],
 \qquad\{Q,\tau_3\}=0.                                  \tag{1}
\]

Q is Hermitian, first order in the matrix angular derivatives, and has
a paired nonzero spectrum. Consequently the finite Grassmann integral
with kernel \(m+iQ\) has

\[
 \det(m+iQ)=\prod_{\omega>0}(m^2+\omega^2)>0,
 \qquad\Gamma_F=-\tfrac12\operatorname{Tr}\log(m^2+Q^2).
\]

The statistics sign is the ordinary fermionic determinant sign; we
have not inserted anticommuting scalar regulator fields. The auxiliary
factor doubles the product spinor spectrum, giving the continuum heat
coefficients of two Dirac species. This finite Euclidean construction
does not itself prove that those species form a physical Lorentzian
microscopic phase.

The audit constructs Q explicitly through dimension 648, checks (1)
and its spectrum, and compares the determinant from complex pivoted LU
with the squared-spectrum formula.

## 2. Exact finite counting and the complete matter determinant

For one sphere, the scalar and squared-Dirac heat traces are

\[
 H_B(t)=\sum_{\ell=0}^{N-1}(2\ell+1)e^{-t\ell(\ell+1)},
\]
\[
 H_F(t)=4\sum_{n=1}^{N-1}n e^{-tn^2}+2N e^{-tN^2}.
\]

Thus \(H_B(0)=N^2\), \(H_F(0)=2N^2\). Q has 8N^4 components,
exactly matching eight real product-sphere scalars. Their heat-trace
combination is

\[
 \mathcal S_N(s)=8H_B(s/r_1^2)H_B(s/r_2^2)
                  -2H_F(s/r_1^2)H_F(s/r_2^2),
 \qquad\mathcal S_N(0)=0.                               \tag{2}
\]

This equality is a chosen matter-content condition, not a consequence
of a proved supersymmetry. The massless scalar constant modes may be
removed to define the ordinary Gaussian determinant; their fixed number
does not affect shape derivatives or the leading cutoff result.

With \(r_1=re^u,r_2=re^{-u}\), the full massless action is

\[
 \Gamma_N(u)=4\sum_{\ell,k}'(2\ell+1)(2k+1)
 \log[\ell(\ell+1)e^{-2u}+k(k+1)e^{2u}]
 -\sum_{n,m}w_nw_m\log[n^2e^{-2u}+m^2e^{2u}],             \tag{3}
\]

up to shape-independent dimensional factors. Here
\(w_n=4n\) for n<N and \(w_N=2N\). Both finite spectra, including
their highest modes, occur in (3). It is not an intermediate-window
approximation.

Matter cancellations in induced-gravity models are an established
possibility; see [Frolov, Fursaev, and Zelnikov](https://arxiv.org/abs/hep-th/9607104)
and [Visser's review](https://arxiv.org/abs/gr-qc/0204062).
The specific complete determinant and its cutoff-shape term below
are the benchmark being tested here.

## 3. A quadrature identity exposes what survives the cancellation

Define

\[
 f_z(x)=2x e^{-zx^2},\quad
 I(z)=\int_0^1f_z(x)dx=\frac{1-e^{-z}}z,
\]

and let M_N and T_N denote composite midpoint and trapezoidal quadrature
on [0,1] with spacing 1/N. The spectral sums have the exact forms

\[
 H_B(z/N^2)=N^2e^{z/(4N^2)}M_N f_z,
 \qquad\tfrac12H_F(z/N^2)=N^2T_N f_z.                    \tag{4}
\]

The top-mode weight in H_F is essential to the second identity. With
\(\delta f_z'=f_z'(1)-f_z'(0)\), quadrature expansion gives

\[
 M_N f_z=I(z)-\frac{\delta f_z'}{24N^2}+O(N^{-4}),
 \qquad T_N f_z=I(z)+\frac{\delta f_z'}{12N^2}+O(N^{-4}).
\]

It follows that

\[
 H_B(z/N^2)-\tfrac12H_F(z/N^2)
 \longrightarrow d(z):=\frac{1+(z-1)e^{-z}}2.              \tag{5}
\]

This limit is uniform with any fixed number of z derivatives on compact
positive z intervals. In particular, the boundary correction does not
vanish when the leading number of bosonic and fermionic modes agrees.

Put \(a=e^{-2u}\), \(b=e^{2u}\), and rescale proper time by
\(s=r^2t/N^2\). Equations (2)--(5) imply

\[
 \frac{\mathcal S_N(r^2t/N^2)}{N^2}
 \longrightarrow8[d(at)I(bt)+I(at)d(bt)].                 \tag{6}
\]

The order N^4 term cancels. The remaining contribution is order N^2,
at the same cutoff order at which an induced Einstein coefficient
could occur. Its shape dependence must still be checked.

## 4. Passing the full determinant variations through the limit

The compact-t expansion alone is insufficient to integrate from zero
to infinity. The following bounds justify that step for shape variations
through fourth order, uniformly on a fixed compact u interval. Constants
may depend on that interval and the derivative order, but not on N.

Write \(\mathcal D_N(z)=H_B(z/N^2)-H_F(z/N^2)/2\).
The midpoint and trapezoid error estimates with
\(\int_0^1|f_z''(x)|dx\) give, also after up to four z-log derivatives,

\[
 |\mathcal D_N(z)|\leq Cz\quad(0<z\leq1),\qquad
 |\mathcal D_N(z)|\leq C\quad(1\leq z\leq C_0N^2).
\]

To see the uniformity of the second bound, rescale x by sqrt(z) in
\(\int|f_z''|\). The integral is bounded independently of z>=1.
Applying z derivatives only inserts Gaussian-weighted polynomials.
The extra exponential in (4) stays bounded when z<=C0 N^2; its
difference from one contributes at most Cz times the normalized heat
sum, which is O(1/z). At small z the same derivative integrals and
the exponential correction are O(z).

The corresponding normalized heat sums and their log derivatives are
bounded by C/t for \(1\leq t\leq N^2\). Using the exact product
difference in (2), for p=1,...,4 one obtains

\[
 \frac{|\partial_u^p\mathcal S_N(r^2t/N^2)|}{N^2}
 \leq
 \begin{cases}
 Ct,&0<t\leq1,\\
 C/t,&1\leq t\leq N^2.
 \end{cases}                                           \tag{7}
\]

For t>=N^2, the nonconstant modes have a fixed gap in t/N^2. The same
left side is bounded by
\(CN^{-2}(1+t/N^2)^p e^{-ct/N^2}\), with a possibly larger polynomial
power for a common bound. The constant scalar contribution has zero
shape derivative. Its integral with dt/t over that tail is O(N^-2).

Thus the small-time integral is uniformly bounded by C epsilon, the
intermediate large-time tail by C/T, and the remaining tail by C/N^2.
Together with (6) on [epsilon,T], these estimates prove convergence
of the complete first through fourth shape derivatives. Integrating
the first derivative also proves convergence of action differences.
No convergence rate for the whole normalized action is inferred from
the finite numerical grids.

The limiting function, up to a shape-independent constant, is

\[
 W(u)=-4\int_0^\infty\frac{dt}{t}
             [d(at)I(bt)+I(at)d(bt)].                     \tag{8}
\]

Let

\[
 S=a+b=2\cosh(2u),\qquad
 F=S\log S-a\log a-b\log b
   =S\log S-4u\sinh(2u).
\]

Integrating the exponentials in (8), or differentiating the elementary
integral \(\int(1-e^{-at})(1-e^{-bt})t^{-2}dt=F\), gives

\[
 \boxed{W(u)=4\log S-4SF.}                               \tag{9}
\]

Specifically,
\([\Gamma_N(u)-\Gamma_N(0)]/N^2\to W(u)-W(0)\), and the first
through fourth normalized derivatives converge to those of W.
This proves cancellation of the earlier N^4 obstruction in the complete
determinant, rather than only in a selected proper-time interval.

## 5. The sign improves; the full Einstein matching test still fails

At the equal-radius background,

\[
 W''(0)=80-128\log2\simeq-8.722839,
\]
\[
 W''''(0)=1408-2048\log2\simeq-11.565426.
\]

The complete matter shape Hessian has become negative at leading order,
as does the Euclidean Einstein term with positive Newton coefficient.
For example, the computed \(\Gamma_N''(0)/N^2\) is approximately
-8.81406 at N=32, -8.73035 at N=128, and -8.72342 at N=512.

On this fixed-volume family, a pure Einstein term plus a volume term
has the form C0+C1 cosh(2u), so its fourth derivative must equal four
times its second derivative at zero. Instead,

\[
 W''''(0)-4W''(0)=1088-1536\log2\simeq23.325931\ne0.       \tag{10}
\]

For example, the elementary bound log(2)<7/10 already proves positivity
of (10). An overall normalization and a volume counterterm cannot fix
this identity. The residual is at leading order N^2; it is not a
subleading finite-cutoff correction to an Einstein action.

This is a necessary homogeneous Euclidean matching test. It neither
proves a ghost from the sign nor tests all metric components, wave
directions, or Lorentzian gravitational propagation.

## 6. A constant scalar curvature coupling is insufficient

As an explicit further model variation, replace the scalar operator by
\(\Delta+\xi R\), with fixed \(\xi\geq0\). On this product, this
replaces each angular eigenvalue \(\ell(\ell+1)\) by
\(\ell(\ell+1)+2\xi\). The scalar operator stays nonnegative.
For xi>0 its former constant mode is positive; its finitely many
contributions to normalized shape derivatives vanish as N grows.

Equation (4) gains the scalar factor \(e^{-2\xi z/N^2}\). Repeating
the same quadrature calculation gives

\[
 \boxed{W_\xi(u)=4\log S+(8\xi-4)SF.}                    \tag{11}
\]

The proof of the variation limit extends for each fixed nonnegative xi.
One can tune individual derivatives with xi. No constant xi, however,
makes (11) equal C0+C1 cosh(2u) with C1 nonzero on an open u interval.
All these functions are real analytic. Equality on such an interval
would extend to all real u, but as u tends to positive infinity,

\[
 \log S=2u+o(1),\qquad SF=1+4u+o(1),
\]

so W_xi grows at most linearly, while a nonzero cosh term grows
exponentially. The no-matching statement is for this one constant
curvature coupling and these fixed-size matrix operators, not for
arbitrary matter interactions or regulator changes.

## 7. The geometric window still has the expected Einstein coefficient

Below the matrix edge, the continuum sphere expansions are

\[
 H_B(t)=1/t+1/3+O(t),\qquad H_F(t)=2/t-1/3+O(t).
\]

Their product supertrace cancels the volume coefficient and gives

\[
 \mathcal S(s)=\frac{V}{(4\pi s)^2}[2sR+O(s^2)]
\]

at xi=0. Consequently the properly separated window retains

\[
 \Gamma_{EH,\Lambda,\mu}
 =-\frac{\Lambda^2-\mu^2}{16\pi^2}\int\sqrt gR,
 \qquad G^{-1}=\frac{\Lambda^2-\mu^2}{\pi}>0.
\]

The audit verifies this window response independently. For nonminimal
scalars the supertrace coefficient becomes (2-8xi)R, so its positive
Newton sign requires xi<1/4. That continuum coefficient does not
remove the finite matrix edge term in (11), even at xi=1/4 where the
window's Einstein coefficient cancels. The full determinant remains
the controlling physical test for this specified microscopic model.

## 8. Model decision and outstanding requirements

The scalar-only sign obstruction does not survive the addition of the
specified fermionic matter. Future microscopic matching should retain
the possibility of boson/fermion balance rather than infer a general
no-go from scalar loops. The cancellation demonstrated here uses the
complete determinant, including the matrix edge, and produces a
nonzero curvature response.

The remaining result also prevents a premature Einstein claim. Matching
mode counts and the sign of one derivative does not fix the full
geometry dependence. The explicit leading function (9) identifies the
term that a revised regulator, measure, or dynamics must change. The
constant curvature coupling (11) does not suffice.

The matter multiplicities have been chosen to balance this constructed
operator. They are not predicted Standard Model content, and no symmetry
has been shown to protect them or their couplings under interactions.
The growing Euclidean matrix geometry is still supplied, with no proved
uniform local embedding into the original fixed-spin carrier. Physical
state selection, Lorentzian reconstruction, the gravitational mode
reduction, and the nonlinear normal/spatial clock algebra all remain
open. The full TOE objective remains unachieved.

## 9. Reproduction

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/balanced_matter_induction_audit.py
```

The audit checks three dense first-order fermion constructions, sixteen
exact quadrature representations and their limits, four independent
integrals for W, thirty complete-determinant cases including nonminimal
couplings, four finite-variation cases, and four continuum-window cases.
It writes `data/balanced_matter_induction_audit.json` with eight source
hashes. The asymptotic convergence argument above is analytical; the
reported floating-point tests are not interval certificates. Earlier
sources and reports are preserved. No Lean source is changed.
