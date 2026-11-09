# A spectral-edge obstruction and a local interaction taper

Date: 2026-09-11

The connected density fluctuations in the
[finite-coupling enclosure](NONPERTURBATIVE_MATTER_BOUND.md) fail a
necessary regularity test for a local two-derivative response. An exact
finite-sphere identity isolates a positive spectral-boundary term.
It makes the first-harmonic gradient coefficient grow at least linearly
with radius, even at positive mass. In the associated flat momentum
benchmark the same sharp boundary produces an anisotropic |p| cusp.

A specified polynomial taper in the interaction vertices removes this
obstruction in the density channel. It preserves the entire free
determinant, has an all-size gradient bound, and retains an exact
finite-species nonlinear action enclosure. Its homogeneous Gaussian
curvature term must be recomputed: it has the Einstein sign in a finite
coupling range and changes sign at sufficiently strong coupling.

These results do not prove full observable locality, the intended
eight-species Einstein limit, or a TOE. The taper changes the interaction.
Unfiltered observables retain their sharp spectral boundary, and a
positive Euclidean construction still does not supply Lorentzian
reconstruction or microscopic refinement dynamics. No new Lean theorem
is claimed.

## 1. Which connected fluctuation is being tested

Let C_N(x,y) be the massive scalar covariance on the retained product
harmonics, and v_N=C_N(x,x), constant by homogeneity. For q independent
reference Gaussian fields define

\[
 s(x)=q^{-1}\sum_{a=1}^q\phi_a(x)^2,\qquad
 \langle(s(x)-v_N)(s(y)-v_N)\rangle=\frac2q C_N(x,y)^2.  \tag{1}
\]

This is the same centered density that occurs inside the exact
nonlinear remainder in the preceding stage. It is not an invented
graviton observable. Equation (1) is also the exact free density
covariance at q=8. Its nonlocality is not removed by keeping a fixed,
finite number of species.

The test below concerns the kernel K_N=C_N^2. The physical density
covariance has the additional factor 2/q. A local massive derivative
expansion with a bounded kinetic coefficient would give changes of
order p^2 for a small physical momentum p. We first test that property
on the actual finite sphere, without assuming a flat limiting formula.

## 2. An exact positive edge term on the finite sphere

Set r_i=N_i/kappa, P=N1^2N2^2, and c=m^2/kappa^2>0. With z,w the
cosines of the two angular separations, write

\[
 x_\ell=\ell(\ell+1)/N_1^2,\quad y_k=k(k+1)/N_2^2,
 \quad a_{\ell k}=(x_\ell+y_k+c)^{-1}.
\]

The addition theorem gives the complete finite covariance

\[
 C_N(z,w)=\frac{\kappa^2}{16\pi^2P}
   \sum_{\ell,k}(2\ell+1)(2k+1)a_{\ell k}P_\ell(z)P_k(w).       \tag{2}
\]

Let Pi_N(J1,J2) be the eigenvalue of the integral operator with kernel
C_N^2 on a product harmonic of degrees J1,J2. The Funk-Hecke formula
reduces it to an integral of C_N(z,w)^2 P_J1(z)P_J2(w).
Orthogonality and the elementary recurrence for z P_l(z) give

\[
 \boxed{\Pi_N(0,0)-\Pi_N(1,0)=
  \frac1{16\pi^2P}\sum_k(2k+1)
  \left[N_1a_{N_1-1,k}^2+
       \sum_{\ell=0}^{N_1-2}(\ell+1)(a_{\ell+1,k}-a_{\ell k})^2\right].}
                                                               \tag{3}
\]

The algebraic identity behind this decomposition is

\[
 \sum_{\ell=0}^{N-1}(2\ell+1)a_\ell^2
 -2\sum_{\ell=0}^{N-2}(\ell+1)a_\ell a_{\ell+1}
 =Na_{N-1}^2+\sum_{\ell=0}^{N-2}(\ell+1)(a_{\ell+1}-a_\ell)^2.
\]

Both terms are nonnegative. The first is the boundary of the retained
angular spectrum. Since x_l,y_k<1 and sum_k(2k+1)=N2^2,

\[
 \Pi_N(0,0)-\Pi_N(1,0)\ge
             \frac1{16\pi^2N_1(2+c)^2}.               \tag{4}
\]

The physical squared momentum of the first sphere harmonic is
p1^2=2/r1^2=2kappa^2/N1^2. Hence

\[
 \boxed{\frac{\Pi_N(0,0)-\Pi_N(1,0)}{p_1^2}
       \ge\frac{N_1}{32\pi^2\kappa^2(2+c)^2}
       \longrightarrow\infty.}                      \tag{5}
\]

This all-size lower bound disproves a uniform local gradient coefficient
for this unfiltered channel. It also applies to the untapered Gaussian
reference at fixed positive quartic coupling: its self-consistent mass
is bounded above independently of N, so c can be replaced by that upper
bound in (5).

More precisely, along growing product spheres the edge term in (3) is

\[
 \frac1{16\pi^2N_1(1+c)(2+c)}+o(N_1^{-1}),
\]

whereas the difference-square term is O(N1^-2). This follows from
ordinary Riemann sums for the edge and
|a_(l+1,k)-a_(l,k)|<=2(l+1)/(c^2 N1^2) for the bulk.

The audit independently integrates the polynomial finite kernel and
checks (3), including its normalization. No fit to a divergent sequence
is used to prove (5).

## 3. The flat sharp-cutoff cusp

The associated flat comparison has two two-dimensional momentum disks,

\[
 D=\{k=(k_A,k_B): |k_A|\le\kappa,\ |k_B|\le\kappa\},\qquad
 h(k)=\frac{\mathbf1_D(k)}{k^2+m^2}.
\]

Its density bubble is

\[
 \Pi(p)=\int\frac{d^4k}{(2\pi)^4}h(k+p/2)h(k-p/2).
\]

At zero momentum,

\[
 \Pi(0)=\frac1{16\pi^2}\log\frac{(1+c)^2}{c(2+c)}.
\]

The interior denominator has no term linear in p. The intersection of
the shifted disks does: its boundary displacement removes a strip of
width proportional to |p|. For a shift within the first disk, its
weighted boundary loss is

\[
 \frac{2\kappa |p_A|}{(2\pi)^4}
       \int_{|k_B|\le\kappa}
               \frac{d^2k_B}{(\kappa^2+|k_B|^2+m^2)^2}.
\]

The second disk contributes the same expression with A and B exchanged;
overlap of the two removed strips is quadratic in momentum. Therefore

\[
 \boxed{\Pi(p)=\Pi(0)
 -\frac{|p_A|+|p_B|}{8\pi^3\kappa(1+c)(2+c)}
 +O(|p|^2/\kappa^2).}                                \tag{6}
\]

At equal |p|, dividing the momentum equally between the two planes
increases the cusp coefficient by sqrt(2). This leading response is
neither analytic in p^2 nor four-dimensionally rotation invariant.
At c=0.1, kappa=1, the axial cusp coefficient is 0.001745212902.
Independent disk-intersection integrals check (6).

Nonanalytic momentum dependence from sharp cutoffs is an established
regulator effect; see [Morris](https://arxiv.org/abs/hep-th/9508017).
The exact finite-sphere decomposition (3) identifies its counterpart
inside this repository's chosen regulator. We do not need to assume
uniform convergence from (2) to the flat bubble to obtain (5).

This is a failed regularity test for the specified collective response.
It is not a proof that every sharp-cutoff construction fails to recover
Einstein gravity after suitable matching, nor that this scalar density
is a physical graviton.

## 4. A polynomial taper changes the interaction and repairs this test

On the existing harmonic space define

\[
 F_N=(1-\Delta_{N,1}/\kappa^2)(1-\Delta_{N,2}/\kappa^2),
 \qquad \psi_a=F_N\phi_a.                             \tag{7}
\]

Each factor is a second-order local differential operator on the
supplied sphere. Their product is a fourth-order differential operator.
Its finite eigenvalues are (1-x_l)(1-y_k)>0. Replace the scalar
interaction by

\[
 \frac{g}{4q}\int\left(\sum_a\psi_a^2\right)^2dV,
\]

while keeping the original Gaussian kinetic operator, fermion operator,
and integration variables phi unchanged. Thus the entire free
determinant, including the homogeneous Einstein term, is exactly
preserved. No change-of-variable Jacobian is dropped. The vertex and
the operators to which it couples are different from the preceding
untapered interaction.

The covariance of psi has (2) with

\[
 a_{\ell k}^{\,F}
       =\frac{(1-x_\ell)^2(1-y_k)^2}{x_\ell+y_k+c}.     \tag{8}
\]

Identity (3) is still exact. Its edge now contains
(1-x_(N1-1))^4=N1^-4, so

\[
 \mathrm{edge}_F\le\frac1{16\pi^2c^2N_1^5}.
\]

Let D_c=2/c+1/c^2. The derivative with respect to x of
(1-x)^2(1-y)^2/(x+y+c) has magnitude at most D_c. Using
x_(l+1)-x_l=2(l+1)/N1^2 and the exact sum of cubes in (3) gives

\[
 \mathrm{bulk}_F\le\frac{D_c^2}{16\pi^2N_1^2}.
\]

Consequently

\[
 \boxed{0\le
 \frac{\Pi_N^F(0,0)-\Pi_N^F(1,0)}{p_1^2}
 \le\frac{D_c^2+c^{-2}}{32\pi^2\kappa^2}.}            \tag{9}
\]

This is uniform in both sphere sizes. It repairs the divergence in (5)
for the tapered density observable.

It also holds for the tapered self-consistent Gaussian reference below.
That reference replaces (8) by r/(x+y+c+s r), where
r=(1-x)^2(1-y)^2 and s>=0. Differentiation gives

\[
 \partial_x\frac r{x+y+c+s r}
       =\frac{r_x(x+y+c)-r}{(x+y+c+s r)^2}.
\]

The s-dependent numerator terms cancel. The same derivative bound D_c
and the same edge bound therefore hold for every nonnegative shift s.
This remains a reference-Gaussian statement, not a theorem about all
exact interacting correlation functions.

## 5. The repaired flat channel has a controlled quadratic expansion

The flat tapered covariance is

\[
 h_F(k)=\frac{(1-|k_A|^2/\kappa^2)_+^2
                (1-|k_B|^2/\kappa^2)_+^2}{k^2+m^2}.
\]

Its zero extension has square-integrable weak derivatives through
second order. The quadratic zeros at the disk boundaries make both
the function and its first derivative continuous there. Therefore
h_F belongs to H2(R4). The autocorrelation identity

\[
 \Pi_F(0)-\Pi_F(p)
       =\frac12\int\frac{d^4k}{(2\pi)^4}
                      |h_F(k+p)-h_F(k)|^2
\]

has a quadratic expansion. Integration by parts, or Parseval applied
to the cosine expansion, yields

\[
 \boxed{\Pi_F(p)=\Pi_F(0)-\beta(c)|p|^2/\kappa^2
                         +O(|p|^4/\kappa^4),\quad\beta(c)>0.}    \tag{10}
\]

The fourth-order error is bounded by
|p|^4 times the squared L2 norm of the corresponding second directional
derivative of h_F, divided by 24(2pi)^4. Plane rotations and exchange
of the two planes make the quadratic coefficient the same in all four
directions. They do not force a rotation-invariant fourth-order term.

With

\[
 H(u,v)=\frac{(1-u)^2(1-v)^2}{u+v+c},
\]

the coefficient is the positive integral

\[
 \beta(c)=\frac1{16\pi^2}\int_0^1\int_0^1
                                 u\,(\partial_u H)^2du\,dv.     \tag{11}
\]

The finite-sphere ratio in (9) tends to beta(c)/kappa^2 by applying
Riemann sums to its bulk difference squares. Its edge term vanishes
after this normalization. At c=0.1, kappa=1, beta=0.007881967553.
For N1=512,N2=768 the finite ratio is 0.007882133614. The unfiltered
ratio at those same sizes is approximately 0.712198 and has the
diverging lower bound (5).

This restores a local two-derivative expansion in one collective
channel. The sharp projection and the tails of unfiltered observables
remain. Equation (10) is not full microscopic locality, reflection
positivity, or a tensor gravitational Ward identity.

## 6. The exact nonlinear enclosure survives the revised vertex

The Gaussian reference now has the positive operator

\[
 A_s=\Delta_N+m_0^2+\kappa^2 s F_N^2.
\]

Put gamma=g/(16pi^2), r_lk=(1-x_l)^2(1-y_k)^2, and choose s_N as the
unique positive solution

\[
 s_N=\frac{\gamma}{P}\sum_{\ell,k}
       \frac{(2\ell+1)(2k+1)r_{\ell k}}
                   {x_\ell+y_k+c_0+s_Nr_{\ell k}}.     \tag{12}
\]

The right side decreases with s, and the left side increases. Also
s_N^2<=gamma. Completing the square in q^(-1)sum_a psi_a^2 gives
exactly the preceding finite-species argument, now with this filtered
covariance. In particular,

\[
 0\le\frac{\Gamma^F_{q,g}}q-\mathcal M^F_N
       \le\frac{P s_N^2}{2\gamma q}\le\frac P{2q},      \tag{13}
\]

where

\[
 \mathcal M^F_N=\frac{\Gamma_{8,0}}8+
 \frac12\sum_{\ell,k}(2\ell+1)(2k+1)
       \log\left(1+\frac{s_Nr_{\ell k}}{x_\ell+y_k+c_0}\right)
       -\frac{P s_N^2}{4\gamma}.
\]

Thus the taper retains the nonlinear enclosure. It does not turn its
volume-order error into curvature control at fixed q.

## 7. Recomputing curvature reveals a strong-coupling limit

The changed vertex does not inherit the previous explicit curvature
coefficient. A general spectral quadrature formula makes the new
calculation direct. For smooth phi on a neighborhood of [0,1],

\[
 \sum_{\ell=0}^{N-1}(2\ell+1)\phi(\ell(\ell+1)/N^2)
 =N^2\int_0^1\phi(u)du+\mathcal B\phi+O(N^{-2}),
\]
\[
 \mathcal B\phi=\frac{\phi(0)-\phi(1)}3-\frac{\phi'(1)}6.         \tag{14}
\]

To prove it, write the sum as midpoint quadrature of
2x phi(x^2-1/(4N^2)). Expanding the shift gives
-(phi(1)-phi(0))/4; the midpoint boundary correction gives
-(phi(1)-phi(0))/12-phi'(1)/6. The fourth-derivative remainder
and Taylor remainders are bounded, for example, by
110||phi||_(C4)/N^2 on the required neighborhood.
For the logarithms here that neighborhood exists because c0>0;
take N large enough that the shifted arguments remain inside it.

Applying (14) in both variables yields a remainder bounded by
(12500+250rho^2)||Phi||_(C8), where
rho=max(N_i)/min(N_i). This follows by expanding the two
N_i^2-integral, boundary, and remainder operators; the ratios of sizes
are bounded and their remainder norms are at most 110/N_i^2.
The bound is uniform on each fixed compact interval of reference shifts.

Let r(u,v)=(1-u)^2(1-v)^2. Define s_star by

\[
 s_*=\gamma\int_0^1\int_0^1
       \frac{r(u,v)}{u+v+c_0+s_*r(u,v)}du\,dv.         \tag{15}
\]

Set

\[
 H_F=\frac12\int_0^1\int_0^1
     \log\left(1+\frac{s_*r(u,v)}{u+v+c_0}\right)du\,dv
                                      -\frac{s_*^2}{4\gamma}.
\]

For the logarithmic integrand, both its value and its first derivative
vanish at u=1. Its u=0 value is
log[1+s(1-v)^2/(v+c0)]. Thus (14), followed by the stationary-envelope
argument from the preceding stage, proves

\[
 \boxed{\mathcal M_N^F=P H_F+S C_F+O_{c_0,g,\rho}(1),}
\]
\[
 \boxed{C_F=-\frac{J(c_0)}2+
       \frac16\int_0^1
            \log\left(1+\frac{s_*(1-v)^2}{v+c_0}\right)dv.}      \tag{16}
\]

The gap equation has slope at least one, so s_N-s_star=O(S/P).
Stationarity of the volume functional suppresses its shift to O(1).
These statements include changes of the two radii at bounded aspect
ratio. The fixed-q error in (13) remains separate.

Unlike the untapered coefficient, C_F increases without bound as the
reference shift increases. It starts at -J(c0)/2<0, is strictly
increasing, and has exactly one zero. The root s_star also increases
without bound as g grows. At c0=0.1 the zero occurs at approximately

\[
 s_{\rm zero}=32.95490987,\qquad
 g_{\rm zero}=352269.4070.
\]

This is a sign change of the **Gaussian homogeneous curvature
coefficient**, not a proved physical phase transition or an exact
eight-species gravitational threshold. At g=1,100,1000 its values are
approximately -0.4408651, -0.4189166, -0.3547819, respectively, so a
nonzero range with the Einstein sign remains. The model must justify
its physical coupling and phase rather than assume all couplings work.

For comparison with the previous first-order result, the filtered
resolvent has bulk coefficient
int_[0,1]^2 r(u,v)/(u+v+c0) du dv and curvature coefficient

\[
 \frac13\int_0^1\frac{(1-v)^2}{v+c_0}dv
 =\frac{(1+c_0)^2\log(1+1/c_0)-c_0-3/2}{3}>0.
\]

The same finite-q Wick calculation therefore retains a volume term
and an Einstein curvature term at first order in the revised coupling.
No higher-order fixed-q claim is inferred from that check.

## 8. Model decision and reproduction

The sharp spectral edge is now a demonstrated obstacle to the proposed
local collective derivative expansion. A pointwise vertex and narrow
packets did not by themselves remove it. The polynomial taper is a
concrete model revision that fixes this particular response while
preserving the free curvature result and the nonlinear enclosure.
Its changed curvature coefficient restricts the useful Gaussian coupling
range.

The next target is a controlled shape dependence of the full interacting
remainder at the intended finite species count, with the revised
vertices and their contact terms included. Uniform locality for the
physical observable algebra, independent sites, geometric phase
selection and refinement, arbitrary-metric response, Lorentzian
reconstruction, Einstein constraints, Standard Model dynamics, and
the TOE remain unproved.

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/spectral_edge_locality_audit.py

The [audit](scripts/spectral_edge_locality_audit.py) checks exact finite
kernel integrals, positive edge decomposition, all-size gradient bounds,
independent flat integrals, the taper's quadratic response, revised
Gaussian gap and curvature expressions, and the strong-coupling sign
change. The [report](data/spectral_edge_locality_audit.json) records
source hashes and scope. Earlier research artifacts and Lean sources
are preserved.
