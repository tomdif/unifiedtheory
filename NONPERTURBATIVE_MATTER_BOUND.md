# A finite-coupling enclosure and a controlled many-species curvature limit

Date: 2026-09-11

The [local symbol interaction](LOCAL_SYMBOL_INTERACTION.md) retained the
homogeneous Einstein curvature dependence at first order in its quartic
coupling. This stage obtains an exact inequality for the full nonlinear
partition function at every nonnegative coupling and every finite species
count. It encloses the action per species between a self-consistent
Gaussian expression and that expression plus an explicit error no larger
than P/(2q), where P is the number of scalar modes per species and q is
the number of real scalar species.

The Gaussian expression has a size-independent curvature remainder on
the supplied product-sphere family. Its curvature coefficient has the
Einstein sign for all positive coupling, proved by a formula consisting
entirely of negative terms. The exact enclosure then controls the full
nonlinear second and fourth shape variations in a specified joint limit
of increasing geometry and species count. This is not a coupling series.

The inequality also applies at q=8, but does not prove its large-radius
Einstein limit. Growing q at fixed proper cutoff makes the total inverse
Newton coefficient grow, rather than establishing a fixed physical
Newton constant. Independent microscopic sites, a refinement dynamics,
arbitrary-metric response, Lorentzian gravity, and the TOE remain open.
The arguments are analytical, with executable checks, not new Lean
theorems.

## 1. The same positive interaction with a species parameter

Use the real harmonic symbol spaces and the exact free spectra from
the preceding stage. Let q be a positive multiple of eight, with q/8
copies of its first-order fermion operator. There are q real scalars
and exactly qP fermion components, where

\[
 P=N_1^2N_2^2,\quad S=N_1^2+N_2^2,\quad
 r_i=N_i/\kappa,\quad V=16\pi^2P/\kappa^4,
 \quad\int\sqrt g R=32\pi^2S/\kappa^2.
\]

The bare scalar and fermion masses are the same m0>0. Set
c0=m0^2/kappa^2. Keep the fermions free, and take

\[
 S_{q,g}=\frac12\sum_{a=1}^q
       \langle\phi_a,(\Delta_N+m_0^2)\phi_a\rangle
       +\frac{g}{4q}\int\left(\sum_{a=1}^q\phi_a^2\right)^2dV,
 \qquad g\ge0.                                       \tag{1}
\]

At q=8 this is exactly the preceding scalar interaction with
lambda=6g/q=3g/4. Varying q supplies a family of models; it is not a
claim that physical matter contains infinitely many species. Standard
large-species vector-model methods and variational formulations are
reviewed by [Moshe and Zinn-Justin](https://arxiv.org/abs/hep-th/0306133).
Here square completion gives a direct finite-q inequality without
evaluating an auxiliary-field contour.

Let lambda_alpha be the dimensionless scalar eigenvalues
ell(ell+1)/N1^2+k(k+1)/N2^2, with their full multiplicities. Define

\[
 T_N(c)=\sum_\alpha\frac1{\lambda_\alpha+c},\qquad
 v_N(c)=\frac{\kappa^2 T_N(c)}{16\pi^2P}.
\]

The addition theorem implies that v_N is the constant diagonal of the
Gaussian covariance (Delta_N+kappa^2 c)^(-1). This statement holds
exactly at finite cutoff.

## 2. The unique reference mass and an exact nonlinear identity

For g>0 put gamma=g/(16pi^2). Choose c_N>c0 to solve

\[
 \boxed{c_N-c_0=\gamma T_N(c_N)/P.}                    \tag{2}
\]

The left side minus the right side has derivative
1+(gamma/P)sum_alpha(lambda_alpha+c)^(-2)>1. It is negative at c0
and positive sufficiently far to the right, so (2) has exactly one
solution. Since T_N(c)/P<=1/c,

\[
 (c_N-c_0)c_N\le\gamma,\qquad
 (c_N-c_0)^2\le\gamma.                               \tag{3}
\]

This is a variational Gaussian mass. We have not identified it with
the exact physical pole mass at finite q.

Set sigma=kappa^2(c_N-c0), and let the reference Gaussian measure have
this increased mass. Write s(x)=q^(-1)sum_a phi_a(x)^2. The change from
the original mass, together with the quartic interaction, obeys the
pointwise identity

\[
 \frac{q\sigma}{2}s-\frac{qg}{4}s^2
       =\frac{q\sigma^2}{4g}
            -\frac{qg}{4}(s-\sigma/g)^2.              \tag{4}
\]

Equation (2) is exactly sigma/g=v_N(c_N). With all normalized Gaussian
measures and the unchanged fermion determinants included, (4) yields

\[
 \frac{\Gamma_{q,g}}q=\mathcal M_N+\varepsilon_{N,q},   \tag{5}
\]
\[
 \mathcal M_N=
 \frac{\Gamma_{8,0}(c_0)}8
 +\frac12\sum_\alpha
       \log\frac{\lambda_\alpha+c_N}{\lambda_\alpha+c_0}
 -\frac{P(c_N-c_0)^2}{4\gamma},                       \tag{6}
\]
\[
 \varepsilon_{N,q}=-\frac1q\log\left\langle
   \exp\left[-\frac{qg}{4}\int(s-v_N)^2dV\right]
                         \right\rangle_{c_N}.        \tag{7}
\]

The expectation in (7) still integrates every field configuration.
Its integrand lies in (0,1], hence epsilon>=0. Gaussian independence
of the q species gives, at each point,

\[
 \langle(s-v_N)^2\rangle_{c_N}=2v_N^2/q.
\]

Jensen's inequality in (7), followed by (3), proves the exact enclosure

\[
 \boxed{0\le\frac{\Gamma_{q,g}}q-\mathcal M_N
       \le\frac{gVv_N^2}{2q}
       =\frac{P(c_N-c_0)^2}{2\gamma q}
       \le\frac{P}{2q}.}                             \tag{8}
\]

This holds at every finite cutoff and every g>0; at g=0 the error is
zero by continuity. It does not assume the interacting configurations
are homogeneous or Gaussian. The reference covariance is homogeneous,
which allows the Gaussian mean of the completed square to be computed.
The action bound alone does not prove Gaussianity of all correlations.

For fixed geometry, (8) proves that Gamma_q,g/q tends to M_N as q
increases through multiples of eight. For finite q it supplies an
explicit error, rather than silently identifying a saddle calculation
with the full partition function.

## 3. Finite coupling and the uniform geometric expansion

At fixed positive c0 and bounded aspect ratio rho=max(N_i)/min(N_i),
the previous [full resolvent bound](LOCAL_SYMBOL_INTERACTION.md#4-exact-first-derivative-in-the-interaction-coupling)
gives, uniformly on every compact mass interval with c>=c0,

\[
 T_N(c)=P A_0(c)+S A_1(c)+R_N(c),\qquad |R_N(c)|\le B(c_0,\rho),
                                                               \tag{9}
\]
\[
 A_0(c)=c\log c-2(c+1)\log(c+1)+(c+2)\log(c+2),
\]
\[
 A_1(c)=\frac13\log\frac{(c+1)^2}{c(c+2)}
       +\frac16\left[\frac1{c+1}-\frac1{c+2}\right].
\]

Both functions are positive. Also
A0'(c)=log[c(c+2)/(c+1)^2]<0. The limiting reference mass c_star is
the unique root

\[
 c_*-c_0=\gamma A_0(c_*).                              \tag{10}
\]

Since the finite gap equation has slope at least one, evaluating it
at c_star and using (9) gives

\[
 |c_N-c_*|\le\gamma\left[\frac SP A_1(c_*)
                                      +\frac{B(c_0,\rho)}P\right].       \tag{11}
\]

In particular c_N-c_star=O(S/P), uniformly on the aspect family.
Expansion of this equation also gives the checked first correction

\[
 c_N-c_*=
 \frac{\gamma A_1(c_*)}{1-\gamma A_0'(c_*)}\frac SP+O(P^{-1}).
                                                               \tag{12}
\]

Define antiderivatives

\[
 L_0(c)=\tfrac12[c^2\log c-2(c+1)^2\log(c+1)+(c+2)^2\log(c+2)],
\]
\[
 L_1(c)=-A_0(c)/3-\tfrac16\log[(c+2)/(c+1)],
 \qquad L_i'=A_i.
\]

Integrating (9) between c0 and c_N and using the complete free action
from the [proper-resolution theorem](PROPER_RESOLUTION_INDUCTION.md)
puts (6) in the form

\[
 \mathcal M_N=P H(c_N)+S C(c_N)+O_{c_0,g,\rho}(1),
\]
\[
 H(c)=\tfrac12[L_0(c)-L_0(c_0)]-(c-c_0)^2/(4\gamma),
\]
\[
 C(c)=-J(c_0)/2+\tfrac12[L_1(c)-L_1(c_0)].             \tag{13}
\]

The essential cancellation is H'(c_star)=0. Thus the shift in (11)
changes P H only by O(P(S/P)^2)=O(1). Its change to S C is also O(1),
because S^2/P=(rho+rho^(-1))^2. Consequently

\[
 \boxed{\mathcal M_N=P H_*+S C_*+O_{c_0,g,\rho}(1),
 \quad H_*=H(c_*),\quad C_*=C(c_*).}                  \tag{14}
\]

This uniform remainder includes the mass feedback; the gap equation
has not been solved only at the round background.

An explicit bound can be obtained without differentiating an unknown
remainder. Let a=A1(c0), B=B(c0,rho), Delta=c_max-c0, where
c_max=(c0+sqrt(c0^2+4gamma))/2. Let A be the preceding balanced free
action remainder bound, and Rrho=(rho+rho^(-1))^2. Since
|H''|<=1/(2c0^2)+1/(2gamma), a sufficient error bound in (14) is

\[
 \frac A8+\frac{B\Delta}{2}
 +\frac{\gamma^2}{4}(c_0^{-2}+\gamma^{-1})
             [a^2R_\rho+4aB+B^2]
 +\frac{a\gamma}{2}[aR_\rho+2B].                     \tag{15}
\]

The constants are loose and depend on fixed coupling and bare mass,
but not on the sphere sizes. Formula (12) uses the smoothness of A0,A1
and the bounded R_N itself; a derivative bound on R_N is not required.

## 4. The Einstein sign survives every positive coupling

Set l(c)=log[(c+2)/(c+1)]>0. The coefficient from the preceding free
theorem satisfies J(c)=(A0(c)+l(c))/2. Substitution into (13) gives

\[
 \boxed{C_*=-\frac{A_0(c_0)}{12}-\frac{l(c_0)}6
                -\frac{A_0(c_*)}6-\frac{l(c_*)}{12}<0.}        \tag{16}
\]

Every term is strictly negative. Thus the self-consistent curvature
term keeps the Einstein sign at all g>=0. As g grows, c_star increases,
and C_star increases from -J(c0)/2 toward the still-negative limit
-A0(c0)/12-l(c0)/6. This is an all-coupling identity, not numerical
extrapolation from a weak-coupling expansion.

For c0=0.1:

| g | c_star | H_star | C_star |
|---:|---:|---:|---:|---:|
| 0 | 0.100000 | 0 | -0.441189 |
| 1 | 0.107004 | 0.00195779 | -0.438927 |
| 10 | 0.164575 | 0.0179793 | -0.422557 |
| 100 | 0.544823 | 0.115575 | -0.359617 |
| 1000 | 2.147339 | 0.398940 | -0.277825 |

In geometric notation, the Gaussian expression per species is

\[
 \mathcal M_N=\frac{H_*\kappa^4}{16\pi^2}V
      +\frac{C_*\kappa^2}{32\pi^2}\int\sqrt g R+O(1).             \tag{17}
\]

The associated inverse Newton coefficient per species, in the Euclidean
Einstein convention, is -C_star kappa^2/(2pi)>0. The volume term is
positive at g>0 and has not been dynamically tuned away. It cancels
in the exact-volume comparisons below, which does not solve the
cosmological-constant problem.

## 5. What the finite-q bound does and does not settle

Combining (8) and (14) gives the full nonlinear statement

\[
 \frac{\Gamma_{q,g}}q=P H_*+S C_*+O(1)+\varepsilon_{N,q},
 \quad0\le\varepsilon_{N,q}\le P/(2q).                \tag{18}
\]

At bounded aspect ratio, P is of order n^4 and S of order n^2,
where n=min(N_i). Thus the enclosure controls the curvature scale if
q/n^2 tends to infinity. At fixed q, the bound alone is too large.

There are nevertheless finite eight-species consequences. Compare
(N1,N2)=(K,K) with (4K/3,3K/4), for K a multiple of twelve, so P and
V agree exactly. Let delta M be the computed Gaussian action difference
per species and let E0,E1 denote the two explicit upper errors in (8).
The exact full interacting shape difference obeys

\[
 \delta\mathcal M-E_0
     \le\frac{\Gamma_{q,g}(\mathrm{shape})-\Gamma_{q,g}(\mathrm{round})}{q}
     \le\delta\mathcal M+E_1.                         \tag{19}
\]

At c0=0.1, g=1, q=8, K=12, this interval is approximately
[-31.84965,-11.41883], establishing a negative finite shape change.
At K=24 it widens to approximately [-247.4514,75.2226], which no
longer decides the sign. A wide enclosure is inconclusive, not a
counterexample to Einstein behavior. These endpoints are floating-point
evaluations of the analytical bounds, not interval-arithmetic certificates
or direct numerical integrations of the large field space.

## 6. Full interacting shape variations in a controlled joint limit

For k>=2 set K=[k(k+1)]^2 and h=log((k+1)/k). Use the exact-volume
pairs from the previous stages,

\[
 (K,K),\quad(k(k+1)^3,k^3(k+1)),\quad((k+1)^4,k^4),
\]

with negative shapes obtained by swapping factors. Every pair has
P=K^4 and the same species count within its stencil. Define
E_q(u)=Gamma_q,g(u)/(q K^2). Its volume term is independent of u.
The Gaussian part from (14) has shape dependence

\[
 E_G(u)=\text{constant}+2C_*\cosh(2u)+O(K^{-2}).
\]

At each stencil point the additional error in (18), divided by K^2,
lies in [0,K^2/(2q)]. Therefore the symmetric differences

\[
 D_2=[2E_q(h)-2E_q(0)]/h^2,\quad
 D_4=[2E_q(2h)-8E_q(h)+6E_q(0)]/h^4
\]

differ from their Gaussian values by at most

\[
 \boxed{|D_2-D_{2,G}|\le K^2/(qh^2),\qquad
        |D_4-D_{4,G}|\le4K^2/(qh^4).}                 \tag{20}
\]

These constants use the nonnegative range of the errors: the positive
and negative stencil weights each sum to two for D2 and eight for D4.
The Gaussian remainder contributes O(K^-2 h^-4), which already tends
to zero. It follows that whenever q is a multiple of eight and

\[
 \frac{q h^4}{K^2}\longrightarrow\infty,
\]

the **full finite-coupling partition functions**, not only their
Gaussian estimates, satisfy

\[
 \boxed{D_2\longrightarrow8C_*,\quad
        D_4\longrightarrow32C_*,\quad D_4-4D_2\longrightarrow0.} \tag{21}
\]

For example q_k=8k^16 satisfies the requirement: K grows as k^4 and
h as 1/k, so the full fourth-difference uncertainty in (20) is O(k^-4).
The audit evaluates the complete Gaussian spectra and gives the
analytical full-action enclosures around their stencils. It does not
claim to integrate the enormous q_k-species field spaces numerically.

The total inverse Newton coefficient of (17) before dividing by q is
-q C_star kappa^2/(2pi). It diverges in this joint limit at fixed kappa.
Dividing the action by q is useful for the controlled mathematical
limit; it is not a derivation of finite physical Newton coupling.
A justified physical scaling and control at the intended finite matter
content remain necessary.

## 7. Remaining target and reproduction

The first-order coupling restriction has been removed in a controlled
many-species limit. An exact bound also constrains the original
eight-species model, but its error does not yet close the curvature-scale
gap as geometry grows. The next target is the **shape dependence of
epsilon_N,q at fixed q**, including any volume contribution that cancels
in (19), rather than another bound on its absolute size alone.

No symmetry protects the matched bare masses once the scalars interact;
the fermions remain free. The carrier, Euclidean geometry, proper-cutoff
rule, and interaction are supplied. A selected microscopic geometric
phase, independent local site algebra, refinement law, arbitrary-metric
effective action, Lorentzian reconstruction, gravitational constraints,
Standard Model dynamics, and the original TOE objective are unproved.

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/nonperturbative_matter_bound_audit.py

The [audit](scripts/nonperturbative_matter_bound_audit.py) checks square
completion and coefficient identities, independent coefficient integrals,
finite gap equations and geometric remainders, exact finite-q radial
integrals, eight-species shape enclosures, and the joint-limit stencils.
The [report](data/nonperturbative_matter_bound_audit.json) distinguishes
Gaussian evaluations from full-partition enclosures and records source
hashes. Older research artifacts and Lean sources are preserved.
