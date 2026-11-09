# Nonabelian Yang–Mills heat: curvature control and energy-stable approximations

Date: 2026-11-09

This continues [the local Fourier-cutoff theorem](NONABELIAN_YANG_MILLS_LOCAL_LIMIT.md).
There are three distinct results here: a curvature maximum principle for the
continuum equation, an energy-defect bound for the existing DeTurck cutoffs,
and a second, exactly dissipative finite-dimensional approximation that
exists for all nonnegative times. The last result is global at each finite
cutoff; it does not establish a global continuum limit of that approximation.
These are applications of established methods, with no novelty claim.

## 1. The curvature equation closes in two dimensions

Work on the unit flat two-torus with smooth periodic su(m)-valued connection
A=A1 dx1+A2 dx2. Define

\[
 F=\partial_1 A_2-\partial_2 A_1+[A_1,A_2],\quad
 D_j=\partial_j+[A_j,\cdot],\quad \phi=\partial_jA_j,
 \qquad G(A)=(-D_2F,D_1F).
\]

The original Yang–Mills heat equation is A_t=G(A), and the DeTurck equation
from the previous note is A_t=G(A)+D_A phi. Use the positive invariant inner
product on su(m)

\[
 \langle X,Y\rangle=-m^{-1}\operatorname{Re}\operatorname{tr}(XY),
 \quad |X|^2=\langle X,X\rangle,\quad
 \mathcal E(A)=\tfrac12\int_{\mathbb T^2}|F|^2.
\]

This is the normalized Hilbert–Schmidt norm, not the operator norm of the
previous note. It satisfies |X|<=||X||op, so the previous upper bounds still
apply. Under the imaginary-quaternion representation of su(2), this inner
product is the ordinary dot product on R^3, and [u,v]=2u cross v.

Curvature variation in direction V is

\[
 d_A V=D_1V_2-D_2V_1.
\]

Consequently the DeTurck curvature obeys the exact equation

\[
 F_t=(D_1^2+D_2^2)F+[F,\phi]. \tag{1}
\]

Indeed d_A G=D1(D1 F)+D2(D2 F), while
d_A(D_A phi)=[D1,D2]phi=[F,phi]. There is only one curvature component in two
dimensions; no additional interaction between different curvature components
remains. This is a dimension-specific statement.

Ad-invariance gives <[a,u],v>=-<u,[a,v]>. Apply the product rule twice and
use <F,[F,phi]>=0 to obtain the pointwise identity

\[
 (\partial_t-\Delta)|F|^2=-2\bigl(|D_1F|^2+|D_2F|^2\bigr)\le0. \tag{2}
\]

The scalar maximum principle on the compact torus now gives

\[
 \boxed{\|F(t)\|_{L^\infty}\le\|F(0)\|_{L^\infty}.} \tag{3}
\]

For completeness, apply the maximum argument to |F|^2-epsilon*t: a new
positive-time maximum has nonnegative time derivative and nonpositive
Laplacian, contradicting (2). Let epsilon decrease to zero. For the W_q
initial data of the earlier theorem, apply this at time delta>0 and let
delta decrease to zero; continuity in W_q, q>=3, supplies uniform curvature
continuity at zero. The estimate holds throughout any smooth existence
interval and has no lifespan-dependent constant.

Integrating (2), with periodic boundary terms zero, also gives

\[
 \boxed{\mathcal E(A(t))+\int_0^t\|G(A(u))\|_{L^2}^2du
                 =\mathcal E(A(0)).} \tag{4}
\]

Here ||G||_2^2=||D1 F||_2^2+||D2 F||_2^2. The DeTurck gauge term contributes
zero to the energy derivative. These identities control curvature, rather
than the full gauge-dependent connection norm. In particular a bounded
curvature norm cannot simply be substituted for the W_q hypothesis in the
previous contraction proof: large pure-gauge potentials can have zero
curvature. A global continuation argument needs additional gauge and
regularity estimates.

## 2. Quantify the existing DeTurck projection's energy error

Let P_N be the orthogonal Fourier projection to |k|infinity<=N, and Q_N=I-P_N.
The previously constructed approximation satisfies

\[
 (A_N)_t=\Delta A_N+P_N\mathcal N(A_N)
         =G(A_N)+D_{A_N}\phi_N+r_N,\qquad
 r_N=-Q_N\mathcal N(A_N). \tag{5}
\]

The full energy variation is

\[
 d\mathcal E_A[V]=\int\langle F,d_AV\rangle
                =-\langle G(A),V\rangle_{L^2}. \tag{6}
\]

This follows by periodic integration by parts and skew-adjointness of
[A_j,cdot]. Moreover <G,D_A phi>_L2=0, either from (6) and
d_A D_A phi=[F,phi], or directly by integration by parts. Therefore (5) gives

\[
 \frac d{dt}\mathcal E(A_N)=-\|G(A_N)\|_2^2-\langle G(A_N),r_N\rangle.
 \tag{7}
\]

The previous local theorem supplies ||A_N||_(W_q)<=R, q=s+p, s>=2, p>=1,
and ||N(A_N)||_(W_(q-1))<=b(R)=16*pi*R^2+4R^3. Projection tails and the
normalized Hilbert–Schmidt norm imply

\[
 \|r_N\|_2\le b(R)(N+1)^{-p}=:\rho_N.
\]

For a pair of fields, its L2 norm is bounded by the sum of its component
uniform operator norms, so no hidden dimension factor is needed. Cauchy–Schwarz
and Young's inequality in (7) yield, on that same proved interval [0,T],

\[
 \boxed{\mathcal E(A_N(t))+\tfrac12\int_0^t\|G(A_N(u))\|_2^2du
       \le\mathcal E(A_N(0))+\tfrac12t\,b(R)^2(N+1)^{-2p}.} \tag{8}
\]

Thus the original cutoff has a quantitative vanishing energy allowance.
Exact monotonicity and a pointwise curvature maximum principle for that
finite ODE do not follow from the continuum identities. In particular (8)
is not asserted beyond the interval on which its common W_q bound is known.

The previous strong convergence also recovers the entire continuum energy
balance on [0,T]. Write e_N for the explicit W_s error bound from that note,
and set

\[
 M=2\pi R+2R^2,\quad C_F=2\pi+4R,\quad
 Q=(4\pi+2R)M,\quad C_G=(4\pi+2R)C_F+2M.
\]

The product and derivative bounds give
||F(A_N)-F(A)||_(W_(s-1))<=C_F e_N and
||G(A_N)-G(A)||_2<=C_G e_N. In the latter estimate, the two differentiated
curvature terms cost at most 4*pi*C_F e_N; the bracket differences cost
2*M*e_N+2*R*C_F*e_N. Both gradient norms are at most Q. Therefore

\[
 \sup_{t\le T}|\mathcal E(A_N(t))-\mathcal E(A(t))|\le M C_F e_N,
\]
\[
 \sup_{t\le T}\left|\int_0^t\|G(A_N)\|_2^2-
                          \int_0^t\|G(A)\|_2^2\right|
       \le2TQ C_G e_N.
\]

Thus energy and accumulated dissipation converge along the entire original
DeTurck cutoff sequence on its established local interval.

## 3. A second approximation: project the Yang–Mills gradient itself

For an energy-dissipative finite model, define a different ODE on the same
real Fourier coefficient space V_N:

\[
 \dot B_N=P_NG(B_N),\qquad B_N(0)=P_N A_0. \tag{9}
\]

The energy is the actual polynomial E_N(B)=E(B) restricted to V_N; in
particular curvature is computed before any projection. Because P_N is
L2-orthogonal, (6) gives

\[
 \boxed{\frac d{dt}E_N(B_N)=-\|P_NG(B_N)\|_2^2=-\|\dot B_N\|_2^2.} \tag{10}
\]

This is the finite-dimensional negative gradient flow of E_N. Its vector
field is polynomial, hence locally Lipschitz. Integrating (10) and using
Cauchy–Schwarz in time gives the explicit excursion bound

\[
 \boxed{\|B_N(t)-B_N(0)\|_2
       \le\sqrt{t E_N(B_N(0))}.} \tag{11}
\]

This proves **global existence for every finite N**: if the maximal time
T_* were finite, (11) would keep all coefficients in a bounded ball up to
T_*. Finite dimension makes its closure compact; the polynomial vector
field is bounded and Lipschitz on a slightly larger ball. The solution has
a limit at T_* and the ordinary differential equation extends it, a
contradiction. This argument does not require the energy itself to be
coercive; flat directions cause no finite-time escape because the integrated
squared speed is bounded.

For A0 in the earlier W_q class, E_N(P_N A0) has a common bound. For example
||P_N A0||_q<=a0 implies E_N(P_N A0)<=0.5*(2*pi*a0+2*a0^2)^2. Thus (11) even
provides an L2 excursion bound independent of N. However, that weak bound
alone supplies neither compactness in the strong norm nor convergence of
nonlinear products. A global continuum-limit theorem for (9) is not claimed.
The local convergence theorem previously proved for (5) cannot be transferred
to (9) by silently changing the equation.

Constant conjugations commute with (9). General spatially varying gauge
transformations do not preserve V_N, so finite-cutoff local gauge equivariance
is not asserted. This is still a spectral approximation, not a local Wilson
link flow.

## 4. An energy-decreasing time step

Equation (10) concerns exact ODE solutions. To also control discrete steps,
let H=P_NG(B) and accept a trial step Bnew=B+tau*H only if

\[
 E_N(Bnew)\le E_N(B)-\tfrac12\tau\|H\|_2^2. \tag{12}
\]

If H=0 the state is stationary. Otherwise a backtracking line search that
repeatedly halves positive tau terminates, since
d/dtau E_N(B+tau*H)|_(tau=0)=-||H||_2^2, strictly below the slope required
in (12). Every accepted step decreases the energy. This is an adaptive
explicit Euler step with an Armijo condition, not an assertion about arbitrary
step sizes or about exact continuous-time error.

There is a useful exact quartic formula for this line search. Put
L=d_B H and C=[H1,H2]. Then

\[
 F(B+\tau H)=F(B)+\tau L+\tau^2 C,
\]
\[
 \begin{split}
 E_N(B+\tau H)={}&E_N(B)+\tau\langle F,L\rangle_2\\
 &+\tau^2(\tfrac12\|L\|_2^2+\langle F,C\rangle_2)
 +\tau^3\langle L,C\rangle_2+\tfrac12\tau^4\|C\|_2^2.
 \end{split} \tag{13}
\]

It permits an independent check of energy and directional derivatives,
including all nonabelian terms. Floating-point line searches are numerical
implementations of (12), not interval-certified inequalities.

## 5. Formalization, numerical checks, and literature

The accompanying Lean module checks the noncommutative covariant-derivative
identity, su(2) invariant-inner-product and pointwise Bochner algebra,
curvature and energy expansions, projection orthogonality, and scalar energy
inequalities. The integration by parts, maximum principle, global finite-ODE
continuation, and continuum energy estimates are analytic proofs in this
note, not fully formalized PDE results.

The numerical audit computes curvature and the full gradient before Fourier
projection. It checks the energy directional derivative independently,
the DeTurck energy-defect identity, and the projected-gradient dissipation
identity. It also tests the curvature evolution and Bochner identities on
nonconstant fields, integrates the new finite ODE with an accumulated
dissipation variable, and exercises the energy-decreasing time step.
Numerical time-integration diagnostics are kept distinct from proofs.

For background on the gauge formulations, see Oh and Tataru,
[The Yang–Mills heat flow and the caloric gauge](https://arxiv.org/abs/1709.08599),
especially the introductory formulations in their
[published monograph excerpt](https://smf.emath.fr/sites/default/files/2023-09/smf_ast_436__sample.pdf).
Global Yang–Mills heat-flow results in dimensions two and three already
exist in the literature: Hamilton's
[Monotonicity formulas for parabolic flows on manifolds](https://www.intlpress.com/site/pub/files/_fulltext/journals/cag/1993/0001/0001/CAG-1993-0001-0001-a007.pdf)
explicitly credits Råde's theorem. The limitation stated here concerns
what this repository's quantitative approximation argument has established,
not an assertion that global continuum existence in two dimensions is open.

## 6. Reproduction record

- [Supporting Lean module](UnifiedTheory/LayerA/NonabelianYangMillsEnergy.lean)
- [All-theorem axiom check](scripts/CheckNonabelianYangMillsEnergy.lean)
- [Executable audit and energy-decreasing solver](scripts/nonabelian_yang_mills_energy_audit.py)
- [Numerical audit data](data/nonabelian_yang_mills_energy_audit.json)
- [Verification manifest](data/nonabelian_yang_mills_energy_verification.json)

The module has 15 supporting theorems. Its pointwise Bochner calculation is
formalized in su(2) coordinates; the covariant-derivative commutator identity
is proved in an arbitrary ring. The general su(m) invariant-inner-product
argument is given analytically above. No complete PDE or global finite-ODE
existence formalization is asserted.

The executable audit passed 80 exact rational checks and checked nonconstant
fields at cutoffs 1, 2 and 3. The largest pointwise Bochner residual was
1.30e-10 or less; the exact energy-defect identity's largest numerical
residual was below 4.7e-13. The independent quartic energy comparison agreed
within 1.8e-15, and centered finite differences agreed with the energy
directional derivative within 7.4e-10.

For the new projected-gradient ODE at N=2, the test uses fifteen times the
projection of the previous note's initial field and evolves to t=0.4.
Energy decreases from approximately 0.0978906592 to 0.0321568963. Including
an accumulated squared-speed variable, the maximum observed energy-balance
error at 41 sample times is below 1.15e-12. Tightening tolerances and maximum
step size gives a balance error below 4.4e-15 and changes the sampled fields
by at most 1.01e-11 in L2. These are diagnostics, not rigorous numerical error
enclosures. The observed L2 excursion is 0.15709, below the analytic bound
0.19788 from (11).

The separate Armijo Euler experiment takes 24 accepted steps, rejects 49
trial steps, and reaches t=0.4 with energy about 0.0311527861. Every accepted
step satisfies the tested decrease condition. Its different final energy
reflects its finite time-step error; no equality with the exact ODE endpoint
or convergence order is claimed.

Run from the repository root, in order:

```sh
lake build UnifiedTheory.LayerA.NonabelianYangMillsEnergy
lake env lean scripts/CheckNonabelianYangMillsEnergy.lean
python3 scripts/nonabelian_yang_mills_energy_audit.py
```

The manifest records build and axiom-audit results, scope, and SHA-256 hashes
of the new files and their direct prior-stage dependencies. The previous
local theorem and its verification record remain unchanged.
