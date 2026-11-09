# Global-in-time spectral convergence for smooth nonabelian Yang–Mills heat

Date: 2026-11-09

This closes the continuum-limit gap left by
[the energy-dissipating finite model](NONABELIAN_YANG_MILLS_ENERGY.md), for
smooth initial data. The exact finite equations remain

\[
 \dot B_N=P_NG(B_N),\quad B_N(0)=P_NB_0,\qquad
 G(B)=(-D_2F_B,D_1F_B).
 \tag{1}
\]

For every finite T and smooth periodic su(m)-valued B0 on the unit two-torus,
the entire sequence B_N converges to the unique Yang–Mills heat solution B
uniformly on [0,T] in L2 and in spatial uniform norm. Curvature, energy,
parallel transport, and accumulated dissipation converge as well. Quantitative
bounds are given below. “Global” means convergence on each fixed finite time
interval, not a single error bound uniform over all t>=0 or an exchange of
the limits N->infinity and t->infinity.

**Dependency boundary.** We use the established global existence and
smoothness theorem for the continuum reference. We prove the approximation
estimate here. The complete PDE theorem is analytic and partly dependent on
that literature result; the accompanying Lean module proves specified
algebraic and scalar comparison ingredients. No novelty claim is made.

## 1. The continuum reference and the norms

Global smooth existence and uniqueness for smooth data on the three-torus
is stated explicitly in Cao and Chatterjee,
[A State Space for 3D Euclidean Yang–Mills Theories, Theorem 3.14 and Appendix B](https://link.springer.com/article/10.1007/s00220-023-04870-y).
That theorem credits Råde and Charalambous–Gross. It applies to SU(m).
It supplies the two-dimensional statement used here: extend B0 independently
of the third coordinate with third component zero. Translation invariance
and uniqueness preserve independence of that coordinate. Reflection of the
third coordinate and uniqueness then force the third component to remain
zero. The remaining components solve the two-dimensional equation.

Fix m>=2, a finite T>=0, and an integer p>=2. All smoothness bounds below
are on this fixed interval. Retain the previous operator-norm Fourier spaces
W_r with weight w(k)=1+|k1|+|k2| and component-sum norm. Choose

\[
 R\ge\sup_{t\le T}\|B(t)\|_{W_2},\qquad
 S\ge\sup_{t\le T}\|B(t)\|_{W_{p+2}},\qquad R,S>0.
 \tag{2}
\]

These numbers are finite: smoothness on a compact spacetime slab implies
uniform bounds on sufficiently many spatial derivatives, whose Fourier
decay makes the weighted sums finite. We do not assert a new explicit bound
for R or S in terms of B0 alone. Rates conditional on any such bounds are
fully explicit; the worst-case constants can be very large.

Use the normalized Hilbert–Schmidt norm |X|^2=tr(X*X)/m, extended to complex
Fourier coefficients, and the corresponding pair L2 norm. Pointwise

\[
 |X|\le\|X\|_{op}\le\sqrt m\,|X|,\qquad
 |[X,Y]|\le\kappa |X||Y|,\quad \kappa=2\sqrt m.
 \tag{3}
\]

For su(2) one may instead take the sharper kappa=2 in quaternion coordinates.
P_N is orthogonal in this L2 norm. If e=P_Ne and d_N=2N+1, Fourier
Cauchy–Schwarz and Parseval give

\[
 \|e\|_{L^\infty(HS)}\le d_N\|e\|_2. \tag{4}
\]

There are d_N^2 retained frequencies. This estimate is for the Euclidean
pair norm, so no extra factor from the two connection components appears.

## 2. The relative-gradient identity

For two connections U=V+e, put

\[
 L=d_Ve=D_1^Ve_2-D_2^Ve_1,\qquad C=[e_1,e_2].
\]

Then F_U=F_V+L+C and d_Ue=L+2C. The first-variation identity from the energy
note yields, with all pairings integrated over the torus,

\[
 \begin{split}
 \langle e,G(U)-G(V)\rangle
 &=-\|L\|_2^2-3\langle L,C\rangle-2\|C\|_2^2-2\langle F_V,C\rangle\\
 &=-\|L+\tfrac32C\|_2^2+\tfrac14\|C\|_2^2-2\langle F_V,C\rangle.
 \end{split} \tag{5}
\]

This exact completion of a square avoids estimating the derivative of e
by a growing Lipschitz constant for the full vector field.

Set y=||e||_2^2. If ||F_V||infinity<=M and e=P_Ne, then
|C|<=kappa*|e|^2/2 implies

\[
 2|\langle F_V,C\rangle|\le\kappa M y,\qquad
 \|C\|_2^2\le\frac{\kappa^2}{4}d_N^2 y^2.
\]

Dropping the nonpositive square in (5) gives

\[
 \boxed{\langle e,G(V+e)-G(V)\rangle
        \le\kappa M y+\frac{\kappa^2}{16}d_N^2y^2.} \tag{6}
\]

Only the quadratic-in-y term grows with the cutoff. This is the term the
comparison below controls. No uniform high-derivative bound on B_N is assumed.

## 3. Consistency against the projected smooth reference

Take V_N=P_NB, e_N=B_N-V_N, and y_N=||e_N||_2^2. The initial error e_N(0)
is exactly zero. Projection orthogonality gives

\[
 \tfrac12 y_N'=\langle e_N,G(B_N)-G(V_N)\rangle
                  +\langle e_N,r_N\rangle,\quad
 r_N=P_N\{G(V_N)-G(B)\}. \tag{7}
\]

This r_N is a consistency error against the smooth reference; it differs
from the DeTurck projection residual used in the previous note.
Define

\[
 M=2\pi R+2R^2,\quad C_F=2\pi+4R,\quad
 C_G=(4\pi+2R)C_F+2M,\quad K=1+C_GS.
 \tag{8}
\]

The weighted product and derivative estimates already established give
||F_(V_N)||infinity<=M and
||G(V_N)-G(B)||_2<=C_G||V_N-B||_(W_2). The latter follows by first bounding
the curvature difference in W_1, then differentiating it and expanding the
two bracket differences in G. Thus

\[
 \|r_N\|_2\le C_G S(N+1)^{-p}\le\rho_N:=K(N+1)^{-p}. \tag{9}
\]

The harmless addition of 1 makes rho_N strictly positive, including the
zero-solution case. From (6), (7), and 2 sqrt(y)*rho<=y+rho^2,

\[
 y_N'\le a y_N+\beta d_N^2 y_N^2+\rho_N^2,\qquad
 a=2\kappa M+1,\quad\beta=\kappa^2/8. \tag{10}
\]

## 4. A closed comparison bound on any fixed time interval

Put

\[
 Z_N(t)=2\rho_N^2e^{(a+1)t},\qquad
 D=\sqrt2 K e^{(a+1)T/2}.
\]

Choose N sufficiently large that

\[
 \boxed{(N+1)^{2p-2}\ge16\beta D^2.} \tag{11}
\]

Since d_N<=2(N+1), this ensures beta*d_N^2*Z_N(t)<=1/4 on [0,T]. Also
Z_N(t)>=2*rho_N^2>0. At any potential contact y_N=Z_N, (10) gives

\[
 y_N'\le aZ_N+\tfrac14 Z_N+\tfrac12 Z_N
          <(a+1)Z_N=Z_N'.
\]

Initially y_N(0)=0<Z_N(0). The scalar comparison principle therefore prevents
y_N from crossing Z_N. This proves

\[
 \sup_{t\le T}\|B_N(t)-P_NB(t)\|_2\le D(N+1)^{-p}.
 \tag{12}
\]

Adding the Fourier tail yields the main quantitative conclusion

\[
 \boxed{\sup_{t\le T}\|B_N(t)-B(t)\|_2
          \le(D+S)(N+1)^{-p}.} \tag{13}
\]

The finite solutions exist throughout [0,T] by the global finite-ODE proof
in the energy note. Since p>1, a cutoff satisfying (11) always exists.
Equations (12)-(13) hold for all sufficiently large N, so the entire sequence
converges, without subsequences. As T was arbitrary and the same unique B is
used on every interval, convergence holds in C_loc([0,infinity);L2).
Smooth data permit any fixed p>=2, with constants depending on p and T.

The comparison theorem does not create a new continuum solution or replace
the cited global existence theorem. It proves that these particular exact
projected-gradient ODEs converge to that established solution.

## 5. Curvature, energy, transport, and dissipation

From (4), (12), and ||X||op<=sqrt(m)|X|, each component has the uniform bound

\[
 \sup_{t\le T}\|B_{N,i}-B_i\|_{L^\infty(op)}
 \le\eta_N:=2\sqrt m D(N+1)^{1-p}+S(N+1)^{-p}. \tag{14}
\]

Hence for any piecewise C1 path gamma with coordinate length ell_1,

\[
 \sup_{t\le T}\|W_{B_N(t)}(\gamma)-W_{B(t)}(\gamma)\|_{op}
       \le\ell_1\eta_N. \tag{15}
\]

This follows by the unitary transport comparison proved in the earlier notes.
Normalized closed-loop Wilson traces obey the same bound. Arbitrary fixed
spatial derivatives can also be controlled by choosing larger p and using
the corresponding differentiated Fourier inverse estimate.

For an explicit curvature bound, let delta_N=D(N+1)^(-p). Expanding F_(B_N)
about V_N and using Fourier differentiation gives

\[
 \sup_{t\le T}\|F_{B_N}-F_B\|_2\le\zeta_N:=
 (4\pi N+\kappa R)\delta_N
 +\tfrac\kappa2 d_N\delta_N^2+C_FS(N+1)^{-p}.
 \tag{16}
\]

Indeed ||d e_N||_2<=4*pi*N*||e_N||_2, the two mixed brackets cost at most
kappa*R*||e_N||_2, and the quadratic bracket costs at most
(kappa/2)*d_N*||e_N||_2^2. The remaining curvature difference is the smooth
projection tail. Thus zeta_N=O((N+1)^(1-p)).

Energy dissipation for both evolutions bounds their curvature L2 norms by M:
their initial data have W_2 norm at most R. Consequently

\[
 \sup_{t\le T}|\mathcal E(B_N(t))-\mathcal E(B(t))|\le M\zeta_N. \tag{17}
\]

Using the two exact energy balances gives uniform convergence of cumulative
dissipation, with error at most 2*M*zeta_N:

\[
 \int_0^t\|\dot B_N\|_2^2\longrightarrow\int_0^t\|\dot B\|_2^2.
 \tag{18}
\]

In fact dot B_N converges strongly to dot B in spacetime L2 on [0,T]. The
energy bounds give weak compactness of those velocities. Strong convergence
of B_N in C_t L2 identifies every weak derivative limit as dot B by testing
against smooth compactly supported time functions and spatial L2 fields.
Equation (18) at T gives convergence of squared norms; weak convergence plus
norm convergence in a Hilbert space is strong convergence. This establishes
the assertion for the entire sequence. It does not assert convergence of
the unprojected G(B_N) in that spacetime norm by this argument alone.

## 6. An exact spatially varying SU(2) benchmark

There is an explicit reference with infinitely many Fourier modes. Let

\[
 a(t)=a_*/\sqrt{1+8a_*^2t},\quad
 \theta(x)=\epsilon_1\sin(2\pi x_1)+\epsilon_2\sin(2\pi x_2),
 \quad g(x)=\exp(\theta(x)e_3).
\]

Apply this fixed spatial gauge transformation to the homogeneous nonlinear
solution from the local note. In imaginary-quaternion coordinates,

\[
 B_1=(a\cos2\theta,\ a\sin2\theta,\ -\partial_1\theta),\qquad
 B_2=(-a\sin2\theta,\ a\cos2\theta,\ -\partial_2\theta). \tag{19}
\]

Direct substitution gives F_B=2a(t)^2 e3 and B_t=G(B). The spatial derivatives
and commutators cancel exactly in the curvature; none is discarded. This
field varies spatially, has nonzero nonabelian curvature, and evolves for all
time. It tests spectral projection in a nonconstant gauge, even though the
finite spectral ODE itself is not locally gauge equivariant.

The audit initializes P_NB(0) using Bessel coefficients: for k in Z^2, put
j_k=J_(k1)(2*epsilon1)*J_(k2)(2*epsilon2). The cosine coefficient is j_k when
k1+k2 is even, and zero otherwise; the sine coefficient is -i*j_k when the
sum is odd, and zero otherwise. The third components have only modes
(+-1,0) or (0,+-1), with coefficients -pi*epsilon1 or -pi*epsilon2. A direct
physical-space evaluation of (19) checks this representation independently.
The Bessel series implies

\[
 |J_n(2\epsilon)|\le e^{\epsilon^2}|\epsilon|^n/n!,\qquad n\ge0.
\]

For u>=0 set L(u)=exp(u^2)*(2*exp(u)-1) and, when u<K_ref+2, set

\[
 H(u)=\frac{2e^{u^2}u^{K_{ref}+1}}
 {(K_{ref}+1)!\,[1-u/(K_{ref}+2)]}.
\]

L bounds the full absolute coefficient sum in one coordinate, and H bounds
its tail. The component-sum Fourier tail outside the reference square is at
most

\[
 2|a_*|\{H(|\epsilon_1|)L(|\epsilon_2|)
          +L(|\epsilon_1|)H(|\epsilon_2|)\}. \tag{20}
\]

This isolates reference truncation from time integration. Values of (20)
computed in ordinary floating point are not interval certificates.

## 7. Scope and verification boundary

This result addresses exact Fourier–Galerkin projected-gradient ODEs with
smooth periodic data. It is not a rough-data theorem, a local Wilson-link
discretization, a cutoff-uniform local gauge symmetry statement, or a theorem
uniform over infinite time. Constants (2) come from the smooth reference and
may make the explicit cutoff threshold impractical. Numerical tests below
do not assume their tested cutoffs satisfy that conservative threshold.

The Lean module checks the relative-gradient algebra and square completion,
the complete scalar exponential-barrier comparison, supporting inequalities,
and the nonconstant-gauge witness's curvature and gradient algebra. It does
not formalize the Fourier Banach spaces, integration by parts, or the external
global existence theorem. No new axiom is introduced to stand for that theorem.

## 8. Reproduction record

- [Lean supporting proofs](UnifiedTheory/LayerA/NonabelianYangMillsGlobal.lean)
- [Every-theorem axiom check](scripts/CheckNonabelianYangMillsGlobal.lean)
- [Executable convergence audit](scripts/nonabelian_yang_mills_global_audit.py)
- [Numerical results](data/nonabelian_yang_mills_global_audit.json)
- [Verification manifest](data/nonabelian_yang_mills_global_verification.json)

There are 16 supporting Lean theorems. In particular,
`riccati_envelope_bound` proves the scalar comparison from continuity,
right derivatives, the Riccati differential inequality, and smallness of the
explicit envelope. It does not assume in advance that the unknown error
stays small. `relative_gradient_identity` and `relative_square_completion`
hold in a general real Hilbert space; the benchmark's Lie-algebra identities
use su(2) coordinates.

The audit passed 64 exact rational checks. On independent nonconstant fields
at N=1,2,3, the relative-gradient identity agreed to within 1.43e-14. The
physical and Bessel representations of (19) agreed to within 3.34e-16. Its
curvature and Yang–Mills equation residuals were below 2.3e-15 and 2.33e-13,
respectively. The absolute reference-tail bound with K_ref=18 is about
1.17e-27, evaluated without interval arithmetic.

For a_*=0.7, epsilon1=0.28, epsilon2=0.19 and T=0.25, the errors against
the exact reference were:

| Cutoff | Maximum sampled L2 field error | L2 field error at T |
| --- | ---: | ---: |
| 1 | 7.89982e-2 | 7.89982e-2 |
| 2 | 5.27938e-3 | 4.41338e-3 |
| 3 | 5.86388e-4 | 5.86388e-4 |
| 4 | 2.00465e-5 | 1.58628e-5 |
| 6 | 3.72197e-8 | 3.04770e-8 |

Each maximum is over nine time samples, including zero, not over a certified
continuous interval. Tightening the N=6 integrator changes its endpoint by
less than 1.90e-12 in L2. The largest sampled curvature L2 error at N=6 is
about 1.16e-6. Energy and accumulated dissipation also converge in the audit;
their N=6 errors reach floating-point/time-integration scales, so those
small numbers are not presented as independently certified accuracies.

Fifteen transport comparisons use three axis-aligned paths at five cutoffs.
Their exact references are obtained by multiplying constant-connection
transports and applying g at the endpoints, so they do not depend on a
second numerical path integral. At N=6 the largest transport operator error
is about 1.63e-8. Tightening the path integrator changes the rectangular-loop
transport by about 2.72e-12. All observed errors are consistent with the
computed field-error transport allowance. These diagnostics do not replace
the theorem or certify time-discretization error.

Run from the repository root, in order:

```sh
lake build UnifiedTheory.LayerA.NonabelianYangMillsGlobal
lake env lean scripts/CheckNonabelianYangMillsGlobal.lean
python3 scripts/nonabelian_yang_mills_global_audit.py
```

The manifest records the targeted build, axiom audit, numerical checks,
external-theorem dependency, and file hashes. Prior-stage proof and audit
files are preserved unchanged.
