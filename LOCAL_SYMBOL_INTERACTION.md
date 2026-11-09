# A local symbol interaction and its first curvature correction

Date: 2026-09-11

The [proper-resolution benchmark](PROPER_RESOLUTION_INDUCTION.md)
has the Einstein leading curvature functional, but its matrix coherent
states spread over growing proper distances. This stage constructs a
different interaction algebra on exactly the same finite free mode spaces.
A unitary map to truncated ordinary spherical harmonics preserves the
complete scalar and fermion determinants. Pointwise scalar interactions
then have explicitly localized field packets whose proper widths are
bounded independently of the sphere sizes.

For a positive O(8) quartic interaction, the first derivative of the full
action in the coupling is a volume term plus a positive multiple of
integrated scalar curvature, with a uniformly bounded remainder on the
homogeneous product family. Its exact-volume shape variations retain the
Einstein dependence through fourth order. A separate convexity estimate
bounds the finite-coupling Taylor error per unit volume.

The interaction algebra is a new input. Localized, overlapping packets
and a pointwise vertex do not give independent local microscopic sites.
The finite-coupling remainder is not controlled at the smaller curvature
scale. Arbitrary-metric dynamics, a microscopic refinement law, Lorentzian
reconstruction, Einstein constraints, and the TOE remain unproved. No
new Lean theorem is asserted.

## 1. An exact isometry that preserves the free model

Let H_N be the span of ordinary scalar spherical harmonics Y_lm with
0<=ell<N. Under conjugation by the spin-j representation, j=(N-1)/2,
the matrix Hilbert space decomposes as

\[
 \operatorname{Mat}_N=\bigoplus_{\ell=0}^{N-1}V_\ell.
\]

Choose orthonormal matrix tensor harmonics T_lm for the Hilbert-Schmidt
inner product, with

\[
 [J_3,T_{\ell m}]=mT_{\ell m},\quad
 [J_\pm,T_{\ell m}]=\sqrt{(\ell\mp m)(\ell\pm m+1)}T_{\ell,m\pm1},
 \quad T_{\ell m}^\dagger=(-1)^mT_{\ell,-m}.
\]

For a sphere of radius r, define

\[
 U_{N,r}T_{\ell m}=Y_{\ell m}/r.                         \tag{1}
\]

This is unitary into L2(S2_r), intertwines every ad(J_a) with the
ordinary angular generator L_a, and maps Hermitian matrices to real
functions. Consequently it intertwines both the scalar Casimir and
the first-order spinor operator I+sigma_a ad(J_a) with their truncated
ordinary harmonic counterparts. Tensoring the two maps and retaining
the auxiliary tau factor preserves the product fermion operator as well.

The scalar real Gaussian measure and the paired fermion determinant
are unchanged under this isometry. In particular, with r_i=N_i/kappa
and common positive mass m, the full free result remains exactly

\[
 \Gamma_0=-\frac{J(c)\kappa^2}{8\pi^2}\int\sqrt g R+O_{c,\rho}(1),
 \quad c=m^2/\kappa^2>0,
\]
\[
 J(c)=\tfrac12[c\log c-(2c+3)\log(c+1)+(c+3)\log(c+2)]>0. \tag{2}
\]

Equation (1) does not preserve multiplication. For example, in the
mean-square-one convention, Z=sqrt(3) J3/sqrt(j(j+1)) corresponds, up to
an irrelevant sign, to z=sqrt(3) cos(theta). However,

\[
 \frac1N\operatorname{Tr}Z^4=\frac95-\frac{3}{5j(j+1)},
 \qquad\frac1{4\pi}\int z^4d\Omega=\frac95.             \tag{3}
\]

The difference is already 4/5 at N=2. Replacing a matrix trace quartic
by the pointwise harmonic quartic is an actual model change. It cannot
be described as just relabeling the old interacting theory. No unital
algebra isomorphism can turn the noncommuting matrix product into a
commutative one for N>1.

## 2. Field packets at fixed proper width

The symbol map is not the positive coherent-state expectation map.
There is therefore no requirement that its packets have the coordinate
variance of a spin coherent state. An elementary construction shows the
different physical localization scale.

Choose integer p>=2 and n=ceil(N/p). Set

\[
 q_n(\theta)=\left[\frac{\sin(n\theta/2)}{n\sin(\theta/2)}\right]^2
 =\frac{1-T_n(\cos\theta)}{n^2(1-\cos\theta)},
 \quad f_{N,x}(y)=q_n(d(x,y)/r)^p.                     \tag{4}
\]

The quotient is a polynomial of degree n-1 in cos(theta), with its
continuous value one at theta=0. Thus f lies in H_N because
p(n-1)<=N-1. It is nonnegative and obeys

\[
 0\le q_n\le\min\{1,[n\sin(\theta/2)]^{-2}\}.
\]

On theta<=1/n, sin(z)/z>=23/24 for z=n theta/2<=1/2.
Hence, using 1-cos(1/n)>=2/(pi^2 n^2),

\[
 \|f\|_2^2\ge a_p r^2/n^2,
 \qquad a_p=\frac4\pi(23/24)^{4p}.                    \tag{5}
\]

Use chord distance s=2r sin(theta/2), for which dA=2pi s ds, and
q_n<=min(1,(2r/(ns))^2). Splitting the chord second-moment integral
at s=2r/n and extending the upper limit to infinity gives

\[
 \int s^2|f|^2dA\le\frac{8\pi p}{p-1}\frac{r^4}{n^4}.
\]

Geodesic distance is at most pi/2 times chord distance. For the normalized
packet psi=f/||f||, (5), r=N/kappa, and n>=N/p imply

\[
 \boxed{\int d(x,y)^2|\psi_{N,x}(y)|^2dA_y
 \le\frac{C_p}{\kappa^2},\qquad
 C_p=\frac{\pi^4}{2}\frac{p^3}{p-1}(24/23)^{4p}.}       \tag{6}
\]

The constant is loose but independent of radius and N. For p=2 and
kappa=1, the actual RMS widths at N=8,16,32,64,128 are approximately
3.341, 3.308, 3.299, 3.297, 3.297. Product packets have the sum of the
two variances, bounded by 2C_p/kappa^2. These field profiles remain
localized at a fixed proper scale while the geometry grows.

One also obtains uniform vertex decay. Equations (4)--(5) give

\[
 \|\psi\|_\infty\le\kappa/\sqrt{a_p},\quad
 \|\psi\|_1\le L_p/\kappa,
 \quad L_p=\frac{4\pi p^2}{(p-1)\sqrt{a_p}},
\]
\[
 |\psi_x(y)|\le\kappa D_p(1+\kappa d(x,y))^{-2p},
 \quad D_p=(1+\pi p)^{2p}/\sqrt{a_p}.                 \tag{7}
\]

The L1 estimate follows by the same chord integral, now applied to
q_n^p. For a product packet Psi on the two spheres, the corresponding
bounds are kappa^2/a_p, L_p^2/kappa^2, and
kappa^2 D_p^2(1+kappa d)^(-2p). Here the product geodesic distance is
sqrt(d1^2+d2^2), and (1+kappa d1)(1+kappa d2)>=1+kappa d.

If four packet centers have diameter D, choose a pair separated by D.
At every integration point one of that pair is at least D/2 away. Split
the integral into those two regions, use the decaying bound on that
packet, L-infinity on two others, and L1 on the last. This proves

\[
 \left|\int\Psi_{x_1}\Psi_{x_2}\Psi_{x_3}\Psi_{x_4}dV\right|
 \le\frac{2D_p^2L_p^2}{a_p^2}\kappa^4
                         (1+\kappa D/2)^{-2p}.        \tag{8}
\]

This is a uniform bound on quartic vertex matrix elements in an
overlapping packet family. It is not an operator-norm interaction bound
for independent tensor factors. Increasing p improves the algebraic
tail at the cost of a larger fixed physical width.

Exact cubature also checks the separated-packet vertex directly. For
p=2, kappa=1, N1=N2=64, moving one packet center by proper distance
4, 8, and 16 on the first sphere reduces the vertex
int(Psi_x^2 Psi_y^2) to approximately 0.493, 0.0546, and 0.00000952
times its coincident value. The physical separation, not the fractional
sphere angle, is held fixed when comparing sizes.

## 3. A positive, finite, pointwise interaction

Let eight real fields phi_a belong to H_N1 tensor H_N2 with the free
quadratic form inherited through (1). Define

\[
 U(\phi)=\frac1{24}\int\left(\sum_{a=1}^{8}\phi_a(x)^2\right)^2dV,
 \quad S_\lambda=S_0+\lambda U,\qquad\lambda\ge0.       \tag{9}
\]

The fermions remain free in this revision. Equation (9) is nonnegative,
convex, rotation invariant, and O(8) invariant. The resulting finite
Euclidean integral is well defined. For positive mass its Hessian is
bounded below by m^2 times the identity in orthonormal mode coordinates.

The vertex is exactly a finite positive weighted sum. On each sphere
let L=N-1. Use 2L+1 Gauss-Legendre nodes in cos(theta) and 4L+1 equally
spaced azimuths. Products of four cutoff fields have degree at most 4L.
Azimuthal quadrature kills all nonzero Fourier modes in that range;
the remaining integrand is a polynomial in cos(theta) of degree at most
4L, integrated exactly by the positive Gauss rule. Tensor the two sphere
rules to obtain

\[
 U=\frac1{24}\sum_z w_z\left(\sum_a\phi_a(z)^2\right)^2,
 \qquad w_z>0.                                        \tag{10}
\]

No iterated projected product replaces phi^4: multiplication is ordinary
pointwise multiplication before integration. This distinction avoids
losing the harmonics generated inside the quartic vertex.

The sampled values in (10) are constrained linear combinations of the
retained mode coordinates. They are not independent variables at local
sites. The cutoff projector is still spatially nonlocal. Positive
Euclidean weight does not establish reflection positivity, a Lorentzian
Hamiltonian, or a local microscopic refinement process.

## 4. Exact first derivative in the interaction coupling

Let G_N=(Delta_N+m^2)^(-1). Homogeneity and the addition theorem make
g_N=G_N(x,x) independent of x, with

\[
 g_N=\frac{\operatorname{Tr}G_N}{V}.
\]

With the normalization of (9), Wick's rule gives exactly

\[
 \boxed{\left.\partial_\lambda\Gamma_\lambda\right|_{0^+}
 =\langle U\rangle_0=\frac{q(q+2)}{24}Vg_N^2,
 \qquad q=8.}                                        \tag{11}
\]

This is the first coupling derivative of the full finite interacting
partition function, not a selected spectral window. Write
P=N1^2N2^2 and S=N1^2+N2^2. The complete scalar resolvent trace is

\[
 \operatorname{Tr}G_N=\kappa^{-2}
   \int_0^\infty e^{-ct}B_{N_1}(t)B_{N_2}(t)dt.
\]

The preceding [uniform heat-quadrature estimate](PROPER_RESOLUTION_INDUCTION.md#2-exact-quadrature-identities-and-a-uniform-bound)
has B_N=N^2 I+b+R_N, with

\[
 I=(1-e^{-t})/t,\quad
 b=\tfrac13+(t/6-\tfrac13)e^{-t},\quad
 |R_N|\le224N^{-2}\min(t^2,t),\quad t\le N^2.
\]

It follows that

\[
 \boxed{\kappa^2\operatorname{Tr}G_N
       =P A_0(c)+S A_1(c)+O_{c,\rho}(1),}              \tag{12}
\]
\[
 A_0=c\log c-2(c+1)\log(c+1)+(c+2)\log(c+2)>0,
\]
\[
 A_1=\frac13\log\frac{(c+1)^2}{c(c+2)}
           +\frac16\left[\frac1{c+1}-\frac1{c+2}\right]>0.       \tag{13}
\]

Indeed A0=int exp(-ct) I^2 dt, and
\(Ib=(1-e^{-t})^2/(3t)+(e^{-t}-e^{-2t})/6\), which gives A1.
For completeness, a size-independent absolute bound on the remainder
in (12) is

\[
 B(c,\rho)=(102000+900\rho^2)(1/3+e^{-c}/c)
          +\frac{4\rho^2}{e^2c^3}+\frac{1+3\rho^2}{2c}.          \tag{14}
\]

To verify it, multiply the two scalar heat expansions up to
n^2=min(N_i)^2. Their error after P I^2+S Ib is at most
(102000+900rho^2)min(t^2,1). Its integral is bounded by the first term
in (14). Above n^2, the finite heat product is at most P; the maximum
of n^4 exp(-cn^2) is at most 4/(e^2 c^2). The leading P I^2 and S Ib
tails are bounded respectively by rho^2/c and (1+rho^2)/(2c).

Since V=16pi^2 P/kappa^4 and R=2kappa^2 S/P,

\[
 g_N=\frac{\kappa^2 A_0}{16\pi^2}
           +\frac{A_1}{32\pi^2}R+O_{c,\rho}(\kappa^2/P).
\]

Squaring this expression in (11) proves

\[
 \boxed{\left.\partial_\lambda\Gamma_\lambda\right|_{0^+}
     =\alpha(c)\kappa^4 V+\beta(c)\kappa^2\int\sqrt g R
                   +O_{c,\rho}(1),}                  \tag{15}
\]
\[
 \alpha=\frac{q(q+2)A_0^2}{6144\pi^4},\qquad
 \beta=\frac{q(q+2)A_0A_1}{6144\pi^4}>0.
\]

For an explicit remainder bound in this last step, set w=q(q+2)/24.
The absolute error is no more than

\[
 \frac{w}{16\pi^2}
 [A_1^2(\rho+\rho^{-1})^2+2A_0B+4A_1B+B^2],
\]

using S/P<=2 and P>=1. Thus the first interaction correction creates
a leading volume contribution, while its leading fixed-volume shape
response is still Einstein. This does not solve vacuum-energy selection.

The inverse Newton coefficient of the action truncated at first order
in lambda is

\[
 (G^{-1})_{\text{first order}}
   =\frac{2J(c)\kappa^2}{\pi}
       -\lambda\frac{q(q+2)\kappa^2 A_0A_1}{384\pi^3}.            \tag{16}
\]

The positive quartic reduces the inverse Newton coefficient at this
order. Equation (16) is not a proved finite-coupling gravitational
coefficient. In particular, interactions need not preserve the chosen
boson/fermion mass balance.

## 5. Shape variations of the first coupling derivative

Use the preceding exact-volume integer stencil:

\[
 K=[k(k+1)]^2,\quad h=\log((k+1)/k),
\]
\[
 (N_1,N_2)=(K,K),\ (k(k+1)^3,k^3(k+1)),\ ((k+1)^4,k^4).
\]

All pairs have N1N2=K^2, so the volume term in (15) cancels exactly
in shape differences. Divide the first coupling derivative by K^2.
Its remaining shape function is

\[
 2b_c\cosh(2u)+O(K^{-2}),\quad
 b_c=\frac{q(q+2)}{24}\frac{A_0A_1}{8\pi^2}.
\]

The same uniform-remainder argument as before controls the symmetric
second and fourth differences, since K^-2 h^-4 tends to zero. They
converge to 8b_c and 32b_c. At c=0.1 these limits are 0.2476920180
and 0.9907680721. Errors relative to the corresponding finite Einstein
stencils are:

| k | K | second error | fourth error |
|---:|---:|---:|---:|
| 2 | 36 | 0.001168 | 0.02336 |
| 3 | 144 | 0.00006539 | 0.001167 |
| 4 | 400 | 0.000008114 | 0.0001387 |
| 5 | 900 | about 0.00000157 | about 0.0000261 |

These statements concern the exact derivative at zero coupling. They
do not commute the large-volume limit with a finite-coupling expansion.

## 6. A volume-uniform finite-coupling estimate and its limit

Let F(lambda)=-log <exp(-lambda U)>_0 be the interaction contribution
to the action. In each finite mode space,

\[
 F'(\lambda)=\langle U\rangle_\lambda,\qquad
 F''(\lambda)=-\operatorname{Var}_\lambda U.
\]

Since the Hessian of S_lambda is at least A=Delta+m^2, the
[Brascamp-Lieb variance bound](https://arxiv.org/pdf/1106.0709)
(equation 1.3) applies, also after any linear tilt of the measure.
For a linear field evaluation X=phi_a(x), its tilted variance is at
most the free diagonal g_N. Global field reflection gives <X>=0.
Integrating the tilted variance bound twice yields

\[
 \langle e^{tX}\rangle_\lambda\le e^{t^2g_N/2}.
\]

The corresponding two-sided tail bound implies
\(\langle |X|^6\rangle_\lambda\le96g_N^3\).
Writing s(x)=sum_a phi_a(x)^2 and using
s^3<=q^2 sum_a |phi_a|^6 gives <s^3>_lambda<=96q^3 g_N^3.
The orthogonal harmonic projection and Bessel's inequality give

\[
 \|\nabla U\|^2=\frac1{36}\sum_a\|P_N(\phi_a s)\|_2^2
                       \le\frac1{36}\int s^3dV.
\]

Apply Brascamp-Lieb once more, now to U, and use A>=m^2:

\[
 \operatorname{Var}_\lambda U
       \le\frac{8q^3}{3m^2}Vg_N^3,\qquad\lambda\ge0.
\]

All evaluations here are bounded linear functionals on the finite mode
space. The convex measure has the Gaussian tails needed to justify the
moments, derivatives, and polynomial approximations in this argument.
Integration in lambda proves the nonperturbative bound

\[
 \boxed{0\le\lambda\langle U\rangle_0-F(\lambda)
       \le\frac{4q^3}{3m^2}\lambda^2 Vg_N^3.}          \tag{17}
\]

Finally g_N<=P/(Vm^2)=kappa^4/(16pi^2 m^2), so the right side per
unit volume is uniformly bounded in the matrix sizes. Exact radial
integrals for the constant-mode member independently check (17).

This is a controlled first-order expansion of the **action density**.
Its O(lambda^2 V) error can exceed the O(r^2) curvature term as the
radii grow at fixed lambda. A bound on the action density therefore
does not prove the finite-coupling Einstein response, even after the
leading volume term cancels in a shape variation. The needed bound is
on the shape dependence of the remainder itself.

## 7. Consequences for the microscopic proposal

The growing coherent-state width is not an unavoidable consequence of
the free spectrum. A specified alternative symbol algebra supports
properly localized field profiles and decaying quartic vertices while
preserving the complete free determinant. Its first genuine interaction
correction retains the homogeneous Einstein curvature dependence.

The next substantive target is the connected finite-coupling shape
response, with a bound at the curvature scale. Independent local site
variables and a dynamics implementing geometric refinement still have
to be constructed. The supplied product-sphere geometry is not derived
spacetime, and these Euclidean scalar interactions do not establish
physical Lorentzian fermions, a universal gravitational coupling,
Einstein constraints, Standard Model dynamics, or a TOE.

## 8. Reproduction

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/local_symbol_interaction_audit.py
```

The [audit](scripts/local_symbol_interaction_audit.py) checks the scalar
and first-order fermion intertwiners, their distinct quartic products,
polynomial packets, physical widths and separated vertices, exact positive cubature,
convexity and gradient bounds, independent resolvent integrals, full
finite spectra, constant-volume shape differences, and finite-coupling
radial integrals. Its [report](data/local_symbol_interaction_audit.json)
records source hashes and scope. All earlier research artifacts and
Lean sources are preserved.
