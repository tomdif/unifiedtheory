# Fixed proper spectral resolution repairs the homogeneous Einstein functional

Date: 2026-09-11

The complete massive determinant of the preceding
[balanced matter construction](BALANCED_MATTER_INDUCTION.md) has an
Einstein leading curvature functional if the two sphere matrix sizes
track their radii at a common proper spectral resolution. This statement
includes all finite modes. An explicit, size-independent bound controls
the remainder on every bounded-aspect family, at fixed positive mass and
fixed cutoff. Exact-volume integer refinements recover the second and
fourth shape variations that the earlier fixed-size model failed.

This closes the leading homogeneous shape-matching gap under a revised
regulator rule. The rule, curved matrix family, Gaussian measure, matter
balance, and common mass are supplied physical inputs. It does not derive
Einstein equations for arbitrary metrics, a local refinement Hamiltonian,
Lorentzian gravity, or a TOE. In particular, fixed spectral resolution
does not ensure a fixed proper localization scale for matrix products;
section 7 makes that limitation explicit. The proof below is analytical,
with symbolic and numerical checks, and is not a new Lean theorem.

## 1. The revised rule and the complete finite action

Choose a fixed proper momentum scale kappa>0 and common mass m>0. For
each pair of positive integers N1,N2 set

\[
 r_i=N_i/\kappa,\qquad c=m^2/\kappa^2>0.                 \tag{1}
\]

The largest sphere angular momenta then have physical wavenumbers of
order kappa for either radius. For one sphere the dimensionless scalar
eigenvalues and weights are

\[
 b_\ell=\ell(\ell+1),\quad w^B_\ell=2\ell+1,
 \quad 0\le\ell<N,
\]

and the squared first-order spinor spectrum is

\[
 f_n=n^2,\quad w^F_n=4n\ (1\le n<N),\quad w^F_N=2N.
\]

The [previous stage](BALANCED_MATTER_INDUCTION.md#1-a-first-order-fermion-operator-on-the-same-matrix-geometry)
constructs the Hermitian operators
\(D_N=I+\sigma_a\operatorname{ad}(J_a)\) and

\[
 Q=\tau_1\otimes D_{N_1}/r_1\otimes I
      +\tau_2\otimes I\otimes D_{N_2}/r_2.
\]

Its anticommuting tau factors give a paired spectrum and
\(\det(m+iQ)>0\). Its 8N1^2N2^2 components match the count of eight
real scalars. Define the finite half-logdet sums

\[
 B=\frac12\sum_{\ell,k}w^B_\ell w^B_k
       \log(b_\ell/N_1^2+b_k/N_2^2+c),
\]
\[
 F=\frac12\sum_{n,p}w^F_nw^F_p
       \log(n^2/N_1^2+p^2/N_2^2+c).
\]

With normalized scalar Gaussian measure and a fixed Grassmann measure,
the complete matter action is

\[
 \boxed{\Gamma(N_1,N_2;c)=8B-2F.}                       \tag{2}
\]

The multiplicity balance cancels the common log(kappa^2) factor.
The common positive mass makes every scalar mode invertible, including
the constant mode. No mode subtraction, proper-time window, or
shape-dependent counterterm occurs in (2). The species, mass equality,
and measure are chosen; no supersymmetry or interaction-stable vacuum
energy cancellation has been proved. Induction by massive constituents
is an established mechanism, discussed for example by
[Frolov, Fursaev, and Zelnikov](https://arxiv.org/abs/hep-th/9607104).
The complete finite spectral calculation here has the particular
regulator and scope stated above.

For the product of round spheres,

\[
 V=16\pi^2r_1^2r_2^2,\qquad
 \int\sqrt g R=32\pi^2(r_1^2+r_2^2).                  \tag{3}
\]

The scalar mode count is consequently
\(N_1^2N_2^2=\kappa^4V/(16\pi^2)\).
Each sphere's N_i^2 scalar modes are proportional to its physical area.
This is a spectral counting rule, not a derivation of microscopic cells.

## 2. Exact quadrature identities and a uniform bound

Set

\[
 f_t(x)=2xe^{-tx^2},\quad I(t)=(1-e^{-t})/t,\quad
 \delta(t)=f_t'(1)-f_t'(0)=2[(1-2t)e^{-t}-1].
\]

Let M_N and T_N be composite midpoint and trapezoid quadrature on [0,1],
with spacing 1/N. The exact finite heat traces obey

\[
 B_N(t):=H_B(t/N^2)=N^2e^{t/(4N^2)}M_Nf_t,
 \qquad F_N(t):=H_F(t/N^2)/2=N^2T_Nf_t.                \tag{4}
\]

The notation B_N,F_N in this section denotes heat traces, whereas B,F
in (2) denote half-logdet sums. Write

\[
 b(t)=tI(t)/4-\delta(t)/24,\quad f(t)=\delta(t)/12,
 \quad d(t)=b(t)-f(t)=\frac{1+(t-1)e^{-t}}2.
\]

Then

\[
 B_N=N^2I+b+R_{B,N},\qquad F_N=N^2I+f+R_{F,N},
\]
\[
 \boxed{|R_{B,N}(t)|,|R_{F,N}(t)|
       \le\frac{224}{N^2}\min(t^2,t),\quad0<t\le N^2.} \tag{5}
\]

Here is an explicit proof, including the time range needed for the full
determinant. The fourth-derivative form of
[Euler-Maclaurin summation](https://dlmf.nist.gov/2.10.E1), and its shifted
midpoint version, give the safely loose bounds

\[
 |T_N f_t-I-\delta/(12N^2)|\le N^{-4}\int_0^1|f_t''''|dx,
\]
\[
 |M_N f_t-I+\delta/(24N^2)|\le N^{-4}\int_0^1|f_t''''|dx.
\]

For example, the midpoint formula also follows from
\(M_N=2T_{2N}-T_N\); the trapezoid fourth-derivative remainder constant
is at most 1/360, and this combination is still smaller than one.
Direct differentiation gives

\[
 f_t''''=(120t^2x-160t^3x^3+32t^4x^5)e^{-tx^2}.
\]

For t<=1, integrate the absolute polynomial terms on [0,1] and use
t^3,t^4<=t^2, obtaining (316/3)t^2. For t>=1, integrating those terms
on [0,infinity) gives (60+80+32)t. Hence
\(\int|f_t''''|\le172\min(t^2,t)\).

On the range in (5), exp(t/(4N^2))<=exp(1/4). Expanding this exponential
in (4), its quadratic remainder contributes at most
\(e^{1/4}\min(t^2,t)/(32N^2)\), and its cross term with delta
contributes at most the same expression with denominator 16N^2.
Use I<=min(1,1/t) and |delta|<=6min(t,1).
The combined constant is
\(e^{1/4}(172+1/32+1/16)<224\), proving (5).

Also,

\[
 0<d(t)\le\min(t,1),\quad |b(t)|,|f(t)|\le\tfrac12\min(t,1).
\]

These follow directly from the displayed elementary functions. Let
n=min(N1,N2) and rho=max(N1,N2)/n. Multiplication of (5) gives

\[
 B_{N_1}B_{N_2}-F_{N_1}F_{N_2}
   =(N_1^2+N_2^2)I(t)d(t)+E(t),
\]
\[
 |E(t)|\le C_\rho\min(t^2,1),\quad 0<t\le n^2,
 \qquad C_\rho=102000+900\rho^2.                       \tag{6}
\]

To track the loose constant: the b^2-f^2 term costs at most 1/2;
the N_i^2 I R_j terms cost at most 896rho^2; the bR,fR terms cost at
most 448; the products of two remainders cost at most 100352.
For t>=1 use t<=n^2, and for t<=1 use n>=1. All multiply
min(t^2,1). Thus (6) is uniform in the matrix sizes.

## 3. The complete determinant theorem

Finite count balance and the logarithm integral give the exact identity

\[
 \Gamma=-4\int_0^\infty e^{-ct}
       [B_{N_1}(t)B_{N_2}(t)-F_{N_1}(t)F_{N_2}(t)]\frac{dt}{t}.
                                                               \tag{7}
\]

At zero time the square bracket is O(t), and the positive common mass
controls the infrared tail. There is no cutoff in this integration.
Define

\[
 J(c)=\int_0^\infty e^{-ct}I(t)d(t)\frac{dt}{t}>0.
\]

Splitting its integrand as

\[
 \frac{I(t)d(t)}t=\frac12\left[
       \frac{(1-e^{-t})^2}{t^2}+\frac{e^{-t}-e^{-2t}}t\right]
\]

and integrating by parts in the first term gives, using the convergent
Frullani differences,

\[
 \boxed{J(c)=\frac12[c\log c-(2c+3)\log(c+1)
                             +(c+3)\log(c+2)].}        \tag{8}
\]

Integrate the error in (6) up to n^2. It is bounded by
\(4C_\rho[1/2+E_1(c)]\), where
\(E_1(z)=\int_z^\infty e^{-u}du/u\).
For the remaining finite-trace tail use 0<=B_N,F_N<=N^2 and
\(E_1(cn^2)\le e^{-cn^2}/(cn^2)\). This tail is at most
\(8\rho^2/(ec^2)\), since
\(n^2e^{-cn^2}\le1/(ec)\). The corresponding leading-function tail is
at most 4(1+rho^2), using I(t)d(t)/t<=1/t^2 for t>=1.
Therefore, for every c>0 and every bounded aspect ratio,

\[
 \boxed{\Gamma(N_1,N_2;c)=-4J(c)(N_1^2+N_2^2)+\mathcal R,
       \quad |\mathcal R|\le A(c,\rho),}               \tag{9}
\]
\[
 A(c,\rho)=4C_\rho[1/2+E_1(c)]
             +8\rho^2/(ec^2)+4(1+\rho^2).
\]

This is an all-size analytical bound; sampled convergence is not its
proof. The constants are deliberately loose. The actual remainders in
the audit are much smaller.

Combining (1), (3), and (9),

\[
 \boxed{\Gamma=-\frac{J(c)\kappa^2}{8\pi^2}\int\sqrt g R+O_{c,\rho}(1).}
                                                               \tag{10}
\]

In the Euclidean convention \(S_{EH}=-(16\pi G)^{-1}\int\sqrt g R\),

\[
 \boxed{G^{-1}=2J(c)\kappa^2/\pi>0.}                  \tag{11}
\]

For example J(0.1)=0.8823773419939. The coefficient has the continuous
limit J(0)=3log(2)/2, but (9) is a positive-mass theorem. Its constants
are not uniform as c tends to zero. Taking fixed kappa and m while the
N_i grow is a **large-radius, low-curvature limit**, with finite G.
It is not removal of the proper cutoff at fixed Newton constant.

## 4. Controlled refinement variations

As the [continuum bridge](CONTINUUM_EINSTEIN_BRIDGE.md#2-why-a-mean-action-limit-alone-does-not-derive-field-equations)
already emphasizes, action convergence alone does not imply convergence
of equations of motion. Equation (9) does, however, control specified
integer refinements. For a fixed integer vector v, choose integer M
with M tending to infinity and M/min(N_i) tending to zero. Keep all
neighbors in one bounded-aspect family. Then

\[
 \frac{\Gamma(N+Mv)-\Gamma(N-Mv)}{2M}
     =-8J(c)N\cdot v+O(1/M),
\]
\[
 \frac{\Gamma(N+Mv)-2\Gamma(N)+\Gamma(N-Mv)}{M^2}
     =-8J(c)|v|^2+O(1/M^2).                            \tag{12}
\]

These follow by applying the uniform remainder bound to the exact
quadratic leading function. They are collective refinement differences;
no unit-step derivative theorem is inferred.

A stronger shape test keeps both the total volume and the field
dimension exactly constant within each stencil. For integer k>=2 put

\[
 K=[k(k+1)]^2,\quad h=\log((k+1)/k),
\]

and choose the three pairs

\[
 (K,K),\quad(k(k+1)^3,k^3(k+1)),\quad((k+1)^4,k^4).    \tag{13}
\]

Their products are all K^2. Swapping factors gives negative shapes.
They represent r1=(K/kappa)exp(u), r2=(K/kappa)exp(-u) at u=0,h,2h.
They have exactly the same scalar dimension K^4, total fermion
dimension 8K^4, and volume 16pi^2 K^4/kappa^4. Thus the shape test
redistributes representation factors without changing the total field
dimension. It is not merely comparing unrelated numbers of fields.

With E(u)=Gamma/K^2, (9) gives

\[
 E(u)=-8J(c)\cosh(2u)+O(K^{-2}).
\]

The symmetric second and fourth differences are

\[
 D_2=[2E(h)-2E(0)]/h^2,
 \quad D_4=[2E(2h)-8E(h)+6E(0)]/h^4.
\]

Relative to the identical finite stencils of the Einstein function,
their errors are O(K^-2 h^-2) and O(K^-2 h^-4). Since K grows as k^4
and h as 1/k, both vanish. The Einstein stencils themselves have
O(h^2) truncation error, proving

\[
 \boxed{D_2\longrightarrow-32J(c),\quad
 D_4\longrightarrow-128J(c),\quad D_4-4D_2\longrightarrow0.}       \tag{14}
\]

For c=0.1, the errors relative to the same finite Einstein stencil are:

| k | K | second-difference error | fourth-difference error |
|---:|---:|---:|---:|
| 2 | 36 | -0.02368 | -0.4712 |
| 3 | 144 | -0.001330 | -0.02373 |
| 4 | 400 | -0.0001650 | -0.00282 |
| 5 | 900 | about -0.0000319 | about -0.00054 |

These are compressed sums over exact finite eigenvalues and
multiplicities, not dense diagonalizations of the enormous field spaces.
An identification of equal-dimensional field spaces can be chosen.
No local Hamiltonian implementing their representation redistribution
has been constructed.

## 5. A same-mass fixed-size control

Adding a common mass alone does not explain the improvement. Hold both
matrix sizes at N and instead change radii to
r1=N exp(u)/kappa, r2=N exp(-u)/kappa. With a=exp(-2u), b=exp(2u),
the limiting normalized full action is

\[
 W_c(u)=-2[(1/a+1/b)F_c(a,b)
       +(a/b)\log((c+a+b)/(c+a))
       +(b/a)\log((c+a+b)/(c+b))],                    \tag{15}
\]
\[
 F_c=c\log c-(c+a)\log(c+a)-(c+b)\log(c+b)
                         +(c+a+b)\log(c+a+b).
\]

The preceding stage's heat-quadrature proof applies with the additional
factor exp(-ct); it improves the infrared control. At c=0.1,

\[
 W_c(0)=-8J(c),\quad W_c''(0)=-6.6093020536,\quad
 W_c''''(0)=-1.2991204968,
\]
\[
 W_c''''(0)-4W_c''(0)=25.1380877175\ne0.
\]

The audit differentiates (15) symbolically and compares independent
exact finite spectral derivatives. Thus the matched positive mass
leaves the old fixed-size obstruction in place. The revised spectral
resolution rule changes the leading homogeneous functional.

## 6. What principle the calculation supports

The candidate principle is: **geometric changes preserve a universal
proper spectral mode density, with balanced matter integrated using the
same microscopic measure.** At fixed volume this requires redistributing
modes among directions as the geometry changes. At changing volume it
requires refinement of the field space. Applying that principle as an
input produces (10) in this benchmark; it has not been deduced from the
causal growth law or from the four-spin Hamiltonian.

The next mathematical target is a corresponding result for arbitrary
smooth metric perturbations, including controlled variations. A product
of round spheres samples only a two-parameter Euclidean family. Other
functionals can agree on this family. Agreement here cannot fix the
constraint algebra, the number of propagating modes, a universal
matter cone, or Lorentzian reconstruction. The
[conditional Einstein constraint derivation](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
still requires its microscopic suppliers.

## 7. A remaining localization obstruction in the matrix realization

The distinction between spectral resolution and matrix localization is
quantitative. On one fuzzy sphere set

\[
 X_a=\frac{rJ_a}{\sqrt{j(j+1)}},\qquad j=(N-1)/2.
\]

In the north-pole highest-weight coherent state,

\[
 \langle[X_1,X_2]\rangle
       =i\frac{r^2}{j+1}=i\frac{2r^2}{N+1},\qquad
 (\Delta X_1)^2=(\Delta X_2)^2=\frac{r^2}{N+1}.       \tag{16}
\]

With r=N/kappa, this proper position variance grows as r/kappa,
although its ratio to r^2 tends to zero. The natural coherent-state
localization length is therefore of order sqrt(r/kappa), not 1/kappa.
The spectral cutoff stays fixed while this matrix localization scale
grows. Direct small-spin matrix checks verify (16).

This does not invalidate the free determinant theorem or exclude every
possible observable algebra. It prevents identifying (1) with a proved
uniformly local interacting regulator at fixed physical lengths. Smooth
global modes and arbitrary fixed physical wavelengths are different
limits. Matrix regularization and approximate diffeomorphisms are
studied by [Ishiki and Matsumoto](https://arxiv.org/abs/1904.00308), but
that framework does not supply the local dynamical realization required
here. A new local carrier, an interaction-locality proof in a specified
physical sector, or a different joint scaling remains necessary.

The immediate Einstein shape mismatch is repaired under stated inputs.
The proposed microscopic model still needs local refinement dynamics,
selection and stability of its geometric phase, protected matter
matching, arbitrary-metric response, and a Lorentzian constraint
reduction. The Standard Model and original TOE objective remain open.

## 8. Reproduction and scope

Run:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/proper_resolution_induction_audit.py
```

The [audit](scripts/proper_resolution_induction_audit.py) checks symbolic
identities, the independent coefficient integral, exact quadrature sums,
complete determinant/proper-time agreement, scaling remainders, radius
refinements, constant-volume shape profiles and fourth differences, the
same-mass fixed-size control, and the coordinate localization scale.
The [report](data/proper_resolution_induction_audit.json) records source
hashes and explicit scope. No older research source or Lean file is
changed by this stage.
