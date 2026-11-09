# Nonlinear tensor backreaction and the homogeneous clock mode

Date: 2026-09-10

The periodic Einstein target needs a constraint that the free tensor
benchmark did not test: the integrated nonlinear normal constraint.
A nonzero transverse-traceless momentum perturbation of a static flat
torus cannot extend to nearby vacuum initial data if the first-order
trace momentum is held at zero. A spatially uniform expansion or
contraction can supply the missing balance. Below, an explicit TT
pattern and such a trace mode solve the full vacuum constraints
exactly, with nonzero spacetime Weyl curvature.

This is a nonlinear benchmark for the Einstein equations already
identified as the conditional target. It is not a derivation of those
equations from microscopic spins. The construction uses a supplied
smooth torus, metric variables, vacuum Einstein constraints, and their
known Cauchy-development theorem. The compact spin phase, its linear
gravitational poles, and a TOE remain unproved.

## 1. The missing integrated constraint

Use units 16 pi G=1, zero cosmological constant, and no matter. Adopt
K_ij=(1/2) L_n q_ij, so positive trace K describes expansion for
positive lapse and zero shift. The vacuum initial-data constraints are

```
R(q)+(tr_q K)^2-K_ij K^ij=0,
nabla_j K^ij-nabla^i tr_q K=0.                            (1)
```

Consider a twice-differentiable family on a fixed flat three-torus,
with periodic coordinates and

```
q(epsilon)=delta+epsilon^2 r+O(epsilon^3),
K(epsilon)=epsilon [Sigma+(tau_1/3)delta]+O(epsilon^2),
tr Sigma=0,        partial_j Sigma^ij=0,
tau_1 constant.                                          (2)
```

The first metric variation is set to zero in this test. It selects
a pure TT momentum perturbation, not all possible linearized initial
data. Both linearized constraints hold, including when tau_1=0.
At second order the scalar constraint requires

```
partial_i partial_j r_ij-Delta tr r
                    +(2/3)tau_1^2-|Sigma|^2=0.
```

The derivative terms integrate to zero on the torus. Thus, writing
angle brackets for the flat volume average,

```
(2/3) tau_1^2 = <|Sigma|^2>.                             (3)
```

If tau_1=0, then Sigma=0. Allowing an arbitrary second-order metric
correction r cannot repair a nonzero TT seed with its first-order
trace frozen at zero. This is an explicit instance of the established
linearization-instability issue for compact flat backgrounds; see
[Brill and Deser](https://link.springer.com/article/10.1007/BF01645610).
It is not a newly discovered obstruction to all gravitational waves.
The topology and the specified perturbation family are essential.
On an asymptotically flat slice, boundary contributions change the
integrated argument.

The six homogeneous variables were retained in the compact code count
but excluded from the positive wave statement in
[the preceding benchmark](COMPACT_TENSOR_CONSTRAINTS.md). Equation (3)
shows why freezing their trace sector would fail an Einstein matching
test. This does not identify a finite qudit's spectrum with the
noncompact trace momentum; that microscopic representation is still
required.

## 2. An exact nonlinear completion of a TT momentum pattern

Let all coordinate periods be 2 pi, take a nonzero integer k, and set

```
Sigma(z)=A [[ cos(kz), sin(kz), 0],
            [ sin(kz),-cos(kz), 0],
            [       0,       0, 0]],
q_ij=delta_ij,
K_ij=Sigma_ij+(tau/3)delta_ij,
tau=+sqrt(3) A  or  -sqrt(3) A.                           (4)
```

Sigma is traceless and divergence-free: its only spatial dependence
is in z and its z row vanishes. Its squared norm is the constant
2 A^2. Therefore the momentum constraint holds and

```
R=0,      tr K=tau,      |K|^2=2 A^2+tau^2/3,
(tr K)^2-|K|^2=(2/3)tau^2-2 A^2=0.                      (5)
```

These are exact nonlinear equations for any A. For A>0, the two signs
give initial expansion and contraction. As A tends to zero, these
data approach the static flat torus, but the trace momentum changes
at the same order as the TT momentum. The family is therefore
consistent with (3).

Flat spatial geometry does not make the resulting spacetime flat.
For vacuum data, use the electric and magnetic parts of the spacetime
Weyl tensor, with an orientation choice for the latter:

```
E_ij=R_ij+tau K_ij-K_i^l K_lj,
B_ij=epsilon_i^kl nabla_k K_lj.
```

For (4), the exact calculation gives

```
B=-k Sigma,              B_ij B^ij=2 A^2 k^2>0.          (6)
```

E and B are symmetric and traceless. A nonzero B proves that these
data cannot be a slice of flat spacetime. The periodic TT pattern is
initial momentum data; we do not call it an exact traveling wave.

Smooth vacuum data satisfying (1) have a unique maximal globally
hyperbolic Einstein development up to the appropriate isometry, by
the known [Choquet-Bruhat--Geroch theorem](https://link.springer.com/article/10.1007/BF01645389).
This imports Einstein evolution as a theorem about supplied Einstein
initial data. It neither proves geodesic completeness nor derives
that evolution from the repository's microscopic Hamiltonian.

## 3. Nonconstant TT sources have a positive conformal completion

The constant norm in (4) makes the scalar constraint algebraic. For
a general smooth flat TT tensor sigma on the three-torus, use

```
q_ij=psi^4 delta_ij,
K^ij=psi^(-10) sigma^ij+(tau/3)q^ij,
tau constant,                psi>0.                      (7)
```

Conformal covariance of TT divergence gives the momentum constraint.
Direct contraction and differentiation give

```
tr_q K=tau,
|K|_q^2=psi^(-12)|sigma|^2+tau^2/3,
R(q)=-8 psi^(-5) Delta psi.
```

Thus (1) reduces to

```
-8 Delta psi+c psi^5-S(x) psi^(-7)=0,
c=(2/3)tau^2,             S=|sigma|^2.                   (8)
```

This is the established constant-mean-curvature conformal method,
not a new replacement for the Einstein equations. A primary discussion
of conformal data on tori is
[Maxwell](https://arxiv.org/html/0909.5674). We give a direct argument
for the restricted case needed here: c>0 and
0<S_min<=S(x)<=S_max everywhere. Seeds with zeros, nonconstant mean
curvature, and other conformal classes are outside this simple proof.

The constants

```
l=(S_min/c)^(1/12),       u=(S_max/c)^(1/12)              (9)
```

are respectively a subsolution and supersolution of (8). The derivative
of its nonlinearity is

```
f_psi(x,psi)=5 c psi^4+7 S(x) psi^(-8)>0.                (10)
```

Existence follows constructively by monotone iteration. Choose a
constant M at least the maximum of (10) on [l,u] and set

```
(-8 Delta+M) psi_(n+1)=M psi_n-c psi_n^5+S psi_n^(-7),
psi_0=l.
```

The right side is nondecreasing in psi on [l,u], and the elliptic
inverse preserves order by the maximum principle. Inductively the
sequence increases and remains below u. Uniform elliptic estimates
on this positive interval give a convergent subsequence in a space
strong enough to pass to the equation; monotonicity identifies the
whole limit. Elliptic regularity makes the solution smooth.

For two positive solutions, the difference obeys
(-8 Delta+a(x))w=0 with a(x)>0. Multiplication by w and integration
give 8 integral |grad w|^2+integral a w^2=0, hence uniqueness.
The same constants bound any positive solution by the maximum principle.
Equivalently, (8) is the stationarity equation of the strictly convex
functional

```
F[psi]=integral [4|grad psi|^2+c psi^6/6+S psi^(-6)/6].   (11)
```

This convexity concerns solving an initial constraint. It is not
positivity of the unrestricted gravitational Hamiltonian, a microscopic
ground-state theorem, or a many-body spectral gap.

For c=0 and nonzero nonnegative S, integration of (8) would give
integral S psi^(-7)=0, which is impossible. Within this conformal
class a nontrivial TT source therefore requires nonzero mean curvature.

## 4. Fixing the volume determines the magnitude of the clock momentum

One can specify the physical volume instead of specifying c. Let psi(c)
be the solution above. Differentiating (8) gives

```
[-8 Delta+f_psi] partial_c psi=-psi^5.
```

The maximum principle implies partial_c psi<0. Thus the physical volume
V(c)=integral psi(c)^6 is strictly decreasing and continuous. The
constant bounds (9) imply

```
V_0 sqrt(S_min/c) <= V(c) <= V_0 sqrt(S_max/c),            (12)
```

where V_0 is the flat coordinate volume. These bounds give V(c) tending
to infinity as c tends to zero and tending to zero as c tends to
infinity. Hence every positive target volume determines a unique c>0,
a unique psi, and two signs tau=+/-sqrt(3c/2). This proves existence
and uniqueness within the stated conformal data and each sign branch.
It does not select a cosmological arrow of time.

Restore a=16 pi G for the canonical interpretation. With our sign
convention,

```
pi^ij=(sqrt(q)/a)(K^ij-tau q^ij),
pi=q_ij pi^ij=-2 tau sqrt(q)/a.
```

Under a uniform volume variation, delta q_ij=(2/3)q_ij delta V/V.
The gravitational symplectic form therefore contains

```
integral pi^ij delta q_ij = P_V delta V + shape terms,
P_V=-4 tau/(3a)                on a CMC slice.           (13)
```

At unit lapse, dV/dt=tau V on such a slice. Nonzero tau gives a local
monotonic volume variable on a branch with fixed sign and positive
lapse. This motivates retaining a volume--mean-curvature clock pair
in the target. It does not prove a global CMC foliation, quantize that
pair, or identify it with the previously supplied causal-order clock.

The negative trace contribution in the canonical normal constraint
is part of this balance. At q=delta and a=1, pi=Sigma-(2tau/3)I gives

```
pi^ij pi_ij-(tr pi)^2/2=|Sigma|^2-(2/3)tau^2.            (14)
```

Requiring this unreduced quadratic form to be positive in every trace
direction would remove the cancellation required by (5). A physical
stability argument must address the constrained or reduced system.
Equation (14) alone is not evidence for a physical negative-energy mode.

## 5. The first nonlinear correction produces an inverse Laplacian

To approach the flat background at fixed volume V=V_0, set
sigma=epsilon sigma_0, S_0=|sigma_0|^2>0, lambda=epsilon^2, and
(2/3)tau^2=lambda c(lambda). Equations (8) and the volume condition read

```
-8 Delta psi+lambda[c psi^5-S_0 psi^(-7)]=0,
<psi^6>=1.                                               (15)
```

The normalized small-amplitude branch is regular in lambda. A direct
implicit-function argument removes the constant-Laplacian degeneracy:
split the first equation into its mean-zero part, impose separately
<c psi^5-S_0 psi^(-7)>=0, and append the volume equation. At
lambda=0, psi=1 and c=<S_0>. The linearization first solves the
mean-zero Laplace equation, then the volume equation fixes the mean
of delta psi, and finally the averaged scalar equation fixes delta c.
This is an isomorphism on periodic Holder spaces with the indicated
mean-zero component. The implicit-function theorem gives a smooth
positive branch for sufficiently small lambda on the fixed torus.

Write psi=1+lambda u+O(lambda^2). Comparing coefficients yields

```
<u>=0,
-8 Delta u=S_0-<S_0>,
u=(1/8)(-Delta)^(-1)(S_0-<S_0>),
c(lambda)=<S_0>-7 lambda <S_0 u>+O(lambda^2).             (16)
```

The inverse Laplacian acts on mean-zero functions. Multiplying the
equation for u by u gives
<S_0 u>=8<|grad u|^2> >= 0, with strict positivity for nonconstant S_0.
Thus the conformal adjustment gives a computable correction to the
relation between TT amplitude and mean curvature at fixed volume:

```
tau^2=(3/2)epsilon^2 <S_0>
      -(21/2)epsilon^4 <S_0 u>+O(epsilon^6).              (17)
```

This supplies a precise mechanism for a nonlocal response after
solving local constraints. It does not insert a nonlocal microscopic
interaction. It also does not repair the old cubic dispersion: the
conformal response here starts at second order in amplitude and
has not changed the compact model's quadratic physical Hamiltonian.
The Einstein constraints in (15) are supplied inputs to this test.
The inverse Laplacian and the implicit-function bounds need not be
uniform as the physical size of the torus grows.

For the audited seed

```
sigma_0(z)=[[a(z),b(z),0],[b(z),-a(z),0],[0,0,0]],
a(z)=cos z+(1/4)cos 2z,
b(z)=sin z+(3/20)sin 3z,
```

S_0 has mean 417/200 and cosine coefficients
(1/2,3/10,1/2,-19/80,-9/400) at frequencies (1,2,3,4,6).
Its positive lower bound follows from
sqrt(a^2+b^2)>=1-sqrt((1/4)^2+(3/20)^2)>0. Exact Fourier algebra gives

```
<S_0 u>=6999949/368640000,
c'(0)=-48999643/368640000.                               (18)
```

## 6. A local discretization and what its residual proves

Replacing Delta by the nearest-neighbor periodic difference operator
gives a local nonlinear constraint equation. The sub/supersolution,
strict monotonicity, and uniqueness arguments also hold on that finite
graph. For fixed c and S, if a trial solution and the exact solution
both lie in [l,u], the discrete maximum principle gives

```
||psi_trial-psi_exact||_infinity <= ||residual||_infinity/m,
m=5 c l^4+7 S_min u^(-8)>0.                              (19)
```

For the scaled equation (15), multiply m by lambda and use c,S_0
in this expression. The computed c is held fixed in (19); the
normalization error is checked separately. Reported numerical bounds
evaluate this analytical inequality in floating point and are not
interval-arithmetic certificates.

For a smooth continuum solution on a cubic mesh of spacing h, the
one-dimensional centered-difference remainder in each coordinate gives

```
||Delta_h psi-Delta psi||_infinity
       <= (h^2/12) sum_i ||partial_i^4 psi||_infinity.
```

Combining this with (19) bounds the sampled-continuum versus discrete
solution error, at the same fixed c, by
(2h^2/(3m)) sum_i ||partial_i^4 psi||_infinity. This explains the
second-order convergence when those bounds are controlled. It is
not a proof of the full discrete hypersurface-deformation algebra or
of any finite-spin Hamiltonian limit.

The numerical audit solves (15) and the volume condition with a
positive Newton iteration. Four one-dimensional grids from 32 to 256
sites give successive error ratios near four. Four decreasing
amplitudes test the next-order remainders in (16). Six genuinely
three-dimensional nonconstant source cases use TT patterns along all
three axes, through 1,000 vertices. Their scalar and volume residuals,
positive barriers, and fixed-c error estimates are recorded.

## 7. Consequence for the microscopic model

The existing protected compact code remains a valid finite-spin
construction with the scope already proved. It has not implemented
the nonlinear balance (3), (15), or (17). Keeping its exact linear
checks while changing the off-code dynamics is already restricted
by [the averaging result](COMPACT_CONSTRAINT_NORMALIZER.md).

For a proposed Einstein phase on the periodic carrier, the next
microscopic normal generator must include both the homogeneous
trace/volume sector and the quadratic energy of the nonzero tensor
modes. Its constraints must select states obeying the nonlinear
balance, and its evolution must preserve that physical domain.
This gives an explicit test family, including nonzero Weyl curvature,
against which a candidate generator can be checked. The same generator
must still yield two positive linear tensor modes and the local
metric-dependent clock algebra with common matter sources.

The backreaction calculation therefore changes the target state
selection; it does not establish that the supplied Einstein initial
data are microscopic ground states or that the old cubic modes become
linear. The full gravity derivation, quantum consistency, spacetime
emergence, and recovery of physical matter remain open parts of the
unchanged TOE objective.

## 8. Reproduction

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/nonlinear_tensor_backreaction_audit.py
```

The [script](scripts/nonlinear_tensor_backreaction_audit.py) writes
[the source-hashed report](data/nonlinear_tensor_backreaction_audit.json).
Exact symbolic checks verify the nonlinear conformal identities,
the explicit vacuum data and nonzero magnetic Weyl tensor, the
canonical trace balance, and the Fourier response coefficients.
Numerical checks concern the local elliptic constraint solver and
its stated limits. The arguments are analytical and audited; no
new Lean theorem or spacetime evolution simulation is claimed.
