# Positive scalar transfer and the directional Einstein test

Date: 2026-09-10

The isotropic Euclidean scalar regulator constructed here has a positive
transfer operator. Its exact Gaussian Hamiltonian has exponentially local
coefficient matrices, and positive finite-range approximants converge with
an explicit volume-independent relative quadratic-form bound. This closes
a free-field transfer/locality subproblem.

It does **not** close the microscopic Einstein gap. For the specified
centered-derivative tensor source, time-space exchange symmetry fixes the
previous response mismatch along a lattice axis. The same action fails
the transverse-traceless (TT) matching test in other directions. Independent
finite-momentum calculations verify that failure. The leading long-wave
coefficients retain the lattice's orientation dependence.

These are analytical Gaussian results and floating-point audits, not new
Lean theorems. The background lattice, scalar field, and source coupling
are supplied model choices. A finite-spin gravitational phase, nonlinear
constraint algebra, physical graviton, and TOE remain unproved.

## 1. Precisely what changes

[The previous induced-tensor calculation](INDUCED_TENSOR_DYNAMICS.md)
used continuous Euclidean time and a spatial lattice. Its axial temporal
and spatial shear coefficients were unequal. Here time is also discretized
with the same spacing, set to one. At flat reference background the scalar
inverse covariance is

\[
 M(q)=m^2+2\sum_{\mu=0}^3(1-\cos q_\mu),\qquad G(q)=M(q)^{-1}.
\]

Its spatial stiffness and transfer energy are

\[
 L(\mathbf q)=m^2+2\sum_{i=1}^3(1-\cos q_i),\qquad
 E(L)=2\operatorname{arsinh}(\sqrt L/2).
\]

At zero mass, \(E(\mathbf q)=|\mathbf q|+O(|\mathbf q|^3)\), so the
scalar acoustic speed is one in every direction. Finite-volume Gaussian
expectations require positive mass or removal of the constant mode;
massless response integrals below are infinite-volume limits. The
massless transfer operator itself includes a free-particle zero mode.

The tensor remains a commuting external spatial source in this calculation:

\[
 \delta M=\gamma\sum_{ij}D_i^\dagger h_{ij}D_j,
 \qquad D_i=(T_i-T_i^{-1})/2.
\]

It couples to the same centered-derivative strain term as before. The
remaining positive lattice terms and the time-step regulator are fixed.
For sufficiently small bounded \(\gamma h\), the Gaussian form stays
positive. This is not a complete metric-dependent discretization. In
particular no shift/lapse sector or nonlinear covariant contact vertices
are claimed. The flat four-dimensional propagator is isotropic under
coordinate permutations; that discrete symmetry is weaker than continuous
rotational symmetry or diffeomorphism invariance of the source action.

## 2. Exact positive transfer and its Gaussian Hamiltonian

For one spatial eigenmode of stiffness \(L\geq0\), with \([Q,P]=i\),
the Euclidean step is the positive self-adjoint operator

\[
 \mathcal T_L=e^{-LQ^2/4}e^{-P^2/2}e^{-LQ^2/4}.
\]

Positivity follows from \(\langle f,\mathcal T_Lf\rangle
=\|e^{-P^2/4}e^{-LQ^2/4}f\|^2\). Its coordinate kernel is

\[
 K_L(x,y)=\frac1{\sqrt{2\pi}}
 \exp\{-\tfrac12[(1+L/2)(x^2+y^2)-2xy]\}.
\]

Comparing this Gaussian kernel with oscillator evolution gives the exact
operator identity

\[
 \mathcal T_L=e^{-H_L},\qquad H_L=\tfrac12 A(L)P^2+\tfrac12 B(L)Q^2,
\]
\[
 A(L)=\frac{E(L)}{\sinh E(L)},\qquad
 B(L)=E(L)\sinh E(L)=L(1+L/4)A(L).
\]

The removable zero-stiffness limits are \(A(0)=1\), \(B(0)=0\).
For \(L>0\), the transfer eigenvalues are
\(e^{-E(L)(n+1/2)}\). The normalized vacuum coordinate correlator is

\[
 \langle Q_tQ_0\rangle=\frac{e^{-E(L)|t|}}{2\sinh E(L)}.
\]

There is positive spectral weight and one positive oscillator energy at
each nonzero spatial momentum. Products of these transfer operators give
the flat finite-volume Gaussian construction. Reflection through a time
slice yields a positive inner product by transfer factorization. This is
the free lattice setting of the reflection-positivity reconstruction
principle; full continuum Euclidean invariance is a separate requirement
in [Osterwalder and Schrader's reconstruction framework](https://projecteuclid.org/journals/communications-in-mathematical-physics/volume-31/issue-2/Axioms-for-Euclidean-Greens-functions/cmp/1103858969.full).

The audit independently discretizes the integral kernel with Hermite
quadrature at five positive stiffnesses and two resolutions, and compares
its first five eigenvalues with the exact spectrum. This numerical test
supplements the operator identity; positivity does not depend on it.

## 3. Uniform locality of the Gaussian coefficient matrices

Let \(L\) now be the massless nearest-neighbor cubic graph Laplacian, on
any periodic volume or on the infinite lattice. Then
\(0\leq L\leq12I\) and \(\|L-6I\|\leq6\). The coefficient has the
integral representation

\[
 A(z)=\int_0^1
 \frac{dt}{\sqrt{1+z/4}\sqrt{1+t^2z/4}}.
\]

It is holomorphic on a neighborhood of \(|z-6|\leq8\). On that disk,
\(\operatorname{Re}z\geq-2\), and each square-root factor has modulus
at least \(1/\sqrt2\); hence \(|A(z)|\leq2\). If

\[
 A(z)=\sum_{n\geq0}a_n(z-6)^n,\qquad
 P_R(L)=\sum_{n=0}^R a_n(L-6I)^n,
\]

Cauchy's estimate and the geometric series prove

\[
 |a_n|\leq2\,8^{-n},\qquad
 \|A(L)-P_R(L)\|\leq\epsilon_R:=8(3/4)^{R+1}.
\]

The integral representation also makes \(A\) positive and decreasing
on \([0,12]\), with \(A(12)\simeq0.380173\). For every \(R\geq13\),
\(\epsilon_R<A(12)/2\); consequently

\[
 P_R(L)\geq[A(12)-\epsilon_R]I>0,
 \qquad B_R(L)=L(1+L/4)P_R(L)\geq0.
\]

The two polynomials have graph ranges at most \(R\) and \(R+2\).
They retain the exact zero of the potential coefficient on the constant
mode, and \(\|B(L)-B_R(L)\|\leq48\epsilon_R\).

For graph distance \(d=d(x,y)\geq1\), truncate before a polynomial can
connect the two sites to obtain

\[
 |A(L)_{xy}|\leq8(3/4)^d.
\]

For \(d\geq3\), truncating \(A\) at degree \(d-3\) similarly gives

\[
 |B(L)_{xy}|\leq384(3/4)^{d-2}.
\]

The bound \(384\) suffices at shorter distances. Cubic-lattice shell
counts grow at most quadratically, so these exponential coefficient
bounds are summable uniformly in volume, including with an exponential
weight of rate strictly below \(\log(4/3)\).

There is also a useful energy-form statement. For the Gaussian
Hamiltonians with coefficients \((A,B)\) and \((P_R,B_R)\), their
quadratic forms obey

\[
 |\langle\psi,(H-H_R)\psi\rangle|
 \leq\frac{\epsilon_R}{A(12)}\langle\psi,H\psi\rangle.
\]

Indeed \(|A-P_R|\leq[\epsilon_R/A(12)]A\), and multiplying by the
commuting nonnegative \(L(1+L/4)\) gives the corresponding inequality
for \(B\). Apply these matrix inequalities to the momentum and coordinate
quadratic forms on their common form domain. The constants are independent
of the number of sites.

This proves locality of the **Gaussian coefficients** and convergence in
relative energy form. Because \(Q\) and \(P\) are unbounded, it is not
a bounded-operator-norm interaction estimate. Nor does the logarithm of
a general interacting spin-field transfer product inherit this proof:
the scalar functional calculus used here no longer applies. No uniform
locality theorem for that full interacting logarithm is asserted.

## 4. Exact frequency integral and axial equality

Writing \(c=\cosh E=1+L/2\), \(s=\sinh E=\sqrt{L(1+L/4)}\), the
frequency propagator is \([2(c-\cos\nu)]^{-1}\). Fourier summation
using the positive correlator above gives

\[
 J(E_a,E_b;p_0)=\int_{-\pi}^{\pi}\frac{d\nu}{2\pi}
 G(\nu,E_a)G(\nu+p_0,E_b)
 =\frac{\sinh(E_a+E_b)}{4\sinh E_a\sinh E_b
 [\cosh(E_a+E_b)-\cos p_0]}.
\]

Useful zero-frequency moments are

\[
 I_2=\int G^2=\frac{c}{4s^3},\quad
 I_3=\frac{2c^2+1}{16s^5},\quad
 I_4=\frac{c(2c^2+3)}{32s^7},\quad
 \int\sin^2\nu\,G^4=\frac{c}{32s^5}.
\]

All single-frequency integrals include \(d\nu/(2\pi)\). The source
Hessian from \(\tfrac12\operatorname{Tr}\log(M+\delta M)\) is
\(-\gamma^2/2\) times the vertex bubble. Its zero-momentum mass
matrix is negative; removing it is explicit source-mass tuning.

For TT tensors transverse to \(\hat z\), their vertices depend on
\(q_x,q_y\) alone. Exchanging \(q_0\) and \(q_z\) in the complete
four-dimensional Brillouin-zone integral proves equality of the temporal
and axial spatial derivative matrices. This holds for each polarization
and for every positive mass, with a convergent massless limit. Positive
time coefficients follow from a weighted Gram integral. Thus the
loop-only axial response ratios are exactly one.

This equality concerns the induced source response. A bare spin time
coefficient changes the total response, as in the previous note; it
cannot silently be omitted when claiming an actual collective mode.

## 5. The off-axis vertex terms that the axial test misses

Let \(n\) be a unit spatial vector and let \(T\) be symmetric,
\(Tn=0\), \(\operatorname{tr}T=0\). The exact source vertex for external
momentum \(pn\), with symmetric loop routing, is

\[
 v_T(q,pn)=\sin(q+pn/2)^T T\sin(q-pn/2)
          =a^TTa-b^TTb,
\]
\[
 a_i=\sin q_i\cos(pn_i/2),\qquad b_i=\cos q_i\sin(pn_i/2).
\]

Consequently \(v_T=v_{0,T}+p^2v_{2,T}+O(p^4)\), where, writing
\(s_i=\sin q_i\) and \(c_i=\cos q_i\) in this paragraph,

\[
 v_{0,T}=s^TTs,\qquad
 v_{2,T}=-\tfrac14[(s\mathbin{\odot}n^2)^TTs+
 (c\mathbin{\odot}n)^TT(c\mathbin{\odot}n)].
\]

The continuum TT condition annihilates the momentum correction to the
vertex built from linear momenta. It does not annihilate this lattice
vertex correction at generic internal momentum. On a coordinate axis
the correction vanishes because the relevant row and column of \(T\)
vanish. In other directions it contributes to the leading \(p^2\)
coefficient, including contributions from large internal momentum.

Define \(d_1=2\sum_i n_i\sin q_i\),
\(d_2=2\sum_i n_i^2\cos q_i\). For two Frobenius-orthonormal TT
tensors labelled \(a,b\), the exact derivative coefficients are

\[
 (Z_t)_{ab}=\gamma^2\int_{\mathrm{BZ}_3}
 v_{0,a}v_{0,b}\frac{\cosh E}{32\sinh^5 E},
\]
\[
 (Z_n)_{ab}=\frac{\gamma^2}{8}\int_{\mathrm{BZ}_3}
 v_{0,a}v_{0,b}(d_2I_3-d_1^2I_4)
 -\frac{\gamma^2}{2}\int_{\mathrm{BZ}_3}
 (v_{2,a}v_{0,b}+v_{0,a}v_{2,b})I_2.
\]

Every spatial integral uses \(d^3q/(2\pi)^3\). These formulas follow
by expanding both shifted propagators and both vertices, then using the
exact frequency moments. The audit separately evaluates the unexpanded
spatial bubble at three decreasing momenta and positive mass: errors
relative to these coefficients decrease by a factor near four each time
momentum is halved. Finite temporal differences provide another check.

In the massless limit, 96 midpoint samples per spatial axis give:

| Spatial direction | Generalized eigenvalues of \((Z_n,Z_t)\) |
| --- | --- |
| \((0,0,1)\) | 0.998580, 0.999898; exact integral: 1, 1 |
| \((1,1,0)/\sqrt2\) | 3.020665, 3.372696 |
| \((1,1,1)/\sqrt3\) | 3.643951, 3.643951 |
| \((1,2,3)/\sqrt{14}\) | 3.039533, 3.205605 |

Grids of 32, 64, and 96 points per axis check convergence; the reported
numbers are floating-point estimates, not certified intervals. The axial
error is an infrared quadrature effect. The off-axis departures are far
larger than the changes between the two finest grids.

These are **TT-projected response ratios**, not established squared
physical graviton speeds. Off-axis tensors can mix with other strain
components, and the model has no gravitational gauge constraints. Even
as a necessary source-response benchmark for the proposed identification
with the metric, however, the result fails: Einstein TT kinetics on a
flat background would give a common unit ratio in every direction.

The full six-component temporal response is again positive definite.
Analytically, its quadratic form is a positive weight times
\((s^TTs)^2\); the polynomial is identically zero only for \(T=0\).
There is no constraint reduction in this Gaussian response.

## 6. Consequence for the model and the remaining gap

The positive transfer and locality results remove a specific objection
to using a discretized Euclidean time step in the free matter sector.
They do not turn a fixed lattice source action into a covariant metric
regulator. A direction-independent clock rescaling, regular invertible
change of tensor coordinates, or multiplying by identical scalar species
does not remove the unequal generalized response eigenvalues. Under
tensor changes the two matrices transform by the same congruence.

These discrepancies are coefficients of the leading \(p^2\) response
in lattice units. Merely probing longer wavelengths, or scaling a
massless copy of this same action to a smaller spacing, preserves their
dimensionless ratios. This observation does not exclude a different
interacting renormalization flow or a revised microscopic coupling.

The next construction must specify how **all** ultraviolet terms and
the measure couple to the candidate geometry, then verify its Ward
identities and all-direction response. Adding the same covariant TT
kinetic matrix to time and space leaves \(Z_n-Z_t\) unchanged; symmetry
breaking counterterms could tune it, but their origin and protection
would be new obligations. A low-energy scalar cone by itself is not
enough to determine the ultraviolet-sensitive induced tensor kinetic
term.

Geometric heat-kernel coefficients are available when one starts with
appropriate operators on an already specified geometry; this is the
setting described by [Vassilevich](https://arxiv.org/abs/hep-th/0306138).
The broader induced-gravity mechanism is reviewed by
[Visser](https://arxiv.org/abs/gr-qc/0204062). Importing those coefficients
does not derive the missing covariance of the present microscopic source
action. That distinction is the model-development inference from the
calculation here.

Protected masslessness, the interacting spin state, elimination of extra
modes, universal matter coupling, and the nonlinear clock-deformation
algebra remain independent requirements. The conditional Einstein
derivation in [the clock-constraint benchmark](GRAVITY_FROM_CLOCK_CONSTRAINTS.md)
still assumes that algebra. Spacetime emergence and the full TOE remain
open.

## 7. Reproduction

Run from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/isotropic_tensor_regulator_audit.py
```

The script checks exact frequency-moment identities, twelve independent
frequency integrals, 32 vertex expansions, twelve directional grid cases,
twenty finite-momentum/frequency comparisons, ten transfer spectra, three
positive finite-range approximants, polynomial matrix supports, and the
full temporal Gram rank. It writes
`data/isotropic_tensor_regulator_audit.json` with eight source hashes.
Numerical bounds are supporting checks; the transfer positivity and
uniform Gaussian locality estimates above have analytical arguments.
Earlier source and report hashes are preserved. No Lean source is added
or changed in this stage.
