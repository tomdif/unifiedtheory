# A refinement model whose dynamics supply the continuum hypotheses

Date: 2026-11-09

We close the reconstruction program for a specific deterministic abelian
model. Starting from any bounded measurable real curvature f0 on the unit
two-torus, evolve its cell averages by the nearest-neighbor discrete heat
equation and reconstruct U(1) links on an open square. The evolution itself
preserves a curvature bound and produces uniform positive-time regularity.
The entire lattice family converges to a unique smooth axial connection for
every positive time, with an explicit O(h) transport estimate on each interval
0<t0<=t<=T. No initial differentiability or assumed convergence is required.

This is a complete analytic existence, smoothing, convergence, and uniqueness
proof for the stated model. The companion Lean module proves specified
ingredients, not the entire Fourier argument. Heat-flow approximation is
classical mathematics; no novelty claim is made. This is a linear U(1)
curvature diffusion model, not a derivation of nonlinear nonabelian dynamics.

## 1. Define the model before taking the limit

Fix a real f0 in L-infinity(T^2), ||f0||_infinity<=M, M>=0. The torus has
period one and total area one. All integrals of f0 refer to its almost-everywhere
class. For n>=3 put h=1/n and use indices i,j in Z/nZ. Define the initial
curvature by actual cell averages:

\[
 f^n_{ij}(0)=h^{-2}\int_{ih}^{(i+1)h}\int_{jh}^{(j+1)h} f_0(x,y)\,dy\,dx.
 \tag{1}
\]

Point sampling would not work for arbitrary measurable data: changing a
function on all rational points leaves its L-infinity class unchanged while
changing every rational-grid sample. Cell averages avoid that defect.

The discrete model is the finite linear ODE

\[
 \dot f^n_{ij}=\Delta_h f^n_{ij}
 =h^{-2}(f^n_{i+1,j}+f^n_{i-1,j}+f^n_{i,j+1}+f^n_{i,j-1}-4f^n_{ij}).
 \tag{2}
\]

Indices in (2) wrap periodically. Time is the diffusion parameter. The
solution exists uniquely for all t>=0 by the matrix exponential, equivalently
by the convergent positive-series construction in section 2.

From this real lifted curvature form U(1) plaquettes and links on [0,1]^2:

\[
 P^n_{ij}(t)=e^{\mathrm i h^2 f^n_{ij}(t)},\qquad
 H^n_{ij}(t)=1,\qquad
 V^n_{ij}(t)=\exp\!\left(\mathrm i h^2\sum_{a=0}^{i-1}f^n_{aj}(t)\right).
 \tag{3}
\]

There are n-by-n plaquettes, n-by-(n+1) horizontal links and (n+1)-by-n
vertical links. Their actual plaquette products are exactly P^n. Arbitrary
vertex gauges may be applied to (3); the rooted tree gauge recovers (3).
The dynamics are specified in terms of gauge-invariant U(1) curvature lifts.

**Boundary and lift scope.** Periodicity is imposed on the scalar curvature
equation (2). The reconstructed gauge field has open-square boundaries: no
opposite link boundaries are identified. Thus we do not assert a global
periodic connection or silently ignore flux quantization and torus holonomies.
For all sufficiently fine grids h^2 M<pi, section 2 implies the compact
plaquettes remain in the principal-logarithm sector. In that sector the real
lifts used in (2) are uniquely recoverable from the compact plaquettes.
Outside it, a lift is extra state data. Equation (2) is not being identified
with gradient flow of the compact Wilson link action.

## 2. Bounds derived from the actual dynamics

Let P be the four-neighbor averaging matrix, so Delta_h=4h^{-2}(P-I).
It has nonnegative entries and preserves constants. For s=4t/h^2,

\[
 f^n(t)=e^{-s}\sum_{r=0}^{\infty}\frac{s^r}{r!}P^r f^n(0).
 \tag{4}
\]

The series converges absolutely, since ||P^r f||_infinity<=||f||_infinity.
Its scalar weights are nonnegative and sum to one. Differentiation on compact
time intervals, justified by the exponentially summable majorants, gives
the generator 4h^{-2}(P-I) and initial value f^n(0). Thus (4) is the actual
solution of (2), not an unrelated bounded proxy.

It follows directly that

\[
 \|f^n(t)\|_\infty\le M,\qquad
 \|f^n(t)-g^n(t)\|_\infty\le\|f^n(0)-g^n(0)\|_\infty.
 \tag{5}
\]

The mean is conserved because each neighbor shift permutes the grid.
Periodic summation by parts gives the exact energy identity

\[
 \frac{d}{dt}\frac{h^2}{2}\sum_{ij}(f^n_{ij})^2
 =-\sum_{ij}\left[(f^n_{i+1,j}-f^n_{ij})^2+
                         (f^n_{i,j+1}-f^n_{ij})^2\right]\le0.
 \tag{6}
\]

For example, expanding sum f_ij(f_(i+1,j)+f_(i-1,j)-2f_ij) and shifting the
second sum gives minus sum(f_(i+1,j)-f_ij)^2. The y terms are identical.
The curvature bound in (5) therefore propagates from bounded initial data;
no small mesh-dependent assumption is added to obtain it.

## 3. Dynamics generate positive-time regularity

Use the representative frequency set

\[
 K_n=\{-\lfloor n/2\rfloor,\ldots,\lceil n/2\rceil-1\}^2,
 \quad r_1(k)=|k_1|+|k_2|,\quad r_2(k)^2=k_1^2+k_2^2.
\]

Discrete Fourier inversion diagonalizes (2):

\[
 f^n_{ij}(t)=\sum_{k\in K_n}c^n_k e^{-\lambda_{n,k}t}
                         e^{2\pi\mathrm i(k_1ih+k_2jh)},
 \quad
 \lambda_{n,k}=4h^{-2}\{\sin^2(\pi h k_1)+\sin^2(\pi h k_2)\},
 \tag{7}
\]

where c^n_k=h^2 sum_ij f^n_ij(0) exp(-2pi i k dot (ih,jh)); hence |c^n_k|<=M.
Conjugate symmetry ensures that (7) is real, including the even-n Nyquist
frequencies when interpreted on the discrete grid.

For |h k_a|<=1/2, the elementary bounds 2|z|/pi<=|sin z|<=|z| on
|z|<=pi/2 imply

\[
 16r_2(k)^2\le\lambda_{n,k}\le4\pi^2r_2(k)^2.
 \tag{8}
\]

For q>=1 define the finite Gaussian moment constant

\[
 C_q(t_0)=\sum_{k\in\mathbb Z^2\setminus\{0\}}
                 r_1(k)^q e^{-16t_0r_2(k)^2},\qquad t_0>0.
 \tag{9}
\]

Its finiteness follows without any continuum limit: the shell max(|k1|,|k2|)=m
has 8m points, r1<=2m, and r2^2>=m^2. Thus
C_q(t0)<=2^(q+3) sum_(m>=1) m^(q+1) exp(-16t0 m^2)<infinity.
For a fully explicit, albeit loose, bound put rho=exp(-16t0):

\[
 C_q(t_0)\le 2^{q+3}(q+1)!\frac{\rho}{(1-\rho)^{q+2}}.
 \tag{10}
\]

Indeed m^(q+1)<=m(m+1)...(m+q)=(q+1)! binomial(m+q,q+1), and the corresponding
geometric generating series is rho/(1-rho)^(q+2).

Each forward difference D_h,x has Fourier multiplier
(exp(2pi i h k1)-1)/h, of modulus at most 2pi|k1|. Consequently, for a+b=q>=1,

\[
 \sup_{t\ge t_0}\|(D_{h,x})^a(D_{h,y})^b f^n(t)\|_\infty
 \le (2\pi)^q M C_q(t_0),
 \tag{11}
\]

uniformly in n. In particular neighboring curvature values differ by at most
h L0, where

\[
 L_0=2\pi M C_1(t_0).
 \tag{12}
\]

Likewise ||dot f^n(t)||_infinity<=4pi^2 M C_2(t0). These are bounds derived
from the discrete evolution, not assumptions about evolved curvature.
They can blow up as t0 goes to zero, as expected for discontinuous data.

## 4. Construct and identify the unique continuum solution

Let c_k=integral_(T^2) f0(z) exp(-2pi i k dot z) dz. Set

\[
 f(t,z)=\sum_{k\in\mathbb Z^2}c_k e^{-4\pi^2r_2(k)^2t}
                                  e^{2\pi\mathrm i k\cdot z},\qquad t>0.
 \tag{13}
\]

Since |c_k|<=M, all differentiated series converge uniformly for t>=t0>0.
Thus f is smooth for positive time, real, and satisfies partial_t f=Delta f.
Because f0 lies in L2, Parseval and dominated convergence of its square-summable
Fourier coefficients give f(t)->f0 in L2 as t decreases to zero.

This solution is unique in C([0,T];L2(T^2)) among distributional heat
solutions: testing the equation against each Fourier mode gives
dot c_k(t)=-4pi^2 r2(k)^2 c_k(t), whose solution with initial coefficient c_k
is forced to be (13). Fourier completeness then identifies the solution.
This also supplies uniqueness in the usual bounded mild-solution class.

We next prove a quantitative comparison with the *whole* discrete sequence,
rather than appeal only to compactness.

## 5. Explicit convergence for bounded, possibly discontinuous data

The difference of the initial Fourier coefficients can be estimated directly
from the cell averages. For z in the cell with lower-left corner z_ij,
|exp(-2pi i k dot z_ij)-exp(-2pi i k dot z)|<=2pi h r1(k).
Multiplying by |f0| and integrating over all cells gives

\[
 |c^n_k-c_k|\le2\pi M h r_1(k).
 \tag{14}
\]

Put mu_k=4pi^2 r2(k)^2. The elementary estimate
0<=z^2-sin^2 z<=z^4/3 on |z|<=pi/2 gives

\[
 0\le\mu_k-\lambda_{n,k}
 \le\frac{4\pi^4}{3}h^2(k_1^4+k_2^4).
 \tag{15}
\]

For the upper bound on z^2-sin^2 z, use
||z|-|sin z||<=|z|^3/6 and |z|+|sin z|<=2|z|.
The former follows by integrating 0<=1-cos s<=s^2/2.
The exponential mean-value bound then gives, for t0<=t<=T,

\[
 |e^{-\lambda_{n,k}t}-e^{-\mu_kt}|
 \le\frac{4\pi^4}{3}T h^2 r_1(k)^4e^{-16t_0r_2(k)^2}.
 \tag{16}
\]

Split the error between (7) and (13) into initial-coefficient error (14),
eigenvalue error (16), and continuum frequencies outside K_n. If k is outside
K_n then r2(k)^2>=n^2/4, so its indicator is at most 4h^2 r2(k)^2. Since
4pi^2>16 and r2^2<=r1^2, the omitted frequencies contribute at most
4 M h^2 C_2(t0). It follows that

\[
 \boxed{\sup_{t_0\le t\le T}\max_{ij}
 |f^n_{ij}(t)-f(t,ih,jh)|\le E_n,}
 \tag{17}
\]

where the fully specified error is

\[
 E_n=M\left[2\pi C_1(t_0)h+
       \left(\frac{4\pi^4}{3}T C_4(t_0)+4C_2(t_0)\right)h^2\right].
 \tag{18}
\]

The constants are independent of n. No initial Sobolev norm is hidden in
(18). The first-order term reflects the robust cell-average coefficient
estimate for arbitrary bounded data; it is not a claim of an optimal rate.

In particular E_n->0 along the entire sequence. The uniform discrete bound
(5), approximation of each continuum point by grid points, and continuity
of f show ||f(t)||_infinity<=M. Its directional derivatives are bounded by
L0 from the same Fourier calculation as (11). Bilinear interpolation of f^n,
using periodic values on the last row and column, therefore converges uniformly
to f on [t0,T] times the square, with error
at most E_n+2L0 h. This last statement is separate from the nodal bound (17).

If the actual initial lattice values differ from (1) by at most eta_n, the
contractivity in (5) adds only eta_n to (17). Thus any eta_n->0 still gives
the same unique limit. Persistent arbitrary initialization error is not
discarded by the theorem.

## 6. Reconstruct the limiting gauge connection and its observables

Define, in the head-to-tail convention of
[the reconstruction theorem](GAUGE_DISCRETE_CONTINUUM.md),

\[
 A(t)=\mathrm i\,a_y(t,x,y)\,dy,\qquad
 a_y(t,x,y)=\int_0^x f(t,s,y)\,ds,\qquad a_x=0.
 \tag{19}
\]

For t>0 this connection is smooth, its curvature is i f dx wedge dy, and
a_y(t,0,y)=0. The curvature and these two gauge conditions uniquely determine
it, by integrating partial_x a_y=f. This is uniqueness of the axial
representative. Gauge-equivalent descriptions are still permitted.

By |exp(iu)-exp(iv)|<=|u-v|, (17) implies
|P^n_ij-exp(i h^2 f(t,ih,jh))|<=h^2 E_n. Thus every hypothesis of the earlier
discrete-to-continuum theorem has now been obtained from this model and its
bounded initial data. It already supplies convergence of transports.

In U(1) we can improve its constant. A vertical continuum edge at x=ih has
phase integral_(jh)^((j+1)h) integral_0^(ih) f(t,s,r) ds dr. Its lattice phase
is h^2 sum_(a<i) f^n_aj. The latter differs from h integral_0^(ih) f(t,s,jh) ds
by at most h E_n+L0 h^2/2 (the nodal error and the x Riemann-sum error).
Variation across the vertical edge contributes another L0 h^2/2. Therefore

\[
 |V^n_{ij}(t)-W_{A(t)}(\text{same edge})|\le hE_n+L_0h^2.
\]

Horizontal transports agree exactly. Inverse links have the same error, and
the unitary product estimate sums errors without amplification. For any
grid path gamma, including backtracking and repeated edges,

\[
 \boxed{\sup_{t_0\le t\le T}
 |W_n(t,\gamma)-W_{A(t)}(\gamma)|
 \le\ell_y(\gamma)\,[E_n+L_0h].}
 \tag{20}
\]

Unlike the general nonabelian bound, this abelian estimate needs no M^2 h
term. With initialization perturbations add eta_n inside the brackets.
Closed-loop Wilson observables obey the same bound. All comparisons use the
same geometric grid path; no convergence of an arbitrary changing path to
an unstated curve is assumed. Fixed axis-aligned polygons present on the
meshes consequently have their usual fixed continuum limit.

Equations (5), (11), (17), (19), and (20) close the requested chain:
specified lattice dynamics -> derived bounds -> constructed smooth limit ->
uniqueness -> full-sequence convergence with controlled observables.

The limit need not be flat. For f0=c the model preserves f^n=c and produces
A=i c x dy; the unit-square Wilson loop is exp(i c) at every mesh size and
time. More generally, mean conservation fixes that boundary loop to
exp(i integral f0). For the discontinuous example used below the flux is
0.44*0.56=0.2464, so the macroscopic holonomy remains nontrivial even though
every individual plaquette approaches the identity as h decreases.

## 7. Precise scope and relation to existing mathematics

This result allows genuinely discontinuous initial curvature and obtains
smoothness from diffusion at positive time. It does not assume a smooth
continuum target and then sample it. Its limitations are equally concrete:

- The dynamics are linear, deterministic, and abelian, with cell-average
  initialization from a common bounded datum. They are specified inputs.
- The Fourier estimates use a regular periodic curvature lattice. Gauge
  reconstruction takes place on an open square, not a torus bundle.
- Uniformity is on t>=t0>0. No smooth limit at t=0 is asserted for rough data.
- Nonlinear nonabelian evolution, quantum measures, irregular meshes, and
  deriving this diffusion law from another microscopic model remain outside
  the result.

The relevant methods are established. Praveen C.'s primary teaching notes
[Finite difference method for heat equation](https://math.tifrbng.res.in/~praveen/notes/cm2013/heat_1d.pdf)
explain the averaging/maximum-principle approach to stability. Hasegawa,
Saigo, Saito and Sugiyama's
[Lattice sums of I-Bessel functions, theta functions, linear codes and heat equations](https://link.springer.com/article/10.1007/s40687-024-00472-9)
(2024) treat explicit heat evolution on lattices. These references establish
context; all estimates used here are derived above. This targeted comparison
does not certify the exact theorem or its formalization as new mathematics.

## 8. Formalization and verification boundary

[AbelianCurvatureHeat.lean](UnifiedTheory/LayerA/AbelianCurvatureHeat.lean)
defines the actual nearest-neighbor averaging operator, its iterates, the
Poisson weights, their convergent heat series, and the n-by-n periodic grid
generator. The formal results prove bounds, positivity, translation symmetry,
constant preservation, the zero-time value, initial-data stability, and the
generator's uniformization identity. It also verifies the lower and upper
one-coordinate spectral bounds in (8) and the U(1) phase Lipschitz estimate.
In particular the maximum principle is
about the actual infinite-series evolution, not an abstract error recurrence.

The follow-up
[AbelianCurvatureHeatDynamics.lean](UnifiedTheory/LayerA/AbelianCurvatureHeatDynamics.lean)
now formalizes the series-to-ODE identification on finite grids, the semigroup
law, conserved sum, and uniqueness among global differentiable ODE solutions.
It also identifies the initial-data derivative and proves its operator norm is
at most one for nonnegative time, uniformly in the grid size. These 15 additional
results are recorded in the [open-obligation attack](OPEN_OBLIGATIONS_ATTACK.md).

The next three modules formalize the Fourier comparison:

- [AbelianCurvatureHeatFourier.lean](UnifiedTheory/LayerA/AbelianCurvatureHeatFourier.lean)
  diagonalizes the original Poisson heat for every function on a finite
  additive group. The explicit grid characters have exactly the sine-squared
  eigenvalues in (8).
- [AbelianCurvatureHeatContinuum.lean](UnifiedTheory/LayerA/AbelianCurvatureHeatContinuum.lean)
  proves summability of every polynomially weighted Gaussian on `Z²`,
  convergence of the discrete eigenvalues, and convergence of the full heat
  series uniformly over space at each fixed `t>0`. The coefficient error also
  tends to zero after any fixed polynomial frequency weight. The limiting
  series is continuous.
- [AbelianCurvatureHeatGridLimit.lean](UnifiedTheory/LayerA/AbelianCurvatureHeatGridLimit.lean)
  identifies the truncated series at grid nodes with the actual `gridHeat`
  evolution of Fourier-reconstructed initial data. It proves the resulting
  uniform-over-nodes limit and its stability under initialization errors
  tending to zero.

The general Fourier convergence hypotheses are `|c_n(k)|<=M`, `|c(k)|<=M`, and
`c_n(k)->c(k)` for every fixed integer frequency. The grid has side `n+1` and
uses the centered half-open window `-1/2 <= h*k_j < 1/2`, so the Nyquist
frequency is included only once. The initial datum in this theorem is the
real part of the finite Fourier reconstruction using these coefficients.
The theorem holds for every fixed positive time; its conclusion is qualitative
and uniform in space, with no time interval or convergence rate asserted.

The [cell-average extension](UnifiedTheory/LayerA/AbelianCurvatureHeatCellAverage.lean)
now supplies these hypotheses from the actual initialization. It defines the
lower-left grid sampling map, proves its convergence to the identity, and
applies dominated convergence to the Fourier coefficient integrals. Both
the discrete and continuum coefficients are bounded by the same `L¹` norm.
[Normalized grid inversion](UnifiedTheory/LayerA/AbelianCurvatureHeatGridInversion.lean)
identifies the finite reconstruction with the normalized cell integrals.
The modular cells, restricted to the unit square, are proved equal to the
ordinary half-open grid rectangles, each of area `1/(n+1)²`.

The theorem `bounded_cellAverage_limit` therefore starts with an essentially
bounded, almost-everywhere strongly measurable real function on the unit
square and its exact real cell averages. It proves convergence of the actual
`gridHeat` uniformly over all grid nodes at every fixed `t>0`. The underlying
complex-valued construction requires only integrability. The Fourier
coefficient bounds and consistency are conclusions of this construction.

[AbelianCurvatureHeatPDE.lean](UnifiedTheory/LayerA/AbelianCurvatureHeatPDE.lean)
uses polynomial Gaussian majorants to justify first spatial and time
derivatives of the actual continuum series, including series whose
coefficients have polynomial growth. Applying the spatial result twice
identifies the second derivatives. Theorems `continuum_heat_equation` and
`real_heat_equation` prove `∂t u = ∂x² u + ∂y² u` at every positive time.

The remaining Lean obligations for the original rough-data theorem are the
stated `L²` initial trace and continuum uniqueness, the quantitative estimates
uniformly for `t0<=t<=T`, and the axial reconstruction and transport bounds
(17)-(20).

These statements retain their analytic proofs above. The finite path-product
estimates are available in the earlier
[GaugeTransportStability.lean](UnifiedTheory/LayerA/GaugeTransportStability.lean).
The new [Fourier verification record](data/abelian_curvature_heat_fourier_verification.json)
records the earlier conditional comparison. The
[cell-average and PDE verification record](data/abelian_curvature_heat_cell_average_verification.json)
records the subsequent instantiation and differentiation proofs. Physical gate
verdicts are unchanged.

The audit script uses a discontinuous rectangle indicator as initial data,
exact cell averages, the discrete Fourier solution, and an independently
computed continuum Fourier series with an explicit truncation bound. It
checks curvature convergence, smoothing, conservation, dissipation, gauge
reconstruction, and path transport. Numerical checks supplement the proof.

Reproduction commands, from the repository root:

```sh
lake build UnifiedTheory.LayerA.AbelianCurvatureHeat
lake env lean scripts/CheckAbelianCurvatureHeat.lean
lake build UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
lake env lean scripts/CheckAbelianCurvatureHeatFourier.lean
lake build UnifiedTheory.LayerA.AbelianCurvatureHeatCellAverage
lake env lean scripts/CheckAbelianCurvatureHeatCellAverage.lean
python3 scripts/abelian_curvature_heat_audit.py
```

Only the named target and its dependencies are built; a whole-repository
build is not claimed.

### Original numerical and exact checkpoint

The following counts and `abelian_curvature_heat_verification.json` describe
the original 23-theorem checkpoint. Its hashes precede the documentation update
above; the follow-up formal results have their own verification record.

- The targeted Lean build passed without warnings. All 23 theorem declarations
  were checked with `#print axioms`, using only `propext`, `Classical.choice`,
  and `Quot.sound`. The complete output is saved in
  [abelian_curvature_heat_axioms.txt](data/abelian_curvature_heat_axioms.txt).
- 92 exact rational checks passed for the averaging bound, mass conservation,
  the generator's energy identity, and exact cell-average initialization.
- All eigenvalue inequalities passed on 5,378 discrete frequencies. Six
  independent comparisons between real-space Poisson evolution and FFT
  evolution passed, with separately estimated Poisson-series tails.
- Nine mesh sizes and three positive times gave 27 convergence, smoothing,
  conservation, dissipation, and initialization-stability cases. All 378
  path comparisons and their gauge-reconstruction checks passed.

For the discontinuous rectangle datum at t=0.02, curvature error decreased
from 0.12202015 on the n=8 grid to 0.00787526 on n=128. Initial maximum finite
differences grew from 7.04 to 117.76; after evolution they were 1.506719 and
1.502153. These measurements illustrate the mesh-independent smoothing
proved in (11). They are not used as hypotheses of that proof.

The universal estimates deliberately use only the initial L-infinity bound.
They are conservative: (18) gives about 1.24896 for n=128 on the entire
[0.02,0.08] interval, much larger than the measured error at t=0.02. No sharp
finite-resolution certificate is claimed from that numerical measurement.
The theorem's certified conclusion is its explicit bound and O(h) limit.

The continuum reference uses the analytically known Fourier coefficients of
the rectangle indicator, truncated at coordinate frequencies +/-32; its
omitted Gaussian tails are bounded separately. Floating-point rounding is
not formally certified. Results are retained in
[abelian_curvature_heat_audit.json](data/abelian_curvature_heat_audit.json).
