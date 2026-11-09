# A free continuum limit and a variational bridge to Einstein gravity

Date: 2026-09-10

Two concrete results are established here:

* The repository's **free flat overlap operator** converges to the Euclidean
  Dirac operator, with a quantitative low-momentum error and strong
  convergence of its positive-mass resolvents.
* An explicitly constructed **classical metric–scalar lattice action** has
  an `O(a^2)` continuum error in both its value and its first variation.
  Every sufficiently smooth convergent sequence of its stationary fields
  therefore satisfies the full nonlinear Einstein–scalar equations.

The second action, its metric variables, and its parameters are **new
physical inputs**, not consequences of the earlier locality theorem or the
causal growth law. Existence and compactness of stationary sequences are
not proved. The free Euclidean fermion limit and the Lorentzian classical
gravity benchmark are separate results; a common interacting quantum
continuum has not been constructed. These distinctions prevent a
consistency calculation from being mistaken for emergent spacetime or a TOE.

Nineteen Lean results support the finite variation algebra, error transfer,
and a counterexample below. The complete spectral, quadrature, and metric
calculus arguments remain analytic, with independent executable checks.

## 1. The actual free overlap operator has a controlled continuum limit

Let the physical spacing be `a>0`, physical momentum be `p`, and `k=a p`.
Use the same four Hermitian Euclidean Clifford matrices as the existing
overlap audit. Define

\[
 u_\mu=1-\cos k_\mu,\quad w=\sum_\mu u_\mu-1,\quad
 r=\sqrt{w^2+\sum_\mu\sin^2k_\mu},
\]

\[
 D_a(p)={1\over a}\left[I+
 {wI+i\sum_\mu\gamma_\mu\sin k_\mu\over r}\right],
 \qquad D(p)=i\sum_\mu\gamma_\mu p_\mu. \tag{1}
\]

This is the momentum symbol of the actual Wilson-projector construction;
the audit compares it independently with `FlatFamily.blocks`. No
low-momentum truncation is used to redefine the gauge-dependent regulator.

The exact radius identity from the preceding flat-holonomy work is

\[
 r^2=1+2\sum_{\mu<\nu}u_\mu u_\nu\ge1. \tag{2}
\]

Put `q=|k|_2`. Since `0<=u_mu<=k_mu^2/2`,

\[
 0\le r-1\le\sum_{\mu<\nu}u_\mu u_\nu\le q^4/8,
 \qquad |1+w/r|\le q^2/2+q^4/8. \tag{3}
\]

Taylor's integral remainder gives `|sin x-x|<=|x|^3/6`. The Clifford
relations give `||sum gamma_mu v_mu||=|v|_2` for real `v`. Consequently

\[
 \left|{\sin k\over r}-k\right|_2\le q^3/6+q^5/8.
\]

For `q<=1`, combining the scalar and Clifford parts of (1) yields

\[
 \|aD_a(p)-aD(p)\|
 \le q^2/2+q^4/8+q^3/6+q^5/8\le q^2,
\]

and therefore the explicit bound

\[
 \boxed{\|D_a(p)-D(p)\|\le a|p|_2^2\quad(a|p|_2\le1).} \tag{4}
\]

On a fixed flat physical torus, embed lattice spinors into the continuum
Fourier space using the lattice's Brillouin-zone modes and the specified
spin structure. For every fixed spectral cutoff `P`, the operator
difference restricted to `|p|<=P` is at most `a P^2` once `aP<=1`.
This is a convergence statement about test subspaces, not a proposed
gauge-invariant fixed momentum filter for interacting fields.

For a fixed positive real `m`, both resolvents have norm at most `1/m`.
Indeed `D(p)` is anti-Hermitian, while the Hermitian part of `D_a(p)` is
the nonnegative scalar `(1+w/r)/a`. The inverse identity gives

\[
 \|(D_a+m)^{-1}-(D+m)^{-1}\|_{|p|\le P}
 \le {aP^2\over m^2}. \tag{5}
\]

Extend the lattice resolvent by zero on Fourier modes outside its
Brillouin zone. These extensions have uniformly bounded norm `1/m`.
For any continuum `L^2` spinor, first approximate it by a finite Fourier
sum, apply (5), and bound the two remaining tails by `2/m` times the
approximation error. This proves **strong resolvent convergence on the
fixed continuum Hilbert space**. It establishes an actual free continuum
operator, rather than identifying a density-independent finite matrix
with one by definition.

The chiral projector also has a quantitative limit. At zero momentum its
range is `P_L=(I-gamma5)/2`, and the exact relation is

\[
 P_a(p)-P_L={1\over2}\gamma_5 aD_a(p).
\]

Equation (4) implies `||P_a-P_L||<=a|p|` when `a|p|<=1`.
This is free Euclidean chirality. The auxiliary positive-mass resolvent
in (5) is an operator comparison, not a construction of a gauge-invariant
mass term for an isolated Weyl fermion. Interacting chiral Schwinger
functions, renormalization, and a Lorentzian quantum reconstruction remain
additional work.

## 2. Why a mean action limit alone does not derive field equations

The existing BDG action module proves convergence from supplied
asymptotic coefficients and remainders. Even a proved action-value limit
would not by itself transfer its stationary fields. A simple exact
counterexample is

\[
 F_n(x)=x-{\sin(nx)\over n},\qquad F(x)=x,\quad n\ge1.
\]

Then `sup_x |F_n(x)-F(x)|<=1/n`, and every `F_n` is stationary at zero:
`F_n'(0)=0`. However `F'(0)=1`. Thus stationary points can converge to a
nonstationary point under uniform convergence of action values.
The new Lean module proves this example, including the vanishing error
bound and the unequal derivatives.

This is why the construction below controls **first variations** and
requires a convergent family of fields. It does not infer dynamics from
an action mean, a Bianchi identity, or locality alone.

## 3. Specify a concrete metric lattice action

Work on a bounded four-dimensional coordinate box, with a smooth
neighborhood supplying boundary stencils, or on a periodic coordinate
domain. The continuum metric has Lorentz signature `(-,+,+,+)`. Take
`kappa>0`, `Lambda` real, and a real scalar with

\[
 V(\phi)=\tfrac12 m^2\phi^2+\tfrac14\lambda\phi^4,
 \qquad m^2,\lambda\ge0.
\]

Sample `g_mu nu` and `phi` at the lattice sites. All ten independent
symmetric metric components vary. Write

\[
 D^a_\rho f(x)={f(x+a\hat\rho)-f(x-a\hat\rho)\over2a},
\quad v=\sqrt{-\det g},\quad g^{\mu\nu}=(g^{-1})_{\mu\nu},
\]

\[
 \Gamma^{a\,\rho}_{\mu\nu}
 ={1\over2}g^{\rho\sigma}
 (D^a_\mu g_{\sigma\nu}+D^a_\nu g_{\sigma\mu}
                           -D^a_\sigma g_{\mu\nu}),
\]

\[
 Q_a=g^{\mu\nu}
 (\Gamma^{a\,\rho}_{\mu\sigma}\Gamma^{a\,\sigma}_{\nu\rho}
 -\Gamma^{a\,\rho}_{\mu\nu}\Gamma^{a\,\sigma}_{\rho\sigma}).
\]

Denote the density in square brackets below, including `v`, by
`F(g,z,phi,p)`, where `z` and `p` are derivative arrays. A preliminary
centered-stencil action would be

\[
 S_a^0(g,\phi)=a^4\sum_x v(x)\left[
 {Q_a(x)-2\Lambda\over2\kappa}
 -\tfrac12 g^{\mu\nu}D^a_\mu\phi D^a_\nu\phi-V(\phi)\right]. \tag{6a}
\]

It has an exact defect: on an even periodic lattice a field alternating
from site to site has zero centered derivative. In particular,
`g(x)=[1+c(-1)^{x_1/a}] eta`, `0<|c|<1`, with zero scalar and `Lambda=0`,
has `D^a g=0`, zero action, and zero first variation for every test metric.
These spurious stationary fields have no uniformly smooth continuum limit.

The final action averages the **densities evaluated with one-sided
derivatives**, not the derivatives before evaluating the density. Define

\[
 D^+_\rho f={f(x+a\hat\rho)-f(x)\over a},\qquad
 D^-_\rho f={f(x)-f(x-a\hat\rho)\over a},
\]

\[
 \boxed{S_a(g,\phi)={a^4\over2}\sum_x
 [F(g,D^+g,\phi,D^+\phi)+F(g,D^-g,\phi,D^-\phi)].} \tag{6}
\]

For the alternating conformal metric above, unit coordinate volume and
`kappa=1`, direct contraction gives

\[
 S_a={3c^2\over a^2(1-c^2)},\qquad
 {dS_a\over dc}={6c\over a^2(1-c^2)^2}\ne0.
\]

Thus this false stationary example is removed. For a massless scalar on a
flat background, the spatial kinetic eigenvalue becomes
`sum_i 4 sin^2(k_i/2)/a^2`, whose only zero in the Brillouin zone is the
constant mode. The centered stencil instead has `sum_i sin^2(k_i)/a^2`
and checkerboard zeros. This does not prove stability or absence of every
spurious gravitational mode in the nonlinear indefinite action.

On a rectangular box use the corresponding midpoint cells and fixed halo
data. Compactly supported variations avoid boundary ambiguity. The finite
action is an explicit smooth function on the open set of nondegenerate
Lorentz metrics. It has a bounded stencil and retains the nonlinear
inverse-metric and volume factors. Its continuum coordinate covariance
is recovered below; exact diffeomorphism symmetry or the gravitational
constraint algebra at finite spacing is not claimed.

Equation (6) is a **chosen discretization of gravitational dynamics**.
It is not selected by the repo's growth probabilities, anomaly
cancellation, or uniform locality. In particular `kappa=8 pi G` and
`Lambda` remain parameters, and geometry is now a dynamical variable by
construction rather than an emergent variable already derived from order.

## 4. Derive the continuum action and both Euler equations

Use the curvature convention

\[
 R_{\mu\nu}=\partial_\rho\Gamma^\rho_{\nu\mu}
 -\partial_\nu\Gamma^\rho_{\rho\mu}
 +\Gamma^\rho_{\rho\sigma}\Gamma^\sigma_{\nu\mu}
 -\Gamma^\rho_{\nu\sigma}\Gamma^\sigma_{\rho\mu}.
\]

Expanding the derivative of the inverse metric and volume gives the
exact coordinate identity

\[
 vR=vQ+\partial_\rho\left[
 v(g^{\mu\nu}\Gamma^\rho_{\mu\nu}
             -g^{\rho\mu}\Gamma^\sigma_{\mu\sigma})\right]. \tag{7}
\]

Here `Q` is the expression in (6a) with ordinary derivatives. Thus the
continuum limit of (6) is the Einstein–Hilbert action plus the scalar
action, with the explicit boundary divergence subtracted. For periodic
fields, or for variations supported in the interior, this boundary term
does not affect the bulk equations. Other boundary-value problems require
their boundary action to be specified separately.

For a covariant metric variation `h_mu nu=delta g_mu nu`, direct
differentiation gives

\[
 \delta g^{-1}=-g^{-1}h g^{-1},\qquad
 \delta v=\tfrac12 v g^{\mu\nu}h_{\mu\nu},
\]

\[
 \delta\Gamma^\rho_{\mu\nu}
 =\tfrac12 g^{\rho\sigma}
 (\nabla_\mu h_{\sigma\nu}+\nabla_\nu h_{\sigma\mu}
                                     -\nabla_\sigma h_{\mu\nu}). \tag{8}
\]

The first identity follows by differentiating `g g^{-1}=I`; the second
is Jacobi's determinant formula. Substituting (8) into the variation of
the Ricci tensor yields

\[
 \delta R_{\mu\nu}=
 \nabla_\rho\delta\Gamma^\rho_{\nu\mu}
 -\nabla_\nu\delta\Gamma^\rho_{\rho\mu}.
\]

After integration by parts, its contracted contribution is a boundary
term. The remaining metric variation, including the volume and scalar
terms, is

\[
 \delta_g S[h]=-{1\over2\kappa}\int v
 [G^{\mu\nu}+\Lambda g^{\mu\nu}-\kappa T^{\mu\nu}]h_{\mu\nu}\,d^4x,
\tag{9}
\]

\[
 T_{\mu\nu}=\partial_\mu\phi\partial_\nu\phi
 -g_{\mu\nu}[\tfrac12 g^{\rho\sigma}
       \partial_\rho\phi\partial_\sigma\phi+V(\phi)].
\]

The scalar variation is

\[
 \delta_\phi S[\psi]=\int v[\Box_g\phi-V'(\phi)]\psi\,d^4x. \tag{10}
\]

All symmetric `h` and scalar `psi` of compact support are allowed. The
fundamental lemma of the calculus of variations applies componentwise.
Since `v>0` and `g` is invertible, stationarity is equivalent to

\[
 \boxed{G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu},
 \qquad\Box_g\phi-m^2\phi-\lambda\phi^3=0.} \tag{11}
\]

These are full nonlinear equations, including the scalar backreaction.
Their compatibility follows directly from
`nabla^mu T_mu nu=(box phi-V'(phi)) partial_nu phi` and the contracted
Bianchi identity. Conservation is a consequence of the scalar equation
in this model, rather than a separately prescribed source condition.

## 5. Quantitative convergence of the actual first variations

Here are sufficient hypotheses and the proof, without an unspecified
remainder that already assumes the conclusion. On the fixed coordinate
domain and its stencil neighborhood require

\[
 \|g\|_{C^3}+\|\phi\|_{C^3}+\|g^{-1}\|_{C^0}\le M,
\]

with fixed Lorentz signature. Test variations `h,psi` are `C^3`, with
periodic data or the stated boundary support. Constants may depend on
`M`, the domain and fixed parameters, but not on spacing.

1. The one-dimensional integral Taylor formula gives, componentwise,
   `||D^a_rho f-partial_rho f||infinity <= a^2 ||partial_rho^3 f||infinity/6`.
   The quadratic Taylor terms cancel in the centered difference. This
   applies separately to `g,phi,h,psi`.
2. Treat the density in (6a) as the explicit finite-dimensional function
   `F(g,z,phi,p)`, where `z` stores the first metric derivatives and `p`
   the scalar derivatives. Its first and second derivatives are uniformly
   bounded on the allowed compact jet sets. Inverses and `sqrt(-det g)`
   are smooth there because the metric eigenvalues stay away from zero.
   The mean value theorem, applied along the segment replacing ordinary
   derivatives by the centered ones, therefore bounds the density error
   for the preliminary centered action by `C a^2`, and its directional-
   derivative error by `C a^2 ||(h,psi)||C^3`.
3. The final one-sided average has the same order, for an exact algebraic
   reason. At fixed `g,phi`, write `F=F_0+B_g(Z,Z)`, where `Z` combines
   the metric and scalar derivative arrays. The density is quadratic in
   these arrays. Set `Delta^a_rho f=(f(x+a)-2f(x)+f(x-a))/a^2`. Since
   `D^+ = D^a+(a/2)Delta^a` and `D^- = D^a-(a/2)Delta^a`, the average
   density is exactly

   `F(g,D^a g,phi,D^a phi)+(a^2/4) B_g(Delta^a(g,phi),Delta^a(g,phi))`.

   The mixed terms cancel. The second differences of smooth fields and
   test variations are uniformly bounded by their `C^2` norms. Both this
   correction and its first variation are therefore `O(a^2)`. It remains
   large for lattice-scale alternating fields, as required by the explicit
   check above. The quadratic identity is Lean-proved for an arbitrary
   bilinear form, including the indefinite gravity form.
4. A composite midpoint rule on a unit coordinate box has error at most
   `(a^2/24) sum_rho ||partial_rho^2 f||infinity`, by applying the
   one-dimensional rule successively. The continuum density and its first
   variation have bounded `C^2` norms under the stated `C^3` hypotheses.
   Periodic midpoint grids obey the same bound. Combining quadrature and
   stencil errors gives

\[
 |S_a(I_ag,I_a\phi)-S(g,\phi)|\le C a^2,
\]

\[
 \boxed{|\delta S_a(I_ag,I_a\phi)[I_ah,I_a\psi]
           -\delta S(g,\phi)[h,\psi]|
 \le C a^2\|(h,\psi)\|_{C^3}.} \tag{12}
\]

Here `I_a` is literal sampling. The proof applies to the actual rational
metric action (6), not to an action whose continuum derivatives were
postulated. Smoothness of the jet function follows from its displayed
finite algebra; compactness supplies finite constants independent of `a`.

There are also exact finite integration-by-parts identities. A periodic
shift is a permutation, so changing its summation index gives

\[
 \sum_x A_xD^+_\rho h_x=-\sum_x(D^-_\rho A)_x h_x,\qquad
 \sum_x A_xD^-_\rho h_x=-\sum_x(D^+_\rho A)_x h_x.
\]

If a componentwise variation of (6) is written as
`a^4 sum_x [A_x h_x + (1/2) sum_rho (Bplus_rho,x Dplus_rho h_x
+ Bminus_rho,x Dminus_rho h_x)]`, its exact Euler derivative is
`A-(1/2)sum_rho(Dminus_rho Bplus_rho+Dplus_rho Bminus_rho)`.
This works for each of the ten metric components and for the scalar.
The Lean module proves both one-sided adjoint identities, as well as
the centered identity and its finite stationarity theorem. The same
point-supported variation argument gives the displayed final residual.
Interior variations on a box have the same identity without boundary
contributions once the stencil fits inside their support neighborhood.

## 6. What is sufficient to pass stationary lattice fields to Einstein fields

Let `a_n -> 0`. Suppose the stationary lattice fields are samples of
interpolants `(g_n,phi_n)` that satisfy the uniform bounds in section 5
and converge in `C^1` to a smooth pair `(g,phi)`. Suppose their discrete
first variations vanish, or tend to zero for every fixed smooth test pair.

The continuum first variation is continuous in these `C^1` fields, since
its unintegrated expression uses only first field derivatives. For a
fixed test pair, (12) gives the explicit bound

\[
 |\delta S(g,\phi)[h,\psi]|
 \le C\|(h,\psi)\|_{C^3}
 [a_n^2+\|(g_n-g,\phi_n-\phi)\|_{C^1}]
 +|\delta S_{a_n}(I_{a_n}g_n,I_{a_n}\phi_n)[I_{a_n}h,I_{a_n}\psi]|.
\tag{13}
\]

Each term tends to zero. Thus the limit is stationary, and (9)–(11)
give Einstein gravity with scalar matter. The Lean module checks the
quantitative variation transfer and the limiting argument with these
analytic and convergence inputs explicit.

This theorem is **conditional on an appropriate convergent sequence**.
It does not prove such a sequence exists for given physical data, exclude
spurious lattice solutions, establish stability of an evolution scheme,
or control the oscillatory Lorentzian quantum path integral. Those issues
cannot be supplied by the first-variation estimate alone. In particular,
the existence/compactness hypothesis does not follow from the earlier
weak-chart chiral-measure locality proof.

## 7. Independent checks on nontrivial metrics

The executable differentiates the inverse metric, volume factor, connection,
and scalar density directly. An independent routine computes Ricci and
Einstein tensors from first and second metric jets and evaluates (9)–(10).
It checks the boundary identity (7) on 24 generic metric jets involving
all four coordinate directions.

The refinement tests sample three one-coordinate-dependent fields with
unit spatial volume; they do not claim to solve a four-dimensional initial
value problem. Each test includes all ten symmetric metric variation
directions and an independent scalar variation.

* A smooth metric with off-diagonal frame entries and a nonconstant scalar
  tests nonzero first variations and their source signs.
* The conformal de Sitter metric
  `g=(t-2)^(-2) diag(-1,1,1,1)`, for `0<=t<=1`, has `Lambda=3` and
  zero matter. The independently computed `G+3g` vanishes.
* The massless-scalar cosmology
  `g=diag(-1,(1+t)^(2/3),(1+t)^(2/3),(1+t)^(2/3))` and
  `phi=sqrt(2/3) log(1+t)` has `kappa=1`, `Lambda=0`. Its
  `G-T` and scalar equation both vanish, testing genuine backreaction.

The metric checkerboard has zero action and every first variation in the
preliminary discretization. The final action and its amplitude derivative
are both nonzero and agree with their explicit rational formulas. An
independent scalar Fourier test verifies removal of its extra zero mode.

Test variations use a polynomial bump whose value and first three
derivatives vanish at the two time endpoints. A finite difference of the
full action supplies an additional check of the analytic discrete
variation. Meshes from 16 to 256 points give approximately fourfold
reductions of the first-variation error per halving of spacing, as (12)
predicts. The report records every residual, the free-overlap checks, and
source hashes. Numerical convergence supports the implementation; the
all-spacing consistency proof is section 5.

In the final run the tensor/action variation identity has maximum error
`5.00e-16`, and the independent finite difference of the discrete action
has error `1.69e-12`. At 256 time points the largest first-variation errors
are `7.64e-5` for the general metric, `1.28e-5` for de Sitter, and `2.67e-7`
for the backreacting scalar solution. The final refinement ratios are
`3.9990`, `4.0003`, and `4.0005`. The checkerboard amplitude derivative
changes from exactly zero to `77.1854448` at the tested spacing and
amplitude; it is not inferred from a nonzero action value alone.

```sh
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/continuum_einstein_audit.py
lake env lean UnifiedTheory/Audit/KFCausalContinuumEinstein.lean
lake build
```

Lean/Lake jobs in this repository must be run sequentially.

The full build passes with 8,928 jobs. All nineteen new theorem audits use
only the standard logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`, or a subset); there are no unfinished proofs in the new module.

## 8. Relation to the existing gravity claims and next physical obligation

`KFCausalCSpecBDGContinuumLimit` assembles named asymptotic inputs. The
new action-value counterexample shows why recovering a BDG mean would
still require a first-variation or a suitable stationary-measure limit.
`KFCausalCSpecEinsteinEquations` proves a null-equilibrium/conservation
implication. Here the source and nonlinear Einstein tensor instead arise
by varying the specific action (6). The equilibrium condition is not
retroactively proved for the old growth model.

Some older file headers describe a "complete Lovelock" derivation. The
actual theorem `LovelockComplete.complete_lovelock_4d` is a conjunction of
curvature contractions, vanishing generalized-delta tensors, an epsilon
identity, and parity. It does not classify an arbitrary natural tensor
or prove that the microscopic dynamics lie in the second-order Lovelock
class. The new bridge does not use that header as an extra theorem.

The immediate shared-model obligation is to couple the actual chiral
regulator to metric/spin-connection variables while retaining its gap,
Ward identities, locality, and a controlled continuum limit. An external
gravity overlap construction exists in
[Hayakawa, So and Suzuki](https://arxiv.org/abs/hep-lat/0604003); it supplies
a relevant construction to examine, not a theorem already implemented
in this repository. It does not select gravitational dynamics.

The continuum metric variation in section 4 is standard Einstein–Hilbert
calculus; see the field-equation discussion in
[Carroll's GR lectures, section 4](https://arxiv.org/html/gr-qc/9712019v1). The contribution
here is an explicit discretized candidate, its first-variation error
argument, the connection to the existing free overlap operator, and
independent checks. No new derivation of Einstein gravity from locality
alone is claimed.

Physical closure still requires the microscopic selection of geometry and
the action, existence and control of its relevant limits, a common
interacting chiral quantum theory, and determined/tested parameters.
Accordingly this is a constructive continuum/GR benchmark, not a
completed derivation of spacetime and gravity from the original microscopic law.
