# A quantitative square-grid reconstruction theorem

Date: 2026-11-09

We prove an explicit deterministic discrete-to-continuum result for U(m) links
on a square. The key estimate is dimension independent in operator norm:

\[
 \boxed{\|W_h(\gamma)-W_A(\gamma)\|
 \le \ell_y(\gamma)\{\varepsilon_h+(M^2+L)h\}.}
 \tag{1}
\]

Here the rescaled plaquette discrepancy is at most epsilon_h, the proposed
limiting curvature is bounded by M and Lipschitz with constant L, and ell_y
is total vertical path length, including backtracking. The continuum
connection is constructed explicitly below. The comparison uses the same
geometric grid path on both sides; it is uniform over paths of bounded length.

This is a complete analytic proof in a restricted setting, with Lean-checked
algebraic and analytic ingredients. It is not a fully formalized proof of (1).
The precise boundary is recorded in section 7. The construction uses standard
tree-gauge, product-stability, and compactness methods. No claim of mathematical
novelty is made. It does not construct a quantum field theory or prove a mass gap.

## 1. Conventions and exact reconstruction

Let h=1/n, n a positive integer, and take vertices (ih,jh), 0<=i,j<=n.
H_ij is a positive horizontal link and V_ij a positive vertical link, both in
U(m). A link maps the head frame to the tail frame. Thus path products are
written in traversal order and reversed links are inverses. A vertex gauge g
acts by

\[
 H^g_{ij}=g_{ij}H_{ij}g_{i+1,j}^{-1},\qquad
 V^g_{ij}=g_{ij}V_{ij}g_{i,j+1}^{-1}.
\]

The counterclockwise plaquette, based at its lower-left corner, is

\[
 P_{ij}=H_{ij}V_{i+1,j}H_{i,j+1}^{-1}V_{ij}^{-1}.
\]

For a path from a to b, W^g=g_a W g_b^{-1}; for a loop it is conjugation.
Accordingly operator norm comparisons in a common frame and normalized
traces of closed loops have the expected gauge interpretation.

Choose the spanning tree consisting of all horizontal edges and the vertical
edges on x=0. There is a unique gauge with g_00=I making these links I.
Explicitly let

\[
 B_j=V_{0,0}\cdots V_{0,j-1},\qquad
 R_{ij}=H_{0,j}\cdots H_{i-1,j},\qquad g_{ij}=B_jR_{ij}.
\]

The recurrences g_(i+1,j)=g_ij H_ij and g_(0,j+1)=g_0j V_0j prove the
assertion, and recursively determine g uniquely. All remaining quantities
in the theorem are in this rooted axial gauge. Write its plaquettes as Ptilde.
Then

\[
 \widetilde P_{ij}=\widetilde V_{i+1,j}\widetilde V_{ij}^{-1},
 \qquad
 \widetilde V_{ij}=\widetilde P_{i-1,j}\cdots\widetilde P_{0,j}.
 \tag{2}
\]

Equation (2) is exact for any group. Its order cannot be reversed for
noncommuting matrices. On this square, the axial plaquettes determine the
rooted-gauge link field completely. Periodic boundaries require additional
holonomy data and are not covered.

## 2. Exact stability before taking any limit

For unitary factors A_k and B_k, replacing factors one at a time gives

\[
 \|A_{r-1}\cdots A_0-B_{r-1}\cdots B_0\|
 \le\sum_{k<r}\|A_k-B_k\|.
 \tag{3}
\]

All prefactors and postfactors have operator norm one. This explains why
there is no dimension factor or exponential growth in path length.

For two axial link fields whose corresponding plaquettes differ by at most
delta, (2)-(3) give ||V_ij-V'_ij||<=i delta<=delta/h. Also
||U^{-1}-V^{-1}||=||U-V|| for unitaries. If a path has N_y vertical edges,
including reverse traversals, its horizontal factors agree exactly. Applying
(3) once more yields

\[
 \boxed{\|W_h(\gamma)-W'_h(\gamma)\|
 \le N_y n\delta=\ell_y(\gamma)\,\delta/h^2.}
 \tag{4}
\]

The same bound holds for normalized Wilson traces because
|tr(X)|/m<=||X||. It is valid for self-intersecting paths and repeated edges.

## 3. Main discrete-to-continuum theorem

Let F:[0,1]^2 -> u(m) be anti-Hermitian and satisfy

\[
 \|F(x,y)\|\le M,\qquad
 \|F(x,y)-F(x',y')\|\le L(|x-x'|+|y-y'|),\quad M,L\ge0.
 \tag{5}
\]

Assume the actual rooted axial plaquettes satisfy

\[
 \|\widetilde P_{ij}-\exp(h^2F(ih,jh))\|\le h^2\varepsilon_h,
 \qquad \varepsilon_h\ge0.
 \tag{6}
\]

This is a substantive hypothesis about the rescaled curvature, not a
consequence of plaquettes merely approaching I. It is checked after the
rooted tree gauge: norms of curvature alone do not specify its matrix
direction or its variation between points. No logarithm branch is needed
in (6). Changing the initial frame conjugates both F and all rooted data.

Construct

\[
 A=A_y\,dy,\qquad A_y(x,y)=\int_0^x F(s,y)\,ds,\qquad A_x=0.
 \tag{7}
\]

This is an anti-Hermitian connection for D=d+A. Its curvature is
dA+A wedge A=F dx wedge dy: A wedge A=0 and partial_x A_y=F.
For Lipschitz F this identity holds distributionally (and partial_x exists
classically). If F is smooth on a neighborhood of the square, A is smooth.

In the head-to-tail convention a positive vertical segment has transport
T'(t)=T(t) A_y(x,y+t), T(0)=I. Horizontal transport is I. Both coefficient
and its transports are uniquely determined by F and the axial normalization.

**Theorem.** Under (5)-(6), every grid path gamma satisfies (1). Therefore
if epsilon_h -> 0 and h -> 0, the lattice transports in the rooted gauge
converge to those of the constructed connection, uniformly over grid paths
with bounded total vertical length. For a fixed axis-aligned polygon present
in all sufficiently fine meshes, this is convergence to its fixed continuum
transport. Arbitrary moving paths are compared to their own continuum
transports; no convergence to an unspecified limiting curve is asserted.

**Proof.** Put x=ih, y=jh and define the ideal vertical link

\[
 Q_i=\exp(h^2F((i-1)h,y))\cdots\exp(h^2F(0,y)).
\]

From (2), (3), and (6), ||Vtilde_ij-Q_i||<=i h^2 epsilon_h<=h epsilon_h.
For an anti-Hermitian X and t>=0, unitarity and integration give

\[
 \|e^{tX}-I\|\le t\|X\|,\qquad
 \|e^{tX}-I-tX\|\le\tfrac12t^2\|X\|^2.
 \tag{8}
\]

Indeed, integrate X e^(sX) for the first bound and X(e^(sX)-I) for the second.
For contractions a_k, increments t_k with ||a_k-I||<=d and
||a_k-I-t_k||<=r, induction gives the noncommutative bound

\[
 \|a_{i-1}\cdots a_0-I-\sum_{k<i}t_k\|
 \le ir+\tfrac12 i(i-1)d^2.
 \tag{9}
\]

For completeness, if U_i=a_(i-1)...a_0 and S_i=sum_(k<i)t_k, the exact
remainder recursion is

\[
 U_{i+1}-I-S_{i+1}
 =(U_i-I-S_i)+(a_i-I-t_i)+(a_i-I)(U_i-I).
\]

Since ||U_i-I||<=id by (3), induction proves (9). Apply it with
t_k=h^2 F(kh,y), d=h^2 M, r=h^4 M^2/2 to obtain

\[
 \|Q_i-I-h^2\sum_{k<i}F(kh,y)\|
 \le\tfrac12 i^2h^4M^2\le\tfrac12 h^2M^2.
 \tag{10}
\]

The left Riemann-sum estimate from (5), retaining its half constant, is

\[
 \|h\sum_{k<i}F(kh,y)-A_y(ih,y)\|
 \le iLh^2/2\le Lh/2.
 \tag{11}
\]

For the continuum vertical edge, let B(t)=A_y(x,y+t).
Then ||B(t)||<=M and ||B(t)-B(0)||<=Lt. Unitarity gives
||T(t)-I||<=Mt, so integration of
T(t)B(t)-B(0)=(T(t)-I)B(t)+(B(t)-B(0)) yields

\[
 \|T(h)-I-hA_y(x,y)\|\le\tfrac12(M^2+L)h^2.
 \tag{12}
\]

Combine (10)-(12) and the measured-plaquette error to get

\[
 \|\widetilde V_{ij}-T(h)\|
 \le h\varepsilon_h+(M^2+L)h^2.
 \tag{13}
\]

Inverse links have the same error; horizontal links have zero error. Sum
(13) over N_y vertical traversals using (3). This proves (1). QED.

The argument does not replace ordered exponentials by commuting ones.
The M^2 h term explicitly pays for ordering and the second-order remainder.

## 4. An existence/compactness corollary

The preceding theorem identifies a limit. The following conditions ensure
that at least one such limit exists without specifying it in advance.

Suppose h_r -> 0 and there are anti-Hermitian values f^(r)_ij with

\[
 \widetilde P^{(r)}_{ij}=\exp(h_r^2 f^{(r)}_{ij}),\quad
 \|f^{(r)}_{ij}\|\le M,
\]

and neighboring values in either grid direction differ by at most L h_r.
These conditions concern the logarithmic curvature in the rooted frame.
When h_r^2 M<pi, the bounded lift is the principal anti-Hermitian logarithm
divided by h_r^2. The existence of these lifts and their regularity are
assumptions, not supplied by the compactness conclusion.

Extend the last row and column by repetition and bilinearly interpolate the
values on the full square. Convexity preserves anti-Hermiticity and the
M bound. Within a cell each directional derivative is a convex combination
of neighboring differences divided by h_r; hence the interpolants are
L-Lipschitz for the l1 metric, including across cell boundaries.

Finite-dimensional Arzela-Ascoli supplies a uniformly convergent subsequence
with anti-Hermitian, M-bounded, L-Lipschitz limit F. For anti-Hermitian X,Y,

\[
 \|e^X-e^Y\|\le\|X-Y\|.
\]

To see this, differentiate e^((1-t)X)e^(tY); its derivative is
e^((1-t)X)(Y-X)e^(tY), and both outer factors are unitary.
Thus (6) holds with epsilon_r the uniform interpolation error. Theorem (1)
gives subsequential convergence of transports to (7).

The resulting connection is Lipschitz. A smooth conclusion requires more:
for example, smooth interpolants with uniform bounds on every derivative
on a fixed neighborhood yield a smooth subsequential limit by diagonal
Arzela-Ascoli. Uniqueness of subsequential F or a direct Cauchy estimate
would be needed to upgrade subsequential convergence to convergence of the
entire original sequence.

## 5. Two sharp limitations

**Plaquettes close to I do not imply convergence to a flat field.** In U(1)
take H_ij=1 and V_ij=exp(i c i h^2) for a fixed real c. Every plaquette is
exp(i c h^2), so each tends to I at rate O(h^2). Nevertheless the boundary
Wilson loop of the whole unit square is exp(i c), independent of h. Choose
c=1, for example, so it is not I. The reconstructed connection is
A=i c x dy with curvature i c dx wedge dy.

Consequently delta=o(h^2) in (4) is sufficient for convergence to a specified
reference and cannot in general be relaxed to delta=O(h^2). This is a
worst-case, coherent-error statement. Cancellation can make particular
noise models better behaved; no stochastic improvement is claimed.

**A curvature bound alone does not imply a smooth limit.** Let
f(x,y)=1_(x>1/2), set A=i max(x-1/2,0)dy, and take its exact U(1) edge
transports. All cell fluxes have magnitude at most h^2, and the rescaled
curvature is bounded by 1, but its limit has a jump at x=1/2. It cannot be
the curvature of a smooth connection. U(1) gauge transformations preserve
curvature, so changing gauge cannot turn this specific limit into a smooth
one. The example does not exclude weaker compactness conclusions.

## 6. What this adds to the project, and relation to existing work

The repository already contains finite gauge models, tree gauges on periodic
lattices, and continuum research modules. This note supplies a self-contained
deterministic bridge with an explicit observable error and a sharp coherent
plaquette-noise scale. In particular, a candidate refinement law can be tested
against (6), rather than against the much weaker claim that its small loops
approach I. For fixed physical path length, controlled curvature consistency
is the quantity that matters.

This is an established subject. Relevant primary sources checked here are:

- P. Hernandez and R. Sundrum, *Interpolation of Non-abelian Lattice Gauge
  Fields*, Nucl. Phys. B 472 (1996), 334-348,
  [arXiv:hep-lat/9602017](https://arxiv.org/abs/hep-lat/9602017). Their work
  already treats nonabelian lattice-to-continuum interpolation and gauge
  covariance. This rules out presenting the broad construction as new.
- J. Dimock, *Covariant Axial Gauge*,
  [arXiv:1410.2798](https://arxiv.org/abs/1410.2798). This develops lattice
  axial gauge with attention to lattice symmetries and block averaging.
  Our rooted gauge singles out axes and is not asserted to preserve those
  symmetries.

This targeted literature check does not establish that the exact estimate
(1), or its formalization, is new. A publishable contribution would require
a more comprehensive comparison and a substantive extension, such as
regularity conditions derived from a specified refinement law or controlled
reconstruction on irregular complexes. Those are future problems, not
conclusions of this note.

## 7. Verification and exact formalization boundary

[GaugeTransportStability.lean](UnifiedTheory/LayerA/GaugeTransportStability.lean)
formalizes the following ingredients directly:

- Exact tree gauge, path and plaquette gauge covariance, and ordered axial
  reconstruction for arbitrary groups.
- Contractive product bounds, perturbation stability, and the second-order
  remainder (9) for a normed ring.
- Plaquette-to-link stability, inverse-link isometry, and the complete
  plaquette-to-word bound (4) for unitary elements of a C*-algebra. The word
  theorem permits arbitrary indices and both orientations; composable paths
  are a special case, with horizontal identity links omitted.
- Stability of the actual Bochner integral F -> integral_0^x F and convergence
  at arbitrary mesh-dependent points under a uniform error bound.

The matrix exponential inequalities (8), the ODE existence and remainder
(12), finite-grid/path assembly into (1), the curvature identity, and the
Arzela-Ascoli corollary are proved analytically above, not assembled in Lean.
The formal integral theorem uses Mathlib's Bochner interval integral and
requires integrability explicitly; it does not assume the desired conclusion.

The reproducible test script
[gauge_discrete_continuum_audit.py](scripts/gauge_discrete_continuum_audit.py)
checks noncommuting SU(2) reconstruction, arbitrary vertex gauges, path
products, the quantitative bounds, and the persistent-flux counterexample.
Its floating-point calculations are regression checks, not proofs.
The audit output records measured errors and analytic bounds separately.

Reproduction commands (from the repository root):

```sh
lake build UnifiedTheory.LayerA.GaugeTransportStability
lake env lean scripts/CheckGaugeTransportStability.lean
python3 scripts/gauge_discrete_continuum_audit.py
```

No full-repository build is implied by these targeted checks.

### Completed verification

- The targeted Lean build passed. All 21 theorem declarations were audited
  with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`
  occur. The output is retained in
  [gauge_transport_axioms.txt](data/gauge_transport_axioms.txt).
- 47 exact rational quaternion identities passed, including arbitrary vertex
  gauge changes, plaquette conjugation, and open-path covariance.
- 15 noncommutative product-remainder cases, 260 path comparisons across ten
  SU(2) meshes/noise configurations, and five persistent-flux cases passed.
- For the noiseless polynomial test, the unit-square boundary error decreased
  from 0.04154672 at n=4 to 0.00262849 at n=64. The analytic bound at n=64
  is 0.0625. These are measured errors against the midpoint reference;
  its separately bounded error is 0.000244140625 for that boundary.

The test curvature, written as a pure quaternion, is
F(x,y)=(0; 0.30+0.20x, 0.15+0.25y, 0.20+0.10xy). Its norm is at most
sqrt(0.5), and both directional derivatives have norm less than 1, so the
chosen M=L=1 bounds are conservative. The test also deliberately reverses
the plaquette product order and confirms that the answer changes.

The reference integrates each vertical edge with 32 midpoint exponential
steps. The unitary ODE perturbation bound and the Lipschitz coefficient give
reference error at most L h^2/(4*32) per edge, by integrating the distance
to each subinterval's midpoint. Floating-point rounding is not formally
certified. Exact identities, analytic estimates, formal proofs, and numerical
checks therefore remain explicitly distinct.
