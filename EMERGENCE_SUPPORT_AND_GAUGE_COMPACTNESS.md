# The emergence gap: support and compactness modulo time coordinates

Date: 2026-09-10

The existing harmonic Born law cannot supply a nondegenerate spacetime
through a reconstruction preserving its causal order and volume. This
follows from its earlier analytic almost-sure chain-collapse theorem.
Here we prove a stronger consequence: no absolutely continuous change of
the infinite-history measure can repair that obstruction. We also derive
an asymptotic finite-stage probability bound and the resulting minimum
relative-entropy cost of selecting macroscopic incomparability.

There is a separate constructive result for the classical metric action
in [the continuum bridge](CONTINUUM_EINSTEIN_BRIDGE.md). Exact stationary
lapse metrics can have divergent coordinate derivatives, even while the
metric and its inverse remain bounded. An explicit proper-time coordinate
turns this whole family into Minkowski geometry. Thus compactness closes
for this lapse-only family after quotienting by coordinate transformations.
This does not prove compactness for physical gravitational degrees of freedom.

Neither result derives a new microscopic action, selects four-dimensional
geometry, or constructs an interacting quantum continuum. The overarching
requirement suggested by the two results is **a refinement-consistent law
on physical geometries, with tightness after coordinate equivalence**.
That is a research criterion, not a principle proved to select a unique theory.

## 1. Faithful volume and causality contradict chain collapse

Let P be the canonical positive-radial harmonic Born trajectory measure.
The [earlier analytic proof](HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md)
establishes that, P-almost surely, all births after a finite random time
are timid: each new event lies above every older event. Therefore the
number I_N of unordered incomparable pairs is eventually constant and

\[
 \frac{I_N}{N^2}\longrightarrow0,
 \qquad r_N=1-\frac{I_N}{\binom N2}\longrightarrow1.
 \tag{1}
\]

The stochastic assembly of that theorem is analytic, with existing Lean
ingredients. We do not silently replace it by a fully formalized theorem.

Consider a fixed finite-volume region of a smooth nondegenerate Lorentzian
spacetime containing two open positive-volume sets U,V whose points are
pairwise spacelike separated. Such sets exist, for example, inside a small
causally convex neighborhood in a globally hyperbolic spacetime of dimension
at least two. Global causal pathologies are excluded from this premise.
Suppose a reconstruction preserves causal comparisons and samples volume:

\[
 \frac{N_U}{N}\to p_U>0,\qquad \frac{N_V}{N}\to p_V>0.
 \tag{2}
\]

Each U–V pair must be incomparable. Since U and V are disjoint, identifying
a cross pair with an unordered pair is injective, so

\[
 I_N\ge N_U N_V,\qquad
 \liminf_N\frac{I_N}{\binom N2}\ge2p_U p_V>0.
 \tag{3}
\]

This contradicts (1). The argument needs neither a fitted dimension
statistic nor an assumed exact sprinkling distribution. Independent volume
sampling would supply (2), but the obstruction holds for any reconstruction
that supplies those positive limiting fractions and preserves the grown order.
It excludes that interpretation of this microscopic law; it does not
exclude other laws, additional degrees of freedom, or a different causal readout.

For measure statements below, G is any **measurable** event of such faithful
reconstructions, or the measurable necessary event of positive limiting
incomparability. Let C be the measurable eventual-timid event. Then
G is contained in C-complement and P(G)=0.

## 2. An infinite-history density cannot repair the support

Let Q be a probability law on the same history space.

**Support theorem.** If Q is absolutely continuous with respect to P,
then Q(G)=0. If instead Q(G)=1, then Q and P are mutually singular.

Proof: absolute continuity transfers every P-null event to a Q-null event.
For the second statement G carries all Q mass and no P mass, which is the
definition of mutual singularity. In particular, for any measurable
nonnegative integrable w with 0<Z=integral w dP<infinity,

\[
 dQ=Z^{-1}w\,dP\quad\Longrightarrow\quad Q(G)=0.
 \tag{4}
\]

This includes an ordinary normalized Gibbs density on complete histories.
Making w very large on a null event does not give that event positive mass.

There is an essential scope distinction: finite-stage measures Q_N may
all have densities relative to P_N while their consistent infinite-history
extension is singular to P. Thus (4) does **not** exclude finite-cutoff
actions whose infinite limit is singular. It requires that singular change
if the limiting law is to give G full probability.

For a concrete consistency example, let P be independent fair bits and Q
independent bits with probability 3/4 of one. Every finite word has positive
mass under both laws, and all Q_N marginals agree. Their almost-sure limiting
frequencies differ, so their infinite laws are singular. The finite density
is

\[
 R_N=(3/2)^{K_N}(1/2)^{N-K_N}.
\]

Under P, N^{-1}log R_N tends to (1/2)log(3/4)<0, so R_N tends to zero
P-almost surely despite E_P R_N=1. The lost uniform integrability is
precisely why no normalized terminal density is obtained. This example
illustrates a legitimate singular limit; it is not a spacetime selector.

## 3. A quantitative cost for changing the finite-stage statistics

The earlier harmonic-law estimates give constants 0<c<=1 and A>0, and a
finite threshold n_*, uniformly over every parent history:

- A timid birth has conditional probability at least c.
- With a unique maximal event, the probability of a non-timid birth is
  at most A/n^2 at rank n.

One may take the constants c=1/(64 C^2), A=32 M^2 from the earlier raw
amplitude bounds, after increasing n_*. They are conservative asymptotic
constants; no small-rank numerical rate is inferred from them.

Let q_n be the probability that the rank-n parent has more than one
maximal event. A child has a unique maximum exactly when the birth was
timid: otherwise both the new event and a maximal nonancestor remain
maximal. Conditioning on the parent's status gives

\[
 q_{n+1}\le(1-c)q_n+A/n^2.
 \tag{5}
\]

Choose an integer n_0>=max(n_*,4/c,1) and
B>=max(n_0^2,2A/c). Then

\[
 q_n\le B/n^2\quad(n\ge n_0).
 \tag{6}
\]

Proof by induction: q_{n_0}<=1 supplies the base. For the step,

\[
 (1-c)B/n^2+A/n^2
 \le(1-c/2)B/n^2\le B/(n+1)^2.
\]

The last inequality uses
1-(n/(n+1))^2<=2/n<=c/2. The Lean theorem
`inverse_square_barrier` checks this algebra directly.

If D_n is the number of incomparable pairs created at birth n to n+1,
then D_n=0 on timid births and 0<=D_n<=n otherwise. Hence

\[
 \mathbb E_P D_n\le n q_{n+1}\le B/n,
 \qquad
 \mathbb E_P I_N\le\binom{n_0}{2}
       +B\sum_{n=n_0}^{N-1}\frac1n
       =O(1+\log N).
 \tag{7}
\]

There is no contradiction between almost-sure eventual constancy and
unbounded expected counts: the random finite prefix need not have finite
expected total incomparability. We assert an upper bound, not a matching
asymptotic or divergence of that expectation.

For fixed delta>0 define

\[
 G_N=\{I_N\ge\delta\binom N2\},\qquad p_N=P_N(G_N).
\]

Markov's inequality gives, for a constant C_delta and sufficiently large N,

\[
 p_N\le C_\delta\frac{1+\log N}{N^2}.
 \tag{8}
\]

This is a necessary-observable bound. G_N includes many orders that have
no manifold interpretation. Giving G_N large probability is insufficient
to select dimension or any Einstein geometry.

Now suppose a candidate Q_N gives G_N probability q_N>=q_0>0. When
0<p_N<1, partitioning the relative entropy into the two conditional laws
gives the exact identity

\[
\begin{aligned}
D(Q_N\Vert P_N)
={}&d(q_N\Vert p_N)
 +q_N D(Q_N(\cdot|G_N)\Vert P_N(\cdot|G_N))\\
 &+(1-q_N)D(Q_N(\cdot|G_N^c)\Vert P_N(\cdot|G_N^c)),
\end{aligned}
\tag{9}
\]

with endpoint conventions for q_N=0 or 1. Nonnegativity of conditional
relative entropy follows from log x<=x-1. Binary entropy is at most log 2,
so

\[
\begin{aligned}
 D(Q_N\Vert P_N)&\ge q_N\log(1/p_N)-\log2\\
 &\ge q_0[2\log N-\log(1+\log N)-\log C_\delta]-\log2
 \quad\text{for sufficiently large }N.
\end{aligned}
\tag{10}
\]

If p_N=0 and q_N>0 the relative entropy is infinite instead. Bound (10)
forces divergent **total** relative entropy. It does not imply positive
entropy per event, an extensive action cost, or a unique replacement law.

For fixed event probability q in (0,1), the smallest relative entropy is
attained by leaving both conditional distributions unchanged:

\[
 \frac{dQ_N^*}{dP_N}=
 \begin{cases}
 q/p_N,&G_N,\\
 (1-q)/(1-p_N),&G_N^c.
 \end{cases}
 \tag{11}
\]

Normalization, event mass, and (9) prove this minimization. The required
ratio of the two weights is

\[
 \frac{w_G}{w_{G^c}}=\frac{q(1-p_N)}{(1-q)p_N}.
 \tag{12}
\]

Using (8), its logarithm must grow at least as
2 log N-log(1+log N)+O(1). This is a lower bound, not an asymptotic equality.
Choosing (11) separately at each N generally fails projective consistency.
A physical construction still has to supply compatible birth transitions,
its causal constraints, and geometric observables beyond I_N.

## 4. An exact stationary family with no coordinate derivative bound

Use the **final averaged one-sided action** from the continuum bridge,
with zero cosmological constant and zero scalar field:

\[
 S_a(g)=\frac{a^4}{4\kappa}\sum_x\sqrt{-\det g(x)}
     [Q(g,D^+g)+Q(g,D^-g)],\qquad \kappa>0.
 \tag{13}
\]

Here Q=g^{mu nu}(Gamma^rho_{mu sigma}Gamma^sigma_{nu rho}
-Gamma^rho_{mu nu}Gamma^sigma_{rho sigma}), exactly as in the bridge.
Spatial lattice directions are periodic. Time may be periodic for the
finite audit or may use fixed boundary data and interior variations.
The periodic-time audit is a stencil identity, not a claim that physical
spacetime has compact timelike circles.

Let L depend only on time and be positive at every site, and put

\[
 g=\operatorname{diag}(-L^2,1,1,1).
 \tag{14}
\]

For either one-sided stencil, the only background metric derivative is
z=D_0 g_{00}. The only nonzero connection component is

\[
 \Gamma^0_{00}=A=\tfrac12 g^{00}z.
\]

The two products in Q cancel, so Q=0. Vanishing action alone would not
establish stationarity. Vary all ten independent metric components h
and all forty first-derivative components Dh. Direct differentiation,
including the inverse-metric variation, gives

\[
 \delta Q=-A g^{00}\sum_{i=1}^3 D_i h_{0i}.
 \tag{15}
\]

For clarity, the two connection variations that survive are

\[
 \delta\Gamma^0_{ii}=g^{00}D_i h_{0i}
                 -\tfrac12g^{00}D_0h_{ii},\qquad
 \delta\Gamma^i_{0i}=\tfrac12D_0h_{ii}.
\]

Their time derivatives cancel in delta Q; terms from delta g^{-1}
cancel as well. Since Q=0, the volume variation contributes nothing.
The coefficient -L A g^{00}/(2 kappa) in the first variation of each
one-sided density depends only on time. Summing the remaining spatial
differences over a periodic slice is exactly zero for arbitrary h.
Thus (14) is stationary under **every** lattice metric variation, separately
for both actions and hence for their average. The scalar variation is
zero at phi=0 for the bridge's quadratic/quartic potential.

This is different from the earlier conformal spatial checkerboard,
whose nonzero variation the improved action correctly detects. Equation
(15) is an exact residual family associated with time reparametrization;
it does not assert that (13) is invariant under arbitrary finite lattice
diffeomorphisms.

Fix 0<c<1 and even N with a=1/N. The smooth lapse

\[
 L_N(t)=1+c\cos(\pi Nt)
 \tag{16}
\]

has samples 1+c(-1)^j at t=j/N. The metric and inverse are bounded
uniformly because 1-c<=L_N<=1+c. But adjacent g_00 samples differ by
4c, so every differentiable interpolant matching those samples satisfies

\[
 \|\partial_t g_{00}\|_\infty\ge4cN.
 \tag{17}
\]

Consequently stationarity plus bounded nondegeneracy cannot supply the
uniform coordinate C^3 assumption of the earlier general limit theorem.
This is a counterexample to that compactness inference in fixed coordinates.

## 5. Proper time closes this particular compactness problem

Define on [0,1]

\[
 \tau_N(t)=t+\frac{c}{\pi N}\sin(\pi Nt).
 \tag{18}
\]

Then tau'_N=L_N>0, tau_N(0)=0, tau_N(1)=1. It is a smooth
diffeomorphism, and

\[
 \|\tau_N-\mathrm{id}\|_\infty\le c/(\pi N),\qquad
 g_N=-d\tau_N^2+dx^2+dy^2+dz^2.
 \tag{19}
\]

In proper-time coordinates every metric is **exactly the same Minkowski
metric**. Their curvature vanishes. Compactness modulo this coordinate
freedom therefore holds exactly, despite (17). The coordinate maps approach
the identity uniformly but their first derivatives do not; small coordinate
displacement alone does not control metric derivatives.

The result extends to any sequence of smooth time-only lapses satisfying
0<m<=L_N<=M. Put T_N=integral_0^1 L_N(t)dt and
s_N(t)=T_N^{-1}integral_0^t L_N(u)du. On the common unit interval,

\[
 g_N=-T_N^2 ds_N^2+dx^2+dy^2+dz^2.
 \tag{20}
\]

Since T_N lies in [m,M], a subsequence converges. Its representatives in
the s coordinate converge smoothly to a constant flat metric. This proves
quotient compactness for the entire bounded positive lapse-only sector,
not just the cosine example. It does not control a spatial metric carrying
physical gravitational waves, nor prove that arbitrary sample interpolants
have a unique geometry.

For general metrics, weakening convergence without controlling nonlinear
derivative products is insufficient. Huneau and Luk construct vacuum
families with nonvacuum weak limits in a symmetry-restricted Einstein
problem, with an effective null-dust source. That is an independent reason
to retain possible effective stress when developing a weaker limit theorem.
[Huneau–Luk, arXiv:1706.09501](https://arxiv.org/abs/1706.09501).
Their theorem is not used to prove the flat lapse result above.

## 6. What is checked and what remains

`UnifiedTheory/Audit/KFCausalEmergenceSupport.lean` proves fifteen supporting
results: finite cross-pair counting, a limiting-density contradiction,
three absolute-continuity consequences, the inverse-square barrier,
two event-tilt identities, two periodic variation cancellations,
proper-time derivative/positivity/error bounds, the pullback algebra,
and the adjacent-sample Lipschitz lower bound. These theorems expose their
inputs; the actual harmonic trajectory collapse, entropy minimization,
full tensor variation, and manifold compactness statements are analytic.

`scripts/emergence_support_audit.py` independently checks:

- Exact symbolic variation in all ten metric and forty derivative
  components, including inverse and connection variations.
- Nontrivial local responses with vanishing integrated first variation
  on periodic 4^4, 6^4, and 8^4 lattices, for both one-sided stencils and
  arbitrary randomly generated full tensor variations.
- Proper-time normalization and the increasing necessary coordinate
  Lipschitz bound through N=128.
- Concrete spacelike cross-pair counts, an inverse-square recurrence,
  the full conditional relative-entropy identity, and projective
  consistency of the biased-coin singular-limit example.

The recurrence test uses clearly labeled synthetic constants. It does not
estimate the harmonic law's asymptotic constants. The finite lattice tests
check the analytic tensor proof rather than asserting stationarity from a
small set of directional tests. Reproducible output and source digests are
in `data/emergence_support_audit.json`.

The next construction must supply a projectively consistent microscopic
law with a justified geometric phase and enough invariant regularity to
control a continuum limit modulo coordinates. For the existing classical
action this also requires control of physical metric oscillations and
their nonlinear effective sources. A compatible interacting chiral quantum
continuum and empirical identification remain separate open obligations.
The lapse-only compactness problem is solved here; the physical emergence
gap cannot be closed by retaining the current law and its faithful-order
interpretation unchanged.
