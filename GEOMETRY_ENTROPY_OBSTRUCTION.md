# Geometry selection in v2: the regular-graph and entropy obstructions

Date: 2026-09-10

**The revised moves work, but they do not by themselves select extended
geometry.** This follow-up to [Relational Quantum Geometry v2](RELATIONAL_QUANTUM_GEOMETRY_V2.md)
establishes two stronger restrictions. An exact reference sector has a
uniform regular-graph ground state whose measured geometry is typically
an expander at large size. More generally, at fixed finite temperature,
any Hamiltonian with norm O(N) on the current carrier fails to concentrate
on a geometric class with only exp(O(N)) distinct unlabelled shapes.

The second statement includes noncommuting quantum interactions. Its
shape-count assumption and equilibrium assumption are essential: this
is not a theorem excluding every manifold approximation, every ground
state, or a nonequilibrium cosmological state. It does rule out relying
on balanced moves and fixed bounded couplings alone to thermally select
such a small geometric class from the unrestricted graph carrier.

## 1. The exchange is a known connected-graph flip

In the trivial-flux sector, the v2 move takes the path a-b-c-d to
a-c-b-d by replacing ab,cd with ac,bd, provided the four vertices are
distinct and the new edges absent. This is exactly the flip in Figure 3
of Cooper, Dyer, Greenhill and Handley. Its transition support connects
all connected regular graphs of a given allowed degree. For even degree
d>=4 and N>=8, their paper also gives a polynomial mixing bound.
Only connectedness of the transition support is needed here.
[The flip Markov chain](https://arxiv.org/pdf/1701.03856).

The normalization can be matched exactly. Let P_flip choose a starting
vertex uniformly, then a length-three simple random walk, allowing
backtracking proposals and rejecting invalid flips. On a d-regular
graph there are N d^3 equally likely proposals. Let L_S be the v2 sum
of S^2-S with unit coefficient over ordered distinct quadruples. Then

\[
 L_S=2Nd^3(I-P_{\rm flip}).
 \tag{1}
\]

Each allowed forward path supplies one proposal. The v2 ordered sum
also includes its reverse description, giving the factor two; rejected
proposals cancel from I-P. The exact six-site audit checks this
multiplicity independently against all ordered quadruples. Therefore
the classical process and the quantum reference Hamiltonian have the
same constant vector and the same transition support. Their time
evolutions are different: stochastic relaxation is not real-time
unitary evolution.

## 2. An exact nongeneric parameter slice has the wrong geometry

Fix N>=8, Delta=d=6, dbar=6, U>0, epsilon>0, rho>0, and set kappa=lambda=0.
Work in the connected, particle-empty physical Z2 sector. The hopping
and mass terms vanish there, whatever their coefficients. Every
remaining term of v2 is nonnegative:

\[
 H=\frac U2\sum_v(d_v-d)^2+\epsilon F+\rho L_S.
 \tag{2}
\]

Zero energy forces exactly d-regular graphs and trivial electric flux.
Conversely the uniform vector over all connected labelled d-regular
graphs is annihilated by every term. By (1), the zero-energy space in
this sector is one-dimensional:

\[
 |\Omega_{N,d}\rangle=\frac1{\sqrt{g^c_{N,d}}}
       \sum_{G\ {m connected},\ d\text{-regular}}|G,+,0\rangle.
 \tag{3}
\]

This is a ground state of the actual finite Hamiltonian on the specified
sector, not an assumed canonical distribution. Taking t=m0=0 additionally
makes it the unique ground state in the full connected Gauss sector:
epsilon F=0 forces all flux positive, and Gauss then forces empty matter.
The same argument applies to other fixed even d>=4 under the cited flip
theorem's size assumptions.

A graph measurement of (3) is uniform over connected regular graphs.
Friedman's theorem, in Bordenave's formulation for uniform simple graphs,
gives, for fixed d>=3 and any eta>0, with probability approaching one,

\[
 \lambda_2(A_G)\le2\sqrt{d-1}+\eta,
 \qquad
 \operatorname{gap}(dI-A_G)\ge d-2\sqrt{d-1}-\eta.
 \tag{4}
\]

The theorem itself implies connectedness with probability tending to one
(a disconnected regular graph has lambda_2=d), so conditioning on
connectedness preserves the conclusion. This is an application of an
external proved theorem, not a new proof of random-graph expansion.
[Bordenave, Theorem 1](https://arxiv.org/html/1502.04482v4).

For degree six the limiting lower bound is 6-2 sqrt(5), about 1.528.
This is the gap of the **spatial graph Laplacian**, not the gap of L_S
on configuration space. A periodic three-dimensional cubic graph with
N=L^3 instead has spatial gap 2-2 cos(2 pi/L), which tends to zero as
4 pi^2/L^2. Thus this reference ground state does not concentrate on
cubic-like large spatial geometries under this diagnostic.

The positive gap also forces rapid volume growth. If |A|<=N/2, use
the mean-zero vector 1_A-|A|/N in the spatial Rayleigh quotient. Then

\[
 |\partial_E A|\ge\operatorname{gap}(dI-A_G)|A|(1-|A|/N)
 \ge\tfrac12\operatorname{gap}(dI-A_G)|A|.
 \tag{5}
\]

At most d boundary edges meet one outside vertex. Therefore a ball with
at most N/2 sites grows by at least a factor 1+gap/(2d) in one step.
Balls exceed half the graph after O(log N) steps; two such balls
intersect, giving diameter O(log N). This contrasts with a growing
Euclidean cubic region and is not fixed by calling degree six a
three-dimensional valence.

This exact result concerns the reference slice kappa=lambda=0. It is
not an exclusion theorem for all v2 ground states or an open region
of its parameter space. A small finite-size perturbation need not stay
small relative to a gap as N grows.

## 3. Locking degree does not remove the wedge energy

Let P select connected d-regular, trivial-flux, empty-matter states,
at cap d and dbar=d. Compress the full v2 Hamiltonian to this subspace.
The degree, electric and matter terms vanish there; exchanges stay
inside it. A wedge deletion goes out of the subspace, while its balanced
diagonal remains. A magnetic triangle flip also goes out, leaving its
face projector. The exact compression is

\[
 P H^{(2)}P=\rho L_S+(3\kappa+\lambda)\,\mathcal T,
 \tag{6}
\]

where T counts triangles diagonally. A present edge e has c_e common
neighbors. There are c_e active elementary deletion moves, and
sum_e c_e=3T. Thus even sending the degree penalty high does not justify
discarding kappa and using the uniform state (3). Compression is also
not exact autonomous evolution when P H (I-P) is nonzero.

For additional information at **fixed N**, let
H0=(U/2) sum(d_v-d)^2+epsilon F on the particle-empty sector and
write H=H0+zV, with V containing the remaining interactions. The
second-order degenerate-perturbation coefficient is

\[
 -PVQ(QH_0Q)^{-1}QVP
 =-\frac{\kappa^2}{U}\sum_{e\in G}c_e^2
  -\frac{\lambda^2}{3\epsilon}\mathcal T
 \quad\hbox{on each regular graph }G.
 \tag{7}
\]

The coefficient is diagonal: two edge toggles can restore all degrees
only by restoring the same edge; two triangular flux toggles restore
trivial flux only for the same triangle. Mixed excursions do not return
to P. A deletion costs U and a flux triangle costs 3epsilon. The first
deletion amplitude is kappa c_e, so squaring gives c_e^2 here, whereas
the first-order balancing diagonal in (6) contains c_e. This distinction
is required by the operator calculation.

Equation (7) is the coefficient in an expansion around z=0. It is not
a claim of convergence at z=1 for arbitrary parameters or a uniform
large-N effective theory; an operator-norm perturbation estimate would
require a hierarchy involving ||V_N|| and the H0 gap. The audit verifies
the actual compressed and second-order matrices on K4: the diagonal is
12kappa+4lambda, and the next coefficient is
-24kappa^2/U-4lambda^2/(3epsilon).

## 4. A quantum entropy bound for arbitrary interactions

Let H act on a finite D-dimensional Hilbert space, let P be an orthogonal
projector of rank m, and set rho_beta=exp(-beta H)/Z with beta>=0.
Suppose the spectral width W=E_max-E_min is finite. **No commutation
between P and H is assumed.** Then

\[
 \operatorname{Tr}(P\rho_\beta)
 \le\frac{m e^{\beta W}}{D-m+m e^{\beta W}}
 \le\frac mD e^{\beta W}.
 \tag{8}
\]

Proof: put B=exp(-beta H), l=exp(-beta E_max), h=exp(-beta E_min).
Spectral calculus gives l I<=B<=h I. Taking traces in a basis adapted
to P yields A=Tr(PB)<=mh and C=Tr((I-P)B)>=(D-m)l.
The function A/(A+C) increases with A and decreases with C, giving
the first inequality. The second uses h>=l. This also proves sharpness:
take H=E_min on range(P) and E_max on its orthogonal complement.
The estimate depends only on rank and spectral width, not on locality,
stoquasticity, an eigenbasis aligned with graph states, or weak coupling.

For v2, the established bound ||H_N||<=K_Delta N implies

\[
 \Pr_\beta(\mathcal G_N)\le
 \frac{\operatorname{rank}P_{\mathcal G_N}}{D_N}
                 e^{2\beta K_\Delta N}.
 \tag{9}
\]

Here P_G measures graph presence in a specified class, retaining all
allowed matter and flux states. One may use the full connected Gauss
space or its particle-empty invariant sector; both contain every
connected regular graph with trivial flux.

Fix an integer d>=3 with d<=Delta and take sizes with Nd even. The
regular-graph enumeration formula and Stirling's formula give

\[
 g_{N,d}\sim
 \frac{(dN)!}{(dN/2)!\,2^{dN/2}(d!)^N}
             e^{-(d^2-1)/4},\qquad
 \log g_{N,d}=\frac d2 N\log N+O(N).
 \tag{10}
\]

This is the fixed-degree specialization of McKay and Wormald's
enumeration theorem. Connectedness holds with probability tending
to one by (4), so log g^c has the same asymptotic form.
[McKay–Wormald](https://users.cecs.anu.edu.au/~bdm/papers/McKayWormaldSqrtN.pdf).

Let M_N be the number of **unlabelled** graph shapes in G_N. Each shape
has at most N! labelings. For a graph with E<=Delta N/2 present edges,
there are 2^E Z2 electric assignments; the Gauss constraints fix the
matter bits uniquely from their incident flux parities. Hence

\[
 \operatorname{rank}P_{\mathcal G_N}
 \le M_N N!\,2^{\Delta N/2},\qquad D_N\ge g^c_{N,d}.
 \tag{11}
\]

If log M_N<=sigma N log N+O(N), with sigma<d/2-1, combining (9)-(11)
proves

\[
 \log\Pr_\beta(\mathcal G_N)
 \le-\left(\frac d2-1-\sigma\right)N\log N
             +O(N)+2\beta K_\Delta N.
 \tag{12}
\]

For fixed finite beta and fixed couplings, the probability tends to zero.
In particular, for exp(O(N)) unlabelled shapes, sigma=0; for d=6 the
leading deficit is **2N log N**. A fixed lattice family and its labelings
satisfy this shape-count assumption. So does a family obtained from a
fixed template through O(N) independent bounded local choices, provided
the number of such choices is bounded exponentially as stated.

We have **not** proved this counting assumption for every possible
three-manifold discretization, or for the event that an arbitrary graph
admits a useful coarse-grained geometric description. Such events may
contain far more microstates. Their rank must be computed before applying
this theorem. The result also does not identify the actual typical phase
for general v2 couplings; it only excludes concentration on the specified
small classes at fixed finite temperature.

Simply restricting to permutation-invariant vectors does not remove this
bound. For the usual invariant subspace with the inherited inner product,
each orbit has one basis vector. There are at least g^c_{N,d}/N!
regular trivial-flux orbits, while G_N contributes at most
M_N 2^{Delta N/2} electric-labelled orbits. Their rank ratio obeys the
same upper bound as (11). Since H and the event commute with relabeling,
their restrictions retain the norm and rank estimates. This is a finite
invariant-subspace statement; it does not construct a complete physical
quotient with relational measuring devices.

The order of limits matters. Equation (12) is a finite-temperature
statement with fixed couplings and beta in the same regulator energy
units. Relating it to fixed physical temperature requires the missing
refinement and energy-scale map. At beta_N growing with N, it need not
vanish. Maintaining a fixed positive target probability p0 requires

\[
 2\beta_N K_{\Delta,N}\ge
       (d/2-1-\sigma)\log N-O(1)+\frac{\log p_0}{N}.
 \tag{13}
\]

This is necessary, not sufficient, and K is an upper bound on energy
per site. It does not establish that cooling selects geometry, or that
changing energy units with N supplies a physical continuum trajectory.

## 5. Independent checks and a finite stress test

[The audit](scripts/geometry_entropy_audit.py) exhaustively generates
regular graphs, checks connectedness, and verifies that the actual
exchange support has one component on each connected graph set:

| Sites | Degree | All regular graphs | Connected regular graphs |
|---:|---:|---:|---:|
| 6 | 3 | 70 | 70 |
| 8 | 3 | 19,355 | 19,320 |
| 8 | 4 | 19,355 | 19,355 |

Across these three sets it checks 1,354,140 directed distinct transitions.
The six-site independent ordered-quadruple comparison checks (1), and
the full capped Z2 matrix verifies a uniform vacuum over three labelled
four-cycles. The projection test checks (6)-(7), including flux excursions.
Twelve exact rational positive-matrix examples test (8) with event
projectors that **do not commute** with the Boltzmann matrix, and a
commuting extremal example saturates the sharp rank bound.

Separately, start from a periodic cubic graph and perform 100N proposed
local flips with each of three fixed seeds. Degrees and connectivity are
preserved. These are finite stochastic stress tests, with no assertion
that this number of flips yields an equilibrium sample:

| Sites | Initial diameter | Final diameter, all three seeds | Initial spatial gap | Final spatial gap range |
|---:|---:|---:|---:|---:|
| 64 | 6 | 4 | 2.000 | 1.745–1.915 |
| 216 | 9 | 5 | 1.000 | 1.661–1.744 |
| 512 | 12 | 6 | 0.586 | 1.571–1.597 |

At 512 sites, the mean radius-three ball grows from 63 to approximately
159–161 sites. The results illustrate loss of the supplied cubic
structure under unbiased flips. They are consistent with the cited
large-N theorem; they neither prove that theorem nor represent real-time
evolution under the quantum Hamiltonian.

[The Lean module](UnifiedTheory/Audit/KFCausalGeometryEntropy.lean)
proves eight supporting results: a weight-ratio inequality, its actual
finite-event sum form, the exponential rank factor, the entropy exponent
bound, a logarithmic suppression threshold, the limiting zero-mass
implication, the sharp complementary-event inequality, and the necessary
spectral budget. The operator exponential/trace argument, orbit counting,
graph enumeration asymptotics, and the external expander theorem are not
claimed as fully formalized Lean proofs. Source hashes and complete
finite results are in [the report](data/geometry_entropy_audit.json).

## 6. How this changes the next model decision

V2 remains the explicit Hamiltonian under study, with a failed reference
ground-state mechanism and a new thermal selection obstruction. Adding
another fixed bounded local energy term cannot defeat (12) for its stated
class: its contribution only changes the O(N) energy budget. The next
model must address the source of the entropy deficit, or demonstrate why
its intended physical state is outside the theorem's scope.

A possible organizing requirement is **finite independent physical
information per cell**. The unrestricted bounded-degree graph carrier
still has log D of order N log N, even after removing vertex label
redundancy when d>2. A replacement with log D=O(N) would have a different
state-count competition. Bounded local dimension on a supplied graph is
not enough: allowing arbitrary endpoint choices reintroduces the excess
graph information. A compositional restriction would need to be specified
and justified physically, without putting the desired spacetime geometry
into the allowed states by hand. This is a candidate principle, not a
derived new law or a construction of four-dimensional spacetime.

Alternatively, derive a controlled ground-state/refinement trajectory,
or a nonequilibrium preparation that maintains geometry and its physical
records. Both must pass common volume, spectral, dispersion, and influence
tests under the same dynamics. Arbitrarily postselecting the desired
graphs does not establish that preparation. The previous conditional
Einstein-action and chiral-locality results remain downstream tools;
the present calculation supplies a sharper requirement for reaching them.
