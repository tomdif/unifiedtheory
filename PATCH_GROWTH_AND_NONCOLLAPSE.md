# Seed growth and the distinction between graph and propagation geometry

Date: 2026-09-10

The actual 124-site seed can grow: **2,064 neutral flips followed by one
lowering flip produce a second adjacent good root**, while retaining
every edge of the first root's induced cubic ball. This is a checked
finite continuation of [the first-seed construction](NEUTRAL_PATCH_NUCLEATION.md).

There is also a stronger obstruction to interpreting local order as
space. A sequence of connected degree-six graphs has all three properties:

\[
\frac{D_3}{N}\longrightarrow0,\qquad
\frac{\text{largest connected good-root component}}N\longrightarrow1,
\qquad
\frac{\operatorname{diam}(G)}{N^{1/3}}\longrightarrow0.     \tag{1}
\]

Even a growing radius test passes at almost every root. Thus neither
local defect density nor a giant connected ordered region guarantees
noncollapse of the full graph distance.

A supplied neutral-probe Hamiltonian offers a conditional repair: allow
hopping only between good roots. On this static family, it deletes every
shortcut, retains an almost-full connected component of diameter of
order N^(1/3), and has a uniform propagation bound measured in the
original cubic metric. A fixed nonzero soft gate instead permits
long-range transmission even between good starting and ending sites.
These are static probe results, not a derivation of matter, the full
fluctuating Hamiltonian, a spacetime continuum, or gravity.

## 1. The retained seed grows by one neighborhood

Start at the endpoint of the 3,360-move witness in the previous note.
Exactly root 31 is good, with D_3=123. Freeze the induced 63-vertex,
114-edge ball around it. The new witness changes only edges that are
not internal to this ball and introduces no additional internal edge.
Degree conservation then prevents new exterior neighbors of its
distance-at-most-two vertices. The original rooted radius-three ball
remains unchanged throughout.

The replay checks every rooted ball after every move and gives

\[
D_3(G_0)=\cdots=D_3(G_{2064})=123,\qquad
D_3(G_{2065})=122.
\]

The final good roots are 31 and 50, and they are adjacent. All graphs
remain connected, simple, and degree six. The audit performs 256,184
rooted tests, including this segment's input. The sequence was found
with target-guided search, shortened by removing loops, and truncated
at the first additional good root. It demonstrates a neutral route
retaining this seed; it does not estimate typical stochastic growth
time or prove that every later seed configuration can continue growing.

## 2. A cubic torus with a sparse tree of shortcuts

Take an ordinary cubic torus of side L=K ell, where K>=2 and ell is
even and at least 16. Divide it into M=K^3 cells of ell^3 vertices;
there are N=(K ell)^3 sites. This partition is used to construct and
analyze the example, not supplied to the intrinsic q_v readout.

Place a binary heap tree on the M cell labels: child i>0 has parent
floor((i-1)/2). Each cell has at most three tree neighbors. For its
p-th incident tree edge, p=0,1,2, select the internal x-directed edge
with local endpoints

\[
(4+2p,4,4),\qquad (5+2p,4,4).
\]

For each tree edge, let ab and cd be its selected edges in the two
cells. Delete ab,cd and add ad,bc. No endpoints are reused. The new
edges were absent: all ports lie well inside distinct cells. Degrees
remain six, and the bipartition by coordinate-sum parity is preserved.
The changed edges therefore do not create triangles.

Each deleted edge can be bypassed by a three-edge detour through local
y=5. None of those detour edges is removed. Thus every original cell
remains connected, and the whole graph is connected. The surgery is a
construction of a graph family, not a claimed zero-energy dynamical
path from the original torus.

The shortcuts form a matching on their actual endpoints. No shortcut
belongs to a square. A four-cycle can contain at most two shortcut
edges. With one, it would require a three-step original lattice path
between ports in different cells, which are too far apart. With two,
the old edges joining port endpoints must be within the corresponding
cells; the same tree-edge pair then requires the deleted edges ab and
cd. Different tree edges cannot supply the required pair of cell links.
This verifies that each shortcut endpoint fails the cubic-root test.

## 3. Almost every ball is cubic, at increasing radii

Let beta_R be the number of sites in a radius-R ball of Z^3:

\[
\beta_R=1+\sum_{r=1}^R(4r^2+2)
=\frac{4R^3+6R^2+8R+3}{3}.                              \tag{2}
\]

There are 4(M-1) changed endpoints. If a root is farther than R from
all of them in the original torus, its induced radius-R ball is
unchanged. If a new path reached a changed edge, its initial segment
before that first edge would already give a short original path to an
endpoint. The same endpoint inclusion covers changed edges internal
to an induced ball. For ell>=2R+2 the original R-balls are cubic, so

\[
\frac{D_R}{N}\le\frac{4(M-1)\beta_R}{M\ell^3}
\le\frac{4\beta_R}{\ell^3}.                             \tag{3}
\]

In particular D_3/N<=252/ell^3. The bound counts all possibly affected
roots, rather than assuming their neighborhoods remain correct.

There is also a connected set of good roots of almost full size.
Within each cell, every possibly affected radius-three root lies in
the box

\[
[1,12]\times[1,7]\times[1,7],\qquad\text{volume }588.
\]

All vertices outside these boxes are good. This set is connected:
a point outside a box has a coordinate outside that box's interval,
which can be held fixed while moving to a cell boundary. Cell boundary
shells connect to each other using untouched lattice edges. Consequently

\[
\frac{|\mathcal C_{\rm good}|}{N}\ge1-\frac{588}{\ell^3},  \tag{4}
\]

where C_good is the connected component containing those shells.
It is the largest good-root component since the lower bound exceeds
one half for ell>=16. All other good-root components, if any, lie
inside one of the fixed boxes and have at most 588 vertices.

## 4. The full graph distance nevertheless collapses

Within a cell, a coordinate path has length at most 3(ell-1).
Replacing each removed edge it uses by its detour adds at most six
steps, since a cell has at most three ports. The cell diameter is
therefore bounded by d_cell=3ell+3, using paths internal to the cell.
The heap tree has height H=floor(log_2 M). Routing through its edges gives

\[
\operatorname{diam}(G)\le(2H+1)(3\ell+3)+2H.              \tag{5}
\]

Choose

\[
K_h=2^h,\quad\ell_h=2h^2+16,\quad R_h=h,\quad
N_h=(2^h\ell_h)^3,\qquad h\ge1.
\]

Here H=3h. Equation (5) implies

\[
\frac{\operatorname{diam}(G_h)}{N_h^{1/3}}
\le\frac{27h+4}{2^h}\longrightarrow0.                   \tag{6}
\]

Meanwhile (3) implies D_{R_h}/N_h<=7/(2h^3), because beta_h<=7h^3
and ell_h>=2h^2. Thus the radius being tested also grows without bound.
Equation (4) gives a giant connected good component of density tending
to one. This proves all assertions in (1).

Under the usual volume normalization assigning each site volume 1/N
and edge length N^-1/3, the full graph's diameter goes to zero. This
excludes a nondegenerate compact spatial limit at that normalization;
it is not an exclusion of every alternative rescaling or measure.

The exact theorem for graphs whose **every** radius-three ball is cubic
does not imply robustness under a vanishing fraction of defective
roots. The former is an external rigidity result of
[Benjamini and Ellis](https://arxiv.org/abs/1409.7587); the construction
above explicitly violates the proposed density-based extension of it.

For any fixed R and bounded, rooted-isomorphism-invariant observable F_R,
the spatial average differs from its lattice value by at most
2 ||F_R||_infinity D_R/N. It therefore converges to the lattice value.
The same conclusion holds for an absolutely summable combination of
uniformly bounded fixed-radius observables, by a finite-head/tail bound.
Such local average energies have no nonzero limiting energy-density
separation between this family and ordinary cubic tori. This is **not**
a no-go theorem for exact finite-size ground-state selection: subextensive
energy differences can matter.

For the actual supplied patch Hamiltonian, each constructed graph is
triangle-free and hence has 150 legal oriented paths per root. Its
configuration exchange row is exactly 300N. Thus its basis-state energy is

\[
\langle G|H_{\rm patch}|G\rangle=300\rho N+JD_3(G),
\]

whose density tends to the perfect torus's 300rho at fixed J,rho.
This calculation concerns trial basis states, not the quantum ground
state or a thermodynamic phase.

## 5. A necessary geometric bound has to cover physical scales

A uniform cubic volume upper bound, |B_G(v,r)|<=C r^3 with C independent
of N and valid through the graph's diameter, implies

\[
N\le C\,\operatorname{diam}(G)^3,\qquad
\operatorname{diam}(G)/N^{1/3}\ge C^{-1/3}.               \tag{7}
\]

It therefore rules out (6). The same contradiction applies if the bound
holds up to a fixed positive multiple of N^(1/3), since (6) eventually
puts the entire diameter within that range. For this family any such
cubic-volume constant must diverge at least as (N^(1/3)/U_h)^3, where
U_h is the explicit upper bound in (5).

A corresponding lower volume bound is needed to exclude the previously
identified thin-torus collapse of dimension. These are necessary
geometric checks across physical scales; they are not supplied by
another fixed-radius mean penalty, and they do not alone derive a
smooth metric, Lorentz symmetry, or Einstein dynamics.

## 6. A supplied neutral probe can see different geometry

On a fixed graph G of this family, define q_v by the intrinsic patch
test and let Q=diag(q_v). For a neutral one-particle probe, supply

\[
H_{\rm probe}=-\kappa Q A_G Q,\qquad\kappa>0,             \tag{8}
\]

where A_G is the ordinary unweighted site adjacency, not the
configuration-space exchange matrix. This is an additional interaction
choice. The probe is neutral; this single-particle calculation does not
claim to construct the charged, Gauss-constrained matter spectrum.

Both endpoints of every shortcut are bad, so (8) removes all shortcuts.
Every remaining hopping edge is an original torus edge. Restrict to
C_good, which contains at least the fraction (4) of all sites.

Its intrinsic diameter has a different scaling from (6). The origin
and its antipodal point are protected and have original torus distance
3L/2. A coordinate path between them is protected, giving exactly that
distance also in the hopping graph. More generally, protected points
can reach a cell corner in at most 3ell steps. Corners connect through
protected coordinate lines in at most 3L/2 steps. Every additional
vertex of C_good lies inside a fixed box and reaches its exterior in
at most 588 good-site steps. Hence

\[
\frac32 L\le\operatorname{diam}(\mathcal C_{\rm good})
\le\frac92 L+1176.                                     \tag{9}
\]

Thus the propagation graph has a noncollapsed macroscopic diameter.
This proves the stated diameter bounds; it is not a complete continuum
or spectral-dimension theorem.

There is also an exact uniform propagation estimate. If d_0(u,v) is
original torus distance, then ((Q A_G Q)^n)_{uv}=0 for n<d_0(u,v),
and the number of n-step walks is at most 6^n. For every mu>0,

\[
\boxed{|\langle u|e^{-itH_{\rm probe}}|v\rangle|
\le\exp\!\left(6\kappa|t|e^\mu-\mu d_0(u,v)\right).}     \tag{10}
\]

This follows by expanding the exponential and using
1_{n>=d_0}<=exp(mu(n-d_0)). Its constants are independent of N in
graph units. No background coordinates enter Q; the original cubic
coordinates are used to prove the bound for this constructed family.

The conclusion is restricted to these static graphs and the supplied
probe coupling. On a dynamically fluctuating graph, q_v changes and
graph transitions must be controlled along with propagation. That
uniform joint estimate and its continuum time scaling remain open.

## 7. Fixed leakage defeats the same uniform locality claim

Replace Q by Q_epsilon=diag(q_v+epsilon(1-q_v)), with fixed
0<epsilon<=1. Shortcut edges then have nonzero hopping. The failure
can be tested between **good** probe sites, not just bad endpoints.

For K=2^h, take the shortcut from the last heap cell to its parent.
Its endpoints have original x separation at least L/2-5. Shift each
endpoint by four steps in the positive local y direction, from y=4
to y=8. Both resulting sites u,v are protected and good. Their
original separation still diverges, but their distance in G is exactly
nine: four steps to a port, one shortcut, four steps out. Any shortcut
route must make those y-displacements, and the original lattice route
is longer than nine for sufficiently large h.

Let A_epsilon=Q_epsilon A_G Q_epsilon. All its entries are nonnegative
and its norm is at most six. There is a nine-step walk of weight at
least epsilon^18, while all lower-order u,v moments vanish. At

\[
\tau=\kappa t_\epsilon=\epsilon^{18}/6^{10},
\]

the exponential-series remainder after order nine is bounded by
(6tau)^10 exp(6tau)/10!. Relative to the leading lower bound
tau^9 epsilon^18/9!, this is at most 1/5, since exp(6tau)<2. Therefore

\[
\boxed{|\langle u|e^{i\tau A_\epsilon}|v\rangle|
\ge\frac{\epsilon^{180}}{2\,9!\,6^{90}}>0.}               \tag{11}
\]

The bound is extremely small but independent of N at fixed epsilon.
It contradicts any bound C exp(vt-mu d_0) with C,v,mu>0 independent
of N as d_0(u,v) tends to infinity. Thus a fixed soft version of this
gate does not retain (10). This is not a no-go theorem for other
energy-filtered models, size-dependent couplings, or weaker notions of
continuum locality; those require separate definitions and estimates.

The audit checks the relevant walk moments exactly, with integer
4A_{1/2}. For all three finite graphs, the selected good-to-good pair
first has a nonzero soft moment at order nine. The hard-gated moments
vanish through order nine because their original distance is larger.

## 8. Consequence for the proposed model

There is now a checked first step of seed growth, but local order must
be paired with a test of actual propagation. A sparse set of defects can
carry a macroscopic shortcut network even when almost all good roots
are connected. The readout “all present links define physical distance”
is therefore not justified by the current defect-density bound.

The proposed next direction is to define geometry through the sector
that carries physical low-energy signals, then prove noncollapse and
uniform propagation in that sector. Equation (8) is one explicit test
of that idea, with its sharp gate visibly supplied. Deriving such a
sector from a physical coupling and reservoir, controlling fluctuations,
and showing continued growth remain open. No TOE or Einstein derivation
is claimed by the static construction.

## 9. Verification boundary

- [`data/patch_growth_path.json`](data/patch_growth_path.json) and
  [`scripts/patch_growth_audit.py`](scripts/patch_growth_audit.py) replay
  the 2,065-move growth witness, preserve the entire original seed ball,
  and check all 124 roots after every move.
- The graph audit constructs 32,768-, 64,000-, and 110,592-site examples.
  It recognizes every potentially affected radius-three ball, certifies
  the untouched balls by the endpoint-neighborhood inclusion, checks a
  connected protected subset and the full good-root components, and
  verifies explicit routes realizing the diameter bound. The observed
  defect counts are 444, 444, and 1,622 respectively. Each finite example
  has one connected component containing all its good roots.
- Probe checks verify deletion of every non-lattice hopping edge, exact
  antipodal distance, and the first nine hard/soft walk moments. The
  asymptotic limits and exponential-series estimates are analytic.
- [`UnifiedTheory/Audit/KFCausalPatchGrowth.lean`](UnifiedTheory/Audit/KFCausalPatchGrowth.lean)
  gives ten supporting proofs: the cubic ball polynomial, route
  normalization, its explicit limit, diameter collapse, the volume
  obstruction, local-observable comparison, gate support and adjoint
  identities, and the final transmission inequality. The graph surgery
  and entire propagator theorem are not claimed as Lean formalizations.
- [`data/patch_growth_audit.json`](data/patch_growth_audit.json) records
  the finite results, exact constants, and source hashes.
