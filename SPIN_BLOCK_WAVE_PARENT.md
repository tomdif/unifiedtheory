# A spin parent that selects its collective wave vacuum

Date: 2026-09-11

The preceding [affine spin metric](AFFINE_SPIN_METRIC.md) used symmetric
seven-state spin blocks as an encoding. It did not establish that a
microscopic Hamiltonian selects those blocks or the low-occupation
states needed by its oscillator limit. This note supplies an explicit
parent and proves those two selections at the scope stated below.

The result is a six-component wave system on a supplied graph. It is
not a two-helicity gravitational sector. In the tested linear canonical
identification, its exact parity also fails the nonzero cubic interaction
of the [conditional Einstein target](REDUCED_TENSOR_HAMILTONIAN.md).
Thus this closes a microscopic selection gap for a revised parent,
while identifying a necessary further change for gravity.

## 1. Microscopic definition and assumptions

Use the same four-spin cell as in
[the microscopic spin seed](MICROSCOPIC_SPIN_TWO_SEED.md). Its sixteen
states contain an active seven-dimensional subspace: a vacuum Omega,
the second singlet eta, and a spin-two quintet. Label the six excitations
by alpha=1,...,d with d=6. Let

    A = projector onto the seven active states,
    b_alpha = |Omega><alpha|,
    X_alpha = b_alpha+b_alpha^dagger,
    Y_alpha = (b_alpha-b_alpha^dagger)/i,
    n = sum_alpha |alpha><alpha|.

X,Y,n vanish on the nine inactive states. These are finite four-qubit
operators, not elementary one-spin exchange couplings. The six excitation
coordinates transform as a scalar plus a real quintet under the original
cell rotations. The Hamiltonian below is invariant under that internal
rotation action; identifying it with spatial rotations remains an input.

Supply a finite undirected graph Gamma with V vertices and maximum
degree z_max. Put R cells at every vertex. Define

    B_(x,alpha) = R^(-1/2) sum_j b_(x,j,alpha),
    Q_(x,alpha) = (B+B^dagger)/sqrt(2),
    P_(x,alpha) = (B-B^dagger)/(i sqrt(2)),
    N_x = sum_j n_(x,j),
    C_x = sum_(j<k) A_(x,j) A_(x,k) (I-Swap_(j,k)).

Swap exchanges whole four-spin cells. The active projectors commute
with it, so C_x is positive and vanishes whenever a pair is not fully
active. Consider the positive Hamiltonian

    H_w = (U/2) sum_(x,alpha) P_(x,alpha)^2
        + (r/2) sum_(x,alpha) Q_(x,alpha)^2
        + (g/2) sum_(<xy>,alpha) (Q_(x,alpha)-Q_(y,alpha))^2,

    H_R = H_w + (lambda/R) sum_x N_x^2
              + (J/R) sum_x C_x
              + delta sum_(x,j) (I-A_(x,j)).                 (1)

Here U>0, r>=0, g>=0. Define a_x=r+g deg(x), a_max=r+g z_max.
For selection assume

    U >= a_max,
    J=J_0+Delta,    J_0 >= (U+a_max)/2,    Delta>0,
    delta > c_rep := J + 3(U+a_max)/2,
    lambda >= 0.                                          (2)

These are sufficient conditions, not optimized thresholds. They can
hold with all coefficients independent of R and V on bounded-degree
graphs. The model is a deliberate revision of the bare wave parent;
the new terms are chosen here, not deduced from causal-order dynamics.

## 2. Interaction order and strength

After expanding the squares, every term of (1) acts on at most two
four-spin cells, hence on at most eight qubits. Internal and adjacent
block pair terms have coefficients proportional to 1/R. There are
complete internal block pairs and complete bipartite pairs between
adjacent blocks.

For one microscopic cell, the sum of the operator norms of the terms
incident on it has the conservative bound

    J_cell <= delta + (9/2)(U+a_max) + 2J
                         + 3g z_max + 2lambda.            (3)

To obtain it, the one-cell wave contribution is at most
3(U+a_max)/(2R). Each internal pair contributes at most
3(U+a_max)/R from the wave term and 2J/R from exchange. Each
interblock pair contributes at most 3g/R, with at most R z_max
such neighbors. Expanding N_x^2 gives a diagonal contribution
lambda/R and R-1 pair contributions 2lambda/R per cell.

Thus the interaction order and the summed interaction strength are
uniform. The number of microscopic neighbors is not uniform. The graph,
block grouping and complete intra-block couplings are supplied; no
embedding with R-independent microscopic Euclidean interaction range
is established. Equation (3) should not be reported as that stronger
locality claim.

## 3. Exact selection of the symmetric blocks

First restrict all cells to their active spaces. In the cell occupation
basis, the wave contribution to an internal pair has off-diagonal
coefficients

    (U+a_x)/(2R)       for (0,alpha) <-> (alpha,0),
    (a_x-U)/(2R)       for (0,0) <-> (alpha,alpha).

Exchange contributes -J_0/R to every swap of distinct active labels.
Interblock off-diagonal terms have coefficient -g/(2R). The occupation
penalty is diagonal. Consequently

    H_0 = H_w + (lambda/R) sum_x N_x^2 + (J_0/R) sum_x C_x

has real nonpositive off-diagonal entries under (2). This assertion is
in the active occupation basis, not the qubit computational basis.

For a real symmetric matrix with nonpositive off-diagonal entries,
replacing any vector by its componentwise absolute value cannot raise
its Rayleigh quotient. Hence H_0 has a nonnegative ground vector.
Average that vector over the independent permutation groups of the
cells in each block. The average is nonzero, since all entries were
nonnegative. It is still a ground vector, because H_0 commutes with
those permutations. It lies in

    P = tensor_product_x Sym^R(C^7).

No uniqueness or irreducibility assumption is needed. C_x vanishes
on P, so the ground energy E_R equals the ground energy of
H_w+(lambda/R)sum N_x^2 restricted to P.

The complete-graph exchange operator obeys the known bound

    C_x/R >= I-P_sym,x.                                  (4)

One way to see (4) is the complete-graph specialization of the
[Caputo--Liggett--Richthammer interchange-gap theorem](https://arxiv.org/abs/0906.1238):
the random walk on R vertices with unit edge rates has gap R.
Every finite tensor representation of the permutation group decomposes
into representations present in its regular representation, so its
nonzero exchange eigenvalues are at least R. Its invariant vectors are
exactly the symmetric tensors. For seven labels and R>=2 the standard
representation is present and the bound is sharp. R=1 has no excluded
active symmetry sector. Equivalently, the transposition class has
eigenvalues

    c_mu = R(R-1)/2 - (1/2) sum_i mu_i(mu_i-2i+1),

for partitions mu of R of length at most seven. The symmetric partition
(R) gives zero; the largest nontrivial transposition-class eigenvalue
comes from (R-1,1), which gives c_mu=R. This is established exchange
spectral theory, not a new spectral-gap theorem.

Combining the variational ground selection with (4) gives the operator
inequality on the all-active space

    H_R-E_R >= Delta sum_x (I-P_sym,x).                   (5)

All active ground states are symmetric, and every excluded symmetry
sector lies at least Delta above the ground energy, independent of R,V.
This is not a separated band containing every collective excited state;
high collective energies can overlap energies in excluded sectors.

## 4. Uniform exclusion of inactive cells

Every cell's active projector commutes with (1). Fix an inactive pattern
and replace its m inactive cells by Omega, keeping the state of the
remaining cells. This quantum channel makes an all-active trial state.
The occupation term has the same expectation. Incident intercell wave
cross terms still have zero expectation because Omega has zero X,Y mean.
The added one-cell wave cost per repaired cell is at most
3(U+a_max)/(2R).

For a newly active pair Omega tensor rho, the exchange expectation is
1-<Omega|rho|Omega>, between zero and one. Repairing a cell therefore
adds at most J in exchange energy; pairs of repaired vacua cost zero.
The sharper repair cost is J+3(U+a_max)/(2R), bounded by c_rep in (2).
Thus the repaired state's energy is at most the old energy minus
(delta-c_rep)m. Since the repaired energy is at least E_R,

    E(inactive pattern) >= E_R+(delta-c_rep)m.            (6)

Equations (5),(6) prove a uniform gap of at least
min(Delta,delta-c_rep)>0 from the ground energy to the complement of
the active symmetric space. They do not assume a volume-independent
norm bound on the full extensive Hamiltonian.

## 5. Why exchange alone does not select the oscillator vacuum

On a symmetric block, label the occupations by n_1,...,n_d, with
N=sum n_alpha<=R. Direct combinatorics gives

    B_alpha^dagger |n> = sqrt((n_alpha+1)(1-N/R)) |n+e_alpha>,

    sum_alpha (Q_alpha^2+P_alpha^2)
      = 2N(1-N/R)+d-(d-1)N/R.                            (7)

Fixed-occupation matrix elements approach oscillator matrix elements,
but that does not imply convergence of the ground state. At N=0 the
right side of (7) is d, whereas at N=R it is only one. For one block
without the occupation penalty, any pure occupation state at N=R has
wave-energy expectation (U+r)/4. For U=1,r=1/4,d=6 this is 5/16,
below the intended six-oscillator ground energy 3/2 for every R.
Those states are already symmetric, so exchange cannot remove them.
This is an analytical obstruction to the bare parent's vacuum limit.

## 6. A vanishing penalty repairs the vacuum limit

Assume r>0 and let c=min(U,r)>0. Since g>=0,

    H_w >= (c/2) sum_(x,alpha) (Q_(x,alpha)^2+P_(x,alpha)^2).

If lambda >= c(d+1)/2=7c/2, substituting (7) proves

    H_R restricted to P >= c sum_x N_x + dcV/2.           (8)

Indeed the difference from the right side is bounded below by

    (1/R) sum_x [(lambda-c)N_x^2-c(d-1)N_x/2] >= 0,

using the integer spectrum N_x^2>=N_x. This estimate holds for every R.
It is enough to stop low-energy vectors escaping to the top of the
finite block. It is a sufficient bound, not a necessary penalty size.

Embed P into the Fock space of dV ordinary oscillators using its
occupation basis. On any fixed finite-occupation input, the embedded
Hamiltonian converges, including all output rows, to

    H_infinity = (U/2) sum p_(x,alpha)^2
       + (1/2) sum_(x,y,alpha) q_(x,alpha)
                              [rI+g L_Gamma]_(x,y) q_(y,alpha). (9)

The error is O(1/R) on each fixed finite-occupation subspace: the square
root in (7) has that error, and lambda N_x^2/R vanishes there. Exchange
is exactly zero. Constants depend on occupation cutoff and fixed V.

Here is the spectral argument, which is stronger than matrix-element
convergence alone. The product vacuum supplies an R-independent upper
bound on E_R at fixed V. Equation (8) bounds total occupation for any
bounded-energy eigenvector. Its squared norm above occupation M is
bounded by a constant divided by M. The occupation-at-most-M subspace
is finite dimensional at fixed V, so these vectors are norm precompact.
For a convergent subsequence, testing the eigenvalue equation against
finite Hermite vectors and using the full-output convergence identifies
the limit as an eigenvector of (9). Those test vectors form an operator
core for the positive finite oscillator Hamiltonian. The variational
principle with finite-support trials gives the matching upper bounds.
The same argument on finitely many orthonormal eigenvectors preserves
multiplicities and yields convergence of every fixed low eigenvalue.
The ground state of (9) is unique, so the embedded collective ground
vectors converge in norm, up to phase, to its Gaussian vacuum.

This proof concerns the selected collective restriction. The full
microscopic parent has additional excluded states above (5),(6); it
does not converge in its entire spectrum to oscillators alone. In
particular, wave excitation levels below that exclusion threshold
are the levels that the full parent selects without extra sectors.

On a periodic cubic graph, the oscillator frequencies are

    omega(k) = sqrt(U [r+4g sum_i sin(k_i/2)^2]).          (10)

There are six components. Taking the block limit first at fixed volume
and positive r yields (9); taking the infinite-volume and r->0 limits
of that Gaussian system gives the usual lattice massless wave theory
in three spatial dimensions, with small-k slope sqrt(Ug). The slope
describes the long-wavelength limit; a continuum lattice-spacing limit
requires the associated rescaling of coordinates and coefficients.
There is no proof here of a critical phase at fixed finite R, or of a
uniform joint R,V,r limit. The coercivity constant in (8) deteriorates
as r->0. A finite periodic exactly massless zero mode has no normalizable
oscillator ground state and must not be silently included in this proof.

## 7. Exact radial audit and Gaussian occupation tails

For one block the six excitation coordinates have an O(6) symmetry.
In angular sector ell, the allowed radial numbers are
N=ell,ell+2,...,R. The exact tridiagonal matrix is

    D_N = (U+r)/4 [2N(1-N/R)+d-(d-1)N/R] + lambda N^2/R,

    O_(N,N+2) = (r-U)/(4R)
        sqrt((R-N)(R-N-1)(N-ell+2)(N+ell+d)).              (11)

This follows by writing the collective creation operator as
a_alpha^dagger sqrt(1-N/R) and using the radial matrix elements of
sum_alpha (a_alpha^dagger)^2. The angular multiplicity is
binom(ell+d-1,d-1)-binom(ell+d-3,d-1), with the second term zero
for ell<2. Including these multiplicities recovers dimension
binom(R+d,d). The audit compares (11) against the full collective
spectrum for R=2,4 and tests every angular sector up to R=256.

For U>=r, the limiting singlet squeezed vacuum has radial amplitudes

    psi_(2n) = (1-t^2)^(d/4) sqrt((d/2)_n/n!) t^n,
    t = (sqrt(U)-sqrt(r))/(sqrt(U)+sqrt(r)).

The audit computes distance to that full infinite vector, retaining
its omitted tail, and separately computes coupled two-block vacua.

A target-vacuum tail estimate also makes the occupation domain concrete.
Only in the already obtained Gaussian theory, take odd L>=3,
V=L^3 and regulator r_L=L^-4, with U,g>0 fixed. A single component's
variances obey

    v_Q = sqrt(U)/(2V) sum_k [r_L+g ell(k)]^(-1/2)
        <= sqrt(U)/2 (1+1/sqrt(g)),
    v_P = 1/(2 sqrt(U)V) sum_k sqrt(r_L+g ell(k))
        <= sqrt((1+12g)/U)/2.                            (12)

For the first bound, use ell(k)>=16|m|^2/L^2 for Fourier representatives
|m_i|<=M_L=(L-1)/2. The shell max_i|m_i|=n has 24n^2+2 points;
sum_(m!=0)1/|m| <= 12M_L(M_L+1)+2(1+log M_L) <= 4L^2.
The zero-mode contribution to the average inverse square root is 1/L.
The second bound follows from ell(k)<=12 and r_L<=1.

Set M=max(1/2,the two upper bounds in (12)) and z=1+1/(2M)>1.
For a centered one-mode Gaussian with diagonal covariance,

    <z^n> = {[(1-z)v_Q+(1+z)/2]
             [(1-z)v_P+(1+z)/2]}^(-1/2) <= 2.            (13)

This follows, for example, by computing the overlap with the normalized
thermal state (1-z)z^n for 0<z<1 and analytically continuing up to the
first positive pole. Our z lies strictly before that pole: each bracket
is greater than 1/2. For v_Q or v_P below 1/2 the negative pole has the
same or larger modulus than the positive one, by v_Q v_P>=1/4, so this
continuation is within the occupation generating series' convergence
radius as well. Six independent flavors give <z^N_x><=64. Spatial
correlations do not obstruct the union bound

    Prob(any N_x>R) <= 64 V z^(-(R+1)).                  (14)

Thus the limiting Gaussian fits the spin cutoff with
R=O(log(V/epsilon)) for prescribed target tail epsilon. Equation (14)
is not an error bound for the actual finite-R parent ground state in a
joint critical limit. Combining those two different assertions would
require a new uniform dynamical or spectral estimate.

## 8. The remaining Einstein mismatch is explicit

The parent has the exact global symmetry

    Z=(-1)^(sum_x N_x),       ZQZ=-Q,       ZPZ=-P.

Every term in (1) commutes with Z. This remains true after the exact
symmetric restriction. Consequently the low-field Hamiltonian under
the direct linear canonical assignment h proportional to Q and
s proportional to P is even under simultaneous (h,s)->(-h,-s).
Projecting to a parity-invariant *linear* TT subspace would retain
that property and cannot supply a cubic vertex.

The reduced Einstein calculation instead has a nonzero curvature
cubic. In its normalized compact TT profile h=a eta,s=b eta,

    kappa E = b^2+(105/4)a^2+c_3 a^3+O((|a|+|b|)^4),
    c_3 = 172125 sqrt(33426748355)/(1051588951 sqrt(pi))
        = 16.8837949274... > 0.

The minimal parent therefore does not match that target in this
identification. This is not a theorem excluding every nonlinear
observable map, every nonlinear constraint reduction, parity-broken
phase, or every spin Hamiltonian. Such changes can alter how parity
acts on the purported metric. They must be supplied and tested; they
are not consequences of the Gaussian selection proof.

The other immediate mismatch is six components versus two physical
tensor helicities. Internal spin-two labels, acoustic poles and the
affine onsite representation do not impose the four gravitational
constraints. The preceding spatial-vacuum representation obstruction
also remains: a six-component unconstrained Gaussian cannot simply
be declared to carry all spatial gauge transformations.

The next substantive task is therefore a constraint-compatible
microscopic interaction and physical reduction whose canonical
observables reproduce the sourced geometry and cubic/quartic
coefficients of the same Einstein target. G, the coarse geometry and
the matter sector remain inputs or open problems. No physical TOE,
novel general exchange theorem, or new Lean theorem is claimed.

## 9. Reproducible checks

Run:

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/spin_block_wave_parent_audit.py

The report is [data/spin_block_wave_parent_audit.json](data/spin_block_wave_parent_audit.json).
Exact identities and 48 numerical cases pass. For U=1,r=1/4,
lambda=1.5, increasing R from 2 to 256 changes the one-block energy
from 1.740791 to 1.507572, toward the Gaussian value 1.5; the full
Gaussian state distance decreases from 0.346050 to 0.019792. With
lambda=0, the R=128 ground state instead has mean occupation
127.871716 and energy 0.248299. These are diagnostic values, not
certified numerical enclosures. The coupled R=2,3,4 cross-covariances
are positive but not monotone toward their Gaussian value; those
small systems test the coupling and encoding rather than its
asymptotic convergence rate.

The audit covers the exact active-cell embedding and scalar identities,
complete-exchange partitions, complete small microscopic spectra,
inactive-state exclusion, full-output collective invariance, parity,
an independent collective construction, complete radial spectra,
large-block radial convergence with unpenalized controls, coupled
vacua and target-Gaussian occupation tails. Numerical tolerances are
stated in the script and do not replace the all-size analytical
arguments above. Prior completed report sources are unchanged.
