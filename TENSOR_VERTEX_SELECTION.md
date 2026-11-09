# Selecting the spin sector with the tensor interaction present

Date: 2026-09-11

The [cubic lift](COLLECTIVE_GRAVITY_COUPLING.md) encoded the supplied
Einstein interaction but did not select its collective sector. The
earlier sign argument only covered a different scalar odd interaction.
This note removes that sign requirement. A local comparison of quantum
states bounds the energy benefit of every nonsymmetric block sector.
Complete exchange then selects the symmetric ground sector with a
strength independent of block size and volume.

For the actual tensor cubic, a separate occupation estimate supplies
a compatible three-cell stabilizer. Together these give an explicit
microscopic parent with the tensor cubic present, a uniform gap to
excluded sectors, and a controlled fixed-volume Gaussian limit.
This closes the sector-selection and vacuum-control gap for that
specified parent at positive regulator. It does not impose the four
gravitational constraints, select two physical helicities, recover
the Einstein quartic, or establish a nonzero-coupling continuum phase.

The proof adapts established Schur--Weyl representation theory and
a quantum state-estimation channel. Neither of those tools is new.
No claim of a new general quantum de Finetti theorem or a new Lean
theorem is made.

## 1. A sign-independent selection theorem

Let V blocks each contain R cells of dimension q>=2. Let F be any
Hermitian Hamiltonian invariant under independent permutations of
the cells in every block. Suppose it has a decomposition

    F=sum_Z f_Z,     |Z|<=k,
    B=sup_cell j sum_(Z containing j) ||f_Z|| < infinity. (1)

k and B are independent of R,V. Terms can have arbitrary signs and
complex matrix entries. No positivity or ground-state gap of F is
assumed. Define the complete exchange and symmetric projector

    C_x=sum_(i<j in block x)(I-Swap_ij),
    P=tensor_product_x P_sym,x,
    E_sym=min spectrum(F restricted to P),
    C_(q,k)=4k(k+q).

Then for

    H=F+(J/R)sum_x C_x,       J>2 C_(q,k) B,             (2)

all ground states lie in P. More precisely,

    H-E_sym >= [J/2-C_(q,k)B] D,
    D=sum_x sum_(mu partition R) (R-mu_1) P_(x,mu),     (3)

where P_(x,mu) projects onto that block's permutation type. Thus
D>=I-P and the ground-energy gap to the excluded sectors is at least
J/2-C_(q,k)B>0, uniformly in R,V. The estimate is deliberately
conservative. It is not a gap separating every collective excited
state from every excluded level.

The interaction order and summed strength remain uniform: exchange
adds at most 2J to the per-cell budget. Complete connectivity inside
a block still grows with R. This theorem does not establish a fixed
microscopic Euclidean interaction range.

## 2. Exposing a large symmetric part of each competing sector

Schur--Weyl decomposition gives

    (C^q)^(tensor R) = direct_sum_mu V_mu tensor S_mu,

where mu has at most q rows. A block-permutation-invariant operator
acts on V_mu and as the identity on S_mu. This also holds for
Hamiltonians coupling several blocks: the permutation multiplicity
spaces can be removed without altering their energy expectations.

Choose a Young tableau of shape mu and apply column
antisymmetrization first, row symmetrization last. Its image is a
copy of V_mu and is symmetric in the mu_1 cells of the first row.
Consequently the same collective representation can be realized in

    Sym^l(C^q) tensor (C^q)^(tensor m),
    l=mu_1=R-m,               m=R-mu_1.                 (4)

The isometry can be chosen unitary between copies of V_mu because
the U(q) representations are unitary. Every collective operator is
intertwined. In particular, representing a state through (4) leaves
the expectation of F unchanged. This uses standard Schur--Weyl and
Young-symmetrizer facts; see
[Barcelo and Ram, Appendix A5](https://math.soimeme.org/~arunram/Preprints/CRTAppendixASectionA5.html).
The order of symmetrization is specified because the first-row
symmetry is used below.

For m=0 leave the block unchanged. For m>=1, trace out the m remaining
cells in (4). Measure the resulting l-cell symmetric state with its
coherent-state POVM, and prepare R identical copies of the measured
one-cell state. This defines a mathematical trial-state channel into
Sym^R(C^q). It is not a measurement postulate for the dynamics, and
the constructed trial state need not be the true ground state.

Apply this channel only to defective blocks. Blocks already in the
symmetric sector are untouched. That distinction makes the energy
cost proportional to the defect number, not to the total volume.

## 3. The local comparison retains entanglement between blocks

Let M_(l->p) be the coherent-state measure-and-prepare channel with
p outputs and let T_(l->p) trace a symmetric input down to p cells.
For p<=l the established channel identity is

    M_(l->p)=sum_(s=0)^p w_s Clone_(s->p) T_(l->s),
    w_s=binom(l,s)binom(p+q-1,p-s)/binom(l+p+q-1,p).

The weights sum to one. The s=p term is T_(l->p), so

    ||M_(l->p)-T_(l->p)||_diamond
      <=2(1-w_p)<=2p(p+q-1)/(l+q).                     (5)

This is [Chiribella's channel decomposition and bound](https://arxiv.org/html/1010.1875v4).
Diamond norm includes an arbitrary external reference, which is
essential for couplings to other blocks. The numerical audit checks
the identity using independent coherent-state moments and cloning
maps, including their complete Choi matrices.

Average the original p selected cell positions over all permutations
of the R cells. The chance that one of them lies among the m cells
discarded in (4) is at most pm/R, by a union bound. Conditional on
all selected positions belonging to the first row, the channel is
exactly T_(l->p), with the external reference retained. Thus the
original local channel and the rounded block's p-cell marginal differ
in diamond norm by at most

    delta_(R,m,p)
      <= min(2, 2pm/R+2(1-w_p)),                         (6)

when p<=l; the trivial bound two applies otherwise. No independence
of the other blocks or product-state assumption is used.

For every defective block, every p<=min(k,R), and all R,

    delta_(R,m,p) <= C_(q,k) m/R.                       (7)

To verify (7), first suppose R>=2k and m<R/2. Then l>R/2>=p,
and (5)-(6) give

    delta <= 2pm/R+4p(p+q-1)/R
           <=4k(k+q)m/R,

since m>=1. If m>=R/2, use 2<=4m/R. If R<2k, use
2<=4k m/R. These cover the remaining cases. Symmetric blocks have
zero comparison error because their channel is the identity.

For a term touching several blocks, the difference of the product
local channels is bounded by the sum of the individual diamond
distances, by telescoping and contractivity of channels. This is why
the construction remains valid for entangled states and complex
interactions.

## 4. Energy comparison and exchange penalty

We may first average the decomposition in (1) over the block
permutations. Its sum remains F, its terms still involve at most
k cells, and its per-cell budget does not increase. For a state rho
of fixed permutation types mu_x, let sigma be its rounded state in P.
Equations (6)-(7) imply

    |Tr(F sigma)-Tr(F rho)|
      <=sum_Z ||f_Z|| sum_(x touched by Z) C_(q,k)m_x/R
      <=C_(q,k)B sum_x m_x.                             (8)

The last step uses that the sum of the norms of terms touching a
block is at most RB. Because sigma is a normalized state in P,

    Tr(F rho) >= E_sym-C_(q,k)B sum_x m_x.               (9)

Meanwhile the complete-exchange eigenvalue in type mu is

    c_mu=R(R-1)/2-(1/2)sum_i mu_i(mu_i-2i+1)
        =(1/2)[R^2-sum_i mu_i^2+2sum_i(i-1)mu_i].

Since mu_i<=mu_1=R-m,

    sum_i mu_i^2 <= R(R-m),      c_mu/R>=m/2.            (10)

Combining (9),(10) proves (3) on every sector and hence on their
direct sum. F has no matrix elements between distinct permutation
types. This completes the selection argument without any constraint
on the signs of the off-diagonal entries.

Unlike a perturbative bound using the norm of the entire extensive
Hamiltonian, (8) pays only for defective blocks. That is what allows
J to remain independent of V. The theorem is a sufficient construction,
not an optimized estimate of the minimum exchange needed.

## 5. Restoring the nine inactive four-spin states

Return to the seven active states of the actual four-spin cell.
Assume the full sixteen-state extension of F commutes with every
cell's active projector A_j and obeys the same per-cell budget B.
Use guarded exchange A_i A_j(I-Swap_ij) and add
delta sum_j(I-A_j).

Fix an inactive pattern with n_bad cells and replace each of them
by Omega. Nonincident terms have unchanged expectation. Each incident
term changes by at most twice its norm, so the total F cost is at
most 2B n_bad. Guarded exchange adds at most J per repaired cell:
the expectation on a new pair Omega tensor rho is
1-<Omega|rho|Omega>, between zero and one. Pairs of repaired vacua
cost zero. Therefore

    E(inactive pattern)
             >= E_sym+(delta-J-2B)n_bad.                (11)

Taking

    J=2[C_(7,k)B+Delta],
    delta>=J+2B+Delta,             Delta>0,              (12)

gives a ground-energy gap of at least Delta to the complement of
the active symmetric sector. These are uniform bounds in R,V. The
specific wave/cubic/guard construction below satisfies the active
projector hypothesis, so no new microscopic cell is needed.

## 6. Occupation control for the actual tensor cubic

Let the six collective coordinates and momenta be Q_(x,alpha),
P_(x,alpha) from the spin-block note. Use U>0, r>0, g>=0 and its
positive wave Hamiltonian H_w on a supplied bounded-degree graph.
Put c=min(U,r)>0. The prior identity on the collective space is

    sum_alpha(Q_alpha^2+P_alpha^2)
                =2N(1-N/R)+d-(d-1)N/R,       d=6.      (13)

Write the supplied cubic after expanding a fixed finite-difference
stencil as

    V_3=(chi/sqrt(R))sum_(abc)c_abc W(Q_a,Q_b,Q_c),
    c_star=sup_x sum_(abc)|c_abc|
                        [1_(x_a=x)+1_(x_b=x)+1_(x_c=x)].

W is the average of all six orderings. The finite block coordinates
need not commute; none are replaced by commuting variables in the
following estimate.

For one ordered triple, every occupation-basis row has at most eight
raising/lowering paths. If N_S is the total occupation of the at most
three touched blocks, each path amplitude is at most
(N_S+3)^(3/2)/(2sqrt(2)). Taking the average over orderings cannot
increase the absolute row sum. Because W is Hermitian, the elementary
bound 2|u_n u_m|<=|u_n|^2+|u_m|^2 converts this row bound into a
quadratic-form bound. Using

    (N_S+3)^(3/2) <= sqrt(3)sum_(x in S)(N_x+3)^(3/2),
    (N+3)^(3/2) <= sqrt(2)N^(3/2)+3sqrt(6),

gives

    |<V_3>| <= (a_3/sqrt(R))sum_x <N_x^(3/2)>
                              +b_3 V/sqrt(R),
    a_3=4sqrt(3)|chi|c_star,      b_3=36|chi|c_star.      (14)

Choose the three-cell diagonal guard

    H_guard=sum_x [alpha N_x/R+lambda N_x^3/R^2],
    alpha=c(d-1)/2,
    lambda=c+lambda_extra,
    lambda_extra=27 a_3^4/(4c^3).                       (15)

The wave-plus-guard identity gives

    H_w+H_guard >= dcV/2+(3c/4)sum_x N_x
                           +lambda_extra sum_x N_x^3/R^2.

For x>=0, Young's inequality in the needed normalization is

    a_3 sqrt(x) <= c/4+lambda_extra x^2.                 (16)

If a_3>0 set t=a_3 sqrt(x)/c; its difference is nonnegative by
27t^4/4-t+1/4=(3t-1)^2(3t^2+2t+1)/4. The case a_3=0 is immediate.
Using x=N_x/R in (14)-(16) proves the operator lower bound

    F:=H_w+H_guard+V_3
       >= (c/2)sum_x N_x+dcV/2-b_3 V/sqrt(R)            (17)

on the collective space. This proof permits the actual signed tensor
coefficients, not only the earlier scalar odd example.

The product Omega vacuum has zero cubic and guard expectations,
and wave expectation at most dV(U+a_max)/4, where
a_max=r+g z_max includes fixed-zero boundary neighbors if present.
Equations (12),(17) therefore prove selected ground states with total
occupation bounded by a constant times V uniformly in R.

The guard is still supported on at most three cells. Its per-cell
budget is at most alpha+3lambda. The cubic contributes at most
|chi|c_star/(2sqrt(2)); the previous conservative wave bound gives
the sufficient combined value

    B=(9/2)(U+a_max)+3g z_max+alpha+3lambda
                                      +|chi|c_star/(2sqrt(2)). (18)

Use (18) in (12). Every term in the full parent now acts on at most
three four-spin cells, hence at most twelve qubits. All coefficients
remain independent of R,V for fixed r>0, chi and bounded stencils.
The prior wave sign threshold U>=a_max is no longer required for
selection; positivity U,r>0 is used separately in (17).

The constants are large. In particular lambda_extra grows like
|chi|^4 c_star^4/c^3. This is a sufficient existence construction,
not evidence for weak exchange or an efficient implementation.
The occupation estimate is not uniform as r approaches zero.
The abstract sector theorem still applies at r=0 if B stays bounded,
but it alone does not select the desired occupation regime there.

## 7. What this selected tensor parent does and does not establish

On fixed occupation inputs, the full-output collective Hamiltonian
approaches the same quadratic oscillator Hamiltonian as before.
The tensor cubic has size R^(-1/2), the quadratic guard counterterm
has size R^(-1), and the other guard contributions vanish faster.
Equation (17) supplies the missing tightness estimate. At fixed V
and positive stiffness, the previous variational/core argument now
gives norm convergence of the selected ground vectors to the unique
Gaussian, and convergence of each fixed low collective eigenvalue.

This is consistent with the coupling analysis: the regular block
limit at fixed physical spacing is not an interacting Einstein
endpoint. At finite R, however, the specified tensor cubic acts
inside an energetically selected microscopic ground sector. Its
presence no longer requires simply assuming the symmetric restriction.

The reference guard has no arbitrary quartic at order 1/R, but the
finite-block wave operators still have their own quartic corrections.
The supplied Einstein quartic also contains a longitudinal momentum
correction, a logarithmic commutator term, local curvature and a
constraint-generated Newton kernel. They have not been generated
by this parent or matched to those finite-block corrections.

The selection theorem can cover future fixed-order local interactions
once their per-cell norm sum is bounded. It does not automatically
cover an extensive inverse-Laplacian reduced interaction with a
volume-dependent norm sum. The gravitational constraints and their
physical reduction must be constructed, rather than declared to be
the permutation constraints used here.

Six oscillator components remain. The earlier spatial-vacuum
representation issue also remains. A two-helicity phase, uniform
critical or physical coarse scaling with nonzero G, inverse-metric
and finite-strain control, universal matter coupling and the TOE
are not established. No symmetry or first-class constraint that
was absent before has been inferred from the exchange theorem.

## 8. Numerical verification

Run

    OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/tensor_vertex_selection_audit.py

The report is
[data/tensor_vertex_selection_audit.json](data/tensor_vertex_selection_audit.json).
It contains exact identities and 53 numerical cases:

- coherent-state channel moments against the cloning decomposition,
  with complete Choi-matrix and trace-preservation checks;
- explicit Young images, first-row symmetry, collective invariance
  and complete-exchange eigenvalues;
- entangled two-cell marginal comparisons through R=128;
- scalar bounds on all represented partitions at the tested sizes;
- entangled two-block energy comparisons and complete spectra of
  complex two- and three-cell interactions;
- the actual tensor-cubic extension, guard, exchange and inactive
  penalties on a two-site cubic-lattice Dirichlet patch.

In that patch, each site has one interior neighbor and five fixed-zero
exterior neighbors. Centered derivatives in the transverse directions
vanish; the longitudinal derivative at one site is plus or minus
half the field at the other. The earlier cubic table then supplies
22 monomials. This is a test of the specified tracefree extension;
the patch is not a physical TT reduction or a gravitational solution.

The inactive-state test compresses the nine identical inactive
one-cell levels to one representative. Since all transition and
guard operators vanish on them and the penalty treats them equally,
this retains the energy of every inactive pattern exactly, while
omitting its factor-of-nine multiplicities. It is not described as
a brute-force diagonalization of the full sixteen-state tensor power.

The positive off-diagonal entries of the tensor parent remain
nonzero even after exchange is added. Its numerical selection is
therefore a test beyond the prior sign argument. Numerical spectra
and matrix tolerances are diagnostics; equations (3),(11),(17)
supply the all-size analytical claims. Completed earlier source
files remain unchanged.
