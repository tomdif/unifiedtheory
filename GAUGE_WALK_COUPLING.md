# Exact gauge coupling of the Weyl walk

Date: 2026-09-09

The [free Weyl walk](WEYL_WALK_CONTINUUM.md) now admits supplied non-Abelian
gauge links with exact unitarity, spacetime gauge covariance, and invariant
finite measurement-history probabilities. A nonzero SU(2) Wilson loop
certifies that the construction includes curved connections. Constant
potentials admit an analytic finite-time continuum bound, including when
the potentials do not commute. Pure gauge links preserve the free spectrum
and therefore do not remove its mirror species.

This is an external-field, one-particle construction on a specified lattice.
The gauge group, representation, and links are inputs. It supplies neither
quantum gauge-field dynamics nor a chiral Standard Model or a TOE.

External gauge coupling of quantum walks is established prior work.
Cedzich, Geib, Werner, and Werner develop unitary gauge coupling in arbitrary
lattice dimension in [Quantum walks in external gauge fields](https://arxiv.org/abs/1808.10850).
Arnault, Di Molfetta, Brachet, and Debbasch construct exact U(N) gauge
invariance and a conditional Dirac continuum limit in one spatial dimension
in [Quantum walks and non-Abelian discrete gauge theory](https://arxiv.org/abs/1605.01605).
The contribution here is a checked extension of this repository's specific
three-dimensional walk, with explicit hypotheses and limitations; no
priority claim for the underlying coupling principle is made.

## 1. Unitary transport and the full step

Let the finite periodic site set be `Λ`, let the color space be `C^N`, and
let `p_j x = x + e_j` be the spatial permutations. In spin-first ordering,
the Hilbert space is

```text
H = C²_spin ⊗ (C^Λ_site ⊗ C^N_color).
```

For each time and direction supply a unitary color matrix `L_j(t,x)` on
the oriented edge from `x-e_j` to `x`. Define

```text
(T_j(t) ψ)(x) = L_j(t,x) ψ(x-e_j),
(T_j(t)† ψ)(x) = L_j(t,x+e_j)† ψ(x+e_j).
```

Both compositions are the identity. This holds for every finite site
permutation, with no commutation hypothesis on the links. In Lean,
`transport p L` is a site matrix whose entries can themselves be color
matrices. `transport_mul`, `transport_adjoint`, `transport_left_unitary`,
and `transport_right_unitary` prove the actual matrix identities over a
possibly noncommutative star ring.

Let `P_j=(I+σ_j)/2`, with `σ_j` the spin Pauli matrices. Set

```text
S_j(t) = P_j ⊗ T_j(t) + (I-P_j) ⊗ T_j(t)†.
```

Orthogonal spin projections eliminate the cross terms in `S_j† S_j` and
`S_j S_j†`. The surviving terms sum to `P_j+(I-P_j)=I`. The generic Lean
theorems `controlled_left_unitary` and `controlled_right_unitary` require
that `P` is a self-adjoint projection, `T` is two-sided unitary, and `P`
commutes with `T`. In this tensor realization the last condition follows
because spin projections and site/color transport act on separate factors.

Supply also a unitary temporal link `L_0(t,x)` from `(t,x)` to `(t+1,x)`.
Writing `D(L)` for a block diagonal site/color operator, the full update is

```text
F_t = [I_spin ⊗ D(L_0(t))] S_z(t) S_y(t) S_x(t).
```

Every factor is unitary. The step has the same spatial reach as the free
walk: one shift in each axis, ending at one of eight offsets `(±1,±1,±1)`.
The links multiply the amplitudes along these ordered paths. Identity
links recover the original free walk with an additional inert color factor.

## 2. Spacetime gauge covariance and all finite histories

Let `g(t,x)` be arbitrary supplied unitary color frame changes, and put
`G_t=I_spin ⊗ D(g(t))`. The endpoint rules are

```text
L'_j(t,x) = g(t,x) L_j(t,x) g(t,x-e_j)†,
L'_0(t,x) = g(t+1,x) L_0(t,x) g(t,x)†.
```

The first rule gives `T'_j=D(g_t) T_j D(g_t)†` directly at every matrix
entry; this is `transport_covariant`. Since color frame changes commute
with the spin projections, `controlled_covariant` gives

```text
S'_j(t) = G_t S_j(t) G_t†.
```

Multiplication cancels the internal frames. The temporal endpoint rule
then gives

```text
F'_t = G_(t+1) F_t G_t†.
```

`spacetime_step_covariant` proves the temporal/spatial assembly identity.
Spatial links alone give covariance under a common frame at a fixed time;
they do not supply the factor `G_(t+1)` required by a time-dependent frame.
In the exact benchmark, transforming spatial links but retaining the
untransformed temporal links leaves a squared Frobenius covariance defect
of `20272/625`, so this distinction is observable in the operator check.

For `P_n=F_(n-1)...F_0`, repeated cancellation yields

```text
P'_n = G_n P_n G_0†.
```

`propagator_covariant` proves this for every finite length. Its steps need
not be unitary: it also applies to a selected sequence of outcome operators
`K_t`, provided `K'_t=G_(t+1) K_t G_t†`. Thus it covers finite branches of
covariantly transformed quantum instruments, including interventions and
their unitary evolution between observations.

If the preparation transforms as `ρ'=G_0 ρ G_0†`, the unnormalized final
branch state transforms as

```text
P'_n ρ' P'_n† = G_n (P_n ρ P_n†) G_n†.
```

`branch_covariant` and `history_expectation` prove, for the transformed
final effect `O'=G_n O G_n†`,

```text
Tr[(P'_n ρ' P'_n†) O'] = Tr[(P_n ρ P_n†) O].
```

For a density matrix, valid outcome operators, and `0≤O≤I`, these are the
same physical branch-and-effect probabilities. The formal trace equality
holds even without positivity assumptions. Setting `O=I` gives branch
weights; dividing by a common nonzero branch weight gives identical
conditional predictions. Neither a reset nor an intermediate
renormalization is used in the proof. A bare color component held fixed
while its frame changes is not a gauge-invariant measurement; site/spin
observations with color traced out are gauge invariant.

## 3. Non-Abelian curvature is present

For commuting spatial permutations consider the loop operator

```text
W_xy = T_x T_y T_x† T_y†.
```

The four spatial shifts return to their starting site, so this operator
is block diagonal in the site basis. Its color block is the ordered
parallel transport around the corresponding elementary loop. In Lean,
`holonomy_covariant` proves `W'_xy=D(g) W_xy D(g)†` and
`wilson_trace_invariant` proves invariance of the full trace. Block
diagonality also gives invariance of each site's color trace, checked
explicitly in the finite audit.

Choose constant links

```text
L_x = (3I-4iσ_x)/5,     L_y = (3I-4iσ_y)/5.
```

Here the Pauli matrices act on color. These are SU(2) matrices with
noncommuting values. The exact color trace is

```text
Tr_color(W_xy(x)) = 226/625,
2-Tr_color(W_xy(x)) = 1024/625 > 0.
```

Identity/pure gauge links have identity contractible-loop holonomy. This
example therefore has nontrivial curvature; the gauge coupling is not
limited to changing the frame of the free walk.

## 4. Continuum generator and sign conventions

Take equal spatial and temporal spacings `a`, smooth prescribed Hermitian
potentials `A_μ(t,x)`, and smooth wavefunctions. Absorb the coupling
constant into `A_μ`, and define

```text
D_μ = ∂_μ + i A_μ,
L_j(t,x) = path-ordered exp[-i ∫_(x-a e_j)^x A_j(t,s) ds],
L_0(t,x) = path-ordered exp[-i ∫_t^(t+a) A_0(s,x) ds].
```

Taylor expansion on smooth fields gives, at fixed time,

```text
T_j = I-a D_j+O(a²),       T_j† = I+a D_j+O(a²),
S_j = I-a σ_j D_j+O(a²),
F = I-ia A_0-a Σ_j σ_j D_j+O(a²).
```

Here spin/color identity factors are suppressed, and the remainders mean
local consistency on smooth states with appropriate bounded derivatives;
they are not a uniform operator-norm statement on arbitrary states with
unbounded momentum. The resulting equation is

```text
i ∂_t ψ = [I_spin ⊗ A_0 + Σ_j σ_j ⊗ (-i∂_j I_color+A_j)] ψ.
```

The endpoint rule expands to

```text
A'_μ = g A_μ g† + i(∂_μ g)g†,
D'_μ(gψ) = g D_μ ψ.
```

With these conventions the field strength is

```text
F_ij = ∂_i A_j-∂_j A_i+i[A_i,A_j],
[D_i,D_j] = iF_ij,
W_ij = I+i a²F_ij+O(a³).
```

For constant fields the last expansion is
`L_i L_j L_i† L_j†=I-a²[A_i,A_j]+O(a³)`. The audit differentiates the
actual SU(2) walk factors and loop at zero spacing, in exact arithmetic,
for a specified noncommuting constant background. The smooth variable-field
derivation above is analytic. A controlled finite-time continuum limit
for general space/time-dependent backgrounds remains to be established.

## 5. Controlled finite time for constant supplied fields

For fixed Hermitian matrices `A_0,A_x,A_y,A_z` and physical momentum `k`,
define

```text
H_0 = I_spin ⊗ A_0,
H_j = σ_j ⊗ (k_j I_color+A_j),
H = H_0+H_z+H_y+H_x,
K = ||A_0|| + Σ_j (|k_j|+||A_j||).
```

All norms here are Hilbert-space operator norms. The actual controlled
transport factor equals `exp(-ia H_j)`: the positive spin subspace carries
`exp[-ia(k_j I+A_j)]` and the negative spin subspace its adjoint. Thus

```text
F(a,k) = exp(-iaH_0) exp(-iaH_z) exp(-iaH_y) exp(-iaH_x).
```

This identity does not require different potentials or different factors
to commute. Each factor is unitary, `F(0)=I`, and `F'(0)=-iH`. The product
rule and unitary norm bounds give `||F''(a)||≤K²`: the diagonal terms are
bounded by the squared individual norms, and each pair contributes at
most twice their product. Also `||H||≤K`, so the second derivative of
`exp(-iaH)` has norm at most `K²`. Taylor's integral remainder gives

```text
||F(a,k)-exp(-iaH)|| ≤ a²K².
```

For every integer `n≥1` and real `t`, telescope powers of the two unitary
operators to obtain

```text
||F(t/n,k)^n-exp(-itH)|| ≤ t²K²/n.
```

The generic telescoping inequality is Lean's `KFCausalWeylWalk.power_error`.
The matrix-exponential realization, derivative bounds, and their assembly
into this continuum estimate are analytic proofs, not a fully formalized
continuum theorem. Constant backgrounds preserve momentum, so a common
fixed bounded momentum band gives a uniform `K` and the same propagator
bound for band-limited states. It does not control all lattice momenta at
once or eliminate the other cones.

For a normalized initial state and bounded observable `O`, the corresponding
expectation error is at most `2||O|| t²K²/n`, by expanding the difference of
the two evolved quadratic forms. The numerical audit checks the propagator
bound in 24 noncommuting SU(2) cases. Its largest error/bound ratio is below
`0.105`; these floating-point checks illustrate the analytic result and
are not interval certificates or a substitute for the proof.

## 6. What gauge covariance cannot select

A static local frame applied to identity links gives

```text
L_j(x)=g(x)g(x-e_j)†,     L_0(x)=I,
F_pure=G F_free G†,
F_pure^n=G F_free^n G†.
```

`conjugate_powers` proves the power identity. Unitary similarity preserves
the spectrum, so these backgrounds cannot remove the free mirror cones
identified in [the Weyl spectrum audit](WEYL_WALK_CONTINUUM.md). On the
infinite lattice multiplication by pointwise unitary matrices is likewise
a unitary operator, giving the same conclusion. A general curved,
inhomogeneous background need not preserve momentum, so this argument does
not classify its spectrum. It establishes the narrower obstruction that
gauge covariance, which permits both identity and pure gauge links, does
not by itself solve the chiral-species problem.

The construction works with any supplied finite-dimensional unitary
representation. SU(2) is the audit example, not a selected gauge group.
Local gauge covariance constrains how the descriptions relate while
leaving the physical connection, representation, and law underdetermined.
This is consistent with the earlier result that
[refinement consistency alone does not select the dynamics](QUANTUM_REFINEMENT_PROOF.md).

The next physical obligation is a joint matter/link dynamics with a
specified gauge-field Hilbert space, gauge constraints, and evolution
preserving those constraints, followed by control of its full chiral
spectrum and continuum behavior. Gauge links here are prescribed matrices;
there is no electric-field Hamiltonian, gauge-field backreaction, anomaly
cancellation argument for this walk, selected Standard Model content, or
dynamical geometry. None of those gaps is discharged by the trace identities.

## 7. Verification and formal boundary

- [Lean module](UnifiedTheory/Audit/KFCausalGaugeWalk.lean): generic controlled
  transport, block-matrix links, spacetime assembly, arbitrary finite-history
  covariance and trace equality, pure gauge powers, and Wilson traces.
  Its 18 printed main-theorem audits use only subsets of `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx` or new axioms.
- [Executable audit](scripts/gauge_walk_audit.py) and
  [recorded results](data/gauge_walk_audit.json): 45 exact operator checks on
  a 32-dimensional periodic `2×2×2` lattice over three time steps; 24 exact
  site/spin reduced-state comparisons; full propagator covariance, norm
  preservation, the temporal-link negative control, eight local Wilson
  traces, and pure gauge similarity/powers. This small lattice aliases
  opposite neighbors, so it is supplemented by a `3×3×3` lattice check.
- The 108-dimensional larger-lattice unitarity and spacetime covariance
  Frobenius residuals are below `3×10^-15`. They are numerical checks.
- The continuum generator and constant-field loop coefficient are checked
  symbolically for one explicit background. Twenty-four separate numerical
  cases check the analytically derived constant-field finite-time bound.

The generic projection and transport proofs are formal. Their tensor
assembly into the full arbitrary-color walk is explained analytically and
tested in the concrete SU(2) pipeline; there is no claim that all continuum
analysis or the complete arbitrary-color pipeline is one assembled Lean
theorem. Source hashes in the data tie the checks to the source versions.
The integrated `lake build` passed all 8,915 jobs; the new module produced
no warnings, and the recorded audit completed successfully.

Reproduce from the repository root:

```sh
python3 scripts/gauge_walk_audit.py --output data/gauge_walk_audit.json
lake build
```

Run the Lean build without another Lean/lake job in this repository. The
construction is imported by the root `UnifiedTheory.lean` module.
