# A gauge-covariant chiral regulator and its physical boundary

Date: 2026-09-09

The repository now has a checked overlap-Dirac construction with a single
free Euclidean Dirac zero, exact deformed chiral algebra, and chiral
projectors that transform with the external gauge field. A separate
formal obstruction rules out retaining a fixed Fourier band while
requiring invariance under every local gauge phase.

This is a concrete way to address free fermion doubling, with explicit
changes to the model class. It is a Euclidean regulator with exponentially
decaying couplings under a kernel-gap assumption. It is not the original
strictly finite-propagation real-time walk. Its unitary polar factor still
has nodes at quasienergy π if reinterpreted as a time update. No chiral
fermion measure, anomaly cancellation for this construction, dynamical
gauge-field integration, Lorentzian reconstruction, or TOE is claimed.

The underlying construction is established prior work: Neuberger's
[Exactly massless quarks on the lattice](https://arxiv.org/abs/hep-lat/9707022)
introduces the massless overlap operator, and Lüscher's
[Exact chiral symmetry on the lattice and the Ginsparg-Wilson relation](https://arxiv.org/abs/hep-lat/9802011)
explains the modified lattice chiral symmetry. The contribution here is
the repository's explicit formal algebra, gap and pole analysis, and
reproducible audits, rather than a claim of a new solution to doubling.

## 1. Why a fixed momentum filter cannot be gauge invariant

Suppose `P` is a fixed operator on a finite lattice, with arbitrary spin
or color components at each site. At each site `x`, let `Z_x` multiply
every component there by `-1` and leave all other sites unchanged. These
are unitary local U(1) frame changes. If

```text
P Z_x = Z_x P  for every site x,
```

then `P_(i,j)=0` whenever components `i,j` lie at different sites. To see
this, choose `x=site(i)` in the commutator. For `site(j)≠x`, the relevant
entry gives `P_(i,j)=-P_(i,j)`, hence zero. Lean proves both the unitarity
of these sign matrices and this obstruction in `siteSign_unitary` and
`fixed_filter_no_interSite`.

A translation-invariant operator with this property has the same internal
matrix at every site, so its Fourier symbol is independent of momentum.
It may select an on-site internal component, but cannot select one
momentum cone while rejecting another. This last translation/Fourier
consequence is analytic; the formal theorem establishes the inter-site
matrix-entry constraint.

The exact four-site example retains only the uniform mode with
`P=J_4/4`. The gauge transformation `diag(1,-1,1,-1)` takes the normalized
retained state entirely outside its range: leakage is exactly one, and
the commutator's squared Frobenius norm is two.

This obstruction assumes a field-independent retained operator and
independent local gauge phases. It does not exclude a field-dependent
family obeying `P[A^g]=G P[A] G†`, nor does it prove a general
Nielsen–Ninomiya theorem. The overlap construction uses such a family.

## 2. Exact overlap and chiral-projector algebra

Let `γ` be a self-adjoint involution, and let `ε` be another self-adjoint
involution. Define dimensionless matrices

```text
D = I+γ ε,         γ_hat = γ(I-D) = -ε.
```

No commutation between the two involutions is assumed. Direct algebra gives

```text
D† = γ D γ,
γD+Dγ = DγD,                     Ginsparg–Wilson relation,
γ_hat† = γ_hat,    γ_hat² = I,
D γ_hat = -γ D.
```

These are formal theorems in `KFCausalOverlapChirality.lean`. The polar
factor `γ ε` is unitary, but `D` itself is a Dirac operator, not a unitary
time-step operator. Restoring the lattice spacing with `D_a=D/a` gives
`γD_a+D_aγ=aD_aγD_a`.

Define

```text
P_± = (I±γ)/2,       P_hat_± = (I±γ_hat)/2.
```

The self-adjoint involutions give orthogonal projectors, and

```text
D P_hat_- = P_+ D.
```

Lean proves the projector identities and this intertwining. It is the
algebraic compatibility required to restrict a fermion and its conjugate
to the respective Weyl spaces. Constructing an interacting chiral
functional integral requires additional data and proofs below.

If the field-dependent involution transforms as `ε'=GεG†` and `G`
commutes with `γ`, then `D'=GDG†` and `γ_hat'=Gγ_hatG†`. The module proves
these covariance identities. The projectors consequently transform with
the field; they need not commute with a frame change when held fixed.

## 3. An actual free four-dimensional operator

Choose four Hermitian Euclidean gamma matrices with
`{γ_μ,γ_ν}=2δ_μν I`, and a Hermitian chirality matrix `γ_5` anticommuting
with all four. The audit uses explicit 4×4 tensor products of Pauli
matrices and verifies these identities exactly.

For dimensionless momentum `q∈[-π,π]^4`, choose Wilson parameter one and
negative kernel mass `m_0=1`. Set

```text
B(q) = Σ_μ (1-cos q_μ)-1,
A(q) = B(q) I+i Σ_μ γ_μ sin q_μ,
ω(q)² = B(q)²+Σ_μ sin² q_μ,
H_W(q) = γ_5 A(q),
ε(q) = H_W(q)/ω(q),
D(q) = I+A(q)/ω(q).
```

The Clifford identities imply `H_W†=H_W` and `H_W²=ω²I`. The sign is
well-defined at every momentum because, writing `a_μ=1-cos q_μ∈[0,2]`,

```text
ω² = 1+2 Σ_(μ<ν) a_μ a_ν,
1 ≤ ω² ≤ 49.
```

The polynomial identity, lower and upper bounds, and the lower bound
instantiated with trigonometric functions are proved in Lean. In
particular, there is a uniform free kernel gap, not merely a gap observed
on a finite momentum mesh.

Exact multiplication gives

```text
D†D = 2(1+B/ω) I.
```

Since `ω>0`, this vanishes exactly when all four sine components vanish
and `B<0`. `pole_scalar_iff` proves this scalar equivalence. All sine
components vanish only at the sixteen corners with each coordinate zero
or π modulo `2π`. If `n` coordinates are π, then `B=2n-1`. It is negative
only for `n=0`. Therefore the **only free Dirac zero is at q=0**; at every
other corner `D=2I`. There are no other singularities of the free inverse,
because `D†D` is the stated scalar matrix everywhere. The trigonometric
classification and Clifford-matrix assembly are analytic/symbolic steps,
not a single fully assembled Lean pole-classification theorem.

The modified chirality equals `γ_5` at the origin and `-γ_5` at the other
corners. The nonzero corner value corresponds to the cutoff scale `2/a`
for `D_a`; it does not delete those microscopic variables from the theory.

The exact symbolic derivative is

```text
D(0)=0,       d/da D(ak)|_(a=0)=i Σ_μ γ_μ k_μ.
```

Thus `D(ak)/a` has the massless Euclidean Dirac operator as its small
momentum limit. This statement concerns a free Dirac carrier containing
both chiralities. It does not identify a Standard Model Weyl multiplet
or prove a continuum interacting quantum field theory.

## 4. External gauge fields and a controlled kernel gap

Use the unitary link transport from the
[external gauge-walk construction](GAUGE_WALK_COUPLING.md), now in four
Euclidean directions. With `T_μψ(x)=L_μ(x)ψ(x-e_μ)`, let

```text
P_μ^±=(I±γ_μ)/2,
S_μ=P_μ^+⊗T_μ+P_μ^-⊗T_μ†,
D_W=Σ_μ(I-S_μ),       H_W=γ_5(D_W-I).
```

Each controlled transport is unitary. Anticommutation with `γ_5` gives
`γ_5 S_μ γ_5=S_μ†`, so `H_W` is Hermitian. Link endpoint covariance
implies `H_W[L^g]=G H_W[L] G†`. Under an invertible-kernel hypothesis,

```text
ε[L]=sign(H_W[L]),       D[L]=I+γ_5 ε[L].
```

The spectral theorem gives `ε†=ε`, `ε²=I`, and covariance of the sign
under unitary conjugation. These finite spectral-functional-calculus
steps are analytic here; the Lean overlap theorems then apply to their
resulting involutions. The exact field-dependent sign function is not
replaced by an approximate involution in the mathematical construction.

A simple sufficient condition supplies an explicit gap. In a chosen
frame let `δ_μ=sup_x ||L_μ(x)-I||` and `η=Σ_μδ_μ<1`. Compared with the
free transport, `||T_μ-T_μ,free||≤δ_μ`. Orthogonal spin blocks give
`||S_μ-S_μ,free||≤δ_μ`. Hence

```text
||H_W-H_W,free|| ≤ η,
||H_W ψ|| ≥ (1-η)||ψ||,
||H_W|| ≤ 7+η.
```

The free lower and upper bounds follow from the Fourier symbol above;
the perturbation bounds follow by the triangle inequality. The condition
is sufficient, not necessary. Closeness to identity is frame dependent;
the resulting spectral gap and all conjugate backgrounds are gauge
invariant. This does not claim that arbitrary rough gauge backgrounds
or all topological sectors satisfy the chosen sufficient condition.

The numerical benchmark uses inhomogeneous SU(2) links selected from
`I` and `(399I-40iσ_j)/401`, for which

```text
δ_μ ≤ 2/sqrt(401),
η ≤ 8/sqrt(401),
gap ≥ 1-8/sqrt(401) > 0.6004.
```

It constructs the full 648-dimensional Wilson matrix on a periodic
`3×3×3×3` lattice with two color components, computes its sign, and
independently rebuilds the operator after a large site-dependent gauge
transformation. The observed kernel gap is about `0.92061`. Gauge
covariance, the Ginsparg–Wilson identity, projector idempotence, and the
chiral intertwining all have Frobenius residuals below `2×10^-13`.
These are floating-point checks, not interval-certified proofs. The
background has nonidentity loop holonomy, so the test is not confined
to a pure gauge field.

## 5. Exponential locality, with its change of assumptions

Suppose `g≤|H_W|≤M` with `0<g≤M`. Set

```text
X=I-H_W²/M²,       r=1-g²/M²<1.
```

The spectrum of `X` lies in `[0,r]`. The convergent binomial series gives

```text
sign(H_W) = (H_W/M) Σ_(n≥0) c_n X^n,
c_n=binomial(2n,n)/4^n,       0<c_n≤1.
```

Truncating at `N` has operator-norm error at most
`r^(N+1)/(1-r)`. Because the Wilson kernel has lattice range one,
the truncated operator has range at most `2N+1`. For two sites farther
apart than that, the exact kernel block is bounded by the same tail.
Choosing `N` proportional to the separation gives exponential decay.
This analytic argument supplies locality under the uniform gap. It
does not restore the walk's strict finite propagation bound.

The audit evaluates six polynomial approximants through order 2048
on the numerical kernel's eigenvalues and compares them with this
analytic error bound. The degree/range argument and infinite-series
convergence are analytic, not fully formalized in Lean. On the small
periodic lattice, high-degree range bounds are uninformative about
distance; the locality proof itself applies uniformly on lattices with
the stated gap and finite-range kernel.

## 6. What this does not solve

Setting `U_polar=I-D=-γ_5 ε` gives a unitary matrix. At the free origin
it equals `I`, but at the other fifteen corners it equals `-I`. These
are π-quasienergy degeneracies if `U_polar` is used as a discrete time
step. Even on the three-spatial-momentum slice `q_4=0`, seven such
corners remain. The audit checks these values exactly. This slice or
reinterpretation is not a derived Lorentzian reconstruction. Removing
extra Euclidean zeros
therefore does not by itself remove every extra quasienergy sector of
a real-time walk, nor does it resolve the original
[Weyl walk's mirror identity](WEYL_WALK_CONTINUUM.md).

A different QCA proposal uses flavor staggering and covering maps.
Bakircioglu, Arnault, and Arrighi explicitly describe preservation of the
overall solution count with additional flavors in their
[Fermion Doubling in Quantum Cellular Automata](https://arxiv.org/html/2505.07900v3#S7).
That proposal should be assessed with its full flavor content and
interaction assumptions. It is not used here as a proof that relabeling
the existing cones removes physical degrees of freedom.

For a Weyl functional integral, a field-dependent projector determines
the allowed subspace but does not choose a globally consistent fermion
integration measure. A basis of that subspace can acquire a phase as
the gauge field varies. Locality, integrability, and cancellation of
local and global anomalies must be addressed for the complete chosen
matter representation. Lüscher's
[Abelian chiral gauge theories on the lattice with exact gauge invariance](https://arxiv.org/abs/hep-lat/9811032)
constructs this for anomaly-free U(1) multiplets; the projectors alone
are not a replacement for that construction.

There is a concrete reason not to promote the SU(2) matrix example to
a complete single-Weyl theory: one left-handed fundamental SU(2) doublet
has the global anomaly established in Witten's
[An SU(2) anomaly](https://doi.org/10.1016/0370-2693(82)90728-6).
Our numerical Dirac operator and its projector identities do not cancel
that anomaly. A complete matter multiplet and a valid measure are
separate obligations. No anomaly calculation for the Standard Model
representation has been supplied by this audit.

The finite S3 rotor model supplies
[dynamical quantum links](DYNAMICAL_GAUGE_MATTER.md) for its own carrier.
It is not yet joined to this continuous-group chiral regulator. The
remaining physical task is a compatible joint quantum theory and its
continuum/vacuum behavior, followed by the geometry, Einstein-dynamics,
and empirical bridges in the [TOE frontier](GUT_CLOSURE_FRONTIER.md).

## 7. Verification

- [Lean module](UnifiedTheory/Audit/KFCausalOverlapChirality.lean): 22
  printed main-theorem audits, covering the overlap algebra, projectors,
  covariance, the fixed-filter obstruction, free kernel bounds, and
  scalar pole criterion. Standard axioms only; no custom axioms or
  unfinished proofs.
- [Executable audit](scripts/overlap_chirality_audit.py) and
  [results](data/overlap_chirality_audit.json): exact Clifford algebra,
  norm and defect identities, continuum derivative, all sixteen corner
  values, and the fixed-filter counterexample. The external-field
  sign-function and polynomial-approximation checks are separately
  labeled numerical.

The full integrated `lake build` passed all 8,917 jobs. The new module
produced no warnings, all 22 printed theorem audits have standard axiom
dependencies only, and the recorded audit's three source hashes match.

Reproduce from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 python3 scripts/overlap_chirality_audit.py --output data/overlap_chirality_audit.json
lake build
```

Run Lean/lake jobs sequentially in this repository. The JSON records
source hashes and library versions. The construction is imported by
`UnifiedTheory.lean`.
