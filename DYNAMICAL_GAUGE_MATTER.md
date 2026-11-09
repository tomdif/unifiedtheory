# Quantum matter and gauge links with exact Gauss constraints

Date: 2026-09-09

The repository now contains a finite non-Abelian model in which matter
and gauge links both have quantum states and evolve jointly. The update
preserves every Gauss constraint and is unitary. Its exact S3 benchmark
exhibits feedback in both directions: interaction changes a gauge-field
observable, and field evolution changes a subsequent matter prediction.
All finite histories of the specified gauge-invariant measurements admit
an exact reduction to the physical subspace without resetting the gauge
register.

This resolves the absence of dynamical quantum links **for this specified
finite model**. It does not complete the TOE. The matter registers are
regular group rotors, not Weyl fermions; S3 is not the Standard Model
group. This is a separate benchmark from the
[Weyl walk with external SU(2) fields](GAUGE_WALK_COUPLING.md), whose links
have not thereby been quantized. Continuous gauge fields, chiral matter,
the physical vacuum, dynamical spacetime, and empirical predictions remain
open bridges in the [closure frontier](GUT_CLOSURE_FRONTIER.md).

Finite-group lattice gauge dynamics and their gauge-invariant Hilbert
spaces are established subjects. See Mariani, Pradhan, and Ercolessi,
[Hamiltonians and gauge-invariant Hilbert space for lattice Yang-Mills-like theories with finite gauge group](https://arxiv.org/abs/2301.12224),
and Mariani's extension to matter,
[Counting gauge-invariant states with matter fields and finite gauge groups](https://arxiv.org/abs/2509.02173).
The work below supplies explicit proofs and an exact executable benchmark
inside this repository; it does not claim to discover finite-group gauge
theory or establish a continuum limit by selecting a finite group.

## 1. A complete set of relative variables

Supply a graph with finite vertex and edge sets `V,E`, endpoint maps
`s,t:E→V`, and a finite group `G` of order `q`. Each vertex has a regular
matter rotor `m_v∈G`, and each edge has a link coordinate `u_e∈G` transporting
from `t(e)` to `s(e)`. Quantization gives

```text
H_total = C[G]^⊗|V| ⊗ C[G]^⊗|E|.
```

The coordinates label a basis, not classical fields externally supplied at
each time. An arbitrary wavefunction assigns complex amplitudes to their
joint configurations. Independent local frame changes `h_v∈G` act by

```text
m'_v = h_v m_v,
u'_e = h_s(e) u_e h_t(e)^(-1).
```

These are permutations of the basis and hence unitary. Physical
wavefunctions satisfy every Gauss constraint: `ψ(h·c)=ψ(c)` for every
configuration `c` and local frame `h`. Equivalently they are fixed by the
orthogonal projector

```text
Q = q^(-|V|) Σ_(h∈G^V) Γ(h).
```

The relative edge variables

```text
r_e = m_s(e)^(-1) u_e m_t(e)
```

are gauge invariant by cancellation. They are also complete: choose
`h_v=m_v^(-1)` to set all matter coordinates to the identity and all links
to `r_e`. Thus

```text
c and d lie in the same gauge orbit  iff  r(c)=r(d),
ψ is physical                       iff  ψ(c)=f(r(c)) for some f.
```

Lean proves both equivalences in `orbit_iff_relative` and
`physical_iff_relative`, for arbitrary groups and graphs. Regular matter
at every vertex makes the action free: if `h_v m_v=m_v`, then `h_v=1`.
For finite graphs every orbit therefore has `q^|V|` members, and the
physical Hilbert space has dimension `q^|E|`. This counting and the
normalized Hilbert-space assembly follow analytically from the formal
orbit characterization; they are not the formula for pure gauge theory
or for arbitrary matter representations.

The normalized orbit embedding is

```text
(W f)(c) = q^(-|V|/2) f(r(c)),
W†W=I,       WW†=Q.
```

The inverse orbit-size factor preserves the inherited inner product. It
removes redundant frame coordinates while retaining the link/matter
correlations encoded by `r`; it does not trace out the gauge register.

## 2. Local quantum updates that preserve the constraints

A matter/link potential can be any real function of the relative variables.
For a local edge interaction, let `Π_e` project onto `r_e=1`, and choose

```text
U_int = I+(i-1)Π_e.
```

This multiplies aligned configurations by `i` and others by `1`, so it is
unitary. It involves both endpoint matter registers and their link. The
Lean theorem `phase_physical` proves Gauss preservation for multiplication
by any supplied function of the relative variables. Unit modulus, required
for unitarity, is an additional condition satisfied by this chosen phase.

For electric evolution, define convolution on a quantum link by

```text
(C_e ψ)(m,u) = Σ_(a∈G) k(a) ψ(m,u with u_e replaced by a u_e).
```

If the kernel is conjugation invariant, `k(h a h^-1)=k(a)`, this operator
preserves the Gauss constraints. A frame change at `s(e)` merely conjugates
the summation variable, while the transformation at `t(e)` cancels at the
other end. `linkConvolution_physical` proves this by an explicit bijective
change of variable. An inverse-symmetric real kernel also makes `C_e`
self-adjoint in the counting inner product, analytically by exchanging
`a` with `a^-1`.

The uniform kernel gives the orthogonal link projector
`P_e=q^-1 Σ_a L_a`. The module proves its idempotence, the corresponding
uniform matrix's self-adjointness, and unitarity of the reflection
`I-2P_e`. This supplies one valid electric update. The S3 benchmark uses a
different central kernel to distinguish electric representation sectors.

For S3 let `T` be the three transpositions and take

```text
C_e = (1/3) Σ_(τ∈T) L_τ.
```

The class is closed under conjugation, and each transposition is its own
inverse. Direct group multiplication gives `C_e†=C_e` and `C_e³=C_e`.
Consequently

```text
U_E = I-C_e²-iC_e
```

is unitary: multiplying its adjoint gives `I-C_e²+C_e⁴=I`.
`cubicRotation_unitary` proves this polynomial implication in Lean; the
S3 table and its cubic identity are checked exactly in the executable audit.
Equivalently `U_E=exp(-iπ C_e/2)`, although the proof and audit do not
need a numerical exponential.

On a single link, the three projectors

```text
P_trivial  = (C_e²+C_e)/2,
P_sign     = (C_e²-C_e)/2,
P_standard = I-C_e²
```

have ranks `1,1,4`. The last rank is the two-dimensional standard
representation with its regular-representation multiplicity. The electric
gate has phases `-i,i,1` on these sectors. This choice goes beyond a
uniform averaging gate; no claim is made that this finite example
uniquely distinguishes S3 from every other possible model.

The full step is

```text
F = U_E U_int.
```

Both factors commute with every gauge transformation, so `FQ=QF` and
`F` preserves the physical space. Lean proves this preservation for the
actual convolution/phase update in `classStep_physical` and for every
finite number of steps in `classIterate_physical`. The generic statement
allows any conjugation-invariant kernel; its unitarity still requires
appropriate conditions, such as the self-adjoint cubic identity used here.

These rules are local on the supplied graph. Applying such local gates
in a specified schedule preserves the constraints by composition. Neither
the graph, its dimension, the schedule, nor relativistic propagation is
selected by this construction. The audited step is a discrete unitary
law; conservation of a separately chosen continuous-time Hamiltonian is
not claimed.

## 3. Exact matter–field feedback in 216 dimensions

The benchmark has two matter rotors and one link, with configuration
`(m_L,m_R,u)∈S3³`. There are 216 basis states and 36 independent local
gauge frames. Each orbit contains 36 configurations, labeled by
`r=m_L^-1 u m_R`, giving six physical basis states. The exact embedding
has entries `W_(c,r)=1/6` when `r(c)=r`, and zero otherwise.

The audit constructs all 216-dimensional matrices from the S3
multiplication table. It checks the complete gauge action, both sides of
unitarity, the Gauss projector as the average of all 36 frame changes,
and the equality of the full evolution with its six-dimensional physical
representation. The electric and interaction operators do not commute.

Start in the normalized product of uniform states in all three registers.
This is physical. Let `P_link` project the link onto its uniform, trivial
electric sector. After the interaction alone,

```text
<P_link>:             1 → 13/18,
Tr(ρ_link²):          1 → 29/54.
```

The field has acquired a nonzero weight `5/18` outside its initial
electric sector. The pure joint state now has a mixed link-register
reduction. Purity here refers to the specified kinematic tensor factors;
the constrained physical space is not being assumed to factor into
independent physical matter and link Hilbert spaces. `P_link` itself is
a gauge-invariant observable, so its probability change is a physical
diagnostic within the model.

After the electric gate, the alignment probability changes from `1/6` to
`5/54`. A stronger feedback test uses `P_matter`, the projector of the
left matter rotor onto its uniform state. It is gauge invariant. Compare
two applications of the interaction with and without intervening field
evolution:

```text
state: U_int U_E U_int ψ_initial      <P_matter> = 73/81,
state: U_int     U_int ψ_initial      <P_matter> = 4/9.
```

Thus the link's evolution changes a subsequent matter prediction. The
audit also checks `[U_E,P_matter]=0`: the link-local gate alone does not
instantaneously change a matter-only observable. Feedback appears through
the next joint interaction, as it should.

For a negative control, replace the interaction condition by the bare
matter relation `m_L=m_R`, omitting the link. The resulting diagonal phase
is still unitary. Nevertheless its action on the same physical initial
state has exact leakage

```text
||(I-Q) U_bad ψ_initial||² = 5/18.
```

This separates unitarity from Gauss preservation with a concrete failing
update. The valid interaction's use of the link is required by the gauge
constraints, not just by a naming convention.

## 4. Exact reduction for every finite branch

Let `f=W† F W` be the physical six-dimensional update. The audit checks
`FW=Wf` directly. The two projective measurement outcomes are alignment
and its complement; each also intertwines with its reduced counterpart.
For any selected finite sequence of these updates and outcome operators,

```text
K_n ... K_1 W = W k_n ... k_1.
```

`intertwined_history` proves this statement for arbitrary rectangular
embeddings and arbitrary finite operator sequences satisfying the
single-step intertwining identities. The operators can be nonunitary
measurement branches. `isometry_branch_weight` proves trace preservation
under `WρW†` when `W†W=I`. Hence the full and reduced unnormalized branch
states give the same branch weights at every finite length, and the same
conditional predictions whenever the common weight is nonzero.

The executable check follows every branch through five measurement
rounds from three physical preparations: 186 branch comparisons, all
nonzero, and 15 complete normalization trees. It compares the full
216-dimensional states with the six-dimensional calculation, and checks
that every full branch stays in the physical subspace. The same quantum
link is reused throughout. The normalized orbit construction retains the
correlations; resetting or tracing out the link is a different operation.

## 5. Verification and remaining physical obligations

- [Lean module](UnifiedTheory/Audit/KFCausalDynamicalGauge.lean): complete
  relative variables, Gauss preservation for local phase/average/class
  convolution updates, repeated-step preservation, projector/reflection
  and cubic-gate unitary identities, and exact finite-history intertwining.
  Its 23 printed main-theorem audits use only subsets of `propext`,
  `Classical.choice`, and `Quot.sound`.
- [Exact audit](scripts/dynamical_gauge_audit.py) and
  [recorded results](data/dynamical_gauge_audit.json): 7,776 configuration
  covariance checks, 144 gauge/operator commutation checks, full finite
  matrix identities, 186 branch comparisons, and the feedback/leakage
  fractions above. Amplitudes are Gaussian rational; probabilities and
  purities are normalized exact rationals. There is no floating-point
  tolerance in this audit.
- The generic algebra and constraint proofs are formal. The specific S3
  multiplication table, matrix assembly, normalized orbit embedding, and
  concrete fractions are verified by exact SymPy computation. This is not
  a claim that the entire 216-dimensional benchmark is one assembled Lean
  theorem or that a continuous-group/continuum limit has been proved.

The integrated `lake build` passed all 8,916 jobs. The new Lean module
produced no warnings or unfinished-proof dependencies, and the exact
audit completed successfully with matching source hashes.

The overarching constraint remains consistency of physical predictions
under changes of description. Here it determines the gauge-invariant
variables and their inherited normalization, and forbids an undressed
matter update. It still admits many phase potentials, electric kernels,
groups, and graphs. Theorems asserting their consistency do not select
which law describes nature.

A physical TOE still needs a selected microscopic law, a controlled
order-to-spacetime and Einstein-dynamics bridge, chiral quantum matter
with a consistent continuous gauge theory and vacuum, and successful
independent empirical predictions. In particular, this rotor benchmark
does not remove the Weyl walk's mirror species or cancel its anomalies.
The next matter target must connect such dynamical constraints to the
actual fermionic carrier and its complete spectrum; adding arbitrary
finite register dynamics alone cannot discharge that target.

Reproduce from the repository root:

```sh
python3 scripts/dynamical_gauge_audit.py --output data/dynamical_gauge_audit.json
lake build
```

Run Lean/lake jobs sequentially in this repository. The data includes
source hashes, and the module is imported by `UnifiedTheory.lean`.
