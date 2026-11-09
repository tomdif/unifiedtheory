# A finite gauge-invariant Weyl measure and its current

Date: 2026-09-09

Follow-up: [the positive-measure construction](POSITIVE_MEASURE_LOCALITY.md)
replaces the tree basis by a normalized inverse-Dirac basis and reduces
the measured distant-link response while retaining phase consistency.
Its analytic locality bound uses a Dirac gap in addition to the Wilson
kernel gap; the massless limit and physical determinant phase remain open.

The previous [local chiral basis](CHIRAL_MEASURE_CONSTRUCTION.md) now extends
across complete compact U(1) gauge orbits over a controlled weak-field
slice. We construct its fermion determinant, its phase correction relative
to the naive basis, and an explicit measure current. The current satisfies
the gauge Ward equation; its curl and closed-loop phase agree with the
projector geometry in independent numerical checks.

The construction has 22 audited Lean algebraic results. Smoothness,
spectral bounds, determinant nonvanishing, and global integrability on the
specified domain are analytic assemblies, not fully formalized Lean
theorems. Exact finite-group and matrix controls and floating-point
overlap calculations are recorded separately.

This is a finite Euclidean construction with external Abelian fields and
supplied charges. It does not establish a spacetime-local measure current,
lattice symmetry of that current, all topological sectors, a dynamical
Standard Model, real-time reconstruction, gravity, or a TOE.

## 1. Derive the gauge frame from links

Choose a root r and a spanning tree of a connected finite graph. Write
`L(x,y)` for link transport from y to x. Define compact tree transport by

\[
 c_r(U)=1,\qquad c_x(U)=L(x,p(x))c_{p(x)}(U),
\]

where p(x) is the tree parent. Under `L(x,y)→g_x L(x,y)g_y⁻¹`, products
along paths give

\[
 c_x(U^g)=g_x c_x(U)g_r^{-1}.
\]

Lean proves this for arbitrary supplied paths ending at x. Set

\[
 \bar L(x,y)=c_x^{-1}L(x,y)c_y.
\]

The tree links become one. All original links are recovered as
`L(x,y)=c_x bar L(x,y)c_y⁻¹`. For a general group, dressed links
transform only by conjugation at the root. For U(1) this conjugation is
trivial, so every dressed link is invariant under the full gauge group.
These statements are formalized.

The construction uses products in U(1), not globally chosen logarithms.
It therefore remains smooth and single-valued when gauge phases cross
principal-log cuts or wind by 2π. The tree, root, and supplied paths are
part of the construction; their physical irrelevance has not been proved.

## 2. Construct the finite Weyl determinant

For integer charge q, let

\[
 C_q(U)=I_{\rm spin}\otimes\operatorname{diag}(c_x(U)^q).
\]

Gauge covariance of the Wilson kernel and its sign gives

\[
 D_q(U)=C_qD_q(\bar U)C_q^\dagger,\qquad
 P_q(U)=C_qP_q(\bar U)C_q^\dagger,
\]

where `P_q=(I+sign H_W,q)/2` is the overlap left-handed domain projector.
The antifermion projector is the field-independent
`P_+=(I+γ₅)/2`; it commutes with C_q.

Choose the previous positive-Gram basis construction on the dressed slice:

\[
 V_q(\bar U)=P_q(\bar U)W_0
  \left(W_0^\dagger P_q(\bar U)W_0\right)^{-1/2}.
\]

Let B₀ be a fixed orthonormal basis of `ran P_+`. Dress both integration
bases:

\[
 V_q^{\rm full}=C_qV_q(\bar U),\qquad B_q^{\rm full}=C_q B_0.
\]

The resulting Weyl matrix is

\[
 \begin{aligned}
 M_q(U)&=(B_q^{\rm full})^\dagger D_q(U)V_q^{\rm full}\\
       &=B_0^\dagger D_q(\bar U)V_q(\bar U).
 \end{aligned}
\]

The cancellation is a Lean theorem for arbitrary unitary C and compatible
rectangular matrices. Since the dressed links are invariant, both M_q and
its determinant are gauge invariant. The residual root phase is the same
scalar on both bases of a fixed-charge, equal-rank block and cancels.

Equivalently, retain B₀ as the antifermion basis and change the fermion
basis by a unitary matrix with determinant
`det(B₀†C_qB₀)⁻¹`. This gives the same measure phase as the two-basis
construction. Moving the antifermion basis is thus an explicit phase
choice, not a change of its chiral subspace or additional particle content.

For an independently chosen naive fermion basis Vₙ of the same subspace,
the exact correction is

\[
 \det M_q^{\rm full}
 =\underbrace{\overline{\det(B_0^\dagger B_q^{\rm full})}
              \det(V_n^\dagger V_q^{\rm full})}_{\text{unit phase}}
   \det(B_0^\dagger D_q(U)V_n).
\]

The general determinant change-of-basis formula is formalized, and the
actual overlap matrices check this correction independently.

## 3. Exact sufficient bounds on the whole domain

Use a periodic `2^4` lattice with periodic link fields and antiperiodic
fermion boundary conditions in Euclidean time. Each Dirac matrix has
dimension 64 and each Weyl matrix dimension 32. The temporal boundary
condition removes the finite-volume free zero mode; it is not a generated
fermion mass or a continuum mass-gap result.

Define the dressed weak slice by

\[
 \bar L_e=e^{i\bar\theta_e},\qquad
 \bar\theta_e=0\text{ on tree edges},\qquad
 |\bar\theta_e|\le 1/48.
\]

The full domain consists of every compact gauge transform of these
configurations. It includes arbitrarily large raw gauge phases, while
its dressed representative stays in the specified slice.

For all integer `|q|≤6`, the norm perturbation from the free Wilson kernel
is at most

\[
 \eta_q\le4|q|\max_e|\bar\theta_e|\le\tfrac12.
\]

The free Wilson-kernel gap is at least one, including the antiperiodic
momenta. Along the straight slice contraction to the free field,
`|H_W|≥1/2`. The Sylvester estimate from the preceding note gives

\[
 \|P_q-P_0\|\le\frac{\eta_q}{2(1-\eta_q)}\le\tfrac12,
 \qquad W_0^\dagger P_qW_0\ge\tfrac34 I.
\]

Thus the chosen basis is well-defined and smooth everywhere on the slice,
with rank 32. Compact tree dressing extends it smoothly across its entire
gauge saturation. These are analytic norm and functional-calculus
arguments with exactly checked scalar margins.

There is also a nonvanishing determinant bound. The free allowed momenta
have spatial components 0 or π and temporal component ±π/2. Their Wilson
mass is `B=2n≥0`, so the free overlap identity gives `D₀†D₀≥2I`.
Since

\[
 \|D_q-D_0\|=2\|P_q-P_0\|\le1,
\]

the smallest singular value of D_q is at least `√2−1>0`. The overlap
intertwining identity sends `ran P_q` into `ran P_+`. Orthonormal bases
therefore give the same lower bound for M_q. Every finite determinant
in this specified domain is nonzero. This particular lower bound is for
the `2^4` benchmark; it is not uniform as the physical volume increases.

No anomaly cancellation is needed for this finite domain construction.
In particular it also applies to a single charged Weyl block. This is
possible because the construction has not supplied the required
spacetime locality and lattice symmetries of a physical measure current.
It is not a way around anomaly constraints on local chiral gauge theory.

## 4. Construct the current, including the gauge directions

The total measure connection, with both bases allowed to move, is

\[
 \mathcal L=i\operatorname{Tr}(V^\dagger dV)
              -i\operatorname{Tr}(B^\dagger dB).
\]

The minus sign arises because the antifermion coefficients use the dual
basis. The new formal moving-frame identity gives

\[
 \mathcal L=\bar{\mathcal L}
       +i\operatorname{Tr}\left(C_q^\dagger dC_q(P_q(\bar U)-P_+)\right).
\]

In a local angle chart write `c_x=e^{iα_x}`, `α_r=0`, and define the real
trace density, in our sign convention,

\[
 a_q(x)=q\,\operatorname{tr}_{\rm spin}(P_q(x,x)-P_+(x,x)).
\]

Then

\[
 \boxed{\mathcal L=\bar{\mathcal L}-\sum_xa_q(x)d\alpha_x.}
\]

Equal ranks imply `Σ_x a_q(x)=0`. Under an infinitesimal gauge variation
ω, the slice does not move and `δα_x=ω_x−ω_r`, giving
`L(gauge ω)=−Σ_x a_q(x)ω_x`. This is the required vertical response in
the stated connection/sign convention.

The formula can be implemented as an explicit link current. Let B be the
edge-by-nonroot-site gauge-gradient matrix, and A the tree-potential map
from link-angle variations to based site angles. The tree gives `AB=I`.
Write `T=I−BA`; then `TB=0`, and `d bar θ=T dθ`. If ℓ denotes the
slice connection coefficients and a the nonroot density vector, set

\[
 \boxed{J=T^T\ell-A^Ta.}
\]

Lean proves

\[
 B^TJ=-a.
\]

It also proves completeness of this decomposition: every current obeying
that equation equals `TᵀJ−Aᵀa`. Thus the Ward equation fixes a
particular component and leaves a transverse component to be determined
by curvature, global consistency, locality, and lattice symmetries.

Here the slice basis supplies that component explicitly. With
`M=W₀†PW₀`, its connection for a slice tangent δP is

\[
 \boxed{\bar{\mathcal L}(\delta P)
 =-\operatorname{Im}\operatorname{Tr}
   \left(M^{-1}W_0^\dagger P\,\delta P\,W_0\right).}
\]

To derive this, differentiate `V=PW₀M⁻¹/²`. In `Tr(V†δV)`, the term
containing `δ(M⁻¹/²)` has real trace because it is a product of Hermitian
matrices. The displayed imaginary part comes from the remaining term;
orthonormality makes the full trace purely imaginary. The executable
computes δP by spectral divided differences and obtains every chord
coefficient ℓ, then all link coefficients J.

All ingredients in J depend on the invariant dressed links. Hence this
Abelian current is gauge invariant. The incidence and tree matrices
depend only on the chosen graph and tree. This statement does not
establish their covariance under changes of the tree or lattice
translations and rotations.

## 5. Curvature and global integrability on the restricted domain

Because the current comes from explicit smooth bases, its curvature for
commuting variations is

\[
 d\mathcal L(\delta_1,\delta_2)
 =i\operatorname{Tr}\big(P[\delta_1P,\delta_2P]\big).
\]

The antifermion projector P₊ is constant, so its curvature contributes
zero even though the chosen basis B moves. For any closed loop in the
specified domain, the bases return to their starting values. The Kato
argument in the previous note therefore gives

\[
 \exp\left(i\oint\mathcal L\right)
 =\det(I-P(0)+P(0)Q(1)).
\]

This analytic conclusion covers all closed loops of this restricted
gauge-saturated domain. It does not cover arbitrary admissible link
fields or other index sectors.

One useful noncontractible loop winds a single nonroot gauge angle by
2π while fixing the dressed field. The integer-charge bases are periodic,
but the measure connection has phase

\[
 \exp\left(i\oint\mathcal L\right)=e^{-2\pi i a_q(x)}.
\]

The extra antifermion winding contributes an integer multiple of 2π.
Thus a nontrivial Kato holonomy is compatible with the gauge-invariant
determinant; it is reproduced by the measure connection. This test does
not identify a nonzero holonomy with a physical gauge anomaly.

## 6. What the locality test does and does not prove

Tree transport and A contain arbitrarily long paths as the graph grows.
A generic divergence inverse cannot be certified as local merely because
it solves the Ward equation.

An exact family makes this concrete. On a rooted line with source a,
define the edge current `j_n=Σ_{k=0}^n a_k`. Lean proves its divergence
equations, uniqueness with the root condition, and closure at the final
site when the total source is zero. For the dipole

\[
 a_k=\delta_{k,0}-\delta_{k,2R+3},
\]

the current at edge `R+1` equals one for every R. The source vanishes
throughout an arbitrarily large neighborhood of the probe edge. This
rules out uniform finite-range or exponentially decaying response for
this inverse as a map on arbitrary zero-sum sources.

The actual anomaly density is a special function of the gauge field.
The result above does not rule out cancellations between the two terms
of J, or a different local current for an anomaly-free multiplet. We have
not proved that this complete fermionic J is nonlocal. What remains is a
bound on its link derivatives, uniform in lattice size, or a replacement
current which has that bound and the needed lattice symmetries.

This distinction follows the physical requirements in
[Lüscher, §§4–5 and appendix B](https://arxiv.org/html/hep-lat/9811032v2):
the current must satisfy locality as well as gauge and integrability
conditions. The established Abelian construction exploits the special
anomaly-free field dependence; a generic tree divergence inverse does
not implement that step.

We also test the **complete fermion current**, beyond that generic
argument. The audit grows a periodic `L×2×2×2` lattice with L=4,8,12,16,
keeps the antiperiodic fermion time boundary, and repeats the same weak
background pattern along the long spatial direction before imposing
the tree slice. It measures the response of `J_1` at the link ending at
`(0,1,0,0)` to a distant link-angle variation ending at `(L/2,1,0,0)`.
All four directions of the distant link are tested.

For a distant link in direction 0, which is a tree direction, the response
does not decrease over this measured range. The sum over the supplied
hypercharge multiplet also remains nonzero:

| L | Minimum endpoint separation | Charge-six response | Full hypercharge response |
| --- | ---: | ---: | ---: |
| 4 | 1 | 2.550 × 10⁻⁶ | 1.417 × 10⁻⁶ |
| 8 | 3 | 3.387 × 10⁻⁶ | 1.884 × 10⁻⁶ |
| 12 | 5 | 3.465 × 10⁻⁶ | 1.928 × 10⁻⁶ |
| 16 | 7 | 3.470 × 10⁻⁶ | 1.931 × 10⁻⁶ |

Halving the finite-difference step from `10⁻³` to `5×10⁻⁴` leaves these
signals well resolved. The other three distant-link directions decrease
toward the numerical floor. This directional control matters: the tree's
global dependence does not imply that every current response is long-range.

The persistent response is finite numerical evidence of a locality issue
with this particular measure choice, including its anomaly-free charge
sum. It is not an asymptotic proof ruling out every possible exponential
bound. Only one lattice direction is enlarged, so this is also not a
four-dimensional continuum test. It supplies a reproducible diagnostic
for replacement phase choices; it does not establish an anomaly of the
Standard Model or rule out the established local Abelian constructions.

## 7. Reproducible results

The [audit](scripts/gauge_dressed_measure_audit.py) records its results in
[JSON](data/gauge_dressed_measure_audit.json).

- Exact rational U(1) transport checks cover 256 gauge frames on a
  four-site tree with a closing chord, including nontrivial root phases.
- An exact matrix control shows that omitting the antifermion phase
  correction changes a determinant by `(3+4i)/5`.
- Exact dipole tests cover radii 1, 4, 16, and 64, alongside the general
  Lean theorem for every radius.
- The overlap audit uses all five supplied hypercharge blocks
  `(q,m)=(1,6),(−4,3),(2,3),(−3,2),(6,1)`. Colors and weak components are
  copies here: the non-Abelian fields are the identity and no Yukawa
  interaction or gauge-field integration is included.
- Twelve large random compact gauge transformations leave each Weyl
  matrix and the 15-component determinant unchanged within numerical
  error. The naive patch basis changes the total phase by up to
  `6.74×10⁻⁷` radians; the explicit correction cancels that change.

The minimum observed kernel gap is approximately 0.95782; the minimum
reference Gram eigenvalue is 0.99874; and the minimum Weyl singular value
is 1.41074. The largest operator/determinant residual is below `10⁻⁹`
(below `3.5×10⁻¹³` in the recorded run).

For a charge-six block, the explicit current's Ward residual is below
`10⁻¹²`, and its gauge-change residual is below `10⁻¹⁰`. Its contraction
with a mixed physical/gauge variation agrees with direct differentiation
of both bases: halving the difference step reduces the error from
`3.94×10⁻⁸` to `9.84×10⁻⁹`.

An independent current-curl check gives projector curvature approximately
`4.3811669×10⁻⁴`. Halving the difference step reduces the disagreement
from about `2.5×10⁻⁸` to about `6.3×10⁻⁹`.

For the full compact gauge loop, the connection predicts approximately
`7.0197740×10⁻⁶` radians. Kato transport discretizations give:

| Steps | Transport phase | Absolute phase-factor error |
| --- | ---: | ---: |
| 64 | 6.8054808 × 10⁻⁶ | 2.14 × 10⁻⁷ |
| 128 | 6.9670297 × 10⁻⁶ | 5.27 × 10⁻⁸ |
| 256 | 7.0066403 × 10⁻⁶ | 1.31 × 10⁻⁸ |

These are floating-point checks, not interval proofs or a continuum
extrapolation. The analytic claims and exact scalar margins are stated
separately above.

## 8. The resulting research target

We now have a constructive finite solution of gauge invariance and phase
integrability on the restricted domain. The remaining measure problem
is more specific: use anomaly cancellation to choose the transverse
current so that locality and lattice symmetries hold uniformly, then
extend the intended gauge and topological sectors.

The first concrete check for a replacement is the persistent direction-0
response above. Any claimed locality improvement should retain the Ward,
curvature, and loop tests while controlling that response with a bound
uniform in lattice size.

The useful principle remains compatibility of quantum amplitudes across
changes of description, with locality imposed as an independent physical
constraint. Ward compatibility alone admits the entire current family
proved above; it does not select a unique microscopic law or a TOE.

The [formal source](UnifiedTheory/Audit/KFCausalGaugeDressedMeasure.lean)
prints 22 main-theorem axiom audits. The integrated `lake build` passed
all 8,919 jobs with no warnings from the new module. Its theorem audits
use only `propext`, `Classical.choice`, and `Quot.sound` where needed.
The complete executable, including the growing-slab probe, passed with
runtime warnings treated as errors. All four recorded source hashes
match, and `git diff --check` passes. Reproduce with:

```sh
lake env lean UnifiedTheory/Audit/KFCausalGaugeDressedMeasure.lean
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/gauge_dressed_measure_audit.py --output data/gauge_dressed_measure_audit.json
lake build
```

Do not overlap Lean or Lake processes for this repository.
