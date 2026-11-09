# A positive finite Weyl measure and the two-gap locality boundary

Date: 2026-09-09

Follow-up: [the radial reconstruction](RADIAL_MEASURE_RECONSTRUCTION.md)
avoids the Dirac inverse and has a locality bound controlled by the
Wilson kernel alone. Its growing-time diagnostic and retained phase
improve on this positive-measure benchmark, but it has an explicit Ward
defect whose gauge-invariant local correction remains to be constructed.

The [tree-dressed measure](GAUGE_DRESSED_MEASURE.md) has a persistent
remote-link response in the measured growing slabs. We now construct a
replacement directly from the invertible Dirac operator. Its Weyl matrix
is positive, its current satisfies the Ward and projector-curvature
identities, and its closed-loop phase has the required integrability.
In the largest repeated probe its summed hypercharge response is about
11,200 times smaller.

An analytic estimate explains what this improvement can establish:
exponential decay of the two-link current response, uniformly in volume,
requires both a Wilson-kernel gap and a Dirac gap in this construction.
The tested slabs have both. The Dirac gap closes when the antiperiodic
time direction grows. An exact inverse then has entries of magnitude
1/2 at arbitrarily large separation. This rules out a uniform exponential
bound for that inverse; it does not alone rule out cancellations in the
complete measure current.

The result is a finite gapped-domain construction and a sharper locality
test, not a completed physical chiral theory. Making the determinant
positive discards its entire phase. Preservation of the desired chiral
continuum physics has not been established. Twenty-two main Lean audits
cover the algebra and exact counterexamples below. Smoothness, spectral
functional calculus, differentiation, loop assembly, and the analytic
locality estimate are explained here rather than formalized in Lean.

## 1. Construct the basis directly from D

Let D be invertible, P an orthogonal projector, and B the fixed
antifermion projector, with

\[
 DP=BD,\qquad R=D^{-1}.
\]

Choose a fixed orthonormal basis B₀ of ran B. Define

\[
 N=B_0^\dagger R^\dagger R B_0,\qquad
 S=N^{-1/2},\qquad V_D=RB_0S.
\]

N is positive definite: for nonzero v, `v†Nv=‖RB₀v‖²>0`.
Its positive inverse square root exists and varies smoothly while D
remains invertible. The intertwining identity gives `PR=RB`. Therefore

\[
 PV_D=V_D,\qquad V_D^\dagger V_D=SNS=I,
 \qquad B_0^\dagger DV_D=S>0.
\]

Invertibility of D also gives `rank P=rank B`, so V_D spans the whole
chiral domain. In particular,

\[
 Z_+(U)=\det S>0.
\]

The inverse intertwining, range, isometry, and Weyl-matrix equalities
are Lean theorems with the displayed algebraic hypotheses. Existence and
positivity of the analytic Gram factor are the finite-dimensional
spectral argument just given. No tree or reference free-field projector
is needed for this basis. The domain is the open set where the Wilson
sign is defined and D is invertible; it excludes zero modes.

For a gauge transformation G commuting with B, put `g_B=B₀†GB₀`.
Then `N→g_B N g_B†`, `S→g_B S g_B†`, and

\[
 V_D(U^g)=G V_D(U)g_B^\dagger.
\]

Thus its Weyl matrix changes by conjugation and its determinant is gauge
invariant. The numerical audit checks this direct basis for all five
supplied hypercharge blocks. This algebra does not require anomaly
cancellation, which is one reason it cannot by itself establish the
physical massless chiral limit.

## 2. The phase correction and its current

On the previous nonvanishing determinant domain, let Z_tree be the old
Weyl determinant. A unit phase makes it positive:

\[
 \omega(Z)=\frac{|Z|}{Z},\qquad |\omega|=1,
 \qquad \omega Z=|Z|.
\]

Lean proves these identities for every nonzero complex Z. Multiplying
one column of the fermion basis by ω realizes the determinant correction.
The direct inverse basis above has the same determinant: orthonormal
bases of the same chiral spaces differ by unitary matrices, which leave
its absolute value unchanged. Both constructions therefore produce
`Z_+=|Z_tree|` on the common domain.

For a link variation η, write

\[
 K_\eta=\operatorname{Tr}(D^{-1}\delta_\eta D\,P),\qquad
 \delta_\eta\log Z=K_\eta-iJ_\eta.
\]

For a fixed antifermion basis, the second term follows by differentiating
`M=B₀†DV`, using `M⁻¹=V†RB₀`, and cycling the trace. A moving antifermion
basis subtracts its basis connection as in the preceding construction.
Because Z_+ is real and positive, its current is explicitly

\[
 \boxed{J_{+,\eta}=\operatorname{Im}
       \operatorname{Tr}(D^{-1}\delta_\eta D\,P).}
\]

Locally this is `J_+=J_tree+d arg Z_tree`. The scalar ω is globally
single-valued on the nonzero domain, even if arg Z winds. The added
one-form is closed and has periods in `2πℤ`; it need not be the derivative
of a globally single-valued real function. Its exponential around a loop
is one, so the determinant-line Wilson phase is unchanged. Equivalently,
the smooth global basis V_D directly supplies the Kato loop condition.
A positive determinant does not imply zero measure curvature or zero
measure holonomy: the imaginary part of K is canceled by J_+.

For a gauge tangent `δD=[X,D]`, matrix trace algebra gives

\[
 \operatorname{Tr}(R[X,D]P)=\operatorname{Tr}(X(B-P)).
\]

For `X=iq diag(α)` this is the prescribed anomalous Ward divergence.
The equality is formalized for arbitrary finite complex matrices with
explicit left/right inverse and intertwining hypotheses.

For two commuting field variations, put `X=Rδ₁D`, `Y=Rδ₂D`.
Differentiating `P=RBD` yields `δ₁P=[P,X]`, `δ₂P=[P,Y]`.
The remaining algebra is

\[
\begin{aligned}
 dK_{12}
 &=\operatorname{Tr}((YX-XY)P+Y[P,X]-X[P,Y])\\
 &=\operatorname{Tr}(P[X,Y])\\
 &=-\operatorname{Tr}(P[[P,X],[P,Y]]).
\end{aligned}
\]

Consequently

\[
 dJ_{+,12}=\operatorname{Re}\left(
 i\operatorname{Tr}(P[\delta_1P,\delta_2P])\right).
\]

Lean proves both trace reductions and the real/imaginary-part identity.
The identification with derivatives assumes the smooth family and
commuting variations specified above; it is not hidden in an axiom.

## 3. What a finite-range phase counterterm can change

For a real phase function f and additive field increments u,v, define

\[
 \Delta_{u,v}f(A)=f(A+u+v)-f(A+u)-f(A+v)+f(A).
\]

If f is unaffected by adding u, or unaffected by adding v, this mixed
increment is zero. Therefore it is zero for a finite sum of terms when
each term misses at least one of the two increments. Lean proves the
statement for arbitrary additive field spaces and finite sums.

Applied in a link-angle chart, a counterterm whose summands have bounded
spatial support cannot change the mixed response between links too far
apart to occur in one summand. Locality here means support in the
original links. Composing an otherwise short formula with a nonlocal
tree dressing does not meet this hypothesis.

For the actual probe links in all four slabs below, the audit enumerates
every elementary plaquette and verifies that none contains both links.
An arbitrary sum of differentiable functions of individual plaquettes
therefore contributes exactly zero to this distant mixed derivative,
regardless of its coefficients. A more general exponentially local phase
can change the response by its own exponentially bounded derivative.
The formal reverse-triangle bound is

\[
 |a+b|\geq |a|-\epsilon\quad\text{when }|b|\leq\epsilon.
\]

This would obstruct canceling a proved nonzero asymptotic tail with a
uniformly exponentially small correction. The old tree current has only
a finite numerical tail diagnostic, not such an asymptotic theorem.
The positive-phase correction is not assumed local relative to that tree
measure. Its resulting current is tested and bounded independently.

## 4. An analytic bound under two uniform gaps

Here is a sufficient bound for the first field derivative of J_+.
Work on finite four-dimensional periodic lattices, with the specified
antiperiodic fermion boundary allowed. Assume uniformly over the field
domain and lattice sizes that

\[
 \operatorname{spec}H_W\subset[-M,-h]\cup[h,M],\qquad
 \sigma_{\min}(D)\geq g>0.
\]

The Wilson hopping range, spin dimension, and charge are fixed. Its
single-link derivative is supported on the two endpoints of that link,
with norm bounded independently of volume. Distinct-link mixed
second derivatives of H_W vanish. These are properties of the explicit
operator in the executable, not consequences of an arbitrary matrix gap.

For any site-distance function f with Lipschitz constant one, conjugate
by the positive diagonal weight `W_μ(x)=exp(μf(x))`. Since the Wilson
kernel has eight directed nearest-neighbor hopping terms of norm at
most one, the Schur bound gives

\[
 \|W_\mu H_W W_\mu^{-1}-H_W\|\leq b(\mu),
 \qquad b(\mu)=8(e^\mu-1).
\]

Take a rectangular positive-spectrum contour Γ whose real sides are
`h/2` and `M+h/2`, and imaginary sides `±h/2`. Its length is
`ℓ=2M+2h`, and its distance from the spectrum is at least `h/2`.
If `b(μ)≤h/4`, the ordinary and conjugated resolvents are bounded by
`2/h` and `4/h`. From the contour formula for P and the resolvent identity,

\[
 \|W_\mu P W_\mu^{-1}-P\|
 \leq \frac{4\ell}{\pi h^2}b(\mu).
\]

Because `D=I+γ₅(2P−I)` and W_μ commutes with γ₅,

\[
 \|W_\mu D W_\mu^{-1}-D\|
 \leq \frac{8\ell}{\pi h^2}b(\mu).
\]

Choose any μ>0 such that

\[
 b(\mu)\leq\min\left(\frac h4,
                   \frac{g\pi h^2}{16\ell}\right).
\]

A second Neumann estimate then gives

\[
 \|W_\mu D^{-1}W_\mu^{-1}\|\leq\frac2g,
 \qquad \|D^{-1}(x,y)\|\leq\frac2g e^{-\mu d(x,y)}.
\]

These estimates apply to weights based at any site or link support, with
constants independent of the volume. They also bound weighted P and
all contour resolvents. Differentiating P inserts a local kernel
variation into its contour resolvent:

\[
 \delta_e P=\frac1{2\pi i}\oint_\Gamma
 (z-H_W)^{-1}(\delta_e H_W)(z-H_W)^{-1}\,dz.
\]

A second derivative at a distinct link f inserts `δ_f H_W` in either
resolvent. Differentiate the current explicitly:

\[
 \delta_f K_e=\operatorname{Tr}\left(
 -R(\delta_fD)R(\delta_eD)P
 +R(\delta_f\delta_eD)P
 +R(\delta_eD)(\delta_fP)\right).
\]

After using the contour formulas and cycling traces, each separated-link
term has two finite-support insertions, one at e and one at f, separated
by products of the uniformly weighted bounded operators above. Project
onto the two endpoint subspaces. Their ranks are bounded independently
of volume; the operators connecting them have an exponential bound in
the minimum endpoint distance. The trace is consequently bounded by a
fixed rank times the operator norm bounds, with the finite contour
length factors included. This avoids an extensive unbounded trace over
all lattice sites. The same-link term includes `δ_e²H_W` and is uniformly
bounded by the same finite-support argument.

There is therefore a constant C depending only on `(h,g,M,q)` and the
fixed local carrier such that

\[
 \boxed{|\delta_f J_{+,e}|\leq C e^{-\mu d(e,f)}.}
\]

The endpoint-projector bounds can absorb fixed endpoint diameters into C.
This is an analytic proof of a uniform two-link response bound on the
stated doubly gapped domain. It is not a Lean theorem or a claim that all
requirements of the physical chiral measure have been discharged.

The Wilson-gap ingredient is consistent with the established overlap
locality result of [Hernández, Jansen, and Lüscher](https://arxiv.org/abs/hep-lat/9808010).
The extra Dirac-gap requirement comes from the inverse in this particular
current; it is not needed just to make the overlap operator itself local.

### Apply the bound to the tested slabs

On `L×2×2×2` with time length two, free time momenta are `±π/2`.
The free overlap formula gives `D₀†D₀=2(1+B/ω)I`, with
`B=Σ_spatial(1−cos p_μ)≥0`. Thus `σ_min(D₀)≥√2`, uniformly in L.
For the raw weak fields `|θ_e|≤1/48`, `|q|≤6`, the previous perturbation
bounds give

\[
 \|H_W-H_{W,0}\|\leq\frac12,\quad h\geq\frac12,\quad
 M\leq\frac{15}{2},\quad \|P-P_0\|\leq\frac12,
 \quad\sigma_{\min}(D)\geq\sqrt2-1.
\]

These bounds also hold on their gauge saturation by unitary covariance.
The new direct basis needs no separate tree-slice Gram condition.
In particular the analytic estimate is uniform as the first spatial
length grows with the time length fixed at two. Its conservative constants
are not fitted to the numerical decay rates.

## 5. The repeated remote-link test

The field, seed, link orientations, charge multiplicities, and central
finite differences are the same as in the preceding audit. The probe is
the direction-1 link ending at `(0,1,0,0)`; the remote variation is the
direction-0 link ending at `(L/2,1,0,0)`. All five left-handed blocks
`(q,m)=(1,6),(−4,3),(2,3),(−3,2),(6,1)` are summed.

| L | Minimum endpoint distance | Old tree response | Positive-measure response |
| --- | ---: | ---: | ---: |
| 4 | 1 | 1.417 × 10⁻⁶ | −1.028 × 10⁻⁶ |
| 8 | 3 | 1.884 × 10⁻⁶ | −8.387 × 10⁻⁸ |
| 12 | 5 | 1.928 × 10⁻⁶ | −4.212 × 10⁻⁹ |
| 16 | 7 | 1.931 × 10⁻⁶ | −1.723 × 10⁻¹⁰ |

At L=16, the ratio of absolute responses is approximately 11,200.
Both `10⁻³` and `5×10⁻⁴` difference steps are recorded. The old L=16
sum is recomputed to verify the baseline rather than relying only on
stored numbers. These are float64 diagnostics, not interval certificates
or an asymptotic fit. Only the first spatial length grows in this table.

Independent consistency checks on `2⁴` give:

- Direct basis isometry, chiral range, positive Weyl matrix, and gauge
  covariance for each supplied hypercharge block: residuals below `10⁻¹⁰`
  (about `10⁻¹⁴` in the recorded run).
- Ward residual about `1.65×10⁻¹⁴`; gauge-change residual below `10⁻¹⁰`.
- Direct-basis connection versus Im K: error decreases from about
  `2.71×10⁻¹⁰` to `6.70×10⁻¹¹` as the step halves.
- Curvature about `2.2771455×10⁻⁴`; current-curl errors at steps
  `2×10⁻⁴`, `10⁻⁴`, and `5×10⁻⁵` are approximately
  `4.67×10⁻⁷`, `1.17×10⁻⁷`, and `2.92×10⁻⁸`.
- A physical field-space circle has current integral about
  `3.8904367×10⁻⁸`. Independent basis transport at 32, 64, and 128
  steps has phase-factor errors about `2.92×10⁻¹⁰`, `7.33×10⁻¹¹`,
  and `1.83×10⁻¹¹`.

The loop check includes both moving bases in the phase-corrected tree
realization. Its antifermion subspace is fixed, so its net closed-loop
transport is trivial. The nonzero projector holonomy remains present.
The direct construction and the corrected tree construction have the
same measure connection, as independently checked by differentiation.

## 6. Why the Dirac-gap assumption is a real boundary

Let the antiperiodic time length now be T. In the free zero-spatial-momentum,
`γ_time=+1` sector, the overlap operator is exactly

\[
 D(p)=1-e^{-ip},\qquad p=\frac{(2k+1)\pi}{T}.
\]

Its smallest singular value in that sector is

\[
 g_T=2\sin\left(\frac{\pi}{2T}\right)\longrightarrow0.
\]

The full Dirac gap is at most g_T, which already suffices to invalidate
a T-independent positive lower gap bound. This happens while the free
Wilson kernel remains uniformly gapped.

The inverse can also be solved exactly in position space. Let S shift
one step around the time circle with the antiperiodic sign, so `S^T=−I`.
Then

\[
 (I-S)^{-1}=\frac12\sum_{k=0}^{T-1}S^k,
 \qquad
 (I-S)^{-1}_{ij}=
 \begin{cases}\frac12,&j\leq i,\\-\frac12,&j>i.\end{cases}
\]

Equivalently, for `T=N+1` and `A_i=Σ_{j=0}^i a_j`, the unique solution is
`x_i=A_i−A_N/2`. It satisfies `x_i−x_(i−1)=a_i` in the bulk and
`x_0+x_N=a_0` at the antiperiodic boundary. Lean proves the bulk and
boundary equations, uniqueness on the finite interval, every delta-source
entry, and magnitude 1/2 at arbitrarily large separation. Exact SymPy
matrices of sizes 2, 4, 8, 16, and 32 verify both inverse products.

For fixed spatial cross-section, projection to zero spatial momentum is
a fixed finite sum. A uniform exponential bound on the full inverse in
time would imply one on this sector, contradicting its entries above.
A bound `C exp(−μr)` with fixed finite C and μ>0 cannot dominate 1/2 for
all r. Thus the inverse estimate used in section 4 cannot survive this
massless large-time limit.

This is not a proof that the complete J_+ has a nondecaying tail: the
trace, its imaginary part, and the anomaly-free charge sum can have
cancellations. Proving or refuting uniform locality of that full current
in the massless domain requires further work. Nor is the long-range
massless propagator itself a defect of a physical theory; it is precisely
why using its inverse-gap bound to justify a microscopic measure needs
care.

## 7. The physical selection criterion this exposes

The appropriate next target is a measure current whose short-distance
locality is controlled by the regulator, uniformly while physical fermion
gaps close. A massless propagator may be long-range. The measure's
regulator-local response must be established separately, with anomaly
cancellation doing actual work in the construction.

This is a requirement on the proposed microscopic theory, not a uniqueness
principle that determines its interactions or geometry. Positive Z_+
removes the imaginary part of the fermionic effective action. Gauge
invariance and loop compatibility alone do not justify discarding that
field-dependent phase. A local counterterm equivalence to the intended
physical chiral determinant has not been shown.

This distinction matches the established measure problem:
[Lüscher's Abelian construction](https://arxiv.org/html/hep-lat/9811032v2)
requires a local current as well as integrability and anomalous divergence;
the effective action of a chiral theory generally has an imaginary part.
Its anomaly-free Abelian construction is broader than this repo benchmark.
An [electroweak lattice construction](https://arxiv.org/abs/0709.3658) also
exists for all SU(2) topological sectors with vanishing U(1) magnetic flux.
The missing step here should not be described as a general absence of
such results in the literature.

For this repo, the concrete next supplier is a regulator-local anomaly
current and reconstruction of its measure, followed by a test with growing
time extent, the same Ward/curvature/loop checks, and control of the
intended chiral continuum phase. Dynamical continuous gauge fields,
physical parameter selection, Einstein dynamics, and empirical TOE closure
remain separate obligations.

## 8. Reproduce and inspect

- [Formal algebra](UnifiedTheory/Audit/KFCausalPositiveMeasure.lean)
- [Executable audit](scripts/positive_measure_audit.py)
- [Recorded results](data/positive_measure_audit.json)

```sh
lake env lean UnifiedTheory/Audit/KFCausalPositiveMeasure.lean
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/positive_measure_audit.py --output data/positive_measure_audit.json
lake build
```

Run Lean/Lake commands sequentially for this repository. The audit records
six source/data hashes, including the preceding locality baseline, and
separates exact controls from float64 results. No numerical threshold is
used as a substitute for a theorem.

Validation: the integrated `lake build` completed all 8,920 jobs. The new
module has no build warnings, and all 22 printed main-theorem audits use
only `propext`, `Classical.choice`, and `Quot.sound` where needed. The
complete Python audit passed with runtime warnings treated as errors;
all six recorded hashes match. `git diff --check` also passes. Existing
warnings elsewhere in the repository remain outside this change.
