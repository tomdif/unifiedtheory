# Local chiral measure: construction and phase compatibility

Date: 2026-09-09

The overlap regulator now has an explicit smooth basis construction on a
controlled patch of gauge fields, together with determinant transport around
closed loops. The construction includes a quantitative bound covering an
entire disk of external U(1) fields. Its algebra has 19 audited Lean theorems;
the norm estimates, differential equations, and smoothness arguments below
are analytic, not fully formalized in Lean.

This closes a local finite-dimensional basis problem. It does not construct
a spacetime-local, gauge-invariant fermion measure for the Standard Model,
integrate dynamical gauge fields, recover real-time QFT, or complete a TOE.
“Local patch” refers to a neighborhood in field space; locality of the
measure current in spacetime is a separate requirement.

## 1. The missing datum after constructing a projector

Use the normalization of [the overlap bridge](OVERLAP_CHIRALITY_BRIDGE.md):

\[
 D=I+\gamma_5\operatorname{sign}(H_W),\qquad
 \widehat\gamma_5=\gamma_5(I-D)=-\operatorname{sign}(H_W),\qquad
 P=\widehat P_-=(I+\operatorname{sign}(H_W))/2.
\]

A rank-k chiral basis is an N-by-k matrix V satisfying
`V†V=I`, `VV†=P`. Expanding a Grassmann field as `ψ=V c` defines its
integration measure only after fixing the determinant phase of V. A
field-dependent projector fixes the subspace, not this phase.

This is an implementation of established measure geometry. Lüscher's
[reconstruction framework, §§6–8](https://arxiv.org/html/hep-lat/9904009v2)
relates the measure connection to projector transport and separates its
local curvature condition from global loop compatibility. Kadoh and
Kikukawa's [electroweak construction](https://arxiv.org/abs/0709.3658)
constructs the required currents for all SU(2) topological sectors with
vanishing U(1) magnetic flux. Thus the corresponding task is not generally
unsolved in the literature; that construction has not been implemented or
proved for the repository's physical supplier. Their Dirac convention is
`D_paper=D_repo/2`, giving the same deformed chirality.

## 2. An explicit patch basis, with a sufficient bound

Let P and P₀ be orthogonal projections in a finite complex Hilbert space,
let W₀ be an orthonormal basis of `ran P₀`, and suppose

\[
 \rho=\|P-P_0\|_{\rm op}<1.
\]

Set

\[
 M=W_0^\dagger P W_0,\qquad
 \boxed{V(P)=P W_0 M^{-1/2}.}
\]

For every coefficient vector z,

\[
 \begin{aligned}
 z^\dagger Mz
 &=\|P W_0z\|^2\\
 &=\|z\|^2-\|(I-P)W_0z\|^2
 \ge(1-\rho^2)\|z\|^2.
 \end{aligned}
\]

Therefore M is positive definite, `||M^(-1/2)|| ≤ (1−ρ²)^(-1/2)`, and
direct multiplication gives `PV=V` and `V†V=I`. Restriction of P to
`ran P₀` is injective, as is restriction of P₀ to `ran P`; finite
dimensionality gives equal ranks. Consequently `VV†=P`. The positive
inverse square root is smooth on positive definite matrices, so a smooth
P produces a smooth basis throughout this patch. At P=P₀, V=W₀.

Lean proves the range and isometry algebra with the normalization identity
for `M^(-1/2)` as an explicit hypothesis. The positivity estimate,
functional calculus, equal-rank argument, spanning conclusion, and
smoothness are analytic steps here.

Under simultaneous changes `P→GPG†` and `W₀→GW₀`, M is unchanged and
`V→GV`, as Lean checks. Holding the chosen reference fixed does not give
this covariance automatically. This patch formula alone therefore does
not prove gauge invariance of the fermion measure.

On overlapping patches, two bases V and W have unitary transition
`T(V,W)=V†W`, with `V T(V,W)=W`. For a third basis Z of the same subspace,

\[
 T(V,W)T(W,Z)=T(V,Z),\qquad
 \det T(V,W)\det T(W,Z)=\det T(V,Z).
\]

These identities are formalized. They expose the determinant transition
phases which a global choice must reconcile; the cocycle identity does
not prove that those phases can all be removed.

## 3. Transport and the measure connection

Differentiate `P²=P` along a smooth path. With `A=Ṗ`,

\[
 AP+PA=A,\quad PAP=0,\quad K=[A,P],\quad K^\dagger=-K,
 \quad[K,P]=A,\quad PKP=0.
\]

Lean checks these algebraic implications. Finite-dimensional ODE existence
and uniqueness then give the analytic Kato evolution

\[
 \dot Q=KQ,\qquad Q(0)=I,\qquad
 Q^\dagger Q=I,\qquad P(t)Q(t)=Q(t)P(0).
\]

Unitarity follows by differentiating `Q†Q`. Differentiating `Q†P Q`
and using `[K,P]=Ṗ` shows that it remains P(0). In particular,
`Q(t)W₀` is a transported chiral basis.

For a closed projector loop, the determinant holonomy is

\[
 h=\det(W_0^\dagger Q(1)W_0)
   =\det(I-P_0+P_0Q(1)).
\]

For a smooth periodic basis V on that loop, define

\[
 \mathcal L_t=i\operatorname{Tr}(V^\dagger\dot V).
\]

Writing `V=QW₀ R`, with R unitary, gives
`Tr(V† dV/dt)=Tr(R† dR/dt)` because `PKP=0`. Since `V(1)=V(0)`, the endpoint
determinant of R is `h⁻¹`. Thus

\[
 \boxed{\exp\left(i\oint\mathcal L\right)=h.}
\]

For commuting field coordinates s,t, differentiating the connection gives

\[
 \partial_s\mathcal L_t-\partial_t\mathcal L_s
 =i\operatorname{Tr}\big(P[\partial_sP,\partial_tP]\big)
 =:\mathcal F_{st}.
\]

One way to see this is to expand the derivatives of `i Tr(V†dV)`;
mixed derivatives cancel, and the tangential frame-rotation terms cancel
under the trace. The remaining terms are
`i Tr((∂sV)†(I−P)∂tV−(∂tV)†(I−P)∂sV)`, which equal the projector
expression. Noncommuting variations require the corresponding bracket
term; the displayed formula is specifically for commuting coordinates.

The new formal gauge-direction identity is

\[
 \boxed{\mathcal F(P;[X,P],B)=-i\operatorname{Tr}(XB),}
 \qquad BP+PB=B.
\]

It follows by expanding the commutators, using `PBP=0`, and cycling the
trace. For a fixed infinitesimal gauge generator X and `B=δP`, its right
side is `−δ(i Tr(XP))`. This is a finite link between projector curvature
and variation of a trace density. It does not construct a current with
the required anomalous divergence or prove its spacetime locality.

Complementary chiralities satisfy
`K(I−P,−A)=K(P,A)` and

\[
 \mathcal F(P;A,B)+\mathcal F(I-P;-A,-B)=0.
\]

Both identities are formal. Pairing complementary sectors of the same
operator is vectorlike completion; it does not produce the desired
chiral Standard Model spectrum.

## 4. Exact controls: local existence does not imply zero holonomy

Take a rank-one projector in C² with the periodic basis

\[
 v(\phi)=\begin{pmatrix}\sqrt3/2\\ e^{i\phi}/2\end{pmatrix},
 \quad P(\phi)=v(\phi)v(\phi)^\dagger,\quad0\le\phi\le2\pi.
\]

Then

\[
 \mathcal L_\phi=-\tfrac14,\qquad
 h=e^{-i\pi/2}=-i,
 \qquad\|P(\phi)-P(0)\|^2=\tfrac34\sin^2(\phi/2).
\]

The whole loop lies in a single patch: its reference Gram matrix is
`1−(3/4) sin²(φ/2) ≥ 1/4`. There is a periodic smooth basis, yet its
parallel-transport holonomy is nontrivial. This is not a topological
obstruction to a basis on the patch.

The exact audit verifies the ODE for

\[
 Q(\phi)=\operatorname{diag}(1,e^{i\phi})
 \left(e^{-i\phi/4}P_0+e^{-3i\phi/4}(I-P_0)\right).
\]

At the endpoint, `Q(2π)=−iP₀+i(I−P₀)`. A zero candidate connection
would give holonomy 1 and fail the required equality.

Two further controls separate different issues. An orthogonal reference
has zero Gram matrix, so the patch formula fails outside its hypotheses.
On a parameter circle with constant P, the connection `dφ/2` has zero
curvature but holonomy −1, while Kato transport is I. Thus local curvature
agreement alone does not enforce global integrability on a noncontractible
parameter space. These are exact geometric examples, not simulations of
a physical gauge anomaly.

## 5. A controlled disk of actual overlap operators

The executable uses a periodic `2^4` lattice and charge-one external U(1)
links, giving a 64-dimensional Dirac carrier and a rank-32 chiral subspace.
It independently builds the same Wilson operator as the previous audit:

\[
 T_\mu\psi(x)=e^{i\theta_\mu(x)}\psi(x-\hat\mu),\quad
 S_\mu=P_{\gamma_\mu,+}\otimes T_\mu+
        P_{\gamma_\mu,-}\otimes T_\mu^\dagger,\quad
 H_W=\gamma_5\left(3I-\sum_{\mu=1}^4S_\mu\right).
\]

The field family is `θ=b+s f+t g`, with the arrays recorded reproducibly
by seed 9811032, `|b|≤0.12`, `|f|,|g|≤1`, and disk `s²+t²≤r²`,
`r=0.045`. The boundary is traversed counterclockwise. No gauge field
integration or non-Abelian background is included in this experiment.

The previous free-gap theorem and a norm perturbation estimate give

\[
 \eta=\sum_\mu\max_x\left(|b_\mu(x)|+
 r\sqrt{f_\mu(x)^2+g_\mu(x)^2}\right)<0.637,
 \qquad |H_W|\ge 1-\eta>0.363.
\]

These estimates apply throughout the disk. They use `|e^{iθ}−1|≤|θ|`;
they are bounds in the chosen gauge frame, not gauge-invariant
plaquette admissibility conditions.

A useful additional analytic estimate guarantees a single basis patch
for this whole disk. For a gapped Hermitian H with `|H|≥g₀`, the
off-diagonal block X of `dP` satisfies the Sylvester equation

\[
 H_+X-XH_-=(dH)_{+-},\qquad
 X=\int_0^\infty e^{-uH_+}(dH)_{+-}e^{uH_-}\,du.
\]

Hence `||dP||≤||dH||/(2g₀)`. Each link direction contributes at most
`√2` to the derivative norm per unit distance in the (s,t) plane.
Integrating along a chord from `(r,0)` to any disk point gives

\[
 \|P(s,t)-P(r,0)\|
 \le \frac{4\sqrt2\,r}{1-\eta}
 <0.701<1.
\]

In particular, the reference Gram matrix is uniformly bounded below
by `1−0.701² > 0.508`. Thus the local basis exists on the entire
specified disk, not just at sampled points. These tighter constants are
floating-point evaluations, not interval-certified bounds.

There is also an exact, looser guarantee independent of the sampled
arrays. From `|b|≤3/25`, `|f|,|g|≤1`, `r=9/200`, and `√2<10/7`,

\[
 \eta\le\frac{129}{175},\qquad g_0\ge\frac{46}{175},\qquad
 \|P(s,t)-P(r,0)\|\le\frac{45}{46}<1,\qquad
 M\ge\frac{91}{2116}I.
\]

The exact scalar arithmetic is checked symbolically. Combined with the
analytic operator estimates above, these inequalities establish patch
existence without relying on floating-point eigenvalues or margins.

For numerical transport between nearby projectors P and R, use

\[
 S=RP+(I-R)(I-P),\quad S^\dagger S=I-(P-R)^2,\quad
 U=S(S^\dagger S)^{-1/2}.
\]

Lean checks the Gram identity, intertwining, and commutation with P.
Positive functional calculus gives a unitary U intertwining the two
subspaces when `||P−R||<1`. Its restriction in orthonormal frames is
the unitary polar factor of `V_R†V_P`, which the audit computes by SVD.
For a smooth path, `U=I+[Ṗ,P]dt+O(dt²)`; products converge to the
Kato evolution. The higher observed convergence rate below is numerical.

For an independent curvature calculation, the code differentiates the
spectral projector using divided differences between positive and
negative eigenvalues. A central-difference check validates the derivative.
It then integrates `i Tr(P[∂sP,∂tP])` over the disk by polar quadrature.

| Boundary steps | Transport phase (radians) | Difference from curvature integral |
| --- | ---: | ---: |
| 32 | −1.0693031 × 10⁻⁷ | 5.42 × 10⁻¹⁰ |
| 64 | −1.0733681 × 10⁻⁷ | 1.35 × 10⁻¹⁰ |
| 128 | −1.0743841 × 10⁻⁷ | 3.39 × 10⁻¹¹ |
| 256 | −1.0746378 × 10⁻⁷ | 8.49 × 10⁻¹² |

The independent curvature integral is approximately `−1.0747227 × 10⁻⁷`.
The minimum observed kernel gap exceeds 0.9048, and the minimum observed
reference Gram eigenvalue exceeds 0.9983. Operator, tangent, basis, and
phase identities have residuals below `10⁻¹⁰`. Checks include independently
rebuilt gauge-transformed links, periodic changes of basis within the
chiral subspace, complementary-sector phase cancellation, and the
gauge-direction curvature identity.

The gauge transformation is fixed as a function of the loop parameters.
For parameter-dependent transformations, the connection gains additional
terms; invariance under those transformations is not established by this
test. No numerical residual here is an exact proof of a lattice anomaly
or of its absence.

## 6. Why the existing anomaly sums do not finish the measure

The existing [anomaly module](UnifiedTheory/LayerC/AnomalyCancellation.lean)
proves representation arithmetic for supplied Standard Model multiplets.
For the all-left-handed hypercharge convention `q=6Y`, the five species
have `(q,multiplicity)` equal to `(1,6), (−4,3), (2,3), (−3,2), (6,1)`.
Their exact sums obey

\[
 \sum_f m_f q_f=0,\qquad \sum_f m_f q_f^3=0.
\]

The new audit also constructs the five corresponding overlap projectors
with trivial SU(3) and SU(2) backgrounds. It scales the entire field
family, including both tangent directions, by `q_f/d`, and evaluates
the total curvature at the disk center. The results are:

| d | Sum of multiplicity-weighted projector curvatures |
| --- | ---: |
| 6 | −1.4604080 × 10⁻⁵ |
| 12 | −4.4237181 × 10⁻⁷ |
| 24 | −1.3714503 × 10⁻⁸ |

These finite-matrix values numerically exclude the zero connection for
this family despite the vanishing anomaly sums. They do **not** imply an
anomaly of the Standard Model. A valid measure connection can have
nonzero curvature. Nor does varying the field amplitude establish a
continuum limit or a universal scaling law.

The next supplier must implement a spacetime-local current with the
required gauge transformation and divergence properties, whose connection
matches this curvature and whose Wilson phases match determinant
transport on every relevant loop. A concrete next implementation target
is the anomaly-free Abelian current construction, followed by the
electroweak reconstruction on its stated admissible sectors. Geometry,
real-time reconstruction, physical matter selection, and empirical
predictions remain separate obligations.

## 7. Scope of the overarching principle

The useful selection requirement is that quantum amplitudes admit
consistent gluing across changes of description. Refinement requires
compatible observable histories; gauge changes require compatible
fermion determinant phases. Here that requirement becomes explicit
local curvature and global holonomy equations, rather than only a
slogan about symmetry.

This is a necessary consistency principle. It does not select a unique
microscopic action, gauge group, representation, or gravitational law.
The [quantum-refinement underdetermination proof](QUANTUM_REFINEMENT_PROOF.md)
continues to apply. The concrete progress is a constructed local basis,
verified phase diagnostics, and a sharper specification of the missing
measure current.

## 8. Reproduce and audit

- [Lean source](UnifiedTheory/Audit/KFCausalChiralMeasure.lean): 19 printed
  theorem audits, with only `propext`, `Classical.choice`, and `Quot.sound`
  where needed. No additional axioms or admitted proofs.
- [Executable audit](scripts/chiral_measure_audit.py): exact symbolic loop
  and controls, numerical overlap basis/transport, and hypercharge tests.
- [Machine-readable results](data/chiral_measure_audit.json): arithmetic
  labels, bounds, residuals, refinements, and source hashes.

The integrated `lake build` passed all 8,918 jobs. The new module has no
build warnings, and its 19 printed theorem audits use only the standard
axioms listed above. The exact/numerical executable passed, all three
recorded source hashes match, and `git diff --check` is clean.

```sh
lake env lean UnifiedTheory/Audit/KFCausalChiralMeasure.lean
OPENBLAS_NUM_THREADS=1 python3 scripts/chiral_measure_audit.py --output data/chiral_measure_audit.json
lake build
```

Do not overlap Lean or Lake processes for this repository.
