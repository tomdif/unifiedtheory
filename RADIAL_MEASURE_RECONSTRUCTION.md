# A regulator-local radial current and its exact Ward defect

Date: 2026-09-09

The [positive-measure construction](POSITIVE_MEASURE_LOCALITY.md) used
`D⁻¹`, making its locality proof depend on a physical fermion gap. We now
implement a radial projector current that uses only the gapped Wilson
kernel. It remains defined when D has exact zero modes. An analytic
bound controls its two-link response uniformly as the fermion gap closes.

On the new `2×2×2×T` test, the positive-measure response remains about
`−2.61×10⁻⁶` at T=24, while the radial response is about `1.12×10⁻¹¹`.
The radial current has the correct curvature and tested loop transport,
and retains a nonconstant determinant phase. It does not yet satisfy the
Ward equation: its exact defect is the anomaly density averaged along
the radial path. We quantify that defect and construct a local pair-flux
primitive whose gauge variation exposes the remaining obligation.

This is a reconstruction component, not a completed gauge-invariant
chiral measure or TOE. The radial formula is the curvature term in
[Lüscher's measure construction, section 5.3](https://arxiv.org/html/hep-lat/9811032v2).
The additions here are its implementation in this repo, formal algebra
and integration-by-parts checks, analytic locality argument in our weak
potential domain, derivative-based diagnostics, and explicit failure
controls. No new general lattice-gauge existence theorem is claimed.

## 1. Build the connection without a Dirac inverse

Use the same overlap conventions:

\[
 P(A)=\frac{I+\operatorname{sign}H_W(e^{iA})}{2},\qquad
 D(A)=I+\gamma_5(2P(A)-I).
\]

Work in a star-shaped weak real-potential chart. A sufficient uniform
condition for all supplied charges is `|A_e|≤1/48`, `|q|≤6`:
`H_W(tA)` has gap at least 1/2 for every `0≤t≤1`, independently of lattice
size or the permitted periodic/antiperiodic fermion time boundary.
This follows from the earlier free Wilson gap and hopping perturbation
bound. It does not give a positive gap for D, and none is required here.

For constant field directions η,ζ define

\[
 F_A(\eta,\zeta)=i\operatorname{Tr}
       \left(P(A)[P'_A[\eta],P'_A[\zeta]]\right).
\]

The trace is real for Hermitian tangent matrices. Set

\[
 \boxed{J^{\rm rad}_A[\eta]
       =\int_0^1 t\,F_{tA}(A,\eta)\,dt.}
\]

The factor t accounts for varying the endpoint A: the variation of P(tA)
is `t P'_(tA)[η]`. Omitting this factor gives the wrong curvature and Ward
identities. The executable uses analytic projector derivatives throughout.

This current is the connection of the chiral basis obtained by Kato
parallel transport from the free projector along each ray tA. Equivalently,
it is the radial-gauge potential of F: `J_rad(A)[A]=0`. The basis is smooth
throughout this chart, since its construction needs only the projector
gap. Its determinant is allowed to vanish where D has physical zero modes.
A logarithmic determinant is not used to define the radial current.

## 2. Why its curvature is correct

If P²=P and A,B,C are projector tangents, each obeys `AP+PA=A`.
The reflection `Q=I−2P` obeys Q²=I and `QAQ=−A`. Therefore

\[
 QABCQ=-ABC,\qquad \operatorname{Tr}(ABC)=0.
\]

Lean proves the reflection and tangent identities and the vanishing trace
for arbitrary finite complex matrices. In particular,
`Tr(A[B,C])=0`. In the exterior derivative of F, the second derivatives
cancel by symmetry and the remaining cubic tangent traces vanish. Thus
F is closed. The radial homotopy identity then gives

\[
 dJ^{\rm rad}=F.
\]

One can see the endpoint calculation explicitly:

\[
 \delta_\eta J^{\rm rad}[\zeta]
 -\delta_\zeta J^{\rm rad}[\eta]
 =\int_0^1\frac{d}{dt}\left(t^2 F_{tA}(\eta,\zeta)\right)dt
 =F_A(\eta,\zeta).
\]

The cubic-trace algebra is formalized; the differential-form and Kato
assemblies here are analytic. On the star-shaped chart, equal curvature
also fixes the closed-loop Wilson phase relative to the Kato connection:
their difference is a closed one-form on a contractible domain. This does
not establish compatibility across all compact-potential identifications
or topological sectors outside the chart.

## 3. The Ward defect, including its sign

Keep the earlier link orientation: a gauge increment is
`(Bω)_e=ω_head−ω_tail`, and `δ_ωP=[X,P]` with
`X=iq diag(ω)`. Write the site density

\[
 a_q(A,x)=q\operatorname{tr}_{\rm spin}(P_q(A)-P_+)(x,x).
\]

The desired Ward contraction is `J_A[Bω]=−〈ω,a_q(A)〉`.
The formal gauge-direction curvature identity, with its arguments swapped,
gives

\[
 F_{tA}(A,B\omega)
 =i\operatorname{Tr}(X\partial_tP_q(tA))
 =-\frac{d}{dt}\langle\omega,a_q(tA)\rangle.
\]

Consequently

\[
 \boxed{J^{\rm rad}_A[B\omega]
       =-\langle\omega,a_q(A)\rangle
         +\left\langle\omega,\int_0^1 a_q(tA)dt\right\rangle.}
\]

The scalar integration-by-parts identity is checked in Lean with actual
`HasDerivAt` and interval-integrability hypotheses. It is not an assumed
Ward equation. The numerical audit independently evaluates the current
on gauge directions and compares it to the endpoint and integrated
projector densities, separately for each charge and for the complete sum.

Define the average density `ā(A)=∫₀¹a(tA)dt`. Cartan's identity, the
curvature equation, and the gauge-direction identity further give

\[
 \delta_{B\omega}J^{\rm rad}_A[\eta]
 =\delta_\eta\langle\omega,\bar a(A)\rangle.
\]

Thus the failure of current gauge invariance and the extra Ward term
are two forms of the same missing correction.

A gauge-invariant local link current k(A) with divergence a(A) would
supply a real phase functional

\[
 C(A)=\int_0^1\langle A,k(tA)\rangle dt.
\]

With summation by parts `〈Bω,k〉=−〈ω,div k〉`, its gauge derivative is
`δ_(Bω)C=−〈ω,ā〉`. Adding dC repairs the Ward equation and gauge invariance
without changing curvature or contractible-loop phases. Both locality
and gauge invariance of k are necessary in this argument; a generic
inverse of the divergence operator is insufficient. This identifies the
specific missing supplier rather than assuming it into the construction.

## 4. Locality controlled only by the regulator

Assume `spec H_W(tA)⊂[−M,−h]∪[h,M]`, with fixed h>0, fixed local spin
carrier, fixed charge bound, and `sup|A_e|≤A_max`. Use the site weights and
positive-spectrum contour from the previous note. If
`8(e^μ−1)≤h/4`, weighted Wilson resolvents are uniformly bounded by `4/h`.
Their contour integral gives exponentially local P. A link derivative
inserts `δ_eH_W` between two resolvents, supported on the endpoints of e.
Two derivatives insert two such terms, with an extra single-link second
derivative when the links coincide. All bounds depend on h,M,q, not on
a smallest singular value of D.

For the curvature coefficient `F_(k,e)`, cycling the trace leaves two
finite-support insertions. Endpoint projections and the weighted
resolvent bounds give

\[
 |F_{k,e}|\leq C_1e^{-\mu d(k,e)}.
\]

Differentiating it at f gives three insertions (or coincident-link
terms). Products connecting their supports give an exponential bound in
the length of a shortest connected tree spanning k,e,f. The constants
are uniform in volume. The trace of three first projector tangents is
zero by the formal theorem, though locality does not require using that
cancellation for an upper bound.

Since

\[
 J^{\rm rad}_e(A)=\int_0^1t\sum_k A_kF_{k,e}(tA)dt,
\]

one obtains

\[
 \delta_fJ^{\rm rad}_e
 =\int_0^1\left(t F_{f,e}(tA)
             +t^2\sum_k A_k\delta_fF_{k,e}(tA)\right)dt.
\]

A connecting-tree length is at least both d(e,f) and d(k,e), up to fixed
endpoint diameters. Half of its exponential decay can bound each distance.
The sum over k is then uniformly finite: the number of links at distance r
on these four-dimensional tori is bounded by a fixed polynomial in r,
independently of the torus lengths. Thus

\[
 \boxed{|\delta_fJ^{\rm rad}_e(A)|\leq
 C(h,M,q,A_{\max})e^{-\mu d(e,f)/2}.}
\]

This is an analytic two-link response bound, not a Lean theorem. It
survives exact zero modes of D. Its hypotheses concern bounded real
potentials and their entire radial paths; the uncorrected J_rad is not a
current on all compact gauge orbits. Those qualifications are essential.

## 5. A local pair-flux primitive and why it is not the needed k

Let `K_t=[∂_tP_t,P_t]`. The Kato identity gives
`∂_tP_t=[K_t,P_t]`. For matrix coordinates x,y define

\[
 f_t(x,y)=(K_t)_{xy}(P_t)_{yx}-(P_t)_{xy}(K_t)_{yx}.
\]

Lean proves

\[
 f_t(x,y)=-f_t(y,x),\qquad
 \sum_yf_t(x,y)=(\partial_tP_t)_{xx},\qquad
 \sum_{x,y}f_t(x,y)=0.
\]

Summing internal spin indices and integrating qf_t along the ray gives
a pair-flux divergence equal to `a_q(A)−a_q(0)=a_q(A)`. The free site
density is zero. Since P_t and K_t have uniform exponential bounds under
the stated conditions, this flux is local in the supplied potential.
It is a useful transgression identity without a Dirac inverse. It is not
yet the required gauge-invariant nearest-neighbor link current.

If both K and P transform by the same fixed diagonal conjugation, the
pair flux is invariant; Lean proves this pointwise. A gauge transformation
of the radial path uses the moving frame `G_t=exp(tX)` instead. Its
transformed generator contains the additional term

\[
 K_t\longmapsto G_t\bigl(K_t+[[X,P_t],P_t]\bigr)G_t^{-1},
 \qquad [[X,P],P]=XP+PX-2PXP.
\]

The extra term changes the pair flux. Its divergence is zero for diagonal
X, because `[X,P]_(xx)=0`. Both the generator formula and the zero
divergence are formalized. The executable supplies an exact rank-two,
four-coordinate counterexample: take
`v=(1,1,1,1)/2`, `w=(1,i,0,−1−i)/2`, `P=vv†+ww†`, and
`X=i diag(1,2,−1,3)`. Its flux change is

\[
 \begin{pmatrix}
 0&-1/4&1/16&3/16\\
 1/4&0&-1/8&-1/8\\
 -1/16&1/8&0&-1/16\\
 -3/16&1/8&1/16&0
 \end{pmatrix}.
\]

Every row sums to zero but the matrix is nonzero. This example prevents
mistaking a local divergence solution for a gauge-invariant primitive.
It does not prove that a suitable primitive cannot be constructed.

## 6. What the hypercharge cancellation actually removes

In our explicit Euclidean gamma representation, `C=γ₁γ₃` obeys
`Cγ_μ* C†=γ_μ`, `Cγ₅* C†=γ₅`, and `CC*=−I`. Exact SymPy matrices check
these identities. Functional calculus then gives

\[
 P_q(-A)=C P_q(A)^*C^\dagger.
\]

The real local spin trace of P is therefore even in A. The numerical
matrix audit also checks this charge-conjugation relation directly.
For a fixed ray, write the charge-one unweighted density as f(s), where
f(0)=0 and f is even and smooth. Each charged anomaly density is

\[
 a_q(sA)=qf(qs)
        =\tfrac12 f''(0)q^3s^2+O(q^5s^4).
\]

The supplied multiplicities and integer charges obey

\[
 \sum_qm_qq=0,\qquad \sum_qm_qq^3=0,\qquad
 \sum_qm_qq^5=4320.
\]

Lean verifies cancellation of arbitrary linear/cubic charge terms and
retention of a general remainder. It also proves that bounds
`|r(q)|≤C|q|⁵|s|⁴` imply

\[
 \left|\sum_qm_qr(q)\right|\leq11436\,C|s|^4,
 \qquad11436=\sum_qm_q|q|^5.
\]

Taylor's theorem supplies this remainder hypothesis when the fourth
derivative of f is bounded on the charge-scaled interval. Contour
resolvent differentiation provides such a volume-independent bound on
our weak-potential domain. The Taylor/functional-calculus assembly is
analytic, while the weighted cancellation and remainder inequality are
formal. The averaged Ward defect has the corresponding fourth-order
bound with an additional integral factor `∫₀¹t⁴dt=1/5`.

The actual overlap density decreases by approximately a factor of 16
when the field is halved, consistent with this fourth-order behavior.
The measured endpoint-density norm ratios are 15.8798 and 15.9701.
For the fixed gauge test direction, the integrated Ward defect is about
`9.04×10⁻⁸`, `5.70×10⁻⁹`, and `3.57×10⁻¹⁰` at field scales 1, 1/2,
and 1/4. Direct current contractions agree with these predicted defects;
the remaining discrepancies are numerical error.

The defect remains nonzero. The fifth moment is not a new four-dimensional gauge
anomaly coefficient, and a nonzero local density remainder does not mean
that the Standard Model anomaly fails to cancel. The remaining density
must be represented by a suitable gauge-invariant local divergence.

## 7. Reproducible closing-gap and phase tests

The new test grows Euclidean time, keeping the spatial cross-section
fixed at `2³`. Potentials use seed 2026090902, are bounded by 0.018, and
repeat a fixed two-site pattern in time. Probe the direction-0 link ending
at `(0,0,0,0)` and vary the direction-1 link ending at `(0,0,0,T/2)`.
Their minimum endpoint distance is T/2. Both currents use exactly the
same fields and the five supplied charge blocks.

| T | Distance | Positive-measure response | Radial response |
| --- | ---: | ---: | ---: |
| 4 | 2 | −2.792 × 10⁻⁶ | 8.983 × 10⁻⁷ |
| 8 | 4 | −5.083 × 10⁻⁶ | 1.897 × 10⁻⁷ |
| 12 | 6 | −3.714 × 10⁻⁶ | 1.898 × 10⁻⁸ |
| 16 | 8 | −3.004 × 10⁻⁶ | 1.685 × 10⁻⁹ |
| 24 | 12 | −2.608 × 10⁻⁶ | 1.119 × 10⁻¹¹ |

The charge-six Dirac gap decreases from about 0.767 to 0.132, while every
measured Wilson gap stays above 0.9. The positive-measure data are finite
evidence of a remaining locality issue on this family, not a proof
against every possible exponential bound. Growing only time is not a
four-dimensional continuum limit. The radial locality claim rests on
the separate analytic estimate in section 4, not a fitted table.

The responses in this table use analytic second projector derivatives.
In an eigenbasis of H_W, first derivatives use divided differences only
between eigenvalues of opposite sign. For the mixed derivative P_ab,
its opposite-sign blocks are fixed by

\[
 [H,P_{ab}]=-[H_a,P_b]-[H_b,P_a]-[H_{ab},P].
\]

Its same-sign blocks are fixed by

\[
 P_{ab}P+PP_{ab}+P_aP_b+P_bP_a=P_{ab}.
\]

Thus degenerate eigenvalues within either spectral cluster cause no
singular division. The executable checks both matrix identities and
independent central differences at three step sizes. Radial integration
uses four Gauss nodes, with eight-node checks for every charge at T=24.
Independent finite differences of both currents at the final volume
provide another control. These are float64 checks, not interval proofs.

The same implementation also evaluates the radial current at the free
periodic field on `2×2×2×4`. Four constant spinors are exact Dirac zero
modes analytically; their numerical residual is below `10⁻¹²`. The Wilson
gap is one, and the radial current remains defined and zero there.

The independent [phase audit](scripts/radial_measure_phase_audit.py)
checks a physical field-space circle. Its radial current integral is
about `1.3688484×10⁻⁸`; Kato transport errors at 32, 64, and 128 steps
are about `7.85×10⁻¹¹`, `1.96×10⁻¹¹`, and `4.92×10⁻¹²`.
Along the ray from zero to the specified weak field, the full supplied
hypercharge determinant gains a relative phase about `7.3133×10⁻⁹`.
Independent radial basis transports agree with the logarithmic-derivative
integrals. This demonstrates retention of a nonconstant phase, not
physical continuum equivalence or gauge invariance of that phase.

## 8. The remaining construction

Latest follow-up: [the second cohomological descent](SECOND_COHOMOLOGY_COMPLETION.md)
now supplies the gauge-invariant primitive and its phase correction on the
bounded weak Abelian chart, with a separate analytic locality argument.
The compact-field and sector compatibility obligations remain open.

The [first local cohomology descent](LOCAL_COHOMOLOGY_DESCENT.md)
implements an invariant divergence component and retains explicit
field-strength and winding remainders. The second descent completes those
terms on the bounded weak chart. These follow-ups address the primitive
left missing by the pair-flux counterexample in this radial construction.

The radial component separates regulator-controlled locality and a
nonconstant phase from the anomaly correction. The
[established Abelian reconstruction](https://arxiv.org/html/hep-lat/9811032v2)
also requires global sector and finite-volume compatibility arguments.
Compact-chart assembly, continuous dynamical gauge fields, the intended
chiral continuum, gravity, and independently tested physical predictions
remain separate requirements for the proposed TOE.

Reproduce the formal and numerical components with:

```sh
lake env lean UnifiedTheory/Audit/KFCausalRadialMeasure.lean
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/radial_measure_audit.py --output data/radial_measure_audit.json
OPENBLAS_NUM_THREADS=1 python3 -W error::RuntimeWarning scripts/radial_measure_phase_audit.py --output data/radial_measure_phase_audit.json
lake build
```

Run Lean/Lake processes sequentially for this repository. The
[formal module](UnifiedTheory/Audit/KFCausalRadialMeasure.lean) audits
18 main results. The [main executable](scripts/radial_measure_audit.py)
and phase audit record exact controls and numerical results separately in
[the main report](data/radial_measure_audit.json) and
[the phase report](data/radial_measure_phase_audit.json), including source
hashes for their dependencies.

Validation: all 8,921 integrated build jobs pass, with no warnings from
the new module. Its 18 audited main results use only `propext`,
`Classical.choice`, and `Quot.sound` where needed. Both Python executables
passed with runtime warnings treated as errors. The main report's six
source hashes and the phase report's seven hashes match the final files;
`git diff --check` passes. Existing warnings elsewhere remain outside
this change. The numerical checks do not formalize the analytic locality,
Taylor, or global reconstruction arguments.
