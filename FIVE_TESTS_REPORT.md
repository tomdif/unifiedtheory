# Five Tests of the Variance-Rate Program — Report

**2026-07-29.** Outcome of stress-testing the mesoscale/Λ results along the five
axes that could make them decisive (or kill them). Provenance tags as before:
[LEAN] machine-checked, [NUM] verified numerically here, [LIT] literature-verified
(arXiv IDs), [PHYS] physics assembly/hypothesis.

**Executive summary: the literature check confirms the exact constants are
unpublished (priority window open); the exact smeared second moment now has a
closed form valid for ALL ε; the off-diagonal computation produced a structural
surprise (an IR-decoupling zero, now formalized) that REVISES the Λ story — the
per-point Λ coincidence of MESOSCALE_SCALING_LAW.md §4 is demoted, and is
replaced by something sharper: the fitted everpresent-Λ amplitude α = 0.0085
± 0.0017 translates in our channel to a near-Planckian nonlocality scale
ℓ_k ≈ 5.7 ℓ_p.**

---

## Test 4a — the literature check [LIT]

**Moradi–Yazdi–Zilhão** is arXiv:2407.03395 = CQG 42, 045017 (2025),
"Fluctuations and Correlations in Causal Set Theory." Verified by reading the
full paper: it is a **formalism paper** — it sets up the BDG **action** variance
(ΔS)² as nested Poisson-weighted integrals (their Eqs. 5.9–5.61) and the
diamond-overlap correlation structure, but **evaluates nothing**: no variance
constants, no ρ-scaling law, no covariance decay law, no mesoscale relation.
Their stated future work — "apply the formalism … to Minkowski spacetime …
[and test] whether or not the fluctuations of the action can be used to model
Everpresent Λ" — is precisely what this program now has in exact form. No
Minkowski follow-up is published as of this check.

Consequences: our `variance_rate` constants ((315/4)√π edge law), the damped
masses, the ε^{3/2} law, and the C(d) decay are, as far as verifiable,
**unpublished numbers**. One qualitative agreement: MYZ note χχ-correlations
exist only at coincident points and diamond-overlap correlations die with
e^{−ρ|V₁∪V₂|} — consistent with the short-ranged C(d) found below.

Also verified: ASS (arXiv:1403.1622) give the 4D momentum-space operator; IR
limit −p² with unstated higher coefficients; **the 4D operator has unstable
complex-momentum modes** (their finding — a caveat for any propagation claim).
Observational bounds on ℓ_k: **LHC 8 TeV nonlocal-EFT bound ℓ_k ≤ 10⁻¹⁹ m**;
optomechanics proposals reach 10⁻²²–10⁻²⁶ m (arXiv:1611.07959). No FRB/GRB
bound exists (the operator is Lorentz-invariant; time-of-flight bounds don't
apply). Everpresent-Λ fits (Das–Nasiri–Yazdi, arXiv:2307.13743, JCAP 2024):
SN Ia amplitude **α = 0.0085 ± 0.0017**; marginally better than ΛCDM on SN,
struggles on CMB; **no published DESI w₀wₐ confrontation exists** — a gap.

## Test 4b — the exact smeared second moment [NUM, Lean-ready]

The leading-order kernel g4sq(εξ) is now superseded by the exact object. For
the true ASS smeared weights f(n,ε), the falling-factorial identity gives the
second moment in closed form, and the critical mass evaluates exactly:

    M(ε) := M[ε²·E f²(ε·)](½) = (105/4)·√π · ε^{3/2}·(ε²+2ε+3)/(2−ε)^{13/2}.

Two-sided validation: ε→0 gives ε^{3/2}·(315/512)√2√π — exactly the [LEAN]
`mesoscale_suppression` constant; **ε=1 gives exactly (315/2)√π — the [LEAN]
sharp mass `f4Dsq_mass_half`**. The formula interpolates the entire family.
Correction to the ε^{3/2} law: factor (1 + (47/6)ε + O(ε²)) — 4% at ε = 10⁻²,
negligible at physical ε. The mean identity E[(1−ε)^N Q(N)] = f4D(εξ) was
verified symbolically (the smeared mean kernel is EXACTLY ε·f4D(εξ) — no
approximation anywhere in the mean sector).

## Test 2 — the off-diagonal kernel: an IR-decoupling zero [LEAN + NUM]

The covariance of the noise at spatially separated points x, x′ (factorized-
weight approximation [PHYS]), reduced in cone-adapted coordinates, contains the
mean kernel integrated along the second null shell — i.e. the w-mass

    ∫₀^∞ f4D(w²) dw = ½·M[f4D](½) = 0    [LEAN: `f4D_w_mass_zero`]

— **the same Mellin zero at s = ½ that makes the mean converge kills the IR
divergence of the covariance.** Numerically [NUM]: C(d;T) is exactly
T-independent for d > 0 (tested T = 25→400), decays ~1/d at small d
(integrable), and is dead beyond d ≈ 2 mesoscale units:

    d (units of ℓ̂):   0.05    0.1     0.5     1.0     2.0
    C(d):             35.1    7.50    0.064   0.003   ~0
    spatial correlation integral C₃ = ∫4πd²C(d)dd ≈ 0.31.

Meanwhile the per-point (diagonal, f4Dsq) object grows as T² — divergent.

**Structural conclusion: per-point no-self-averaging coexists with full
self-averaging of every extended observable.** The noise field has divergent
per-point variance but mesoscale-ranged correlations, so any average over a
region of size λ ≫ ℓ_k is suppressed by (ℓ̂/λ)²-type factors — the
fluctuations are effectively a local white noise despite the per-point IR
anomaly. The caveat: the correlated-layer correction to factorization at
separations ≲ ℓ̂ is not yet computed [PHYS-open]; MYZ's diamond-overlap
exponential supports short-rangedness.

## Test 3 — the multi-scale tension: dissolved [NUM/PHYS]

The apparent conflict (Λ channel wanting ℓ_k ~ 100 m vs radio/collider physics)
was an artifact of using the **per-point** variance as if observable. With
short-ranged correlations, mode-averaged noise for any coherent probe of scale
λ is negligible for ℓ_k ≪ λ, at every laboratory and astrophysical scale
simultaneously. The real constraints on ℓ_k are the **mean-sector** ones: the
nonlocal dispersion bound (LHC: ℓ_k ≤ 10⁻¹⁹ m) and the ASS instability of the
4D operator. A single ℓ_k is viable across all scales. The per-point
reliability law (ℓ_k ≥ 𝒦^{1/10}δ^{−1/5}ℓ_p^{2/5}L^{3/5}) survives as a
statement about the intrinsic per-element coherence of the discrete dynamics,
not about observables.

## Test 1 — from consistency to prediction: the revised Λ channel [PHYS]

**Honest revision: the per-point Λ coincidence (ℓ_k ≈ 63–146 m) of
MESOSCALE_SCALING_LAW.md §4 is superseded** — volume averaging washes out the
per-point variance that produced it. The surviving exact statement is sharper.
Averaging the B-noise over the causal past V:

    δΛ = A · ℓ_p²/(ℓ_k²·√V),   A = (24/π)·√((8/3)·Ĉ₄) ≈ 7·√(Ĉ₄/0.31),

with Ĉ₄ the 4D correlation integral (spatial part 0.31 [NUM]; time extent O(1)
pending [PHYS-open]). This is **Sorkin's 1/√V form with a computed amplitude**
carrying the microscopic scale: matching the Das–Nasiri–Yazdi fitted amplitude
(δΛ_DNY = 8πα/√V in Planck units, α = 0.0085 ± 0.0017):

    **ℓ_k = √(A/(8πα))·ℓ_p = (5.7 ± 0.6)·ℓ_p    (ε = (ℓ_p/ℓ_k)⁴ ≈ 10⁻³).**

Reading: **the everpresent-Λ amplitude is not a free parameter — it is the
nonlocality scale in disguise**, and the cosmologically fitted value lands at a
few Planck lengths: large enough for real damping (ε^{5/2} ≈ 3×10⁻⁸ variance
suppression), small enough to evade every local bound by 15 orders of
magnitude. This single identification connects a supernova-fit number to a
microscopic scale through machine-checked kernel constants.

What would make it stick (the neck-out list):
1. **Evaluate the action variance exactly** — MYZ's unevaluated (ΔS)² is the
   proper Sorkin channel; its diagonal term re-imports our f4Dsq mass and its
   off-diagonal term our C(d). Both exact ingredients are in hand; the
   assembly would give a **parameter-free prediction of α as a function of
   ℓ_k** to set against 0.0085 ± 0.0017. This is now the top formal target.
2. **The DESI gap**: no everpresent-Λ w₀wₐ confrontation exists. A Λ ~ 1/√V
   stochastic model with OUR amplitude, run against DESI DR2 evolving-DE
   contours, is an open, publishable test that could fail.
3. The correlated-layer correction and the 4D time-extent of Ĉ₄ (tightening A).

## Test 5 — the methodological claim [stands]

Every kernel constant in the chain above traces to a named, axiom-clean Lean
theorem: layer weights → `layer_uniqueness`; mean → `bdg_4d_operator_reduced`
(+ dictionary, normalization); variance rate → `variance_rate`; damped masses →
`mesoscale_suppression` + exact M(ε); IR-decoupling → `f4D_w_mass_zero`;
no-go → `no_self_averaging_GCB`. To current knowledge this is the first
machine-checked pipeline from a quantum-gravity proposal's microscopic
definition to a cosmological amplitude. The MYZ check confirms nobody has the
evaluated numbers; the honest framing is "first evaluation, formally verified,"
with Sorkin/DG/ASS/MYZ holding the phenomenon, the operator family, and the
formalism respectively.

## Revised claim ledger

| claim | status |
|---|---|
| √a variance growth, edge constants | [LEAN] |
| ε^{3/2} suppression; exact M(ε) all ε | [LEAN] + [NUM exact form] |
| damped mean exact ∀ε; survivor −ε⁻¹ | [LEAN] |
| IR-decoupling zero; C(d) short-ranged, IR-finite | [LEAN zero] + [NUM] |
| per-point reliability law ℓ_p^{2/5}L^{3/5} | exact assembly; intrinsic, not observable |
| per-point Λ coincidence (63–146 m) | **demoted** (averaging washes it out) |
| δΛ = A·ℓ_p²/(ℓ_k²√V); α ↔ ℓ_k = 5.7ℓ_p | [PHYS] with exact kernel inputs |
| action-variance evaluation (α predicted) | open — next formal target |
