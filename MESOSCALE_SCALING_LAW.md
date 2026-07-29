# The Mesoscale Scaling Law and the Λ-Refinement Bound

> **REVISION NOTE (2026-07-29, same day):** the off-diagonal covariance
> computation (see FIVE_TESTS_REPORT.md) showed the noise correlations are
> short-ranged (IR-decoupling zero `f4D_w_mass_zero`), so volume averaging
> suppresses the per-point variance used in §4. The per-point Λ reading
> (ℓ_k ≈ 63–146 m) is SUPERSEDED by the averaged-channel identification
> ℓ_k ≈ 5.7 ℓ_p from the fitted everpresent-Λ amplitude. §§1–3 stand.

**2026-07-29.** The deliverable of the fluctuation campaign: the exact variance-rate
channel of the 4D causal-set d'Alembertian, assembled into (i) a mesoscale
reliability law with machine-checked constants and (ii) a quantitative refinement
of the everpresent-Λ prediction. Companion Lean units:
`KFCausalMinkowski4DVarianceRate.lean` (variance_rate, cross_channel_bound,
no_self_averaging_GCB), `KFCausalMinkowski4DMesoscale.lean` (g4sq_mass_half,
mellin_scale, damped moments/survivor, mesoscale_suppression). Numbers:
`mesoscale_numbers.py`.

## Provenance discipline

Every claim below is tagged:
- **[LEAN]** — machine-checked in this repo, axiom-clean (propext, Classical.choice,
  Quot.sound), `lake build` green.
- **[PHYS]** — standard physics assembly (Poisson/Campbell bookkeeping, ASS smeared
  operator conventions, everpresent-Λ identification). Not machine-checked; each
  such step is stated explicitly.

## 1. The machine-checked anchors [LEAN]

1. **Diagonal variance rate** (`variance_rate`): for box-supported profiles g,
   √a·∬(v−u)²·f4Dsq(au²v²)·g → (315/4)√π · (∫u·g(u,0)du + ∫v·g(0,v)dv) as a→∞.
   The undamped variance object grows as √a with exact edge constants; the cross
   channel dies like ln a/√a (`cross_channel_bound`).
2. **No-self-averaging no-go** (`no_self_averaging_GCB`): for ANY finite layer
   weights with w₀≠0 the variance kernel's critical Mellin mass Σwₙ²Γ(n+½)/n!
   is strictly positive. No weight choice cancels the fluctuation channel.
3. **Damped kernel masses** (`g4sq_mass_half`, `mesoscale_suppression`): the
   continuum smeared variance kernel g4sq = (f4D)² has M[g4sq](½) =
   **(315/512)·√2·√π ≈ 1.5422**, and the ε-damped mass is EXACTLY
   **ε^{3/2}·(315/512)√2√π** (`mellin_scale`: Mellin zeros and masses scale as
   ε^{−s}). The suppressed mass is still positive (`damped_variance_mass_pos`):
   damping suppresses polynomially, never cancels.
4. **Damped mean family exact** (`damped_moment_half/one/threehalf`,
   `damped_survivor`): the smeared mean kernel ε·f4D(εξ) keeps its Mellin zeros
   at s = ½, 1, 3/2 for EVERY ε > 0 — the damped family still converges to □ —
   and the survivor M(2) = −ε⁻¹ scales exactly so as to force the 1/ℓ_k²
   normalization of the damped operator.
5. **Dictionary** (committed operator chain): ξ = ρV, V = (π/24)τ⁴, τ⁴ = u²v²
   in null coordinates, so the kernel argument is a·u²v² with **a = πρ/24**;
   BDG prefactor 4/√6 gives unit coefficient for the mean (`bdg_4d_normalization`).

## 2. The physical assembly [PHYS, with exact ingredients]

ASS smeared operator at nonlocality scale ℓ_k (ε = ρ_k/ρ = (ℓ_p/ℓ_k)⁴):

    B_kφ(x) = (4/√6)ℓ_k⁻²[−φ(x) + ε Σ_{y≺x} f(n(x,y),ε)φ(y)].

The Poisson expectation of the smeared weights is EXACTLY ε·f4D(εξ) (falling-
factorial identity, no approximation) — so the [LEAN] damped-mean family applies
verbatim: ⟨B_kφ⟩ → □φ for every ε.

Atomic Campbell variance channel (the per-point diagonal noise; the dominant
channel — off-diagonal ⟨ξξ⟩ correlations are the queued next step):

    Var[B_kφ(x)] = (8/3)ℓ_k⁻⁴·ρ·∫d⁴y ε²E[f²](ρV(y))·φ(y)².

Cone reduction (identical measure chain as the committed mean proof: 4π angular ×
Jacobian ½ × r² = (v−u)²/4 → geometric constant **π/2**, argument a·u²v²), the
continuum kernel E[f²](ξ) → g4sq(εξ) at leading order in ε, and the [LEAN]
variance_rate applied at effective boost parameter εa give:

    **Var[B_kφ] = 𝒦 · (ℓ_p⁴/ℓ_k¹⁰) · E[φ²],   𝒦 = (105√3/64)·π ≈ 8.9273 (exact),**

where E[φ²] = ∫u·φ̄²(u,0)du + ∫v·φ̄²(0,v)dv is the null-boundary edge functional
of the (angle-averaged) squared field over the probed causal past. Per-point
fluctuation over mean, for a field configuration of coherence/support scale L
(E ~ φ²L², |□φ| ~ φ/L²):

    **σ(B_kφ)/|□φ| = √𝒦 · ℓ_p²·L³/ℓ_k⁵.**

The suppression relative to the sharp operator at the same ρ is
ε^{5/2}·(√2/256) — one power ε from the ℓ_k-normalization, ε^{3/2} from the
[LEAN] mass suppression. At fixed mesoscale the noise dies as ρ^{−1/2}: this
reproduces, now with exact constants, the Dowker–Glaser 2013 numerical
observation that damping rescues the operator.

## 3. The mesoscale reliability law

Requiring σ ≤ δ·|□φ|:

    **ℓ_k ≥ 𝒦^{1/10}·δ^{−1/5}·ℓ_p^{2/5}·L^{3/5},   𝒦^{1/10} = 1.2447.**

The exponents (2/5, 3/5) and the prefactor are the content — they follow from
the [LEAN] ε^{3/2} mass law + ε-normalization + √a rate. (Sorkin's 2007
heuristic gives a different exponent pair; the difference is that this is the
computed atomic Campbell channel of the actual BDG kernel, not a per-point
noise estimate.)

| probed scale L | ℓ_k minimum (δ=1) |
|---|---|
| 1 fm | 1.5×10⁻²³ m |
| 1 Å | 1.5×10⁻²⁰ m |
| 1 μm | 3.8×10⁻¹⁸ m |
| 1 m | 1.5×10⁻¹⁴ m |
| LIGO 4 km | 2.2×10⁻¹² m |
| LISA 2.5 Gm | 6.6×10⁻⁹ m |
| galaxy 30 kpc | 6.0×10⁻² m |
| Hubble radius | 73 m |
| particle horizon | 146 m |

Reading: any fixed ℓ_k has a fluctuation-domination crossover at
L\* = (ℓ_k⁵/(√𝒦·ℓ_p²))^{1/3}. Coherent propagation observed at scale λ demands
ℓ_k ≳ 1.24·ℓ_p^{2/5}λ^{3/5}; all laboratory and astrophysical coherence scales
are compatible with ℓ_k anywhere between ~10⁻⁹ m and the existing swerve/EFT
upper bounds — the law leaves a wide open window at local scales.

**Caveat [PHYS]:** this is the per-point variance. Mode-averaged noise (what an
interferometer measures) involves the spatial correlation of the fluctuation —
the off-diagonal Campbell/Mecke kernel — which is the queued next computation.
Per-point domination does not immediately imply observable decoherence.

## 4. The Λ-refinement bound

The everpresent-Λ channel is the constant mode: for φ ≡ 1, □φ = 0, and B_k·1 is
PURE fluctuation with an IR cutoff at the causal-past depth T (horizon). Its
edge functional is E[1] = T², so [PHYS identification δΛ ↔ σ(B_k·1)]:

    **δΛ(T) = √𝒦 · ℓ_p²·T/ℓ_k⁵,   √𝒦 = 2.9879.**

This is a 1/L² quantity — a cosmological-constant-type term — sourced by the
discreteness noise of the d'Alembertian itself. Two independent readings:

1. **Λ_obs fixes the mesoscale:** ℓ_k(Λ_obs) = (√𝒦·ℓ_p²T/Λ_obs)^{1/5}
   = **63 m** (T = Hubble radius) / **79 m** (particle horizon).
2. **Reliability saturation at the horizon** (δ = 1 in the law of §3 at L = T):
   ℓ_k = **73 m** / **146 m**.

The two readings agree to within a factor of 2 with NO tuned parameters. The
dimensionless statement is exact under the law:

    **Λ(T)·T² = δ(T)** — and observationally Λ_obs·T² = 2.1 (Hubble) / 21 (horizon).

That is: **the observed Λ sits at the reliability boundary δ = O(1–20) of the
BDG operator evaluated at the horizon** — Sorkin's Λ ~ 1/T² tracking, now with
the exact prefactor chain Λ(T) = √𝒦·ℓ_p²T/ℓ_k(T)⁵, 𝒦 = 105√3π/64, every kernel
constant machine-checked. The refinement over "Λ ~ ±1/√V": the amplitude is not
a free O(1); it is pinned to the variance-rate constants (315/512)√2√π and
(105√3/64)π, and it predicts the specific mesoscale ℓ_k(T) ∝ T^{3/5} (today
~10² m for the constant-mode channel).

**Falsifiable structure [PHYS]:** if the mesoscale is a single scale for all
channels, today's value ~10² m for the Λ channel coexists with local physics
because δ ∝ L³: at L = 1 AU, δ ≈ 10⁻⁴⁵·(ℓ_k/100 m)⁻⁵ — utterly negligible
locally, order unity only at the horizon. The model therefore predicts
Λ(T)·T² = O(1) at ALL epochs (everpresent-Λ phenomenology) with our fixed
prefactor — testable against Λ(z) reconstructions.

## 5. Literature position (per the binding calibration)

- The phenomenon (fluctuations grow with ρ; damping fixes it) is **Sorkin 2007 /
  Dowker–Glaser 2013**. Our contribution on that axis is only the proved-for-
  all-weights no-go (`no_self_averaging_GCB`) and the machine-checked masses.
- The GCB operator family is Aslanbeigi–Saravani–Sorkin; our finite-weights
  statement covers arbitrary finite layer families, and the smeared-kernel
  analysis here uses the ASS continuum kernel exactly.
- Belenchia et al. hold priority on curved −R/2 universality (separate campaign).
- **Moradi–Yazdi–Zilhão 2025** (fluctuations/correlations) must be read and
  cited before any write-up of §§2–4; the variance-rate constants and the
  (2/5, 3/5) mesoscale law with the Λ-saturation statement Λ·T² = δ are, to
  current knowledge, the numbers nobody else has published.
