# The intermediate-coupling band: what a mass-gap proof has to supply

Written 2026-11-06. This summarizes the block-convexity numerics in [`Twisted/README.md`](Twisted/README.md)
("Block convexity of the SU(2) measure", "Are the non-convex blocks a dilute polymer gas?") and the convex Lean
results. It turns them into one statement of the missing step. The setting is 4D SU(2) lattice Yang–Mills with
Wilson action `βS = β Σ_p (1 − ½ tr U_p)` (β = β_std = 4/g²). Nothing here is a theorem about the continuum, and
all twelve Clay obligations remain open.

## 1. The local quantity

For a block B of side s, condition on every link except those with both endpoints in B. For s ≥ 3, also hold one
link per deep-interior site (complete axial gauge, Faddeev–Popov factor 1). The conditional law of the remaining
links `x` is `∝ e^{−βS(x)} dHaar`. Its Bakry–Émery curvature is

  `κ_B(U) = λ_min( Ric + Hess βS )`,  with `Ric = 2·I` on SU(2) ≅ S³ (unit radius).

If `κ_B ≥ κ > 0` uniformly on the support, the conditional block measure satisfies a Poincaré/LSI inequality with
constant `1/κ`.

- **The convex Lean results apply to this quantity.**
  - `TwistedPrekopaMulti` and `TwistedHolderStep`: one RG step preserves two-sided Hessian bounds.
  - `TwistedTiltBL`: the localization bound `α_t ≤ 1/(λ + t)`.
  - All three are proved in flat charts on ℝᵐ. They transfer only where the chart Hessian is bounded below, which
    is the weak-coupling small-field region.
- **On the strong-coupling side, Ricci alone carries `κ > 0`.** This is the mechanism of the stochastic-analysis
  strong-coupling results (e.g. Shen–Zhu–Zhu). Strong-coupling mass gaps go back to the Osterwalder–Seiler
  cluster expansion (1978).

## 2. Measured map (s = 2, N = 8, sampled configurations, Wilson action)

| regime | β_std | fraction of blocks with κ_B ≤ 0 | tool that works |
|---|---|---|---|
| strong coupling | ≲ 0.3 | 0 | Ricci / Bakry–Émery, cluster expansion |
| **band** | 0.5–2 | 98–100% | none known |
| **band** (physical window 2.2–3) | 2.5 / 3 | 72% / 30% | none known |
| band edge | 3.5 / 4 | 7.5% / 1.8% | none: crude polymer margin 6.5 / 1.8 > 1 |
| dilute non-convex gas | 4.5–5 | 0.2% / 0.05% | convex step + polymer expansion (margin < 1) |
| uniformly convex (κ_B ≥ βλ₀/4) | ≳ 6 | 0 | convex step alone |
| uniformly half-convex | ≳ 12 | 0 | convex step with an O(1) constant |

Bad blocks are uncorrelated at block scale: the pair ratio is `P(both bad)/p² = 1.0–1.2`. The band is therefore
not a region of rare, large, correlated excursions, which a polymer expansion could absorb. It is a dense,
short-range-disordered gas of non-convex blocks.

### 2b. Correction (2026-11-06): the RG-relevant quantity gives a lower edge

The table above uses the **Dirichlet** block: all 32 interior links are free, and their block-average (coarse)
directions are free too. That is harsher than what a renormalization-group step needs. The earlier study in
[`Twisted/README.md`](Twisted/README.md) ("Large fields in hypothesis (a)", 2026-11-03/04,
`scripts/yang_mills_block_convexity.py`) measured the one-step quantity. It restricts the Hessian to each
block's **fine (zero-mean) directions**, holds the coarse field fixed, and uses covariant frames and a
background-gauge penalty.

That study found non-convex fractions of 62% / 21% / 3.2% / 0.73% / 0.10% / 0 at β_std = 2.0 / 2.25 / 2.5 /
2.75 / 3.0 / 3.25. Its Peierls bounds are met at β_std ≳ 2.45 (face adjacency) or 2.8–3.0 (touching
adjacency).

In the RG-relevant sense, then, the convex / dilute-polymer edge is **β_eff ≈ 2.5–3**, at the top of the physical
window, not 4.5. The Dirichlet numbers above are an upper bound on the difficulty. The gap between the two
quantities is the soft coarse modes, the same effect that makes Dirichlet side-4 blocks need β ~ 100 (§4).

Caveats:
- The fine-direction Hessian ignores the Ricci term and includes a gauge penalty, which that README notes
  contaminates ratios but not signs.
- A 4⁴ block lattice is too small for a percolation threshold.

With this correction the band is roughly **β_eff ∈ (0.3, 2.5–3)**. That is about 9 perturbative factor-2
blockings, and it contains the physical window, where the theory must cross over to confinement.

## 3. The missing step, stated once

Let `A_k` be the effective action after k blocking steps, and `β_eff(k)` its effective coupling. Perturbatively
`dβ/d ln μ = 8 b₀ = 22/(6π²) ≈ 0.371` for SU(2); this is the `b*` of TargetAGap. So one factor-2 blocking lowers
β_eff by about 0.26.

- The convex machinery, with a polymer expansion for the dilute bad blocks, can plausibly carry `A_k` from the
  UV down to `β_eff ≈ 4.5` if blocks are Dirichlet. With fine-direction blocks (the RG-relevant quantity, §2b)
  it can plausibly reach `β_eff ≈ 2.5–3`.
- The strong-coupling machinery works from `β_eff ≈ 0.3` down.
- A gap proof along these lines must supply a **band-crossing estimate**: a volume-uniform bound that carries a
  usable property of `A_k` through the band `β_eff ∈ (0.3, 4.5)` (Dirichlet), or `(0.3, 2.5–3)`
  (fine directions, §2b). Usable here means a Poincaré constant, decay of
  correlations, or an LSI. Perturbatively that is about 16 factor-2 blockings, about 8 of them between 4.5 and the
  physical window.
- In this band, at block scale 2:
  - (i) the conditional block measures are not log-concave, even in the Riemannian sense;
  - (ii) the non-convex blocks are too dense for any polymer expansion with a crude Kotecký–Preiss criterion;
  - (iii) there is no small coupling for a strong-coupling expansion.

Equivalent targets, any one of which would do:
- **(T1)** A volume-uniform spectral gap or LSI for the Glauber/Langevin dynamics of the effective action at one
  β_eff in the band. By the localization criterion (README, "Stochastic localization") this would give the
  covariance control step 4 needs.
- **(T2)** Exponential decay of gauge-invariant correlations under all boundary conditions at one β_eff in the
  band. By Chatterjee (CMP 2021) this kind of strong mass gap feeds the rest of the argument.
- **(T3)** A computer-assisted bound: a rigorous, interval-arithmetic finite-volume criterion (Dobrushin-type,
  or a block spectral gap on a box of side L₀) that self-improves under one blocking step for every β_eff in the
  band. This is the only route whose inputs are finite computations. Whether a finite L₀ exists at which such a
  criterion closes is itself unknown.

## 4. What the numerics do not show

- The test is pointwise at sampled configurations. Convexity on the whole support could fail even where every
  sample passes. Passing samples is necessary, not sufficient.
- It uses the Wilson action only. RG-blocked actions have different couplings, and improved block variables
  could shift the band. Blocking does not undo asymptotic freedom, so it cannot remove the band: the band in
  β_eff persists whatever the block-spin choice.
- The polymer margin is heuristic (probabilities, not free-energy activities; pair correlations only).
- Block sizes: s = 2 and s = 4 measured.
  - **Free value.** With all outside links fixed (Dirichlet), the free side-4 block is soft.
    - In the axial gauge used: `λ₀(4) = 0.126`, against `λ₀(2) = 3`.
    - Gauge-invariant (horizontal) value: 0.675, still about 1/s².
  - **Where side 4 fails.** Measured by `scripts/yang_mills_block_lanczos.py` (Lanczos validated against dense to
    1e-14; data `data/yang_mills_block_lanczos_n8_2026_11_06.json`). Every side-4 block is Bakry–Émery-negative at
    every β ≤ 32; 67% are at β = 64 and none at β = 128. The Ritz value is an upper estimate of λ_min, so the true
    threshold can only be higher.
  - **Shape of the deficit.** The negative part of the Hessian is nearly β-independent (about −5 to −8 at
    β = 4–32). The free part `βλ₀(s)` falls like 1/s². So fixed-boundary convexity needs β to grow roughly like
    s⁴ (side 2: about 5; side 4: about 100).
  - **Consequence.** Larger Dirichlet blocks do not average out the non-convexity; they make it much worse. The
    soft modes must be frozen by coarse variables, as in a real RG step with block-average constraints. Then the
    relevant competition is at the unit cell, and the β ≈ 4.5 edge of §2 is the operative number.
  - **Pre-registrations** (in the script docstring): all three held.

## 5. Relation to the external claim

The claimed existence proof (see [`EXTERNAL_EXISTENCE_AUDIT.md`](EXTERNAL_EXISTENCE_AUDIT.md)) needs the UV side
only: control of `A_k` for β_eff large, where §2 says the convex/dilute-polymer picture is available. An existence
proof therefore says nothing about crossing the band, and the gap needs exactly the band crossing. Audit item §5
("what would transfer") should be read against §3 here. A volume-uniform estimate valid down to some β_eff in the
band would be the most valuable thing to look for in that proof.

## 6. Numerical attack on T1–T3 (2026-11-06)

Script: `scripts/yang_mills_band_targets.py`. The lattice is `Lx × M³`, periodic, with the spatial links of the
layer x0 = 0 frozen to a boundary condition (BC); heat bath + 2 overrelaxation. BC families:
- cold (U = 1);
- hot (frozen Haar draw);
- anti (boundary plaquettes −1, maximal action);
- flux (a Z₂ vortex pair).

Pre-registered predictions are in the docstring.

**T2 / T3: boundary influence on local observables** (Lx = 16, M = 12, 2000 sweeps per BC, errors about 1e-4;
`data/yang_mills_band_bc_2026_11_06.json`). `Δ(d)` is the shift of the spatial plaquette at depth d relative to
the cold BC. `L0(ε)` is the first depth where the worst BC gives `|Δ| + 2σ < ε`.

| β | Δ_hot(1) | Δ_hot(2) | Δ_hot(3) | Δ_hot(4) | short-depth rate (hot / anti / flux) | L0(1e-2) | L0(1e-3) |
|---|---|---|---|---|---|---|---|
| 1.0 | −0.0036 | −0.0001 | 0 | 0 | — (one significant point) | 1 | 2 |
| 1.5 | −0.022 | −0.0002 | 0.0002 | 0.0003 | — | 2 | 2 |
| 2.0 | −0.074 | −0.0093 | −0.0010 | −0.0002 | 2.1 / 2.2 / 1.7 | 2 | 4 |
| 2.3 | −0.079 | −0.016 | −0.0041 | −0.0011 | 1.4 / 1.5 / 1.7 | 3 | 5 |
| 2.5 | −0.070 | −0.010 | −0.0025 | −0.0008 | 1.05 / 1.15 / 2.2 | 3 | 5 |
| 3.0 | −0.053 | −0.0046 | −0.0008 | −0.0003 | 1.8 / 2.8 / 2.8 | 2 | 4 |
| 4.0 | −0.042 | −0.0024 | −0.0003 | 0 | 2.4 / 3.4 / — | 2 | 3 |

Pre-registrations:
- **(1) Partly failed.** Every fitted rate is ≥ 1.05 at β ≤ 2.5, as predicted (≥ 0.5). But the rates are not
  BC-independent within 30% (flux against hot at 2.5: 2.2 against 1.05). They fall with β only up to 2.5 and rise
  again at 3–4.
- **(2) Failed in its second half.** `L0(1e-3) ≤ 6` at β ≤ 2.3 held. It does not grow past 6 by β = 3: it peaks
  at 5 around β 2.3–2.5 and falls to 3 at β 4.

Reading:
- **What the fitted rates measure.** They come from depths 1–4 and are boundary-layer (UV) rates, not the
  asymptotic 0++ mass. At β ≥ 3 the M = 12 slab is also a physically small box (perturbative), which is why
  influence shrinks again there.
- **What holds.** The influence of the worst tested BC on a local gauge-invariant observable is below 1e-3 within
  5 lattice units at every β in the band.
- **What it does not show.** This is the observable-level analogue of a finite-box mixing condition. The
  Dobrushin–Shlosman-type input T3 needs is much stronger: total-variation influence on the whole conditional law,
  supremum over all BCs, and the long-range sectors (flux, Polyakov), where confinement lives. Four BC families
  are not a supremum.

**T1: dynamical gap of the heat bath** (cold BC; R = 40 replica pairs from cold and hot interior starts; `γ` from
`D(t) = E[P_cold(t) − P_hot(t)] ~ e^{−γt}`, t in sweeps; `data/yang_mills_band_relax_2026_11_06.json`).

| β | γ (M = 4) | γ (M = 8) | γ (M = 12) |
|---|---|---|---|
| 1.5 | — | 1.17 | 1.20 |
| 2.0 | 0.62 | 0.61 | 0.62 |
| 2.3 | 0.50 | 0.44 | 0.35 |
| 2.5 | 0.63 | 0.46 | 0.34 |

- **(3) Failed as pre-registered; the failure is an estimator artifact.**
  - By the script's γ, the drop from M = 8 to 12 at β 2.3–2.5 is real. But that fit uses the last three quarters
    of the significant run, and larger M (less noise) extends the run into a slower late tail.
  - Refit on fixed windows t = 1–5 and t = 5–12 for every M (a post-hoc analysis, decided after seeing the data),
    and the volume dependence disappears.
  - Deconfounded rerun: Lx = 16, so β ≤ 2.5 is confined at N_t = 16; data
    `data/yang_mills_band_relax_lx16_2026_11_06.json`.

| β | γ[1..5], M = 8 / 12 / 16 | γ[5..12], M = 8 / 12 / 16 |
|---|---|---|
| 2.0 | 0.62 / 0.63 / 0.61 | 0.51 / 0.60 / 0.56 |
| 2.3 | 0.50 / 0.51 / 0.51 | 0.35 / 0.37 / 0.35 |
| 2.5 | 0.62 / 0.62 / 0.63 | 0.31 / 0.34 / 0.32 |

  The Lx = 8 run refit the same way is also flat: γ[5..12] at β 2.5 is 0.31 / 0.28 for M = 8 / 12.

**Reading of T1.**
- **Rates.** The relaxation of the gauge-invariant energy has two rates, about 0.6 per sweep early and 0.3–0.35
  late at β 2.3–2.5.
- **Volume.** Both are volume-independent over an 8× volume range (M = 8 to 16) in the confined theory. There is
  no sign of a closing dynamical gap in this sector inside the band.
- **Limits.** This probes one neutral observable from two starts. A spectral gap bound (T1) needs the supremum
  over all observables, including the flux and center sectors and long-wavelength modes the energy does not
  couple to. Numerics cannot give a volume-uniform bound, only the absence of a visible trend.

## 7. Where the three targets stand

- **T1 (dynamical gap).** The cleanest numerical evidence is in its favour: volume-independent relaxation through
  the band. Proving it needs a mechanism (for example, a multiscale Bakry–Émery argument with the Ricci term, or a
  spectral-gap block decomposition, Martinelli–Olivieri style). §2 shows the per-block Bakry–Émery part fails
  inside the band, so such a mechanism must use cancellations between blocks, not block-wise convexity.
- **T2 (BC-uniform decay).** Local influence decays within a few lattice units for every tested BC. The supremum
  over BCs, and the long-range sectors, are untested and are where the gap problem actually sits.
- **T3 (finite-box criterion).** Superseded by §8 (center sector): the boundary-holonomy influence obeys an area law,
  so the box needs σ_eff L₀² ≳ 2 ln(1/ε), i.e. L₀ ≈ 20–28 at β 2.5 (2.5–3.5 × N_t,c). The observable-level influence alone would need only
  L0 ≈ 5 at β 2.3–2.5. A
  Dobrushin–Shlosman-type check on a 5⁴ box would mean a supremum over boundary conditions of a total-variation
  influence for about 2500 links × 3 dof. That is far beyond rigorous interval arithmetic today, and it is the
  concrete size of the computer-assisted route.

None of the three is proved. The band statement (§3) stands as the precise missing step.

## 8. Second round: adversarial boundaries and the slowest sector (2026-11-06)

Pre-registrations (4)–(6) are in the docstring of `scripts/yang_mills_band_targets.py`, written before these
runs.

**T2, adversarial flux family** (Lx = 16, M = 12, 1500 sweeps per BC; `data/yang_mills_band_adv_2026_11_06.json`).
The family is uniform abelian boundary flux φ = 2πk/M in two planes, k = 1…6 (k = 6 is anti-like). Plaquette
shift Δ(d) relative to the cold BC:

| β | k | Δ(1) | Δ(2) | Δ(3) | Δ(4) | Δ(5) |
|---|---|---|---|---|---|---|
| 2.3 | 1 | −0.037 | −0.012 | −0.0037 | −0.0012 | −0.0003 |
| 2.3 | 4 | −0.081 | −0.016 | −0.0041 | −0.0012 | −0.0002 |
| 2.3 | 6 | −0.079 | −0.015 | −0.0042 | −0.0012 | −0.0003 |
| 2.5 | 1 | −0.033 | −0.0086 | −0.0027 | −0.0010 | −0.0006 |
| 2.5 | 4 | −0.069 | −0.010 | −0.0027 | −0.0010 | −0.0006 |
| 2.5 | 6 | −0.064 | −0.0087 | −0.0025 | −0.0007 | −0.0004 |

Errors are 1–2 × 10⁻⁴.

- **(4) Held.** The worst flux at depth 4 (0.0012–0.0013) is within a factor 1.2 of the worst of hot/anti
  (0.0011 / 0.0010).
- **The influence saturates.** Beyond depth 2 it is the same for every boundary flux strength k ≥ 2. The boundary
  layer screens the boundary data, and the deep influence is set by the bulk, not by how adversarial the boundary
  is. Among smooth fluxes there is no hidden adversarial direction.

**T1, slowest sector** (periodic N⁴, no frozen layer, 2000 sweeps, MC-time autocorrelation of the smeared spatial
Polyakov-loop averages; `data/yang_mills_band_auto_2026_11_06.json`).

| β | N | τ_int charged | τ_int neutral (P²) | ⟨P²⟩ |
|---|---|---|---|---|
| 2.3 | 8 | 2.2 | 1.1 | 0.028 |
| 2.3 | 12 | 1.4 | 0.74 | 0.0038 |
| 2.3 | 16 | 0.82 | 0.54 | 0.0009 |
| 2.5 | 8 | 16.8 | 4.8 | 0.22 |
| 2.5 | 12 | 20.1 | 7.1 | 0.046 |
| 2.5 | 16 | 7.7 | 3.2 | 0.0083 |

- **(6) Held.** At β 2.3 the neutral τ_int falls with N.
- **At β 2.5**, N = 8–12 sit at or near the finite-temperature transition (β_c(N_t = 8) = 2.51,
  β_c(N_t = 12) ≈ 2.635; ⟨P²⟩ is large). There the Polyakov sector is slow, about 20 sweeps. At N = 16, deep in the
  confined phase, it drops to 7.7 / 3.2.
- **Reading.** In the confined theory the slowest gauge-invariant sector tested relaxes in O(1–10) sweeps,
  decreasing with volume. Slowness appears only near the deconfinement transition, which is a finite-size effect
  of the periodic box, not a property of the infinite-volume band.

**T2/T3, electric-flux (center) sector** (cold BC, boundary holonomy +1, against center-flipped BC, U₁ = −1 on one
x₁-slice of the frozen layer: same boundary plaquettes, holonomy −1). Smeared spatial Polyakov loop P₁(d) along x₁
(length M = 12), 3000 sweeps; `data/yang_mills_band_p1_2026_11_06.json`. The first attempt (in the adv file) is
invalid: the shared helper `polyakov()` took the loop length from the x₀ extent, which is wrong on non-cubic
lattices. All earlier runs used cubic lattices and are unaffected. The fix is in `scripts/yang_mills_sl_gpu.py`,
and the run asserts that the flipped boundary has holonomy −1.

| β | d = 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 (mid-slab) |
|---|---|---|---|---|---|---|---|---|
| 2.3: P₁^cold − P₁^flip | 1.760 | 1.471 | 0.806 | 0.288 | 0.084 | 0.029 | 0.012 | 0.000 ± 0.004 |
| 2.5: P₁^cold − P₁^flip | 1.832 | 1.667 | 1.310 | 0.973 | 0.731 | 0.570 | 0.463 | 0.382 ± 0.030 |

The plaquette shift under the flip is ≤ 2 × 10⁻⁴ at every depth. Local observables are blind to this sector.

The slab is bounded by the same frozen layer on both sides, so the profile is ∝ cosh(m(D − d)).
- **β 2.5:** the fit gives m ≈ 0.32 per lattice unit. That is the flux-tube energy across the transverse box:
  σa²·M − π/(3M) = 0.034·12 − 0.087 = 0.32 (a√σ ≈ 0.185 at β 2.5, with the Lüscher term).
- **β 2.3:** local rates are 1.0–1.2 per lattice unit.

Prediction (5):
- **Held in its main claim.** The flux sector decays far more slowly than the plaquette at β 2.5: 0.32 against
  1.05–1.15.
- **Held for the rate at β 2.5 at M = 12**, which equals σM with the Lüscher term. The M-scan below shows this
  agreement is partly coincidental: the rate is linear in M, but with a smaller slope and no Lüscher curvature.
- **Inaccurate at β 2.3.** The pre-registered σa² ≈ 0.07 at β 2.3 was wrong; the standard value is about 0.13.

**M-scan, pre-registration (7).** Same run at transverse sizes M = 8 and 16 (Lx = 16, 3000 sweeps;
`data/yang_mills_band_p1_m8_2026_11_06.json`, `..._m16_...`; fit `scripts/yang_mills_band_p1_fit.py`, cosh fit
for d ≥ dmin, 1σ = Δχ² 1). Pre-registered: m(M) = σa²M − π/(3M), β 2.5: m(8) = 0.14, m(16) = 0.48 within 30%;
β 2.3: m(8) ≈ 0.9.

| β | dmin | m(8) | m(12) | m(16) | χ²/dof (8, 12, 16) | σa²M − π/(3M) at 8, 12, 16 |
|---|---|---|---|---|---|---|
| 2.5 | 2 | 0.218 [0.214, 0.220] | 0.318 [0.314, 0.320] | 0.424 [0.420, 0.426] | 1.2/5, 0.1/5, 1.1/5 | 0.141, 0.321, 0.479 |
| 2.5 | 3 | 0.212 | 0.318 | 0.420 | 0.3/4, 0.0/4, 0.8/4 | |
| 2.3 | 2 | 0.708 | 1.074 | 1.442 | 21/5, 18/5, 20/5 | 0.957, 1.545, 2.111 |
| 2.3 | 3 | 0.804 [0.78, 0.83] | 1.200 [1.16, 1.24] | 1.70 [1.62, 1.78] | 0.6/4, 3.6/4, 7.3/4 | |

- **Linearity in M: held, and sharply.** At β 2.5 the increments are 0.100 and 0.106 per ΔM = 4 (dmin 2: 0.103,
  0.104). The rate is m(M) ≈ σ_eff·M + c with σ_eff = 0.026 and c ≈ 0.01. At β 2.3 (dmin 2, which has poor χ²
  because of smearing-radius curvature) the increments are 0.366 and 0.368, so σ_eff ≈ 0.092.
- **Numbers: failed at β 2.5, M = 8.** The measured 0.215 is 53% above the predicted 0.14. M = 16 held (0.42 against
  0.48, −12%). β 2.3, M = 8 held within 30% (0.71–0.80 against 0.9–0.96) but is low.
- **The Lüscher term is not seen.** A fit σL + c/L to M = 8, 16 at β 2.5 gives c = +0.04, not −π/3 = −1.05. The
  slope is σ_eff ≈ 0.75 σa² at β 2.5 and ≈ 0.67 σa² at β 2.3. The same ~0.7 ratio at both couplings suggests a
  systematic of this geometry rather than noise. Candidates, untested: the flux loop lives in a transverse box of
  the same size M, the frozen layer is at distance ≤ 8, and the cosh window is short. The earlier agreement at
  M = 12 is where the line σ_eff·M + c happens to cross σa²M − π/(3M).

What survives is the structural claim: the center-sector boundary influence decays at a rate proportional to the
transverse size, i.e. the boundary-holonomy correlation in a box obeys an area law with an effective tension
σ_eff of order the string tension.

**Consequence for T3, the main result of this round.** A finite-box mixing criterion must control the whole
conditional law, including this sector. In a box of side L₀ the boundary-holonomy influence across the box is
suppressed by about exp(−σ_eff·L₀·L₀/2), an area law. Reaching influence ε needs σ_eff L₀² ≳ 2 ln(1/ε). Since
T_c/√σ ≈ 0.71 for SU(2), 1/√σ is about 0.7 deconfinement lengths N_t,c(β), so this is a statement about boxes a few
times the deconfinement length.
- **At β 2.5** (σ_eff ≈ 0.026): ε = e⁻⁵ needs L₀ ≈ 20 and ε = e⁻¹⁰ needs L₀ ≈ 28. The plaquette-level L₀ ≈ 5 of §6
  gives only σ_eff L₀²/2 ≈ 0.3, no suppression at all.
- **A realistic box** is L₀ ≈ 20–28 at β 2.5, i.e. 2.5–3.5 × N_t,c, about 6 × 10⁵ to 2.5 × 10⁶ links.
- **Along asymptotic freedom**, N_t,c ∝ 1/a doubles every Δβ ≈ 0.26 in perturbative running. A box set by
  N_t,c(β_eff) at the band's weak-coupling edge (β_eff ≈ 2.5–3) is far beyond rigorous computation.

T3 in the naive sense ("a small box suffices because local correlations are short") is therefore ruled out by
the center sector: the box must contain confinement itself. The target can only be rescued with block variables
that make the center sector local, for instance by conditioning on center vortices or 't Hooft fluxes, in the
spirit of the twisted boxes this program uses.
