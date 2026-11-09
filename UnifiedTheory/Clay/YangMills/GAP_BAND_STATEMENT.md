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
- **T3 (finite-box criterion).** §8 found that in *periodic* boxes the boundary-holonomy influence obeys an area law
  (L₀ ≈ 20–28 at β 2.5). §8b shows this is a periodic-geometry artifact: in contractible boxes a boundary center
  vortex is forgotten within 2–3 lattice units. The observable-level influence alone would need only
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

T3 in the naive sense ("a small box suffices because local correlations are short") would therefore be ruled out
by the center sector *in periodic boxes*: the box must contain confinement itself. **§8b shows this does not carry
over to contractible boxes, which is the geometry a Dobrushin–Shlosman / Martinelli–Olivieri criterion on Z⁴ uses.**

## 8b. Contractible boxes: the center-sector obstruction is a periodic-geometry artifact (2026-11-07)

**Why the slab result may not transfer.** In the slab, the transverse directions are periodic, so a center-flipped
holonomy is a large center transformation. It is invisible to every plaquette, and it couples to the non-contractible
Polyakov loop.
- A finite box Λ ⊂ Z⁴ is contractible.
- Gauge transformations at the sites of a sub-box Δ deep inside Λ are symmetries of the conditional law, so the marginal
  on Δ is seen only through contractible Wilson loops (and spin networks) in Δ.
- On a contractible boundary every center cocycle is exact, so a "plaquette-invisible" flip is a gauge transformation
  and has zero influence.
- The nearest legitimate analogue is a thick center vortex in the frozen exterior. Its holonomy around the box is −1,
  it is not gauge-equivalent to the cold boundary, and away from its core each boundary plaquette is perturbed only
  slightly.

**Test.** `scripts/yang_mills_box_vortex.py`, `data/yang_mills_box_vortex_2026_11_06.json`.
- **Box:** C = [1, L₀]⁴ with a frozen two-layer shell (periodic N = L₀ + 2), 4000 sweeps per boundary condition.
- **Boundary condition:** a τ₃ vortex of flux π through the (1,2) plane along the axis of C, extended in x₀ and x₃, with
  Gaussian width s = 1.5 (thin). Its frozen holonomy around the box in the shell is −0.92, −0.96 and −0.96 at
  L₀ = 8, 12, 16. The compensating anti-vortex sits in the shell corner.
- **Observable:** influence Δ(d) = ⟨W⟩_cold − ⟨W⟩_vortex on r × r loops in the (1,2) plane, linked with the axis or
  not, at depth d from the x₀/x₃ faces where the vortex sheet enters.

Thin vortex, linked r = 2 loop (1σ errors ≈ 0.0013–0.005):

| β | L₀ | d = 0 | 1 | 2 | 3 |
|---|---|---|---|---|---|
| 2.5 | 8 | 0.0278 | 0.0116 | 0.0069 | 0.0033 ± 0.0045 |
| 2.5 | 12 | 0.0282 | 0.0118 | 0.0060 | −0.0022 ± 0.0023 |
| 2.5 | 16 | 0.0278 | 0.0095 | 0.0039 | 0.0005 ± 0.0016 |
| 2.3 | 8 | 0.0255 | 0.0068 | 0.0003 | −0.005 ± 0.006 |
| 2.3 | 16 | 0.0234 | 0.0063 | 0.0017 | 0.0026 ± 0.0016 |

The unlinked loop in the same plane gives 0.016–0.018 at d = 0 and the same rapid fall-off. Plaquettes give ≤ 1e-3.

- **(9) H_local held, H_center failed (my guess was H_center).** The profile does not depend on L₀ from 8 to 16. The
  decay rate is about 1.0 per lattice unit from d = 0 to 1 and about 0.7–0.9 from 1 to 2, a glueball-like rate. The
  influence is at the noise level, < 3 × 10⁻³, from d = 3 on at every L₀. Nothing grows with the cross-section, unlike
  the slab's m(M) ∝ M. The interior does not carry the boundary vortex; it forgets it within 2–3 lattice units.
- **(8) failed.** The linked/unlinked ratio at d = 1 is about 1.6–1.8 at L₀ = 8, not ≥ 3. The center-specific excess is
  a modest near-face effect.
- **Defect.** The "thick" vortex (s = L₀/4) is not a clean center boundary condition at large L₀: its flux spreads
  beyond the box cross-section, so its frozen holonomy is −0.54, −0.13 and +0.19 at L₀ = 8, 12, 16. Its rows are in
  the data file but are not used here. A thick vortex with holonomy −1 needs a larger shell.
- **Scope.** Only one family of boundary conditions (thin vortices) and r ≤ 4 loops were tested in contractible
  geometry. The supremum over all boundary conditions remains untested, as in §6.

**Consequence.** The slab result of §8 is correct, but it concerns periodic boxes: torelon / electric-flux states of
a finite torus. Those matter for gaps on a finite torus and for the flux-recursion route (BEST_ATTEMPT step 5d).
They do not matter for a finite-box mixing criterion on Z⁴, where the center sector entering through the boundary is
local. For T3 this reverts the box size to the observable level of §6: boundary influence below 1e-3 to 3e-3 within
about 3–5 lattice units at β 2.3–2.5, on the boundary families tested. The remaining T3 obstacles are those of §7:
the supremum over boundary conditions, a total-variation statement rather than single observables, and the
cutoff-uniformity of the box size along asymptotic freedom (N ∝ 1/a).


## 9. Matching at one coupling: no β* in a 16⁴ box for long-wavelength observables (2026-11-07)

**Question.** §2b puts the end of the convex fine-direction RG at β_eff ≈ 2.5–3. §8b found boundary influence on UV
observables gone within 3–5 lattice units at β 2.3–2.5. If a finite-box criterion also held at one β* ≥ 2.5 for
long-wavelength observables, the missing step of §3 would shrink from a band crossing to a matching at β*: convex RG
down to β*, then a finite-box criterion for the effective measure at β*.

**Test.** `scripts/yang_mills_box_matching.py`, `data/yang_mills_box_matching_2026_11_07.json`.
- Contractible box C = [1, 16]⁴ with a frozen two-layer shell; boundary conditions cold, hot (frozen Haar draw) and
  thin vortex (as §8b); 3000 sweeps, measurements every 4, 20 bins; β = 2.5, 2.65, 2.8, 3.0.
- Observable: e = 1 − mean plaquette after n = 0, 5, 20 steps of stout smearing (ρ = 0.1) built only from plaquettes
  inside C. It is a gauge-invariant function of the interior links alone. Smoothing radius ≈ 0, 2, 4.
- Influence: relative difference (e_BC − e_cold)/e_cold by Chebyshev depth d from the shell (d = 7 is the centre).

n = 20 (radius ≈ 4), relative influence (1σ errors 0.01–0.07 at d = 6–7):

| β | hot d = 3 | hot d = 5 | hot d = 7 | vortex d = 3 | vortex d = 7 | rate (hot, d 2→5) |
|---|---|---|---|---|---|---|
| 2.50 | 1.40 | 0.53 | 0.25 | 0.066 | 0.09 ± 0.09 | 0.51 |
| 2.65 | 1.14 | 0.52 | 0.35 | 0.069 | 0.07 ± 0.04 | 0.43 |
| 2.80 | 0.94 | 0.40 | 0.28 | 0.071 | 0.04 ± 0.03 | 0.45 |
| 3.00 | 0.84 | 0.36 | 0.23 | 0.093 | 0.10 ± 0.02 | 0.44 |

The unsmeared (n = 0) influence reproduces §8b: hot falls to ≤ 3 × 10⁻³ by d = 4 and the vortex is invisible
(≤ 2 × 10⁻³) at every depth.

- **(11) failed.** No β* in [2.5, 2.8] (nor 3.0) has n = 20 influence < 10⁻² at d = 7. The hot boundary still moves the
  smoothed energy at the centre of the box by 23–35 %. The cold profile itself has not plateaued: e(d = 7)/e(d = 0) is
  3.3, 2.3, 2.0 and 1.9 at the four β.
- **(10) failed.** The decay rate barely moves with β: 0.51 → 0.44 (ratio 0.87) on d = 2–5 and 0.48 → 0.38 (0.78) on
  d = 3–6, not ≤ 0.6. The 0++ mass in lattice units should fall by a factor of about 3–4 from 2.5 to 3.0. In a 16⁴
  box the rate is set by the box and the smoothing kernel, not by the glueball. At β 2.8–3.0 the box is physically
  small (L₀ a √σ ≲ 1), so this regime is a small-volume one.
- **Vortex: a non-decaying imprint.** The thin vortex, invisible to plaquettes and 2 × 2 loops, moves the smoothed
  energy by 4–10 % at every depth with no visible decay. The frozen holonomy −1 forces a center-vortex sheet across the
  interior; UV observables do not see it, but radius-4 observables do, wherever the sheet wanders. This qualifies §8b:
  the center sector entering through a contractible boundary is local for UV observables only.

**Consequence.** At the couplings where the convex RG ends (β_eff ≳ 2.5), a finite-box criterion for long-wavelength
observables needs a box much larger than 16. At the measured rate of about 0.45 per unit, the hot influence would reach
10⁻² near depth 14, so L₀ ≈ 30 at least. The vortex imprint shows no decay at all at L₀ = 16, so the
center-vortex boundary conditions may need larger boxes still. A matching at one coupling is therefore not available
with a modest box. The missing step remains the band crossing of §3, or a finite-box criterion on boxes of ≳ 30⁴
with the supremum over boundary conditions, which is far beyond interval-arithmetic reach.

**Caveats.** The bare Wilson action stands in for the effective action at β_eff. Relative influence on a smoothed
energy amplifies small absolute differences, because e_cold at n = 20 is about 10⁻³ of its n = 0 value. Only one box
size was run, and no TV or supremum-over-BC statement was tested.

## 10. Flux bootstrap: the doubling chain as an induction on box size (2026-11-08)

**Idea.** Run the electric-flux recursion as an induction at fixed β instead of crossing the band: H(L) = "y(L) small and
the box thermal constants small". Isotropic doubling L⁴ → (2L)⁴ in four steps: two in-plane, y' ≤ K y²
(TwistedFluxRecursion), and two transverse, y' ≤ (K_B − z²)/(K_B + z²) ≤ 4y + κ (TwistedFluxThermal). If H(L) ⇒ H(2L),
the base case H(L₀) is one finite computation.

**Measurement.** `scripts/yang_mills_flux_bootstrap.py`, `data/yang_mills_flux_bootstrap_2026_11_08{,b}.json`.
- log z on the five chain shapes (twist integration, 7 nodes).
- log Kper = 2 log Z(s) − log Z(s') for each doubling, by split/join interpolation on the doubled lattice. This is
  exact; bulk free energy cancels.
- Check: the λ = 1 half lattice reproduces a standalone lattice within about 1σ in 7 of 8 cases, 2.5σ once.

| β | L | y(L) | log Kper (steps 1–4) | chain bound Y(2L) | P(contract), resampled |
|---|---|---|---|---|---|
| 2.4 | 4 | 0.61 | 2.2, 2.7, 2.3, 5.6 | 1 (empty) | — |
| 2.5 | 4 | 0.74 | 2.7, 3.2, 4.3, 8.8 | 1 | — |
| 2.6 | 4 | 0.85 | 3.4, 4.4, 4.2, 8.5 | 1 | — |
| 2.5 | 6 | 0.67 | 1.6, 1.6, 2.0, 5.5 (± 0.4–0.9) | 1 | — |
| 2.6 | 6 | 0.87 | 3.7, 3.8, 4.4, 4.8 (± 0.5–1.3) | 1 | — |
| 2.4 | 6 | 0.355 | 1.5, 0.5, 0.5, 0.1 (± 0.35–0.9) | 0.67 | — |
| 2.3 | 6 | 0.037 | 0.4, 0.9, −0.6, −0.8 (± 0.3–1.0) | 0.000 | 0.66 |
| 2.4 | 8 | 0.008 | 0.1, −1.3, −0.1, −1.3 (± 0.5–1.5) | 0.000 | 0.37 |

- **(12) Bug checks passed.**
  - log Kper ≥ 0 within 2σ everywhere; the worst is −1.31 ± 0.73.
  - The in-plane theorem holds within errors; the worst is 1.6σ, at β 2.4, L 6, step 2.
- **(13) Failed.** Transverse superadditivity z(2t) ≥ z(t)² is violated at 3.4σ (β 2.5, L 4) and 5.5σ (β 2.6, L 4),
  on (8,8,8,4) → 8⁴. With the short side 4 the twist is almost free; doubling that side restores its cost. The candidate
  multiplicative lemma is false as a statement for all L. It holds within errors on every shape with sides ≥ 6.
- **(14) Contraction part failed.** There is no contraction at β 2.4, L 6, where y = 0.355 against a threshold
  1/K₁ = 0.35. The thermal part held: the constants collapse from L 4 to L 6 at β 2.4 and stay large at 2.6. This is
  the torelon picture: the box goes cold once L√σ ≳ 1.6.
- **(15) Held on central values, not established.** The chain contracts at β 2.3, L 6 and at β 2.4, L 8 (Y = 0.000
  < y). But the resampled probability of contraction is 0.66 and 0.37: the decisive constants are 0 ± 0.5–1.5, while
  contraction needs κ below y ≈ 0.01–0.04.

**What this shows.**
- **Encouraging:** the thermal constants do fall to 0 within errors once L√σ ≳ 2, and y falls with them. Inside the
  band, at β 2.3–2.4 and L 6–8, the hypothesis H(L) looks numerically true.
- **The precision wall:** whether H(L) ⇒ H(2L) closes is decided by κ against y. That requires log K to a precision of
  about y, which is 10⁻² here and falls like e^{−σL²} as L grows. A statistical estimate needs about 10⁴× the present
  statistics. A rigorous interval-arithmetic base case would need certified partition-function ratios on 6⁴–16⁴
  lattices to 10⁻² precision. Both are far out of reach.
- **The structural wall** (header of the script): the transverse step is additive in κ, and κ ≥ e^{−mL} while
  y ~ e^{−σL²}. Even a closed induction would give y ≲ e^{−mL}, a perimeter-type bound, so no area law. The
  multiplicative replacement (13) is false at small L.

The induction is therefore a sound reformulation, and numerically consistent inside the band. It does not reduce the
missing step to a finite computation: the base case would have to resolve κ to the size of y, and the transverse step
must become multiplicative for an area law.

**Addendum (2026-11-08): what replaces the two walls.** `Twisted/TwistedFluxInduction.lean` (axiom-clean).
- **Precision wall removed.** With a multiplicative transverse step y' ≤ 2n·y (`transverse_mult`, from z' ≥ zⁿ), one
  isotropic doubling gives y(2L) ≤ 4n²K₁²K₂·y(L)⁴ (`chain_step`). The in-plane constants then only need an upper bound
  K̄, not smallness. Iterating gives M·y_k³ ≤ (M·y₀³)^(4^k) with 4^k = (L_k/L₀)² (`area_law_iterate`): area-type decay,
  and an area law via Tomboulis–Yaffe. The base case M·y₀³ < 1 is mild: y ≈ 0.01–0.04 at β 2.3–2.4, L 6–8.
- **The structural wall becomes one spectral statement (S).** Take the transfer matrix along the doubled transverse
  direction and write F(t) = tΔ + D(t), with Δ ≥ 0 the twisted-minus-untwisted ground-state gap and
  D = Φ_per − Φ_tw the difference of the two sectors' thermal free energies. Then D(2t) ≤ c·D(t) with c ≥ 2 implies
  F(2t) ≤ c·F(t) (`F_double_le`; no sign condition on D is needed).
- **Remaining open inputs, uniform in L ≥ L₀(β):**
  - (S);
  - K̄: a bound on the box thermal free energy at temperature 1/L. Here bounded is enough, not small: massless
    Stefan–Boltzmann scaling already gives O(1) at T = 1/L.

  Both are spectral statements about the finite-box transfer matrix in the confined, cold regime. The side-4 failure
  of (13) shows (S) is false for thin boxes, so L₀(β) must exceed a thermal length. For Clay, both inputs and L₀(β)
  would also have to be controlled uniformly as β → ∞, which is the renormalization-group content that remains.

## 11. Direct test of the multiplicative transverse step (2026-11-08)

Script `scripts/yang_mills_twist_transverse_scan.py`, data `data/yang_mills_twist_transverse_scan_2026_11_08.json`.
Boxes (8, 8, 8, C) with C ∈ {4, 6, 8, 12, 16, 24}, twist in the (1,2) plane, β 2.5 and 2.6, 8000 sweeps, 7 Gauss nodes.
F = −log z, and R(C) = F(2C)/F(C). Pre-registrations (16) and (17) were committed in 993fa53 before any run.

| β | F(4) | F(6) | F(8) | F(12) | F(16) | F(24) |
|---|---|---|---|---|---|---|
| 2.5 | 0.24(10) | 0.84(15) | 1.27(19) | 1.61(28) | 1.79(26) | 2.62(30) |
| 2.6 | 0.22(12) | 1.63(23) | 3.02(27) | 4.41(34) | 4.25(42) | 7.00(58) |

| β | R(4) | R(6) | R(8) | R(12) |
|---|---|---|---|---|
| 2.5 | 5.3 ± 2.4 | 1.91 ± 0.48 | 1.41 ± 0.29 | 1.62 ± 0.34 |
| 2.6 | 13 ± 7 | 2.71 ± 0.44 | 1.41 ± 0.19 | 1.59 ± 0.18 |

Verdicts:
- **(16), R(C) ≤ 2.6 within 2σ for every C ≥ 6 at both β: HOLDS.** All six qualifying ratios pass. The worst is R(6) at β 2.6,
  0.3σ above 2.6. R(8) and R(12) are 3–6σ below 2.6.
  - The thin-box part, R(4) > 2.6, holds on central values (5.3 and 13) but only at 1.1σ and 1.5σ. It is not
    significant, because F(4) ≈ 0.2 is comparable to its error.
- **(17), R(8) and R(12) in [1.6, 2.4]: FAILS as written.** Three of the four central values fall below 1.6
  (1.41, 1.41, 1.59). The one that passes is R(12) at β 2.5, at 1.62. Every value is within 1σ of 1.6.
  - The miss is on the favourable side: F grows **sublinearly** in C over this range. Linear fits for C ≥ 6 give slopes
    0.094(17) at β 2.5 and 0.29(3) at β 2.6, with positive intercepts.
  - The prediction that F grows roughly linearly, i.e. that the tΔ term dominates, is wrong at these sizes. The
    thermal part D still matters.
- **Consequence for the multiplicative step.** For C ≥ 8 at both β, R ≤ 2 holds on central values and within 1σ, i.e.
  z(2C) ≥ z(C)². So `transverse_mult` applies with n = 2.
  - At C = 6, β 2.5 still has n = 2. β 2.6 needs n = 3, since R(6) = 2.71 ± 0.44.
  - The step fails only at C = 4. That matches the side-4 failure of (13), and puts the onset length L₀ between 4
    and 6–8 at these couplings.
- **Consistency.** Two earlier measurements are compatible within about 2σ:
  - the (8,8,8,4) values from §10: log z = +0.06 and −0.06, versus −0.24 and −0.22 here;
  - 8⁴: log z = −1.11 and −2.54 in §10, versus −1.27 and −3.02 here.

  F(16) < F(12) at β 2.6 is a 0.3σ inversion.

**What this does not settle.**
- The scan varies one transverse side of a fixed 8³ cross-section. It does not cover the chain shapes, more than two β values,
  or L → ∞.
- It tests F(2t) ≤ cF(t) directly, not (S) through the split F(t) = tΔ + D(t).
- K̄ is not addressed.
- Nothing here is uniform in β.

The multiplicative step is therefore an **observed** property at β 2.5–2.6 for transverse sides ≥ 6–8, not a proved
one. The open inputs remain (S) for L ≥ L₀(β) and K̄, both uniform in β.

## 12. Attacking the two open inputs: thermal excess, sub-area growth, flux basis (2026-11-09)

Lean modules: `Twisted/TwistedThermalExcess.lean`, `Twisted/TwistedSubArea.lean` and `Twisted/TwistedFluxBasis.lean`.
All compile with standard axioms only and are not imported by the root. Script: `scripts/yang_mills_thermal_excess.py`.
Data: `data/yang_mills_thermal_excess_2026_11_09{,b}.json`.

**K̄ is a thermal excess.** Take the doubled in-plane direction as time, with the spatial box fixed. Let P(L) be the
excited-state part of the box partition function at T = 1/L, i.e. the thermal excess. Then
1 + P ≤ Kper ≤ (1 + P)² (`kper_sandwich`), and K ≤ 2·Kper (`k_le_two_kper`).

log(1 + P(L)) equals the exact sum Σ_k 2^{-(k+1)} log Kper(2^k L) (`log_z_telescope`). Splitting into the 8 electric-flux
sectors costs at most a factor 64 (`kper_flux_split`, `flux_projection_le`). So K̄ is a statement about the zero-flux
spectrum only.

**The induction needs only sub-area growth, not bounded constants.** With u_k = −log y_k and m_k = log M_k,
u_{k+1} ≥ 4u_k − m_k gives u_k ≥ 4^k(u₀ − A/3 − B/(4−q)) whenever m_k ≤ A + B q^k with q < 4 (`area_law_growing`). So
log M(L) ≤ A + B(L/L₀)^α with any α < 2 is enough. The case α = 2 is the borderline and fails.

**The transverse step in the flux basis.** Set Z₀ = (Z + Z_tw)/2 and Z_e = (Z − Z_tw)/2. Then exactly
y(2t) = [2y/(1+y²)]·K₀/K_e (`transverse_flux_identity`), where K_s = Z_s^split/Z_s(2t) is the split/join interface ratio
in sector s.
- In the twist basis, (S) looked like it needed Kper_tw and Kper to agree to O(y): exponentially fine, and
  confinement-strength. In the flux basis it needs only log K₀ − log K_e = o(L²). Physically both are O(1).
- K̄ and (S) therefore take one common form: in each flux sector, the interface free energy of the split/join cut is
  sub-area.
- **The gap.** The only rigorous bound is |log K_s| ≲ β·(slab volume) ~ βL³. That misses the requirement by more than
  one power of L.
- Closing it needs *local indistinguishability of flux sectors*: the sector difference of the cut observable,
  averaged over the 3D slab, must be o(1/L).
- Three routes tried, none works:
  - Cauchy–Schwarz on the twist reweighting gives 1/√y.
  - Transverse reflection positivity cuts the twist sheet, which brings back an additive perimeter term.
  - Averaging over cut positions fails because the split observable is not translation-invariant.

**Thermal-excess numerics.** log Kper₀ is the first chain step, i.e. time-doubling with spatial L³.

| β, L | log Kper₀ | pre-reg | verdict |
|---|---|---|---|
| 2.5, 8 | 1.25(55) | (18) < 1.0 | fails on central value (0.5σ) |
| 2.6 / 3.0 / 4.0, 4 | 3.73(23) / 2.46(22) / 5.10(47) | (19) monotone rise, last > first + 1 | fails (dip at 3.0, 4σ) |
| 2.5, 12 | −0.08(99) | (20) < 0.8 | holds, not significant |
| 2.6, 12 | 2.78(102) | (20) < 1.0 | **fails** (1.8σ) |
| 2.6, 8 | 2.29(80) | (20) > 1.5 | holds (1σ) |

The working hypothesis was that log Kper₀ is set by T/T_c with T = 1/L, which would give L₀(β) = 1/(a T_c).
- It is consistent with the two small values from §10: β 2.4 L8 gives 0.07, and β 2.3 L6 gives 0.40. Both are boxes
  with L > N_t^c.
- It is not supported at β 2.6 L12.
- A rerun at 6× statistics is pre-registered as (21).

**Status.** Both open inputs now reduce to sector-resolved interface free energies being sub-area, uniformly in β, above
some L₀. That is still unproved. The missing ingredient is a local clustering property of flux sectors, which is
weaker in form than confinement but not established at weak coupling.

**Addendum: a rigorous finite-size criterion on ℤ² × T²_{L⊥}** (`Twisted/TwistedSlabCriterion.lean`).
Fix the transverse sides at L⊥ and double only in-plane. Then no transverse step and no spectral input are needed.
- The elementary interpolation bound log Kper ≤ 2β·N_bnd is only linear in L here: N_bnd = 6LL⊥² and then 12LL⊥².
- So the per-scale log constant is m_k ≤ 3 log 2 + 48βL⊥²·L_k, which is sub-area (q = 2).
- Result: if one finite box has y(L₀, L₀, L⊥, L⊥) < ½·exp(−24βL⊥²L₀), then y(2^k L₀) ≤ exp(−4^k δ) for all k: area-type
  decay, and an area law in the twist plane via Tomboulis–Yaffe (cited).
- Conversely, a genuine area law y ~ e^{−σL²} makes the criterion hold for all large L₀. So area-type decay of the
  flux ratio on ℤ² × T²_{L⊥} is decided by a single finite box.

What it still depends on:
- the by-hand identification of the in-plane step `four_step` with lattice sector traces, as throughout;
- Tomboulis–Yaffe for Wilson loops.

It does **not** reach ℝ⁴. Every transverse doubling costs β·L²L⊥ under the elementary bounds, which is beyond sub-area.
So L⊥ must stay fixed, and the threshold exp(−24βL⊥²L₀) is far below anything measurable. This is the precise form of
the remaining gap: to let L⊥ grow, the transverse interface cost must improve from volume to o(area).

## 13. Does the flux-sector difference on the cut scale sub-area? (2026-11-09)

Script `scripts/yang_mills_sector_slab.py`, data `data/yang_mills_sector_slab_2026_11_09.json`. Pre-reg (22) was
committed in c55d8ce before any run.

S(L) is the zero-flux minus one-flux sector difference summed over one transverse cut slab:
S = 2zD/(1−z²), with D = (1/L) Σ_box(⟨P⟩_tw − ⟨P⟩) over plaquettes in planes (0,3), (1,3), (2,3). Boxes L⁴, 8000 sweeps.

| β | L | z | S | 16–84% | S/L³ |
|---|---|---|---|---|---|
| 2.3 | 4 | 0.42 | −0.73 | [−0.83, −0.63] | −0.011 |
| 2.3 | 6 | 0.91 | −0.57 | [−2.3, 0.8] | — |
| 2.3 | 8 | 1.09 (noise) | undefined | — | — |
| 2.4 | 4 | 0.25 | −0.19 | [−0.23, −0.16] | −0.0030 |
| 2.4 | 6 | 0.46 | −0.57 | [−0.78, −0.39] | −0.0026 |
| 2.4 | 8 | 0.76 | −1.35 | [−3.0, −0.6] | −0.0026 |

**Verdict on (22): FAILS.**
- At β 2.4 the exponent of |S| ~ L^p is p = 2.8 [1.7, 4.1] (16–84%) from L4 to L8, with P(p < 2) = 0.23.
- S/L³ is flat at 0.0026–0.0030, which is **volume scaling**, not string scaling.
- β 2.3 is undetermined, because z is within noise of 1 at L ≥ 6.

**Caveat.** At β 2.4, N_t^c ≈ 5.6, so the L4 and L6 boxes are at or above the deconfinement temperature (T = 1/L). Only
L8 is cold. In a deconfined box the flux sectors genuinely differ throughout the volume, so a volume law there is
expected and does not decide the asymptotic, confined scaling. The one cold point (L8) has a 2× error bar.

The data therefore do **not** support the sub-area hypothesis in the accessible range. They would only become informative
for boxes well above 1/(aT_c) with z measured to ≪ 1 − z, which is beyond the present method.

**Pre-reg (21)** (48000 sweeps; `data/yang_mills_thermal_excess_2026_11_09c.json`):
- β 2.5 L12 gives 0.30(36) < 0.8: holds.
- β 2.6 L12 gives 1.40(58), against a prediction below 1.0: fails on the central value (0.7σ).
- Combined with (20), β 2.6 L12 averages 1.74(50), 1.5σ above 1.0. The T/T_c hypothesis with N_t^c(2.6) ≈ 10–11 is not
  confirmed: log Kper₀ does fall from L8 (2.29) to L12, but more slowly than predicted.

## 14. Attempting confinement directly: the closest prior attempt and the U(1) test (2026-11-09)

**Closest prior attempt.** Tomboulis (arXiv:0707.2179, 2007) claimed confinement for all β in 4D SU(2). He used the same
order parameter as this program, the vortex free energy Z⁻/Z. Z and Z⁻ were bounded above and below by
Migdal–Kadanoff-type decimations, with interpolation parameters (α, t, r) chosen so the bounds become exact.

Ito and Seiler (arXiv:0711.4930, 0803.3019; reply arXiv:0712.2620) identify open steps:
- existence of the matching points t*, t_m (a contractivity argument is missing);
- global continuation of t(λ) from λ = 0 to λ = 1;
- the parameter r: r < 1 is needed for the derivative bounds, but it lets the flow reach the weak-coupling fixed point
  (crossover near β ≈ 4.8 at r = 0.9);
- most importantly, the argument "seems to work even for U(1)", which deconfines at large β. So, as written, it cannot be
  correct.

**The U(1) test applied to this program.** Any valid confinement argument must use an input that is false for U(1) in
its Coulomb phase. Checked against the chain here:
- The in-plane step (y' ≤ K y²), the flux-basis identity (§12), the sub-area tolerance (`TwistedSubArea`) and the slab
  criterion (`TwistedSlabCriterion`) are all algebra plus positivity. They hold verbatim for a Z₂-twist in U(1). For
  U(1) the slab criterion's base condition simply fails: y stays O(1).
- K̄ (bounded thermal excess) holds for U(1) too. The free photon gives log Kper ≈ O(1).
- So the only input that can fail for U(1) is the remaining one: sub-area transverse cost, i.e. local indistinguishability
  of flux sectors on the cut. In the Coulomb phase the electric flux spreads over the whole cross-section (field
  ~ 1/L⊥²). The sector difference is then volume-like, and the hypothesis fails, as it must.

The program therefore passes the U(1) test: everything abelian-blind is proved, and the one open input is exactly where
non-abelian dynamics (flux-tube formation) has to enter. That is also why it cannot be closed by the elementary methods
used here.

**What a proof would need.** The open input is a clustering estimate for the flux-sector measures at weak coupling,
uniformly in β. A flux string must be shown to be localized, with sector differences decaying away from it. The only
known machinery that controls lattice SU(2) uniformly as β → ∞ is multiscale renormalization group (Bałaban's
UV-stability programme). It has never been carried to infrared confinement. No step in this programme supplies that
estimate. The measurements in §13 (volume-like S at accessible sizes) neither support nor refute it in the asymptotic
regime.

**Status: confinement is NOT proved.** The reduction stands:
- proved: the abelian-blind chain (Lean, standard axioms);
- open: sector clustering for the 4D SU(2) flux measures, which is the non-abelian content.
