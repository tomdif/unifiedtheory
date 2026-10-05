# Aharonov–Bohm on causal orders: what this repository can now say

Date: 2026-10-05. Prompted by the external report "Aharonov–Bohm effect open
questions" (Downloads) and its `ring_time_dependent_flux.py`. Revised the same
day after review.

Lean (0 sorry; axioms `propext, Classical.choice, Quot.sound` only):
`UnifiedTheory/Audit/KFCausalAharonovBohm.lean`, `UnifiedTheory/Audit/KFCausalNerveHolonomy.lean`.
Neither is registered in `UnifiedTheory.lean` yet.
Numerics (`python3.11`): `scripts/ab_order_complex_h1.py`, `ab_thickened_antichain.py`,
`ab_window_scaling.py`, `ab_chain_pair_holonomy.py`, each with a matching `.log` in the repository root.

## Proved

| Report candidate | Theorem | Content |
|---|---|---|
| #1 triviality lemma | `OrderCocycle.coboundary_of_directed` | A cocycle on all relations of an upward-directed preorder is a coboundary, for any group. This generalizes CAG `cone_kills_H1`. |
| #1 finite caveat | `Crown.crown_cocycle_not_coboundary` | The crown P₄(S¹) carries a ℤˣ cocycle with holonomy −1. |
| #1 gauge invariance | `wilson_gauge_covariant`, `wilson_gauge_invariant` | The Wilson factor of co-terminal paths is conjugated at the source. In the Abelian case it is invariant. |
| #2 decoherence functional | `dressedD_diagonal`, `dressedD_offdiag`, `dressed_strong_positivity` | In the U(1)-dressed D the flux enters only off the diagonal, and strong positivity is preserved. |
| #2 × Born-from-growth | `unitarity_quantizes_with_flux`, `two_history_flux_periodic` | A flux shifts the repository's normalization condition to cos(θ₁−θ₂+Φ)=0. It is periodic under Φ ↦ Φ+2π. |
| #6 ring model | `ring_rigid_rotation` | For any flux history, the evolution is a rigid rotation of the static-initial-flux evolution by ∫(α−αᵢ)dt, times a global phase. The script's 10⁻¹⁴ agreement is therefore an identity. |
| declared 2-complexes | `hol_homologous`, `hol_gauge_cycle`, `hol_nsmul_generator` | Flat on the declared triangles ⇒ holonomy is additive on 1-chains, kills boundaries and depends only on the homology class. Gauge changes act only through ∂c. With H₁=ℤ, one number (the generator's holonomy) fixes everything. **Not proved:** the converse (trivial holonomy on all cycles ⇒ coboundary). Without it there is no Lean statement that flat cocycles modulo gauge form exactly a circle. |

## Numerics

**1. Global order complex** (`ab_order_complex_h1`). For a short slab, b₁ is noise and much larger than 1. Once the slab is tall enough to be effectively directed, b₁ = 0. The tube and no-tube 2+1 runs cannot be told apart. Reading (reviewer's correction): a thickened antichain is itself a thin slab of the same order. The nerve does not see something the order "couldn't"; it removes the noise loops. Both cutoffs are plausibly the scale at which two elements become joined in two inequivalent ways. The upper one is checked below; the lower one is not.

**2. Thickened-antichain nerve window** (`ab_thickened_antichain`). There is a window of n with b₀=b₁=1, and in it the embedding-angle AB cochain is flat with winding ±1. Calibration:
* **Cylinder: a reproduction.** Major–Rideout–Surya (arXiv:0902.0434) already report stable-homology windows for 2d and 3d sprinklings, and the cylinder is globally hyperbolic, so their theorem covers it.
* **The holonomy is a degree computation.** With phases built from embedding angles, "flat with winding ±1" means the angle map is an isomorphism on H₁, so e^{±iΦ} follows by construction. The order-only version is item 4.
* **2+1 minus the tube is the new part, but only as numerics.** That spacetime is not globally hyperbolic (diamonds that meet the tube are non-compact), so the MRS theorem does not apply. Its upper edge was capped by the slab top and **was not measured**. The expected scaling is ρR³ for tube radius R, with the window closing for tubes only a few discreteness lengths wide. That is untested.
* **No-tube control.** It is ordinary curvature inside the accessible region, not "type II", which was a mislabel. The useful check here is Stokes: the triangle windings over a 2-chain spanning an axis-encircling loop should sum to ±1. That has not been run, and it would give `discrete_stokes` real 2-cells.

**3. Window scaling on the cylinder** (`ab_window_scaling`; ρ = 1000–10⁴, 5 seeds). The prediction is n_max ≈ ρL²/16: height h ≈ √(n/ρ), shadow width 2h, and opposite shadows meet at h = L/4.

| ρ (L=1) | median n_hi | predicted ρ/16 | median n_lo |
|---|---|---|---|
| 1000 | 60 | 62 | 5 |
| 2000 | 114 | 125 | 9 |
| 4000 | 185 | 250 | 9 |
| 7000 | 354 | 437 | 9 |
| 10000 | 574 | 625 | 9 |

The grid is geometric with step ×1.18, and n_hi is the last grid point inside the window, so the true edge lies in [n_hi, 1.18·n_hi). On that basis the data agree with ρ/16 to within about 15% except at ρ=4000 (13–26% low). Fitted exponent: n_hi ∝ ρ^(0.96±0.03). n_lo grows weakly (ρ^(0.24±0.05)). In physical units the window therefore runs from a few discreteness lengths up to L/4; "opens without limit" holds only in units of n. The L = 2 runs are not independent evidence: by scale invariance a 1+1 sprinkling depends only on ρL², and with the same seeds they reproduce the corresponding ρL² runs exactly.

**4. The AB step, order-only** (`ab_chain_pair_holonomy`; cylinder, ρ = 3000 and 10⁴, 3 seeds each, 3000 random pairs p<q per run). Everything except the sprinkling uses the order alone:
* Dowker complex K on A (simplices = subsets of a common shadow), b₁(K) = 1 in every run.
* The integral generator ω of H¹(K;ℝ) is found by solving the triangle-flatness equations in spanning-tree gauge. The AB cocycle is Φ·ω: no angles, and the flat cocycles mod gauge are parametrized by Φ.
* For p below A and q above, the chains p<a<q split into classes = components of J⁺(p)∩J⁻(q)∩A in K. For two classes, the Wilson factor of chains through a₁ and a₂ is exp(iΦ·h), where h = ω(a₁ → a₂ inside J⁺(p)∩A, back inside J⁻(q)∩A).

Results, restricted to pairs where J⁺(p)∩A and J⁻(q)∩A are contractible in K:
* two chain classes: **h = ±1 in 212/212 pairs**, for every choice of a₁, a₂ and path;
* one class: **h = 0 in 5154/5154**;
* the order never produces two classes where the continuum has one arc. The opposite happens in 2–3% of pairs: a second overlap arc smaller than the discreteness contains no element of A.
* When q's past (or p's future) wraps the whole circle, the loop is not defined up to homotopy and h takes mixed values {0, ±1} (130 of about 10⁴ such pairs). There is no AB diamond there, so this is correct behaviour rather than a failure.

**What is forced and what is empirical.** The slice shadows J⁺(p)∩A and J⁻(q)∩A cover the circle. Given b₁(K) = 1 and both pieces contractible (step 7), Mayer–Vietoris fixes h = ±1 between components, and h = 0 within one. So 212/212 and 5154/5154 check the implementation, not physics; the statement belongs in Lean, not numerics. The empirical content is how often step 7 keeps a pair and where two components begin (item 5).

**Limits:**
* only three-element chains p<a<q were tested. A general chain need not contain an element of A, so it needs a crossing rule.
* **the relation p<q is itself a chain with no crossing point.** In the order it is one relation standing for both sides at once. Any propagator summed over relations (Johnston) contains that term, and the directed-order lemma applies to it. Item 5C measures the consequence.

**5. Slicing, short pairs, images, ℤ-cover** (`ab_slicing_and_images.py`; logs `ab_slicing_and_images.log`, `ab_zcover.log`; cylinder, ρ = 3000, n = 40, 2 seeds; C and D at ρ = 2000 and 1500, m = 4).
* **The slices are not maximal as first built.** The minimal elements of {|J⁻(x)| ≥ k} miss 2–10 elements per slice, so they are not maximal antichains. After greedy extension they are (asserted). All slices, including a random greedy maximal antichain, give Dowker b₀ = b₁ = 1. The slices are chosen by past cardinality, which is order-intrinsic.
* **A. Slicing independence** (lower slice k=190 vs upper k=370, about 0.1 apart in time, for pairs below and above both). Chains p<a<b<q map lower classes to upper classes. With one global orientation sign fixed by a reference pair, the holonomy agrees in **298/298** pairs where the class map is a bijection. In **55 of 354 two-class pairs (16%)** it is not. **Correction after diagnosis (item 6):** the earlier reading, "some lower class reaches both upper classes", was never checked and is wrong.
* **B. Short pairs and keep rate** (unbiased pairs, binned by t_q−t_p for diagnosis only). Below L/2: **0 two-class pairs among 1359 kept**. Step 7 keeps 100% up to 0.4, then 74–77% at 0.45–0.5, 37–39% at 0.55–0.6, 10–11% at 0.6–0.7, and **0% above 0.7**: once q's past on the slice wraps the circle, the loop is undefined. Among kept pairs, two classes make up 1–2% at 0.5–0.55, 11–12% at 0.55–0.6, and 8–24% at 0.6–0.7. The AB diamond in this setup is the narrow band t_q−t_p ∈ (L/2, ~0.7).
* **C. The relation term fails** (Johnston K = ½C(I + m²C/2ρ)⁻¹ vs the continuum image sum ½Σ_k J₀(mτ_k)). One-image pairs: K matches ½J₀ to within 0.003 in every bin, which validates the implementation. Two-image pairs: K matches neither the image sum nor a single image (Δt 0.5–0.7: K = 0.090–0.096, one image 0.180, image sum 0.545; Δt 0.7–1.0: K = −0.19, one image −0.10, image sum +0.065). The massless term ½C stays at ½ while the continuum gives ½ × the number of images. **The relation-based propagator does not converge to the cylinder Green function once both ways round are open**, even at zero flux.
* **Novelty:** the literature on causal-set propagators in multiply connected spacetimes has not been searched, so the failure in C should not be called new.
* **D. The ℤ-cover fixes it.** Sprinkle the same points into three deck copies of the unwrapped strip, compute K there, and set K_Φ(x,y) = Σ_k e^{ikΦ} K_cover(x, y+k). This matches the continuum Σ_k e^{ikΦ}½J₀(mτ_k) at Φ = 0, π/2 and π, for one-image and two-image pairs, to within about 1–3% (e.g. two images, Δt 0.5–0.7: 0.543/0.253/−0.038 against 0.544/0.253/−0.038). Charged matter on the cylinder is consistent with propagation on the ℤ-cover, with Φ entering as a character of the deck group. This agreement is forced by linearity once the one-image check validates K; the finding is the failure in C. In the massless case the statement is exact and needs no sprinkling: K = ½C is ½ on every related pair, while the continuum value is ½ × the number of images. **Caveat:** the cover here is built from the embedding, by copying coordinates. An order-intrinsic construction is open; it is what slicing independence (item A) would supply, and item A already shows where that transport is ambiguous.

**6. The 16% diagnosed** (`ab_transport_diagnosis.py` / `.log`; n = 15 and 40, 2 seeds, three slice pairs). Each slice element is labelled with its geometric component (coordinates used for diagnosis only). K's classes **never** disagree with the geometric components: 0 bridged and 0 split cases in every configuration. Every non-bijective case is "only one class linked" (a few are "no links"), and the smallest class almost always has 1–2 elements. It is a sampling artifact: one overlap arc holds one or two slice elements, and none of them is related to the matching class on the other slice. No relation ever joins different geometric components, as the continuum null-ray argument requires. The rate (7–20%) does not fall with thinner shadows (n = 15 vs 40) or with closer slices (separation 0.05 vs 0.1). The reviewer's predicted mechanism, bridging across narrow gaps, was tested and is not what happens.

**7. The ℤ-cover built from the order** (`ab_order_cover.py` / `.log`; ρ = 3000, 25 slices about 0.05 apart, n = 25, 2 seeds).
* X has edges = shadow edges within each slice plus relations between adjacent slices, and 2-cells = all 3-cliques plus squares (a ~ a′ in one slice, a < b, a′ < b′, b ~ b′ in the next, no diagonal).
  - Without the squares, dim H¹(X) = 5 and 8.
  - With the squares but n = 12 (one slice below the window), it is 2.
  - With n = 25, every slice has (b₀,b₁) = (1,1) and **dim H¹(X) = 1**.
* The integral cocycle comes from propagating cell flatness from a spanning tree. **It matches the coordinate winding on every edge after one gauge and orientation match: 0 mismatches out of 19,976 and 18,563 edges.**
* Lift the relations between adjacent slices to sheets and take the transitive closure. Compared entry by entry with the coordinate cover (sheets ±3, about 6.4M entries per seed): **FP = 0 exactly**, FN = 25.6% / 24.8%.
* FN by proper time τ of the lifted pair (non-adjacent slices; adjacent pairs have 0% FN, being the generators): 90% at τ < 0.05, 59%, 52%, 48%, 44% and 40% in successive 0.05 bins, and **17% at τ ≥ 0.3**. The nearly null exceptions are as predicted. The 17% residual at long τ is not diagnosed; likely cause: lifted chains must pass through every intermediate slice, and the slices are sparse.
* Image counts from the order alone, for related base pairs: of pairs with 2 continuum images, 32–35% get 2 sheets, 60–62% get 1 and 6–8% get 0. Of pairs with 1 image, 84% get 1 and 16% get 0. The undercounting has the same cause as the FN.
* **Plateau check** (`ab_plateau_check.log`): the reviewer's guess was that the 17% at long τ comes from elements with no generator into the adjacent slice. **Falsified.** Such elements are about 0.1% of the total. Pairs ending on one are always missed, but there are only 911 such entries in seed 0 and 0 in seed 1; the rate stays near 16% among pairs whose ends both have generators. The slice-chain generating set is too thin, since a maximal antichain need not meet every chain. Item 8 replaces it.
* **Scope:** dim H¹(X) = 1 is not a single point. The n-window scan (`ab_window_scan.log`, ρ = 3000, 5 seeds) gives dim H¹ = 1 on every seed for n = 20, 25, 35 and 50; n = 70 gives [1, 1, 1, 0, 1]. n = 15 fails on one seed, giving 2. At ρ = 1200, n = 25 fails on one of three seeds (dim 0). Johnston's propagator is established in 1+1 and 3+1, so the 2+1 tube runs can test topology and the cover but not a propagator (to be verified).

**8. ℤ-cover from a circular coordinate** (`ab_circular_cover.py`; following the reviewer's proposal; logs `ab_circular_cover*.log`, `ab_seed2_diag.log`, `ab_e2e.log`).
* **Method.**
  - **θ:** take the least-squares (harmonic) representative of the integral cocycle on X, and set θ = f mod 1 on slice elements. Off-slice elements get the circular mean of θ over their past shadow on the highest slice below.
  - **Generators:** base links whose slice span is at most B = 5, lifted by the nearest rule.
  - **Lift:** the transitive closure over sheets. Coordinates are used only for slice levels, as a linear extension, and for the comparison.
  - **Result:** θ tracks the coordinate everywhere to within 0.12.
* **Margin failure.** With no further filter, 3 of 4 seeds at ρ = 3000 are clean. In seed 2, **exactly 2 of 26,157 links were genuinely mislifted.** Both span 5 slices with displacement 0.39, and they produced 39,647 false positives in the closure: one bad generator poisons everything above it. (The "151 mismatched generators" printed by the gauge-matching walk was mostly propagation inside that walk. The gauge-free count is 2.) Lowering B to 3 removes them, at the cost of FN 1.65%.
* **Fix (order-only):** drop generators whose lifted θ-displacement exceeds 0.25. With θ error at most about 0.12 per end, the true displacement stays below ½. **Result, ρ = 3000, n = 25, 4 seeds:** FP = 0 and 0 gauge mismatches in every seed; FN 0.77–0.85%, concentrated near null (19% at τ < 0.05, 11%, 4–5%, 1%, then 0.0–0.2% from τ = 0.2 up). **Two-image pairs get both sheets in 97.8–98.0%** (vs 32–35% for the slice-chain cover of item 7), and three-image pairs get all three in 92–94%. The reviewer's prediction (FN only on long, nearly null links; two-sheet recovery near 100%) holds, provided the margin filter is applied.
* **Low density.** At ρ = 1200 (no filter), FN is 1.4%, two-image recovery 96.2%, and one seed has a single mislifted generator (496 FP). This is the same margin effect, with the harmonic residual up to 0.38.
* **End to end: AB from the order alone on the cylinder** (ρ = 1200, n = 25, B = 5, no filter, m = 4, 3 seeds). Johnston's K is built on the order-built cover and summed over sheets with e^{ijΦ}. As a control, K is also built on the coordinate cover of the same sprinkling, gauge-matched node for node.

  | Two-image pairs, Δt 0.5–0.7 | K_order | K_coord | Continuum |
  |---|---|---|---|
  | Φ = 0 | 0.508 / 0.512 / 0.528 | 0.533 / 0.538 / 0.556 | 0.536 / 0.537 / 0.540 |
  | Φ = π/2 | 0.243 / 0.238 / 0.252 | 0.253 / 0.246 / 0.264 | 0.252 / 0.249 / 0.253 |
  | Φ = π | −0.022 / −0.037 / −0.023 | −0.028 / −0.046 / −0.029 | −0.032 / −0.038 / −0.033 |

  - The bare relation propagator in item 5C gave 0.09 against 0.545 at Φ = 0.
  - **Cover error** (K_order − K_coord) is −0.024 to −0.028 at Φ = 0 (about 5%) and within about 0.01 at Φ = π/2 and π.
  - **Discreteness noise** (K_coord − continuum) is up to 0.02 on seed 2.
  - The 5% cover error exceeds the 1.4% entry-level FN at this density. It plausibly comes from the 3.8% of two-image pairs that miss a sheet, amplified through the interval term, but this is not decomposed.
  - The massless case, where the error should equal the entry FN rate exactly, was not run separately.
  - The e2e run predates the margin filter. A rerun with the filter and at higher density is pending.

**9. End to end with the margin filter at ρ = 3000** (`e2e_fourier` in `ab_circular_cover.py`; logs `ab_e2e_rho3000.log`, `ab_e2e_fourier_validation.log`; n = 25, B = 5, filter 0.25, 4 seeds).
* **Method: deck Fourier transform.** The lifted relation depends only on the sheet difference, so on the infinite cover K_Φ = ½ Ĉ_Φ (I + m²Ĉ_Φ/2ρ)⁻¹ exactly, with Ĉ_Φ(u,v) = Σ_d e^{idΦ} C_d(u,v), the flux-twisted causal matrix. This is Johnston's formula with C replaced by Ĉ_Φ, and at Φ = 0, Ĉ_0 is the order-derived image count. It is N×N and reproduces the dense ρ = 1200 result (0.5087 vs 0.5082).
* **Massless, two-image pairs.** Order cover: 0.973–0.975 (Δt 0.5–0.7) and 0.988–0.989 (Δt 0.7–1.0), where the coordinate cover gives exactly 1. At Φ = π/2 it gives 0.489 / 0.498 against ½; at Φ = π, +0.003 to +0.009 against 0. One-image pairs are within 0.004 of ½. The deficit is the missed-sheet fraction, so the massless error equals the entry-level FN, as predicted.
* **m = 4, two-image pairs, Δt 0.5–0.7.** Order minus coordinate is −0.013 to −0.014 at Φ = 0 (−2.4 to −2.6%), −0.004 to −0.005 at π/2, and +0.003 to +0.005 at π. Values: order 0.522 / 0.525 / 0.535 / 0.541 against coordinate 0.535 / 0.538 / 0.550 / 0.554 and continuum 0.537–0.538. The bare relation propagator gave 0.09.
* **The massive error decomposes.** Its relative size (2.4–2.6%) matches the massless deficit (2.5–2.7%). **Denominator, corrected after review:** that deficit is the fraction of SHEETS missed. A two-image pair missing one sheet loses only half its value, so about 5% of two-image PAIRS in that bin miss a sheet. The one-parameter fit (1−f)·|cos(Φ/2)| + f/2 with f = 5% reproduces the whole |K_Φ| row (0.975, 0.903, 0.697, 0.389, 0.025 vs observed 0.974, 0.902, 0.697, 0.388, 0.025). So the discrepancy is entirely missed sheets, with no phase error. The 5% at ρ = 1200 fits the same picture: 96.2% two-sheet recovery, plus one mislifted generator before the filter.
* **Discreteness, separately.** In seeds 2 and 3 the coordinate cover itself misses the continuum by up to 0.02 (one-image Δt 0.5–1.0, two-image Δt 0.7–1.0). That is sprinkling noise in Johnston's K, not a cover effect.

**10. Gauge-invariant headline** (`ab_e2e_abs.log`, ρ = 3000, filter 0.25, 2 seeds). |K_Φ(p,q)| needs no gauge alignment. For two-image pairs its flux dependence is the interference between the two sheets.
* **Massless, two-image pairs (continuum |cos(Φ/2)|).** At Φ = 0, π/4, π/2, 3π/4, π:
  - order cover: 0.974, 0.902, 0.697, 0.388, 0.025 (Δt 0.5–0.7; seed 1 agrees to 0.001);
  - coordinate cover and continuum: 1, 0.924, 0.707, 0.383, 0.
* **One-image pairs:** |K| is flux-independent at every Φ, in both covers. Only pairs joined in two inequivalent ways see the flux.
* **m = 4, two-image pairs, Δt 0.5–0.7:**
  - order cover: 0.522, 0.491, 0.403, 0.282, 0.185;
  - coordinate cover: 0.535, 0.502, 0.412, 0.287, 0.187;
  - continuum: 0.537, 0.505, 0.414, 0.287, 0.186.
* **The Φ = π residual is bookkeeping** (reviewer's account, consistent with the numbers). Exactly one of the two images crosses the seam, and the nearly null image is the longer one, so it is more often the one wound around. Missing it leaves ½ where the sum should be 0. With a missed fraction of about 2.6%, the expected values are +0.003 (Δt 0.5–0.7) and +0.009 (Δt 0.7–1.0); observed +0.003–0.006 and +0.007–0.009.
* **No continuum limit is claimed.** The missed two-sheet fraction was 3.8% at ρ = 1200 (unfiltered) and 2.1–2.6% at ρ = 3000 (filtered): two points under different settings. Some loss may be irreducible. The reviewer's argument, not yet run: a nearly null link in the cover leaves no trace in the base order when its endpoints are already related the other way round. A controlled density scan at fixed settings is needed.

**10b. Density scan, 1+1** (`density_scan` in `ab_circular_cover.py`, `ab_density_scan.log`). Fixed physical settings: slice spacing 0.05, span bound B = 5, margin 0.25, n ∝ ρ (n = 25 at ρ = 3000). 4 seeds per density; per Δt bin, two-image pairs missing a sheet and sheets missed.
* **FP = 0 in all 13 completed runs.** ρ = 1500 (n = 12) is outside the window in 3 of 4 seeds.
* **Missed fraction ∝ ρ^(−1.06±0.03) in every Δt bin**, for pairs and sheets alike, over ρ = 2250–4500:

  | Δt bin | pairs missing a sheet (ρ = 2250 / 3000 / 4500) |
  |---|---|
  | 0.5–0.6 | 12.2% / 9.2% / 5.9% |
  | 0.85–1.0 | 2.9% / 2.1% / 1.4% |

* No floor is visible, but the range is only a factor of 2 in density. This is consistent with the loss vanishing like 1/ρ; **no continuum limit is claimed.**

**11. Mayer–Vietoris lemma** (`UnifiedTheory/Audit/KFCausalMayerVietoris.lean`, 0 sorry, axioms `propext, Classical.choice, Quot.sound`; not registered in `UnifiedTheory.lean`). At the level of integer 1-chains on the declared complex of `KFCausalNerveHolonomy`:
* `same_component_bounds` / `hol_same_component`: endpoints joined inside P∩Q ⇒ the crossing loop bounds ⇒ holonomy 0.
* `crossing_independent`: the class does not depend on the paths chosen inside P and Q.
* `crossing_generates`: a cycle split as c_P + c_Q with ∂c_P = n·∂p_P is homologous to n·γ.
* `crossing_is_pm_generator` / `hol_crossing_pm`: H₁ generated by z of infinite order and γ a multiple of z ⇒ γ ≡ ±z.
* `split_of_edgeCover` / `hol_crossing_pm_of_cover`: the combined statement with the **cover hypothesis made explicit** (reviewer). Every edge of the generator must lie wholly in P or wholly in Q. A straddling edge is in neither, and without the hypothesis the split, and hence ±1, is unavailable. Geometrically it holds when the overlaps are wider than a simplex. Triangles enter only through the hypothesis that cycles in each shadow bound in K.
* **The reduction is now PROVED.** `deg0_is_boundary`: a degree-zero 0-chain supported on an internally joined set is a boundary there. `reduce_two_components`: applied per component of P∩Q, it gives ∂c_P = n·∂p_P. **`hol_crossing_pm_full`** therefore holds with no assumed reduction. Its hypotheses: two internally joined components of P∩Q, cycles in each shadow bound, the edge cover, and H₁ generated by z of infinite order with γ a multiple of z. Conclusion: holonomy ±hol z.

**12. Prior art** (checked 2026-10-05).
* B. Schmitzer, *Curvature and Topology on Causal Sets*, MSc dissertation, Imperial College London (2010). It introduces the **homotopy matrix** (zone number = the number of equivalence classes of causal trajectories from x to y, in the covering space) to define Johnston's propagator on the cylinder. **At Φ = 0 our twisted matrix Ĉ_0 is exactly this homotopy matrix**, and item 5C (the bare relation propagator fails on the cylinder) restates the reason it was introduced, so 5C is not new.
* L. Bogaardt, MSc dissertation, Imperial College London (2013), §3.7. It gives an order-only zone rule on the cylinder and reports that, as for Schmitzer, "this procedure fails when the spacetime has a dimension larger than two."
* **Schmitzer, full text checked** (67 pp., local text search). No phase, flux, twist, charge, gauge or holonomy weighting anywhere. §3.3 treats compactified M4 only by unrolling the sprinkling ("cheating", in his words, as it remembers coordinates). §4.2 is an order-only 2D reconstruction ("intersecting lightcones"), imperfect at zone boundaries. §4.3: "In dimensions higher than two … the whole procedure will not work. How to solve this problem is still an open question."
* **What may be new:**
  - the flux character e^{idΦ} (the AB propagator as Johnston's formula with the twisted matrix Ĉ_Φ). It is not in Schmitzer.
  - a reconstruction (nerve cocycle → harmonic circular coordinate → nearest-rule lift → closure) whose construction does not depend on dimension.
  - The case they leave open, flat 2+1 with one compact dimension, is therefore the next test, ahead of further 1+1 work.

**13. Flat 2+1 with one compact dimension: the open case** (`ab_cover_2p1.py`; logs `ab_2p1_run_n40.log`, `ab_2p1_run_n40_v2.log`, `ab_2p1_window.log`).
* **Geometry.** S¹_x (L = 1) × [0, 0.6]_y × [0, 0.8]_t at ρ = 3×10⁴, N ≈ 14,400. The circumference is about 31 discreteness lengths.
* **Construction.** Order-chosen maximal slices 0.05 apart, from t = 0.1 to 0.6. The complex X is built on pruned thickened-antichain shadows (n = 40):
  - within a slice, the true nerve;
  - between adjacent slices, edges when some element of one shadow precedes some element of the other, and witness 2-cells (one relation certifies each triangle);
  - then the harmonic circular coordinate, the nearest-rule lift of links (span ≤ 4 slices, |Δθ| ≤ 0.25), and the closure on sheets −1..1.
  - Coordinates are used for slice levels, to delimit the analysed region (shadows touching the y-boundary layer of 0.04 are dropped, as if a larger region were sprinkled), to restrict test sources to the central y band, and for the comparison.
* **Pre-registered outcomes** (reviewer):
  1. a window, FP = 0 and two-image recovery above about 90%;
  2. a window with poor recovery;
  3. no window (inconclusive).
* **Result, 2 seeds** (seed 0 also run once before the edge buffer, with identical numbers to within 0.1%):
  - every slice nerve is (b₀,b₁) = (1,1), and **dim H¹(X) = 1**;
  - θ vs coordinate: median error 0.016–0.018, max 0.13–0.19;
  - **0 gauge mismatches** (465k / 458k generators);
  - **FP = 0** over 14.0M / 14.3M entries;
  - FN 1.69% / 1.71%, entirely nearly null (28% at τ < 0.05, 13–14%, 3%, 0.2%, then 0.0% from τ = 0.2);
  - **two-image pairs: 88.4% / 88.3% get both sheets** (11.6% / 11.8% miss a sheet; 5.9% / 6.0% of sheets missed).
* **Reading.** By the pre-registered rule this sits at the boundary of outcome 1: just under 90% for pairs, above it for sheets. The order alone reconstructs the ℤ-cover and the image-count (homotopy) matrix in 2+1, the case Schmitzer and Bogaardt report their method cannot reach. Recovery is limited the same way as in 1+1 at similar resolution (1+1, Δt 0.5–0.6: 12% of pairs at ρ = 2250, falling as ρ^(−1.06)). A 2+1 density scan is needed to show the same fall.
* **Window.** In the earlier scan with clique cells and no edge buffer, n = 40 gave dim H¹ = 1 (2 seeds) and n ≥ 80 gave dim H¹ = 0. The diagnosis (`ab_2p1` diagnostic, ρ = 10⁴) found boundary half-disc shadows of angular radius up to 0.28 wrapping the circle. **With the witness cells and edge buffer** (`ab_2p1_window.log`, 2 seeds): **n = 40, 60, 80 and 120 all give every slice nerve (1,1) and dim H¹(X) = 1.** n = 20 has noisy slices (b₁ = 2–3 on 2–5 of 11), though X still has dim H¹ = 1. The window spans at least a factor of 3 in n. Its upper edge was not reached (the reviewer's estimate is πρL³/192 ≈ 490, which ran about 25% high in 1+1). The n = 80 failure in the first scan was the boundary artifact, not resolution. The cover comparison has so far been run only at n = 40.

**14. 2+1: density scan and the flux-twisted image-count matrix** (`ab_2p1_density.log`). Settings: ρ = 12k, 18k, 24k, 30k, 2 seeds each; n ∝ ρ (n = 40 at 3×10⁴, constant shadow width); slice spacing, span bound and margin fixed. Seed 1 at ρ = 12k is outside the window (dim H¹ = 2); the 7 others have dim H¹(X) = 1.
* **FP = 0 and 0 gauge mismatches in all 7 runs.**
* **Two-image pairs missing a sheet**, per Δt bin (ρ = 18k / 24k / 30k):

  | Δt bin | missing a sheet |
  |---|---|
  | 0.5–0.6 | 33.3% / 27.7% / 24.4% |
  | 0.6–0.7 | 13.8% / 11.6% / 10.1% |
  | 0.7–0.8 | 8.9% / 7.3% / 6.4% |

  Fitted exponent: **ρ^(−0.62 ± 0.02)**, between −0.56 and −0.65 across bins, for pairs and sheets alike. 1+1 gave ρ^(−1.06 ± 0.03).
* **Observation, not derived:** both exponents are close to ρ^(−2/d), i.e. the missed fraction ∝ ℓ² with ℓ = ρ^(−1/d). No floor is visible, but the range is a factor of 1.7–2.5 in density. **No continuum limit is claimed.**
* **Flux-twisted matrix |Ĉ_Φ(u,v)| = |Σ_d e^{idΦ} C_d(u,v)|** (gauge-invariant; the AB object in 2+1, where no causal-set propagator is established).
  - One-image pairs: flux-independent at every Φ (0.978 → 0.988 as ρ rises; coordinate cover 1).
  - Two-image pairs, ρ = 3×10⁴, at Φ = 0, π/4, π/2, 3π/4, π: order 1.883, 1.748, 1.365, 0.791, 0.114; coordinate and continuum 2|cos(Φ/2)| = 2, 1.848, 1.414, 0.765, 0.
  - The one-parameter form (1−f)·2|cos(Φ/2)| + f, with f = 11.57% the measured pair-miss rate, gives 1.884, 1.750, 1.366, 0.793, 0.116: **all within 0.002. The whole discrepancy is missed sheets, with no phase error, as in 1+1.**

## Caveat on existing code

In `DiscreteAmbroseSinger`, `Plaquette := GraphLoop`, so `discrete_stokes` uses the loop itself as its own plaquette. The theorem is true but has no content. `KFCausalNerveHolonomy` is the declared-2-cell replacement for the homology part.

## Next

0. 2+1: higher density (memory-limited at N ≈ 14k dense R; needs a bit-packed R); a non-flat or multiply-wound case; why the exponent looks like −2/d.
0b. Controlled density scan of the missed-sheet fraction at fixed settings.

1. 2+1 tube: measure the upper edge in a slab tall enough not to cap it; test ρR³ scaling and window closure for thin tubes; run the chain-pair test there.
2. Stokes check in the no-tube control (triangle windings over a spanning 2-chain sum to ±1).
3. Lean: (MV done, item 11) the component-reduction step; massless image-count lemma (½C = ½ vs ½·#images); converse: on a connected declared complex, trivial holonomy on all cycles ⇒ coboundary (spanning-tree gauge, as in `GAUGE_DRESSED_MEASURE`). Together with `hol_homologous` this gives flat cocycles mod gauge ≅ Hom(H₁, K).
4. Link-level pullback of ω, then the covariant BD operator (candidate #3).
