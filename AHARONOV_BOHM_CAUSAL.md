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
* **Not yet:** using all elements rather than slice elements only; denser slices; Johnston's K on the order-built cover. Johnston's propagator is established in 1+1 and 3+1, so the 2+1 tube runs can test topology and the cover but not a propagator (to be verified).

## Caveat on existing code

In `DiscreteAmbroseSinger`, `Plaquette := GraphLoop`, so `discrete_stokes` uses the loop itself as its own plaquette. The theorem is true but has no content. `KFCausalNerveHolonomy` is the declared-2-cell replacement for the homology part.

## Next

0. Order-built cover: find the cause of the 17% long-τ FN (denser slices, or all elements instead of slice elements), then run Johnston's K on the order-built cover.

1. 2+1 tube: measure the upper edge in a slab tall enough not to cap it; test ρR³ scaling and window closure for thin tubes; run the chain-pair test there.
2. Stokes check in the no-tube control (triangle windings over a spanning 2-chain sum to ±1).
3. Lean: Mayer–Vietoris two-set-cover lemma (forced h = ±1 / 0); massless image-count lemma (½C = ½ vs ½·#images); converse: on a connected declared complex, trivial holonomy on all cycles ⇒ coboundary (spanning-tree gauge, as in `GAUGE_DRESSED_MEASURE`). Together with `hol_homologous` this gives flat cocycles mod gauge ≅ Hom(H₁, K).
4. Link-level pullback of ω, then the covariant BD operator (candidate #3).
