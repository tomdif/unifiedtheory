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

So two spacetime chains on either side of the hole differ by exactly e^{±iΦ}, with the phase defined from the causal order. Not done: a phase on every individual link (a full link-level pullback, needed for a gauge-covariant BD operator or Johnston propagator), the 2+1 tube version of this test, and the higher-density continuation.

## Caveat on existing code

In `DiscreteAmbroseSinger`, `Plaquette := GraphLoop`, so `discrete_stokes` uses the loop itself as its own plaquette. The theorem is true but has no content. `KFCausalNerveHolonomy` is the declared-2-cell replacement for the homology part.

## Next

1. 2+1 tube: measure the upper edge in a slab tall enough not to cap it; test ρR³ scaling and window closure for thin tubes; run the chain-pair test there.
2. Stokes check in the no-tube control (triangle windings over a spanning 2-chain sum to ±1).
3. Lean converse: on a connected declared complex, trivial holonomy on all cycles ⇒ coboundary (spanning-tree gauge, as in `GAUGE_DRESSED_MEASURE`). Together with `hol_homologous` this gives flat cocycles mod gauge ≅ Hom(H₁, K).
4. Link-level pullback of ω, then the covariant BD operator (candidate #3).
