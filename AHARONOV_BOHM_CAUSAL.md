# Aharonov–Bohm on causal orders: what this repository can now say

Date: 2026-10-05. Prompted by the external report "Aharonov–Bohm effect open
questions" (Downloads) and its `ring_time_dependent_flux.py`.

Lean: `UnifiedTheory/Audit/KFCausalAharonovBohm.lean`, 0 sorry, axioms
`propext, Classical.choice, Quot.sound` only. It builds on `DiscreteBundles`,
`DiscreteAmbroseSinger` and `KFCausalQuantumMeasure`.
Numerics: `scripts/ab_order_complex_h1.py`, with output in `ab_order_complex_h1.log`.

## Proved

| Report candidate | Theorem | Content |
|---|---|---|
| #1 triviality lemma | `OrderCocycle.coboundary_of_directed` | A cocycle on all relations of an upward-directed preorder is a coboundary g(x)g(y)⁻¹, for any group. This generalizes CAG `cone_kills_H1`, which needs a global top. |
| #1 finite caveat | `Crown.crown_cocycle_not_coboundary`, `Crown.not_directed` | The crown P₄(S¹) carries a ℤˣ cocycle with 4-cycle holonomy −1. Finite causal sets can carry global cocycle holonomy, and it is classified by H¹ of the order complex. |
| #1 gauge invariance | `wilson_gauge_covariant`, `wilson_gauge_invariant` | The Wilson factor hol(γ₁)hol(γ₂)⁻¹ of co-terminal paths is conjugated at the source. In the Abelian case it is invariant. |
| #2 decoherence functional | `dressedD_diagonal`, `dressedD_offdiag`, `dressed_strong_positivity`, `two_slit_flux` | U(1)-dressed D: the diagonal is flux-independent, the off-diagonal entry is the Wilson factor, and strong positivity is preserved. |
| #2 × Born-from-growth | `two_history_flux`, `unitarity_quantizes_with_flux`, `two_history_flux_periodic` | A flux through the two-history diamond turns `unitarity_quantizes` into cos(θ₁−θ₂+Φ)=0. The repository's normalization condition is therefore flux-dependent, and a change of enclosed flux must be absorbed by the action gap. The measure is periodic under Φ ↦ Φ+2π (Byers–Yang). |
| #6 ring model | `ring_rigid_rotation`, `ring_lab_fringe_shift` | For any flux history, ψ(T) is a global phase times the evolution under the static initial flux, rotated rigidly by ∫(α−αᵢ)dt. The 10⁻¹⁴ agreement in the script is therefore an algebraic identity, not independent evidence. The "time-average", "initial-flux" and "cancellation" readings are readouts of this identity against different references. |

## Measured: the bare order complex does not see the hole

The quantities are b₀ and b₁ (over GF(2)) of the order complex of Poisson sprinklings, after reducing each to its Stong core. Beat-point removal was checked to preserve b₁.

* **1+1 cylinder S¹(L=1)×[0,T]** (π₁ = ℤ). For T < L/2, b₁ is spurious and much larger than 1 (13–23 at T=0.2; 2–6 at T=0.5, ρ=1000). For T > L/2, b₁ = 0, because the light cones wrap and the order becomes effectively a cone. As density increases the transition sharpens to T = L/2. **There is no window with b₁ = 1** (ρ = 300, 1000).
* **2+1 window minus a world-tube vs the same window with no tube.** b₁ is in the hundreds in both, and the two are statistically indistinguishable (T=1: hole 141–182, flat 215–273). Both decrease with T.

Conclusion: H¹ of the global order complex never isolates π₁(spacetime). For short slabs it is swamped by sprinkling-noise cycles; this is the "infinitely many link cycles" obstruction. For tall slabs it collapses to zero; this is the directed-order lemma. This supports, numerically, the report's claim that AB data on a causal set must live on a locality-restricted complex with a mesoscale, such as the Major–Rideout–Surya thickened antichains or small-diamond 2-cells. A global cocycle cannot carry it.

## Caveat on existing code

In `DiscreteAmbroseSinger`, `Plaquette := GraphLoop`, so `discrete_stokes` uses the loop itself as its own plaquette. The theorem is therefore true but has no content. A real combinatorial Stokes/Ambrose–Singer statement needs a declared 2-cell set, and that is the natural next Lean target. Natural 2-cell sets here are small diamonds, or the elementary squares of `KFCausalDiamondDirectionCover`.

## Measured: the thickened-antichain nerve sees the hole and carries its flux

`scripts/ab_thickened_antichain.py` (log: `ab_thickened_antichain.log`). It uses the Major–Rideout–Surya construction. A is the set of minimal elements of {t ≥ t₀}. T_n(A) = {x ∈ J⁺(A) : |J⁻(x) ∖ J⁻(A)| ≤ n}. The nerve is built from the shadows J⁻(m) ∩ A of the maximal elements m. On that nerve we place the AB cochain U = exp(iΦ·Δθ/2π), where Δθ is the wrapped angle between shadow centroids. "Flat" means every triangle has zero winding; "w" is the winding of the H₁ generator, so the holonomy is e^{iΦw}.

The window is the set of n where b₀ = 1, b₁ = 1, |w| = 1 and there are zero non-flat triangles:

| Geometry (seeds) | Window in n | Outside the window |
|---|---|---|
| 1+1 cylinder, ρ=1000 (4) | 8/12 – 50 | n small: b₀ > 1 or b₁ = 0. n ≥ 70: shadows wrap the circle, non-flat triangles appear, b₁ → 0 |
| 1+1 cylinder, ρ=3000 (4) | 8/18 – 140 | n = 200: wraps, 28–192 non-flat triangles |
| 2+1 window minus tube, ρ=1500 (3) | 12/18 – 200 (up to the slab top) | small n: noise b₁ of 2–24 with **w = 0** (non-winding) |
| 2+1 window, no tube, ρ=1500 (3) | **none** | b₁ = 0 for n ≥ 18. AB cochain non-flat on 10²–10⁴ triangles |

Findings:
1. **A stable window exists, and it widens with density.** The lower edge, n ≈ 8–18, is fixed by discreteness noise. The upper edge grows roughly in proportion to ρ (50 to 140 for 3× density), because wrapping happens at a fixed spacetime volume. In the continuum limit the window therefore opens without bound. This is the mesoscale that the global order complex lacks.
2. **The flux is carried exactly.** Inside the window the AB cochain is flat on every triangle, and the generator has winding ±1, so its holonomy is e^{±iΦ}. This is candidate #4 realized on a sprinkled causal set.
3. **Flatness separates type I from type II.** With the tube excised, the cochain stays flat at every n: the flux is invisible locally and appears only through holonomy (type I). Without the tube, the same cochain fails to be flat on triangles near the axis: the causal set occupies the region the flux threads (type II, curvature present). Non-winding noise cycles (w = 0 at small n) are distinguished from the hole automatically.

Limits: these are single slices with 3–4 seeds per configuration. The window edges have not been fitted against ρ with error bars. The 2+1 relation uses shortest paths around the tube in Minkowski space minus a world-tube, a spacetime whose global hyperbolicity (and hence the MRS theorem's hypotheses) has not been verified. The flux cochain uses embedding coordinates for shadow centroids; an intrinsic, order-only definition of U is still open.

## Next

1. Fit the window edges against ρ (more seeds, ρ up to 10⁴), and test cylinder circumference scaling.
2. Define the cochain intrinsically from the order, without embedding angles, and prove in Lean that a nerve cocycle with flat triangles has holonomy depending only on the H₁ class, with declared 2-cells.
3. Prove Lean Ambrose–Singer and "flat ⇔ Hom(π₁,U(1))" with declared 2-cells, using the spanning-tree gauge from `GAUGE_DRESSED_MEASURE`.
4. Covariant BD operator via the Fock–Schwinger reduction (candidate #3). This has no host yet.
