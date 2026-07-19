# The Lohmiller-Slotine Bridge — Session Writeup

## 1. Executive summary

The `LohmillerSlotine*` subfamily of `UnifiedTheory/LayerB/` formalizes the bridge between the framework's K/P (source / dressing) algebraic substrate and the standard Madelung-Bohm polar form of single-particle quantum mechanics in Lean 4. The session closes a watershed analytic step: for every C³ real-valued function on ℝ, the centered finite-difference Laplacian converges pointwise to the second derivative (`SmoothConvergenceTheorem_1D_proved`), and the same fact lifts coordinatewise to ℝⁿ (`fdLaplacianND_converges`). Combined with the algebraic core — which makes the Bohm quantum potential precisely the spatial curvature of the dressing magnitude `r = √(Q² + P²)` — the bridge from "discrete K/P amplitude" to "smooth Madelung-Bohm PDE" now has two of its three sub-bridges materially closed, and the third reduced to genuine differential geometry. The total weight: 2857 lines across four files, zero `sorry`, only the standard `propext`, `Classical.choice`, `Quot.sound` axioms.

## 2. The conceptual headline — Bohm Q = dressing curvature

The deepest physical content of the formalization is the pair of theorems `classical_iff_flat_dressing` and `bohm_correction_iff_curvature` in `LohmillerSlotineBridge.lean` (lines 410-438). Both identify the Bohm quantum potential as the spatial curvature of the dressing magnitude `r = √ρ`, which under the K/P identification `(Q,P) = (r cos s, r sin s)` is exactly the complex modulus `|z|`.

The precise Lean statement of the converse half (file `LohmillerSlotineBridge.lean`, lines 421-438) reads:

```lean
theorem bohm_correction_iff_curvature (W : WaveData)
    (hBare : BareHamiltonJacobi W) :
    HamiltonJacobiWithBohm W ↔ W.r_xx = 0
```

`BareHamiltonJacobi` is the standard classical Hamilton-Jacobi equation `∂_t φ + (∂_x φ)²/(2m) + V = 0` (in `(r, s)` variables, multiplied by `r`). `HamiltonJacobiWithBohm` is the same equation with the Bohm quantum potential `Q = −(ħ²/2m)(r_xx / r)` retained on the right-hand side. The theorem says: assuming bare HJ holds, the Bohm correction is consistent iff `r_xx = 0`.

The forward direction (`classical_iff_flat_dressing`, lines 410-416) is symmetric: if `r_xx = 0` then `HamiltonJacobiWithBohm` and `BareHamiltonJacobi` are equivalent.

Physical reading. The dressing magnitude is the K/P-algebra-internal name for the wavefunction modulus. Its second spatial derivative measures whether the modulus varies linearly or nonlinearly in space. The two theorems together say: quantum mechanics, in the K/P framework, IS the regime in which the dressing magnitude is not spatially flat. The Bohm quantum potential is not an extra term grafted onto classical mechanics; it is the algebraic invariant of nonlinear spatial variation of `|z|`. Classicality coincides with `r_xx = 0`. The curved-space generalization `curved_classical_iff_harmonic_dressing` (lines 683-690) reads the same statement on an emergent manifold: classicality ≡ `Δ_g r = 0`, i.e., the dressing magnitude is harmonic in the emergent metric. Quantum mechanics is the obstruction to harmonicity.

L-S themselves do not state this. Their Lemma 1 derives the Madelung-Bohm equations from the polar ansatz; the identification with K/P curvature is what makes the bridge meaningful inside the unified-theory framework.

## 3. The watershed theorem — `SmoothConvergenceTheorem_1D_proved`

The session's main analytic deliverable lives in `LohmillerSlotineSubBridge2.lean`, lines 1041-1043:

```lean
theorem SmoothConvergenceTheorem_1D_proved : SmoothConvergenceTheorem_1D :=
  SmoothConvergenceTheorem_1D_from_TaylorBound
    (fun _ _ x => TaylorBound_CenteredFD_of_contDiff3 x)
```

Unfolding `SmoothConvergenceTheorem_1D` (line 478), the proved content is:

> For every `φ : ℝ → ℝ` with `ContDiff ℝ 3 φ`, every `x : ℝ`, every sequence `h_seq : ℕ → ℝ` of positive reals with `h_seq → 0`, the centered finite-difference Laplacian `(φ(x + h_seq n) + φ(x − h_seq n) − 2 φ(x)) / (h_seq n)²` tends to `deriv (deriv φ) x` as `n → ∞`.

### Proof outline

The proof factors into four named pieces.

1. Right- and left-hand 2nd-order Taylor expansions (`taylor_right_second_order`, lines 881-927; `taylor_left_second_order`, lines 931-1002). These apply Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv` to `φ` on `Icc x (x+h)` and to `g(s) := φ(x − s)` on `Icc 0 h`, then convert `iteratedDerivWithin` to `iteratedDeriv` at the basepoint via `iteratedDerivWithin_eq_iteratedDeriv` and expand the Taylor polynomial via `taylor_within_apply` with an explicit `(E := ℝ)` annotation. The left-hand expansion needs the reflection helper machinery `reflectedAt`, `iteratedDeriv_three_reflectedAt_eq` (Part 4.12, lines 766-867), which tracks the three sign flips through the chain rule for `s ↦ x − s`.

2. `centered_fd_exact_remainder` (lines 1006-1021) combines the two Taylor remainders and an algebraic `field_simp; ring` to extract the exact-remainder identity

   `fdLaplacian1D h φ x − laplacian1D φ x = h · (φ'''(ξ₊) − φ'''(ξ₋)) / 6`

   with witnesses `ξ₊ ∈ (x, x+h)` and `ξ₋ ∈ (x−h, x)`.

3. `BoundedConvergenceForm_from_TaylorBound` (lines 679-728) uses `ContDiff.continuous_iteratedDeriv'` to obtain continuity of `φ'''`, picks `M := max |φ'''|` over the compact interval `Icc (x−1) (x+1)` (via `IsCompact.exists_isMaxOn`), and converts the exact remainder into a Lipschitz-type bound

   `|fdLaplacian1D h φ x − laplacian1D φ x| ≤ (M/3) · h    for h ∈ (0, 1)`.

4. `convergence_from_BoundedConvergenceForm` (lines 599-636) is a standard ε–δ chase: given the bound and `h_seq → 0`, take `N` large enough that `h_seq n` is below both `δ` and `ε/(C+1)`, then `|fd − lap| ≤ C · h_seq n < ε`.

Composition of (3) and (4) gives convergence from the Taylor bound under C³. Theorem A (`TaylorBound_CenteredFD_of_contDiff3`, lines 1025-1028) supplies the bound from (1)+(2), and the watershed theorem follows.

The n-dim extension `fdLaplacianND_converges` (lines 1096-1105) is bookkeeping over `tendsto_finset_sum`: each coordinate slice `t ↦ φ(Function.update x i t)` is C³ via `contDiff_slice` (lines 1070-1088, using `contDiff_pi` and `Function.update_self` / `Function.update_of_ne`), so the 1D theorem applies coordinatewise and the n-dim sum converges to the n-dim sum.

## 4. Bridge architecture

The Lohmiller-Slotine bridge spans four files; each closes a distinct slab.

`LohmillerSlotineBridge.lean` (895 lines, algebraic core). Defines `WaveData` as a record of pointwise scalars `(r, s, r_t, s_t, r_x, s_x, r_xx, s_xx, V, m, ħ)`. Proves the Madelung-Lohmiller-Slotine identity `schrodinger_satisfied_iff` (lines 220-223): the real and imaginary parts of the Schrödinger residual vanish iff the Hamilton-Jacobi-with-Bohm and continuity equations both hold. Proves `psiPolar_obs_eq_r_sq` (Born by construction, lines 135-137), the two-branch and n-branch interference formulas (Part 5, Part 6.3), the connections to `BornRuleUnique` and `PosetGrowthIsQuantum` (Part 6), the deeper theorems `classical_iff_flat_dressing`, `bohm_correction_iff_curvature`, U(1) gauge invariance, quarter-turn 4-phase cancellation (Part 7), and the curved-space extension via `CurvedWaveData` and `metricLaplacianR` (Part 8). Closes 13 of 14 pre-registered components.

`LohmillerSlotineCalculus.lean` (598 lines, PDE bridge). Hooks the abstract `WaveData` scalars to Mathlib's `deriv`. Defines `SmoothWaveField` over `ℝ × ℝ`, `partialT`, `partialX`, `partialXX`, and the pointwise snapshot `WaveData.atPoint sw x t`. Proves the standard product+chain rule expansions `deriv_psiRe_t`, `deriv_psiIm_t`, `deriv_psiRe_x`, `deriv_psiIm_x` (Parts 2-3) using `HasDerivAt.mul`, `HasDerivAt.cos`, `HasDerivAt.sin`; iterates to obtain `partialXX_psiRe_eq`, `partialXX_psiIm_eq` (Part 5). The headline theorem `schrodinger_PDE_iff_HJ_continuity_smooth` (lines 565-571) says: under `SmoothEnough`, the pointwise Schrödinger PDE residual vanishes iff `HamiltonJacobiWithBohm` and `ContinuityEquation` hold at the point. The proof factors through the 2×2 rotation matrix identity `rotation_matrix_invertible` (lines 369-389), which is the algebraic core of the decomposition `PDE_residualRe = schrodResidualReal · cos s − schrodResidualImag · sin s`. This file closes the pre-registered `calculusHookup` component.

`LohmillerSlotineContinuumLimit.lean` (185 lines, scaffolding). States the three sub-bridges as `Prop`s without proof. Sub-bridge 1: the discrete K/P sequence `(Q_n, P_n)` converges to `(r cos s, r sin s)` for some smooth `(r, s)`. Sub-bridge 2: in a Hauptvermutung-emergent manifold, the metric Laplace-Beltrami operator on `r` is well-defined and equals a prescribed scalar. Sub-bridge 3: composition yields the curved-space Hamilton-Jacobi-with-Bohm equation. The headline definition `ContinuumLimitOfKP` (lines 122-132) ties the three together, conjunctively quantified over every spacetime point.

`LohmillerSlotineSubBridge2.lean` (1179 lines, SB2 chartwise core). Sets up abstract `DiscreteLaplacianFamily`, `MetricLaplacian`, `WeakChartwiseConvergence`, `UniformOnCompactsConvergence`, and proves the elementary `uniformOnCompacts_implies_weakChartwise` (lines 106-119) — singleton compacts collapse the uniform-on-K bound to a pointwise bound. The concrete 1D centered finite-difference target is stated and proved through a sequence of polynomial witnesses (quadratics, cubics, quartics) of increasing analytic complexity, culminating in the C³ watershed theorem (Part 4.13). The existential half of sub-bridge 2 — `SubBridge2_realizable` (lines 1127-1131) — is discharged by simply bundling the smooth wave field's snapshot with any prescribed scalar; this leaves the analytic content (matching that scalar to the metric Laplacian on an actual emergent metric) as the open piece. The n-dim flat extension `fdLaplacianND_converges` lives at lines 1096-1105.

The full deductive chain for the SB2 chartwise core is:

`ContDiff ℝ 3 φ` →
`taylor_right_second_order` and `taylor_left_second_order` →
`centered_fd_exact_remainder` →
`TaylorBound_CenteredFD_of_contDiff3` →
`BoundedConvergenceForm_from_TaylorBound` →
`convergence_from_BoundedConvergenceForm` →
`FiniteDifferenceLaplacian1D_ConvergesAt φ x`.

## 5. The remaining frontier

Three things are not done. The honest framing is that all three are genuine work, not bookkeeping.

Curved-chart Laplacian. The watershed theorem closes the *flat* coordinate-wise centered Laplacian. Lifting this to the metric Laplace-Beltrami operator `Δ_g` on a chart of an emergent Riemannian manifold requires the discrete operator family to be `g`-aware: the second-difference stencil has to involve the metric and its inverse, and the convergence has to be uniform on compacts on the chart. This is real differential geometry — pulling back via local charts, partition-of-unity patching, and metric regularity. The infrastructure in `LohmillerSlotineSubBridge2.lean` (uniform-on-compacts → weak-chartwise) is the correct shape but the chart-aware operator is not built. Status: open.

Sub-bridge 1 — discrete K/P compactness. The continuum-limit statement requires showing that the rescaled discrete K/P sequence from `PosetGrowthIsQuantum.GrowthStep` actually converges to `(r·cos s, r·sin s)` for *some* smooth `(r, s)`. This is a probabilistic / measure-theoretic compactness argument, essentially asking for a continuum limit of a discrete substrate. The `SubBridge1_DiscreteAmplitudeToContinuum` proposition (lines 65-70 of `LohmillerSlotineContinuumLimit.lean`) states it; nothing currently proves it for nontrivial sequences. Status: open.

Sub-bridge 3 — weak-form composition. The composition statement `SubBridge3_PolarSchrodingerComposition` is conditional on sub-bridges 1 and 2 having been built consistently — it asks the curved Hamilton-Jacobi equation on the emergent manifold to reduce to the flat-space `HamiltonJacobiWithBohm` precisely when the metric Laplacian matches the coordinate `r_xx`. The reduction theorem `curved_HJ_flat_reduction` (lines 663-667 of `LohmillerSlotineBridge.lean`) gives the iff under the hypothesis `CW.metricLaplacianR = CW.r_xx`; sub-bridge 3 is the global statement that this hypothesis can be discharged from sub-bridges 1 and 2 at every spacetime point. Status: open, and dependent on the prior two.

## 6. Honest framing

What is closed: the algebraic Madelung-Lohmiller-Slotine identity in 1D as an exact iff; the Mathlib-`deriv` calculus hookup from `SmoothWaveField` to the pointwise PDE residual; the conceptual identification of the Bohm quantum potential with the spatial curvature of the dressing magnitude `r = √(Q² + P²)`; the standard polynomial-witness sequence for the 1D centered finite-difference Laplacian; the C³ watershed theorem and its n-dim flat coordinatewise extension; the existential half of sub-bridge 2.

What is not closed: the genuine analytic content of sub-bridge 2 — building a chart-aware metric Laplacian and proving its discrete-to-continuum convergence on smooth scalar fields; sub-bridge 1 — the probabilistic compactness of discrete K/P sequences from `PosetGrowthIsQuantum`; sub-bridge 3 — the global composition under non-trivial chart structure. Each is its own program; none is mechanical.

What the bridge does *not* claim. The formalization does not claim to derive the Schrödinger equation from first principles; it formalizes the L-S construction, which assumes the polar ansatz `ψ = √ρ · e^{iφ/ħ}` and shows the residual splits cleanly. The "Born rule by construction" is honestly labelled — `BornRuleUnique` in LayerA is the stronger statement and the L-S Born identity here is an instance. No claim is made that the continuum limit of the discrete K/P substrate has been proved; only stated.

Audit. 2857 lines across the four files, `lake env lean` build clean as of the closure of theorem A, zero `sorry`, no custom axioms.
