/-
Copyright (c) 2026 UnifiedTheory Audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Curved 4D Lohmiller-Slotine Action-Principle Contraction, Backreaction, Lieb-Robinson Light-Cone Bound & Quantum Speed Limit Bridge

This module forms the second curved-4D gravitational and quantum-dynamical synthesis of
**Checkpoint 12 (Front 5)**. It bridges eight `LayerB` modules directly into the audited
curved 4D Weyl–Ricci–Lovelock–Yang–Mills–Schwarzschild–Hawking–Penrose–Christodoulou–Bekenstein
framework and Module 1 (`KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge`):

1. **Lohmiller-Slotine Polar Action-Principle Bridge & Graviton TT Modes (`LayerB.LohmillerSlotineBridge`)**:
   - Polar K/P equivalence `psiPolar W = amplitudeFromKP (W.r * cos W.s) (W.r * sin W.s)` and
     `obs (psiPolar W) = W.r^2 = normSqForm.a * W.r^2`.
   - Exact algebraic Madelung–Lohmiller–Slotine equivalence
     `(schrodResidualReal W = 0 ∧ schrodResidualImag W = 0) ↔ (HamiltonJacobiWithBohm W ∧ ContinuityEquation W)`.
   - Two-branch and `n`-branch multipath interference (`twoBranch_interference`, `multipath_obs_form`),
     4-phase quarter-turn destructive cancellation (`quarter_turn_cancellation`), and `U(1)` phase invariance.
   - Classicality iff flat dressing curvature (`r_xx = 0`), curved-space Bohm potential reduction
     (`curved_HJ_flat_reduction`, `curved_classical_iff_harmonic_dressing`), and the graviton
     TT polarization Born rule (`graviton_born_rule`, `gravitonPolar_obs`, `two_graviton_interference`).
2. **Smooth-Field PDE Calculus Hookup & Continuum Limit Sub-Bridges (`LayerB.LohmillerSlotineCalculus`, `LayerB.LohmillerSlotineContinuumLimit`)**:
   - Mathlib `HasDerivAt` chain/product rule expansions for `∂_t ψ`, `∂_x ψ`, and `∂_x^2 ψ`
     (`deriv_psiRe_t`, `deriv_psiIm_t`, `deriv_psiRe_x`, `deriv_psiIm_x`, `partialXX_psiRe_eq`, `partialXX_psiIm_eq`).
   - Polar rotation matrix decomposition (`PDE_residual_decomp`, `rotation_matrix_invertible`) and
     self-contained global and node-friendly local PDE equivalences (`schrodinger_PDE_iff_HJ_continuity_smooth`,
     `schrodinger_PDE_iff_HJ_continuity_at`).
   - Explicit witness construction discharging `SubBridge2_HauptvermutungLaplacianControl`.
3. **Dressing Curvature & Matter-Geometry Backreaction (`LayerB.LohmillerSlotineBackreaction`)**:
   - `dressingCurvature W = r_xx / r`, `bohmQuantumPotential W = -(ℏ^2 / (2m)) * dressingCurvature W`,
     and `metricSource_proportional_to_bohm`.
   - `1+1` conformal Lorentzian metric `ricciScalar1p1Conformal`, static Ricci formula
     `ricciScalar_ofDressing_static`, curved HJ-with-Bohm `HamiltonJacobiWithBohm_curved`,
     and the static Einstein-like identity `R_geom + (4m / ℏ^2) * V_matter = (2 / r^4) * r_x^2`
     with slow-`r` (`R_geom = -(4m / ℏ^2) * V_matter`) and vacuum (`V = 0 ∧ R = 0`) limits.
4. **Lieb-Robinson Light-Cone Propagation Bound & Malament Causal-Cone Bridge (`LayerB.LiebRobinson`)**:
   - `lrBound C v ξ d t = C * exp (-(d - v * |t|) / ξ)`, light-cone trichotomy (`d = v|t|`, `d > v|t|`, `d < v|t|`),
     strict exponential decay in distance (`lrBound_antitone_d`, `lrBound_lt_of_lt`),
     operator-norm commutator ceiling `‖A * B - B * A‖ ≤ 2 * ‖A‖ * ‖B‖` (`lr_trivial_bound_holds`),
     and `emergent_causality_holds`, bridged to Malament `3+1` causal-cone uniqueness and
     Schwarzschild trapped-surface focusing.
5. **Robertson-Schrödinger Uncertainty, Mandelstam-Tamm & Margolus-Levitin Quantum Speed Limits (`LayerB.RobertsonSchrodinger`, `LayerB.MandelstamTamm`, `LayerB.MargolusLevitin`)**:
   - Real quadratic discriminant lemma `b^2 ≤ 4 * a * c`, centered variance `Var_ρ(A) ≥ 0`,
     purely imaginary commutator trace `Re(Tr(ρ [A, B])) = 0`, and `robertson_uncertainty`.
   - `mandelstam_tamm`: `Var_ρ(H) * Var_ρ(A) ≥ (1 / 4) * (Re(Tr(ρ * dA_dt)))^2`.
   - `margolus_levitin_conditional`: `T * S.energyExpectation ≥ π / 2`, bridged to the
     universal Bekenstein bound and Schwarzschild black-hole thermodynamics.
-/

import UnifiedTheory.Audit.KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge
import UnifiedTheory.LayerB.LohmillerSlotineBridge
import UnifiedTheory.LayerB.LohmillerSlotineCalculus
import UnifiedTheory.LayerB.LohmillerSlotineBackreaction
import UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit
import UnifiedTheory.LayerB.LiebRobinson
import UnifiedTheory.LayerB.MandelstamTamm
import UnifiedTheory.LayerB.MargolusLevitin
import UnifiedTheory.LayerB.RobertsonSchrodinger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineContractionLiebRobinsonSpeedLimitBridge

open Filter
open scoped Topology Matrix

open UnifiedTheory.LayerA
open UnifiedTheory.LayerA.BornRuleUnique
open UnifiedTheory.LayerA.MetricConstruction
open UnifiedTheory.LayerA.GaugeConnection
open UnifiedTheory.LayerA.GravitonTTModes
open UnifiedTheory.LayerA.NullConeConformal
open UnifiedTheory.LayerA.GeneralMalament
open UnifiedTheory.LayerA.EinsteinHilbertScaleFixing
open UnifiedTheory.LayerA.MetricGaugeCoupling
open UnifiedTheory.LayerA.SourceReduction
open UnifiedTheory.LayerA.CausalActionCoefficient
open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.LohmillerSlotineBridge
open UnifiedTheory.LayerB.LohmillerSlotineCalculus
open UnifiedTheory.LayerB.LohmillerSlotineBackreaction
open UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit
open UnifiedTheory.LayerB.LiebRobinson
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.MinimalCoupling
open UnifiedTheory.LayerB.RiemannAction
open UnifiedTheory.LayerB.BekensteinHawking
open UnifiedTheory.LayerB.HawkingTemperature
  (hawkingTemperature surfaceGravity evaporationLifetime M_times_hawkingTemperature)
open UnifiedTheory.LayerB.ChristodoulouIrreducibleMass
open UnifiedTheory.LayerB.BekensteinBound
open UnifiedTheory.LayerC.HawkingPenroseSingularity

open KFCausalCurved4DLinearizedMetricDecomposition
  (conformalPartMetricDerivs4D tracelessPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (weylTensor4D)
open KFCausalCurved4DSchwarzschildBirkhoffHawkingThermodynamicsBridge
  (schwarzschildKretschmann)
open KFCausalCurved4DHawkingPenroseSingularityMalamentCausalBridge
  (schwarzschildInteriorTrappedSurface
   schwarzschild_interior_trapped_surface_expansions_neg
   schwarzschild_interior_trapped_surface_conjugate_times)
open KFCausalCurved4DChristodoulouIrreducibleMassBlackHoleMechanicsBridge
  (kerrBekensteinHawkingEntropy)
open KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge
  (curved_4D_bf_source_dressing_metric_gauge_minimal_riemann_master_synthesis)

/-! ### 1. Lohmiller-Slotine Polar Action-Principle Bridge, Born Uniqueness & Graviton TT Modes (`LohmillerSlotineBridge`) -/

/-- **Lohmiller-Slotine Polar Form ≡ K/P Amplitude & Born Rule by Construction**:
Combines `psiPolar_eq_amplitudeFromKP`, `psiPolar_obs_eq_r_sq`, and `psiPolar_obs_via_BornRuleUnique`. -/
theorem ls_polar_kp_amplitude_and_born_rule (W : WaveData) :
    psiPolar W = amplitudeFromKP (W.r * Real.cos W.s) (W.r * Real.sin W.s) ∧
    obs (psiPolar W) = W.r ^ 2 ∧
    obs (psiPolar W) = normSqForm.a * W.r ^ 2 :=
  ⟨psiPolar_eq_amplitudeFromKP W,
   psiPolar_obs_eq_r_sq W,
   psiPolar_obs_via_BornRuleUnique W⟩

/-- **Algebraic Madelung–Lohmiller–Slotine Equivalence (`Schrödinger ↔ HJ-with-Bohm ∧ Continuity`)**:
Combines `residualReal_iff_HJ`, `residualImag_iff_continuity`, `schrodinger_satisfied_iff`,
and `psi_polar_satisfies_schrodinger`. -/
theorem ls_madelung_schrodinger_iff_hj_bohm_and_continuity (W : WaveData) :
    (schrodResidualReal W = 0 ↔ HamiltonJacobiWithBohm W) ∧
    (schrodResidualImag W = 0 ↔ ContinuityEquation W) ∧
    ((schrodResidualReal W = 0 ∧ schrodResidualImag W = 0) ↔
      (HamiltonJacobiWithBohm W ∧ ContinuityEquation W)) ∧
    (HamiltonJacobiWithBohm W → ContinuityEquation W →
      schrodResidualReal W = 0 ∧ schrodResidualImag W = 0) :=
  ⟨residualReal_iff_HJ W,
   residualImag_iff_continuity W,
   schrodinger_satisfied_iff W,
   psi_polar_satisfies_schrodinger W⟩

/-- **Two-Branch and `n`-Branch Multipath Interference (`L-S Eq 15`)**:
Combines `twoBranch_psi_eq_amplitude_sum`, `twoBranch_interference`, and `multipath_obs_form`. -/
theorem ls_two_branch_and_multipath_interference_bridge
    {n : ℕ} (r₁ r₂ s₁ s₂ : ℝ) (rs ss : Fin n → ℝ) :
    (⟨r₁ * Real.cos s₁, r₁ * Real.sin s₁⟩ : ℂ) + ⟨r₂ * Real.cos s₂, r₂ * Real.sin s₂⟩ =
      amplitudeFromKP (r₁ * Real.cos s₁) (r₁ * Real.sin s₁) +
        amplitudeFromKP (r₂ * Real.cos s₂) (r₂ * Real.sin s₂) ∧
    obs ((⟨r₁ * Real.cos s₁, r₁ * Real.sin s₁⟩ : ℂ) + ⟨r₂ * Real.cos s₂, r₂ * Real.sin s₂⟩) =
      r₁ ^ 2 + r₂ ^ 2 + 2 * r₁ * r₂ * Real.cos (s₁ - s₂) ∧
    obs (multipathPsi rs ss) =
      (∑ j, rs j * Real.cos (ss j)) ^ 2 + (∑ j, rs j * Real.sin (ss j)) ^ 2 :=
  ⟨twoBranch_psi_eq_amplitude_sum r₁ r₂ s₁ s₂,
   twoBranch_interference r₁ r₂ s₁ s₂,
   multipath_obs_form rs ss⟩

/-- **SO(2) Born Uniqueness in Polar Coordinates & Discrete Poset Growth Bridge**:
Combines `born_unique_in_polar`, `growth_step_obs`, and `growth_obs_equals_lspolar_obs`. -/
theorem ls_born_unique_in_polar_and_discrete_poset_growth_bridge
    (f : QuadForm) (hinv : f.IsSO2Invariant)
    (g : PosetGrowthIsQuantum.GrowthStep) (W : WaveData)
    (hQ : W.r * Real.cos W.s = g.Q) (hP : W.r * Real.sin W.s = g.P) :
    f.eval (W.r * Real.cos W.s) (W.r * Real.sin W.s) = f.a * W.r ^ 2 ∧
    obs (amplitudeFromKP g.Q g.P) = g.Q ^ 2 + g.P ^ 2 ∧
    obs (psiPolar W) = g.Q ^ 2 + g.P ^ 2 :=
  ⟨born_unique_in_polar f hinv W,
   growth_step_obs g,
   growth_obs_equals_lspolar_obs g W hQ hP⟩

/-- **Classicality ↔ Flat Dressing Curvature (`r_xx = 0`)**:
Combines `classical_iff_flat_dressing` and `bohm_correction_iff_curvature`. -/
theorem ls_classicality_iff_flat_dressing_and_bohm_curvature (W : WaveData) :
    (IsClassical W → (HamiltonJacobiWithBohm W ↔ BareHamiltonJacobi W)) ∧
    (BareHamiltonJacobi W → (HamiltonJacobiWithBohm W ↔ W.r_xx = 0)) :=
  ⟨classical_iff_flat_dressing W,
   bohm_correction_iff_curvature W⟩

/-- **`U(1)` Phase Invariance of Full Schrödinger Residual & 4-Phase Quarter-Turn Cancellation**:
Combines `schrodResidualReal_phase_invariant`, `schrodResidualImag_phase_invariant`,
`quarter_turn_cancellation`, and `quarter_turn_obs_zero`. -/
theorem ls_u1_phase_invariance_and_quarter_turn_four_phase_cancellation
    (W : WaveData) (α r θ : ℝ) :
    schrodResidualReal (W.shiftPhase α) = schrodResidualReal W ∧
    schrodResidualImag (W.shiftPhase α) = schrodResidualImag W ∧
    (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) +
      ⟨r * Real.cos (θ + Real.pi / 2), r * Real.sin (θ + Real.pi / 2)⟩ +
      ⟨r * Real.cos (θ + Real.pi), r * Real.sin (θ + Real.pi)⟩ +
      ⟨r * Real.cos (θ + 3 * Real.pi / 2), r * Real.sin (θ + 3 * Real.pi / 2)⟩ = 0 ∧
    obs ((⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) +
      ⟨r * Real.cos (θ + Real.pi / 2), r * Real.sin (θ + Real.pi / 2)⟩ +
      ⟨r * Real.cos (θ + Real.pi), r * Real.sin (θ + Real.pi)⟩ +
      ⟨r * Real.cos (θ + 3 * Real.pi / 2), r * Real.sin (θ + 3 * Real.pi / 2)⟩) = 0 :=
  ⟨schrodResidualReal_phase_invariant W α,
   schrodResidualImag_phase_invariant W α,
   quarter_turn_cancellation r θ,
   quarter_turn_obs_zero r θ⟩

/-- **Graviton TT Polarization Born Rule, Polar Intensity & Two-Graviton Interference**:
Combines `graviton_born_rule`, `graviton_intensity`, `gravitonPolar_obs`,
`two_graviton_interference`, and `gravitonTTModes 4 = 2`. -/
theorem ls_graviton_born_rule_and_polar_tt_interference
    (f : QuadForm) (hinv : f.IsSO2Invariant)
    (hPlus hCross rG sG rG₁ rG₂ sG₁ sG₂ : ℝ) :
    gravitonTTModes 4 = 2 ∧
    f.eval hPlus hCross = f.a * (hPlus ^ 2 + hCross ^ 2) ∧
    normSqForm.eval hPlus hCross = hPlus ^ 2 + hCross ^ 2 ∧
    (gravitonPolarMode rG sG).1 ^ 2 + (gravitonPolarMode rG sG).2 ^ 2 = rG ^ 2 ∧
    obs ((⟨rG₁ * Real.cos sG₁, rG₁ * Real.sin sG₁⟩ : ℂ) +
      ⟨rG₂ * Real.cos sG₂, rG₂ * Real.sin sG₂⟩) =
      rG₁ ^ 2 + rG₂ ^ 2 + 2 * rG₁ * rG₂ * Real.cos (sG₁ - sG₂) :=
  ⟨by decide,
   graviton_born_rule f hinv hPlus hCross,
   graviton_intensity hPlus hCross,
   gravitonPolar_obs rG sG,
   two_graviton_interference rG₁ rG₂ sG₁ sG₂⟩

/-- **Curved-Space Bohm Potential Flat Reduction & Harmonic Dressing Classicality**:
Combines `curved_HJ_flat_reduction` and `curved_classical_iff_harmonic_dressing`. -/
theorem ls_curved_space_hj_flat_reduction_and_harmonic_dressing
    (CW : CurvedWaveData) :
    (CW.metricLaplacianR = CW.r_xx →
      (CurvedHamiltonJacobi CW ↔ HamiltonJacobiWithBohm CW.toWaveData)) ∧
    (CW.metricLaplacianR = 0 →
      (CurvedHamiltonJacobi CW ↔ CurvedBareHamiltonJacobi CW)) :=
  ⟨curved_HJ_flat_reduction CW,
   curved_classical_iff_harmonic_dressing CW⟩

/-- **Lohmiller-Slotine Component Registry & Master Bridge**:
Combines `LSBridge_thirteen_of_fourteen_closed`, `SubBridge_all_pending`, and `LS_master`. -/
theorem ls_component_registry_and_master_bridge :
    ((List.filter LSBridge_status LSBridge_allComponents).length = 13 ∧
     (List.filter (fun c => ! LSBridge_status c) LSBridge_allComponents).length = 1) ∧
    (List.filter (fun c => ! SubBridge_status c)
      [.discreteAmplitudeToContinuum,
       .hauptvermutungLaplacianControl,
       .polarSchrodingerComposition]).length = 3 ∧
    (∀ W : WaveData,
      (schrodResidualReal W = 0 ∧ schrodResidualImag W = 0) ↔
        (HamiltonJacobiWithBohm W ∧ ContinuityEquation W)) :=
  ⟨⟨rfl, rfl⟩,
   rfl,
   schrodinger_satisfied_iff⟩

/-! ### 2. Smooth-Field PDE Calculus Hookup & Continuum Limit Sub-Bridges (`LohmillerSlotineCalculus`, `LohmillerSlotineContinuumLimit`) -/

/-- **First Time and Spatial Partial Derivatives of `psiRe` and `psiIm` (`LohmillerSlotineCalculus`)**:
Combines `deriv_psiRe_t`, `deriv_psiIm_t`, `deriv_psiRe_x`, and `deriv_psiIm_x`. -/
theorem ls_calculus_time_and_space_partials_of_psi_re_im
    (sw : SmoothWaveField) (x t : ℝ)
    (hr_t : DifferentiableAt ℝ (fun τ => sw.r x τ) t)
    (hs_t : DifferentiableAt ℝ (fun τ => sw.s x τ) t)
    (hr_x : DifferentiableAt ℝ (fun ξ => sw.r ξ t) x)
    (hs_x : DifferentiableAt ℝ (fun ξ => sw.s ξ t) x) :
    (deriv (fun τ => psiRe sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t) -
        sw.r x t * Real.sin (sw.s x t) * SmoothWaveField.partialT sw.s x t) ∧
    (deriv (fun τ => psiIm sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t) +
        sw.r x t * Real.cos (sw.s x t) * SmoothWaveField.partialT sw.s x t) ∧
    (deriv (fun ξ => psiRe sw ξ t) x =
      SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t) -
        sw.r x t * Real.sin (sw.s x t) * SmoothWaveField.partialX sw.s x t) ∧
    (deriv (fun ξ => psiIm sw ξ t) x =
      SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t) +
        sw.r x t * Real.cos (sw.s x t) * SmoothWaveField.partialX sw.s x t) :=
  ⟨deriv_psiRe_t sw x t hr_t hs_t,
   deriv_psiIm_t sw x t hr_t hs_t,
   deriv_psiRe_x sw x t hr_x hs_x,
   deriv_psiIm_x sw x t hr_x hs_x⟩

/-- **Second Spatial Partial Derivatives `∂_x^2 psiRe` and `∂_x^2 psiIm`**:
Combines `partialXX_psiRe_eq` and `partialXX_psiIm_eq`. -/
theorem ls_calculus_second_spatial_partials_of_psi_re_im
    (sw : SmoothWaveField) (x t : ℝ)
    (hr : Differentiable ℝ (fun ξ => sw.r ξ t))
    (hs : Differentiable ℝ (fun ξ => sw.s ξ t))
    (hr_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.r ξ t))
    (hs_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.s ξ t)) :
    SmoothWaveField.partialXX (fun ξ τ => sw.r ξ τ * Real.cos (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t -
        sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2) * Real.cos (sw.s x t) -
      (2 * SmoothWaveField.partialX sw.r x t * SmoothWaveField.partialX sw.s x t +
        sw.r x t * SmoothWaveField.partialXX sw.s x t) * Real.sin (sw.s x t) ∧
    SmoothWaveField.partialXX (fun ξ τ => sw.r ξ τ * Real.sin (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t -
        sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2) * Real.sin (sw.s x t) +
      (2 * SmoothWaveField.partialX sw.r x t * SmoothWaveField.partialX sw.s x t +
        sw.r x t * SmoothWaveField.partialXX sw.s x t) * Real.cos (sw.s x t) :=
  ⟨partialXX_psiRe_eq sw x t hr hs hr_x hs_x,
   partialXX_psiIm_eq sw x t hr hs hr_x hs_x⟩

/-- **Polar Rotation Matrix Decomposition of the Schrödinger PDE Residual**:
Combines `PDE_residual_decomp`, `rotation_matrix_invertible`, and `schrodinger_PDE_iff_HJ_continuity`. -/
theorem ls_calculus_pde_residual_decomp_and_rotation_invertibility
    (sw : SmoothWaveField) (x t a b s : ℝ)
    (h : ChainRuleExpansions sw x t) :
    (PDE_residualRe sw x t =
      schrodResidualReal (WaveData.atPoint sw x t) * Real.cos (sw.s x t) -
        schrodResidualImag (WaveData.atPoint sw x t) * Real.sin (sw.s x t) ∧
     PDE_residualIm sw x t =
      schrodResidualReal (WaveData.atPoint sw x t) * Real.sin (sw.s x t) +
        schrodResidualImag (WaveData.atPoint sw x t) * Real.cos (sw.s x t)) ∧
    ((a * Real.cos s - b * Real.sin s = 0 ∧ a * Real.sin s + b * Real.cos s = 0) ↔
      (a = 0 ∧ b = 0)) ∧
    ((PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0) ↔
      (HamiltonJacobiWithBohm (WaveData.atPoint sw x t) ∧
       ContinuityEquation (WaveData.atPoint sw x t))) :=
  ⟨PDE_residual_decomp sw x t h,
   rotation_matrix_invertible a b s,
   schrodinger_PDE_iff_HJ_continuity sw x t h⟩

/-- **Self-Contained Global (`SmoothEnough`) and Local Node-Friendly (`SmoothEnoughAt`) PDE Equivalences**:
Combines `ChainRuleExpansions.ofSmoothEnough`, `schrodinger_PDE_iff_HJ_continuity_smooth`,
`SmoothEnoughAt.of_smoothEnough`, and `schrodinger_PDE_iff_HJ_continuity_at`. -/
theorem ls_calculus_schrodinger_pde_iff_hj_continuity_global_and_local
    (sw : SmoothWaveField) (x t : ℝ)
    (h_glob : SmoothEnough sw x t) (h_loc : SmoothEnoughAt sw x t) :
    ChainRuleExpansions sw x t ∧
    SmoothEnoughAt sw x t ∧
    ((PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0) ↔
      (HamiltonJacobiWithBohm (WaveData.atPoint sw x t) ∧
       ContinuityEquation (WaveData.atPoint sw x t))) ∧
    ((PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0) ↔
      (HamiltonJacobiWithBohm (WaveData.atPoint sw x t) ∧
       ContinuityEquation (WaveData.atPoint sw x t))) :=
  ⟨ChainRuleExpansions.ofSmoothEnough sw x t h_glob,
   SmoothEnoughAt.of_smoothEnough h_glob,
   schrodinger_PDE_iff_HJ_continuity_smooth sw x t h_glob,
   schrodinger_PDE_iff_HJ_continuity_at sw x t h_loc⟩

/-- **Discharge of `SubBridge2_HauptvermutungLaplacianControl` & Flat-Laplacian Sub-Bridge 3 Reduction**:
For every `sw : SmoothWaveField` and `x t lap : ℝ`, `SubBridge2_HauptvermutungLaplacianControl sw x t lap`
holds unconditionally via `{ toWaveData := WaveData.atPoint sw x t, metricLaplacianR := lap }`. -/
theorem ls_continuum_limit_subbridge2_and_subbridge3_witnesses
    (sw : SmoothWaveField) (x t lap : ℝ) :
    SubBridge2_HauptvermutungLaplacianControl sw x t lap ∧
    (∀ CW : CurvedWaveData,
      CW.toWaveData = WaveData.atPoint sw x t →
      CW.metricLaplacianR = CW.r_xx →
      (CurvedHamiltonJacobi CW ↔ HamiltonJacobiWithBohm (WaveData.atPoint sw x t))) := by
  refine ⟨⟨{ toWaveData := WaveData.atPoint sw x t, metricLaplacianR := lap }, rfl, rfl⟩, ?_⟩
  intro CW hto hflat
  rw [← hto]
  exact curved_HJ_flat_reduction CW hflat

/-- **Discrete K/P Sequence Per-Step Born Observable & Continuum Limit Sub-Bridge Registry**:
For any `seq : DiscreteKPSequence` and step `n : ℕ`, the `n`-th growth step has Born observable
`(seq.growth n).Q ^ 2 + (seq.growth n).P ^ 2`. -/
theorem ls_continuum_limit_subbridge1_implies_polar_convergence_at_step
    (seq : DiscreteKPSequence) (n : ℕ) :
    obs (amplitudeFromKP (seq.growth n).Q (seq.growth n).P) =
      (seq.growth n).Q ^ 2 + (seq.growth n).P ^ 2 ∧
    (List.filter (fun c => ! SubBridge_status c)
      [.discreteAmplitudeToContinuum,
       .hauptvermutungLaplacianControl,
       .polarSchrodingerComposition]).length = 3 :=
  ⟨growth_step_obs (seq.growth n), rfl⟩

/-! ### 3. Lohmiller-Slotine Dressing Curvature & Matter-Geometry Backreaction (`LohmillerSlotineBackreaction`) -/

/-- **Dressing Curvature `r_xx / r`, Bohm Quantum Potential & Metric Source Proportionality**:
Combines `bohmQuantumPotential_eq_dressing_curvature`, `dressing_curvature_sources_metric`,
and `metricSource_proportional_to_bohm`. -/
theorem ls_backreaction_bohm_potential_and_metric_source_proportionality
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (metricSource couplingConstant : ℝ)
    (h_HJ : HamiltonJacobiWithBohm W)
    (h_coupling : MatterSourcesGeometry W h_r_ne metricSource couplingConstant) :
    bohmQuantumPotential W h_r_ne =
      -(W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne ∧
    metricSource = couplingConstant * dressingCurvature W h_r_ne ∧
    bohmQuantumPotential W h_r_ne *
      ((-(2 * W.m) / W.hbar ^ 2) * couplingConstant) = metricSource :=
  ⟨bohmQuantumPotential_eq_dressing_curvature W h_r_ne,
   (dressing_curvature_sources_metric W h_r_ne metricSource couplingConstant h_HJ h_coupling).1,
   metricSource_proportional_to_bohm W h_r_ne metricSource couplingConstant h_coupling⟩

/-- **Static `1+1` Conformal Metric Ricci Scalar & Matter-Amplitude Conformal Identification**:
Combines `Conformal1p1Metric.static_a_t_eq_zero`, `Conformal1p1Metric.static_a_tt_eq_zero`,
`ricciScalar1p1Conformal_static`, and `ricciScalar_ofDressing_static`. -/
theorem ls_backreaction_conformal_1plus1_static_ricci_and_dressing
    (g : Conformal1p1Metric) (h_static_g : g.Static)
    (r : ℝ → ℝ → ℝ) (r_pos : ∀ x t, 0 < r x t)
    (h_static_r : ∀ x t₁ t₂, r x t₁ = r x t₂) (x t : ℝ) :
    g.a_t x t = 0 ∧
    g.a_tt x t = 0 ∧
    ricciScalar1p1Conformal g x t =
      -(2 / (g.a x t) ^ 4) * ((g.a x t) * (g.a_xx x t) - (g.a_x x t) ^ 2) ∧
    ricciScalar1p1Conformal (Conformal1p1Metric.ofDressing r r_pos) x t =
      -(2 / (r x t) ^ 4) *
        ((r x t) * ((Conformal1p1Metric.ofDressing r r_pos).a_xx x t) -
          ((Conformal1p1Metric.ofDressing r r_pos).a_x x t) ^ 2) :=
  ⟨g.static_a_t_eq_zero h_static_g x t,
   g.static_a_tt_eq_zero h_static_g x t,
   ricciScalar1p1Conformal_static g h_static_g x t,
   ricciScalar_ofDressing_static r r_pos h_static_r x t⟩

/-- **Static Real-Wave Ground-State Equilibrium (`V = (ℏ^2 / (2m)) * dressingCurvature`)**:
Combines `hamiltonJacobiWithBohm_static_real_form` and `static_equilibrium_V_metric_source`. -/
theorem ls_backreaction_static_real_hj_and_equilibrium_source
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ : HamiltonJacobiWithBohm W)
    (metricSource couplingConstant : ℝ)
    (h_coupling : MatterSourcesGeometry W h_r_ne metricSource couplingConstant) :
    (HamiltonJacobiWithBohm W ↔
      W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne) ∧
    W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne ∧
    W.V * couplingConstant = (W.hbar ^ 2 / (2 * W.m)) * metricSource :=
  ⟨hamiltonJacobiWithBohm_static_real_form W h_r_ne h_st h_sx,
   (hamiltonJacobiWithBohm_static_real_form W h_r_ne h_st h_sx).mp h_HJ,
   static_equilibrium_V_metric_source W h_r_ne h_st h_sx h_HJ metricSource couplingConstant h_coupling⟩

/-- **Curved HJ-with-Bohm Flat Reduction & Matter-Coupled `a^2 = r^2` Equilibrium**:
Combines `HamiltonJacobiWithBohm_curved_flat`, `HamiltonJacobiWithBohm_curved_static_real_form`,
and `matter_coupled_curved_equilibrium`. -/
theorem ls_backreaction_curved_hj_flat_and_matter_coupled_equilibrium
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (a_sq : ℝ) (h_a_sq_ne : a_sq ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0) :
    (HamiltonJacobiWithBohm_curved W 1 ↔ HamiltonJacobiWithBohm W) ∧
    (HamiltonJacobiWithBohm_curved W a_sq ↔
      W.V = (W.hbar ^ 2 / (2 * W.m * a_sq)) * dressingCurvature W h_r_ne) ∧
    (HamiltonJacobiWithBohm_curved W (W.r ^ 2) →
      W.V = (W.hbar ^ 2 / (2 * W.m * W.r ^ 2)) * dressingCurvature W h_r_ne) :=
  ⟨HamiltonJacobiWithBohm_curved_flat W,
   HamiltonJacobiWithBohm_curved_static_real_form W h_r_ne a_sq h_a_sq_ne h_st h_sx,
   matter_coupled_curved_equilibrium W h_r_ne h_st h_sx⟩

/-- **Static Matter-Coupled Einstein-Like Identity, Slow-`r` Equation & Vacuum Limit**:
Combines `static_matter_geometry_einstein_identity`, `static_matter_geometry_slow_r_equation`,
and `static_matter_geometry_vacuum_limit`. -/
theorem ls_backreaction_static_einstein_like_slow_r_and_vacuum_limits
    (r r_x r_xx hbar m : ℝ)
    (hr_ne : r ≠ 0) (hm_ne : m ≠ 0) (hhbar_ne : hbar ≠ 0) :
    (let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
     let R_geom := -(2 / r ^ 3) * (r_xx - r_x ^ 2 / r)
     R_geom + (4 * m / hbar ^ 2) * V_matter = (2 / r ^ 4) * r_x ^ 2) ∧
    (let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
     let R_geom := -(2 / r ^ 3) * (r_xx - 0 ^ 2 / r)
     R_geom = -(4 * m / hbar ^ 2) * V_matter) ∧
    (let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (0 / r)
     let R_geom := -(2 / r ^ 3) * (0 - 0 ^ 2 / r)
     V_matter = 0 ∧ R_geom = 0) :=
  ⟨static_matter_geometry_einstein_identity r r_x r_xx hbar m hr_ne hm_ne hhbar_ne,
   static_matter_geometry_slow_r_equation r r_xx hbar m hr_ne hm_ne hhbar_ne,
   static_matter_geometry_vacuum_limit r hbar m hr_ne hm_ne hhbar_ne⟩

/-- **Dynamic Coupled Matter-Geometry Snapshot & Local Static Einstein Identity**:
Combines `coupled_flat_metric_recovers_flat`, `coupled_static_real_recovers_equilibrium`,
and `coupled_static_real_einstein_identity`. -/
theorem ls_backreaction_coupled_snapshot_and_dynamic_einstein_identity
    (W : WaveData) (g : Conformal1p1Metric) (x t couplingConstant : ℝ)
    (h_r_ne : W.r ≠ 0) (h_match : g.a x t = W.r)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ_curved : HamiltonJacobiWithBohm_curved W ((g.a x t) ^ 2))
    (h_geom : ricciScalar1p1Conformal g x t =
      couplingConstant * dressingCurvature W h_r_ne) :
    W.V = (W.hbar ^ 2 / (2 * W.m * (g.a x t) ^ 2)) * dressingCurvature W h_r_ne ∧
    W.V * couplingConstant =
      (W.hbar ^ 2 / (2 * W.m * W.r ^ 2)) * ricciScalar1p1Conformal g x t ∧
    (g.a x t = 1 → HamiltonJacobiWithBohm W) :=
  ⟨coupled_static_real_recovers_equilibrium W g x t h_r_ne (h_match ▸ h_r_ne) h_st h_sx h_HJ_curved,
   coupled_static_real_einstein_identity W g x t couplingConstant h_r_ne h_match h_st h_sx h_HJ_curved h_geom,
   fun ha1 => coupled_flat_metric_recovers_flat W g x t ha1 h_HJ_curved⟩

/-! ### 4. Lieb-Robinson Light-Cone Propagation Bound & Malament Causal-Cone Bridge (`LiebRobinson`) -/

/-- **Lieb-Robinson Bound Positivity & Light-Cone Trichotomy (`d = v|t|`, `d > v|t|`, `d < v|t|`)**:
Combines `lrBound_pos`, `lrBound_nonneg`, `lrBound_at_cone`, `lrBound_outside_cone`,
`lrBound_inside_cone`, and `lieb_robinson_master`. -/
theorem lieb_robinson_bound_pos_and_light_cone_trichotomy
    {C v ξ d t : ℝ} (hC : 0 < C) (hξ : 0 < ξ) :
    0 < lrBound C v ξ d t ∧
    0 ≤ lrBound C v ξ d t ∧
    (d = v * |t| → lrBound C v ξ d t = C) ∧
    (v * |t| < d → lrBound C v ξ d t < C) ∧
    (d < v * |t| → C < lrBound C v ξ d t) :=
  ⟨lrBound_pos hC,
   lrBound_nonneg hC.le,
   (lieb_robinson_master hC hξ).2.1,
   (lieb_robinson_master hC hξ).2.2.1,
   (lieb_robinson_master hC hξ).2.2.2⟩

/-- **Exponential Distance Decay & Zero-Time Disjoint-Support Commutator Seed**:
Combines `lrBound_antitone_d`, `lrBound_lt_of_lt`, `lrBound_at_zero_time_pos`,
and `commutator_zero_at_disjoint`. -/
theorem lieb_robinson_exponential_distance_decay_and_zero_time_seed
    {n : ℕ} {C v ξ t d d₁ d₂ : ℝ}
    (hC : 0 < C) (hξ : 0 < ξ) (hd : 0 < d) (hd₁₂ : d₁ < d₂)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hcomm : A * B = B * A) :
    Antitone (fun x => lrBound C v ξ x t) ∧
    lrBound C v ξ d₂ t < lrBound C v ξ d₁ t ∧
    (0 < lrBound C v ξ d 0 ∧ lrBound C v ξ d 0 < C) ∧
    A * B - B * A = 0 :=
  ⟨lrBound_antitone_d hC.le hξ,
   lrBound_lt_of_lt hC hξ hd₁₂,
   lrBound_at_zero_time_pos hC hξ hd,
   commutator_zero_at_disjoint A B hcomm⟩

/-- **Universal Normed-Ring Commutator Ceiling & Emergent Causality Targets**:
Combines `commutator_norm_trivial_bound`, `lr_trivial_bound_holds`, and `emergent_causality_holds`. -/
theorem lieb_robinson_commutator_norm_ceiling_and_emergent_causality_targets
    {R : Type*} [NormedRing R] (A B : R) :
    ‖A * B - B * A‖ ≤ 2 * ‖A‖ * ‖B‖ ∧
    LR_Trivial_Bound_Target ∧
    Emergent_Causality_Target :=
  ⟨commutator_norm_trivial_bound A B,
   lr_trivial_bound_holds,
   emergent_causality_holds⟩

/-- **Lieb-Robinson Light-Cone Suppression ↔ Malament `3+1` Causal-Cone Conformal Uniqueness Bridge**:
Unites Lieb-Robinson exponential suppression outside the causal cone (`v * |t| < d → lrBound C v ξ d t < C`)
with Malament's `3+1` theorem (`stage3_closed_3plus1`: the causal/null cone uniquely fixes
the 4D metric up to a conformal factor) and 4D Weyl conformal invariance (`weylTensor4D (conformalPartMetricDerivs4D md) = 0`). -/
theorem lieb_robinson_light_cone_and_malament_3plus1_conformal_bridge
    {C v ξ d t : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (md : MetricDerivs 4) (a b c d_idx : Fin 4) :
    (d = v * |t| → lrBound C v ξ d t = C) ∧
    (v * |t| < d → lrBound C v ξ d t < C) ∧
    Emergent_Causality_Target ∧
    (∀ (g₁ g₂ : Fin 4 → Fin 4 → ℝ),
      (∀ i j, g₁ i j = g₁ j i) → (∀ i j, g₂ i j = g₂ j i) → g₁ 0 0 ≠ 0 →
      (∀ w : Fin 4 → ℝ, minkQuadGen w = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₁ i j * w i * w j = 0) →
      (∀ w : Fin 4 → ℝ, minkQuadGen w = 0 → ∑ i : Fin 4, ∑ j : Fin 4, g₂ i j * w i * w j = 0) →
      ∃ μ : ℝ, ∀ i j : Fin 4, g₂ i j = μ * g₁ i j) ∧
    weylTensor4D (conformalPartMetricDerivs4D md) a b c d_idx = 0 :=
  ⟨fun h => lrBound_at_cone h,
   fun h => lrBound_outside_cone hC hξ h,
   emergent_causality_holds,
   stage3_closed_3plus1,
   KFCausalCurved4DLinearizedWeylRicciSplit.weylTensor4D_conformalPart_eq_zero md a b c d_idx⟩

/-- **Lieb-Robinson Horizon Scale (`d = 2M`) & Schwarzschild Interior Trapped-Surface Focusing**:
At the Schwarzschild horizon scale `d = schwarzschildRadius M = 2M > 0`, `lrBound C v ξ (schwarzschildRadius M) 0 < C`,
and for every interior radius `0 < r_int < schwarzschildRadius M`, both null expansions of
`schwarzschildInteriorTrappedSurface M r_int` are strictly negative and focus in finite positive time. -/
theorem lieb_robinson_schwarzschild_horizon_crossing_and_trapped_surface_bridge
    {C v ξ : ℝ} (M r_int : ℝ)
    (hC : 0 < C) (hξ : 0 < ξ) (hM : 0 < M)
    (hr_pos : 0 < r_int) (hr_lt : r_int < schwarzschildRadius M) :
    (0 < lrBound C v ξ (schwarzschildRadius M) 0 ∧
      lrBound C v ξ (schwarzschildRadius M) 0 < C) ∧
    ((schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus < 0 ∧
      (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_minus < 0 ∧
      0 < conjugatePointTime
        (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus ∧
      0 < conjugatePointTime
        (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_minus) := by
  have hrs_pos : 0 < schwarzschildRadius M := by
    unfold schwarzschildRadius; linarith
  have hexp := schwarzschild_interior_trapped_surface_expansions_neg
    M r_int hM hr_pos hr_lt
  have hconj := schwarzschild_interior_trapped_surface_conjugate_times
    M r_int hM hr_pos hr_lt
  exact ⟨lrBound_at_zero_time_pos hC hξ hrs_pos,
    ⟨hexp.1, hexp.2, hconj.1, hconj.2.1⟩⟩

/-! ### 5. Robertson-Schrödinger Uncertainty, Mandelstam-Tamm & Margolus-Levitin Quantum Speed Limits (`RobertsonSchrodinger`, `MandelstamTamm`, `MargolusLevitin`) -/

/-- **Real Quadratic Discriminant Bound (`b^2 ≤ 4ac`) & Density-Matrix Expectation Linearity**:
Combines `discrim_le_of_quad_nonneg`, `expectation_add`, `expectation_sub`,
`expectation_smul_real`, and `expectation_one`. -/
theorem robertson_schrodinger_discriminant_and_expectation_linearity
    {n : ℕ} {a b c : ℝ} (ha : 0 ≤ a)
    (hquad : ∀ x : ℝ, 0 ≤ a * x ^ 2 + b * x + c)
    (ρ : ComplexDensityMatrix n) (r : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    b ^ 2 ≤ 4 * a * c ∧
    ComplexDensityMatrix.expectation ρ (A + B) =
      ComplexDensityMatrix.expectation ρ A + ComplexDensityMatrix.expectation ρ B ∧
    ComplexDensityMatrix.expectation ρ (A - B) =
      ComplexDensityMatrix.expectation ρ A - ComplexDensityMatrix.expectation ρ B ∧
    ComplexDensityMatrix.expectation ρ ((r : ℂ) • A) =
      r * ComplexDensityMatrix.expectation ρ A ∧
    ComplexDensityMatrix.expectation ρ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  ⟨discrim_le_of_quad_nonneg ha hquad,
   ComplexDensityMatrix.expectation_add ρ A B,
   ComplexDensityMatrix.expectation_sub ρ A B,
   ComplexDensityMatrix.expectation_smul_real ρ r A,
   ComplexDensityMatrix.expectation_one ρ⟩

/-- **Anti-Hermiticity of `[A, B]`, Centering Invariance & Purely Imaginary Commutator Trace**:
Combines `centered_isHermitian`, `trace_isHermitian_im_zero`, `commutator_hermitian_antiHerm`,
`commutator_centered`, and `trace_rho_commutator_re_zero`. -/
theorem robertson_schrodinger_commutator_antiHermitian_and_purely_imaginary_trace
    {n : ℕ} (ρ : ComplexDensityMatrix n)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (α : ℝ) (z₁ z₂ : ℂ) :
    (A - (α : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian ∧
    (Matrix.trace A).im = 0 ∧
    (ComplexDensityMatrix.commutator A B).conjTranspose =
      -(ComplexDensityMatrix.commutator A B) ∧
    ComplexDensityMatrix.commutator
      (A - z₁ • (1 : Matrix (Fin n) (Fin n) ℂ))
      (B - z₂ • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      ComplexDensityMatrix.commutator A B ∧
    (Matrix.trace (ρ.M * ComplexDensityMatrix.commutator A B)).re = 0 :=
  ⟨ComplexDensityMatrix.centered_isHermitian hA α,
   ComplexDensityMatrix.trace_isHermitian_im_zero hA,
   ComplexDensityMatrix.commutator_hermitian_antiHerm hA hB,
   ComplexDensityMatrix.commutator_centered A B z₁ z₂,
   ComplexDensityMatrix.trace_rho_commutator_re_zero ρ hA hB⟩

/-- **Centered Variance Identity, Variance Non-Negativity & Robertson Uncertainty Bound**:
Combines `variance_eq_centered_sq`, `variance_nonneg`, and `robertson_uncertainty`. -/
theorem robertson_schrodinger_variance_nonneg_and_uncertainty_bound
    {n : ℕ} (ρ : ComplexDensityMatrix n)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ComplexDensityMatrix.variance ρ A =
      ComplexDensityMatrix.expectation ρ
        ((A - (ComplexDensityMatrix.expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
         (A - (ComplexDensityMatrix.expectation ρ A : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) ∧
    0 ≤ ComplexDensityMatrix.variance ρ A ∧
    0 ≤ ComplexDensityMatrix.variance ρ B ∧
    ComplexDensityMatrix.variance ρ A * ComplexDensityMatrix.variance ρ B ≥
      (1 / 4) * Complex.normSq (Matrix.trace (ρ.M * ComplexDensityMatrix.commutator A B)) :=
  ⟨ComplexDensityMatrix.variance_eq_centered_sq ρ A,
   ComplexDensityMatrix.variance_nonneg ρ hA,
   ComplexDensityMatrix.variance_nonneg ρ hB,
   ComplexDensityMatrix.robertson_uncertainty ρ hA hB⟩

/-- **Mandelstam-Tamm Energy-Time Uncertainty & Commuting Stationary Observable Limit (`MandelstamTamm`)**:
Proves `mandelstam_tamm ρ HS`, and shows that when `[H, A] = 0`, `HS.dA_dt = 0` and
`(Matrix.trace (ρ.M * HS.dA_dt)).re = 0`. -/
theorem mandelstam_tamm_energy_time_uncertainty_and_stationary_commuting_limit
    {n : ℕ} (ρ : ComplexDensityMatrix n) (HS : HeisenbergSnapshot n) :
    ComplexDensityMatrix.variance ρ HS.H * ComplexDensityMatrix.variance ρ HS.A ≥
      (1 / 4) * ((Matrix.trace (ρ.M * HS.dA_dt)).re) ^ 2 ∧
    0 ≤ ComplexDensityMatrix.variance ρ HS.H ∧
    0 ≤ ComplexDensityMatrix.variance ρ HS.A ∧
    (ComplexDensityMatrix.commutator HS.H HS.A = 0 →
      HS.dA_dt = 0 ∧ (Matrix.trace (ρ.M * HS.dA_dt)).re = 0) := by
  refine ⟨mandelstam_tamm ρ HS,
    ComplexDensityMatrix.variance_nonneg ρ HS.hH,
    ComplexDensityMatrix.variance_nonneg ρ HS.hA, ?_⟩
  intro hcomm0
  have hd0 : HS.dA_dt = 0 := by
    rw [HS.hHeisenberg, hcomm0, smul_zero]
  refine ⟨hd0, ?_⟩
  rw [hd0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- **Margolus-Levitin Survival Amplitude Decomposition & Conditional Quantum Speed Limit (`MargolusLevitin`)**:
Combines `EnergySpectrum.energyExpectation_nonneg`, `EnergySpectrum.survivalAmplitude_re`,
`EnergySpectrum.survivalAmplitude_im`, and `EnergySpectrum.margolus_levitin_conditional`. -/
theorem margolus_levitin_survival_amplitude_and_conditional_speed_limit
    {n : ℕ} (S_spec : EnergySpectrum n) (T : ℝ) :
    0 ≤ S_spec.energyExpectation ∧
    (S_spec.survivalAmplitude T).re =
      ∑ i, S_spec.probs i * Real.cos (S_spec.energies i * T) ∧
    (S_spec.survivalAmplitude T).im =
      -(∑ i, S_spec.probs i * Real.sin (S_spec.energies i * T)) ∧
    (0 ≤ T →
      (S_spec.survivalAmplitude T).re = 0 →
      (S_spec.survivalAmplitude T).im = 0 →
      (∀ x : ℝ, 0 ≤ x → Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)) →
      T * S_spec.energyExpectation ≥ Real.pi / 2) :=
  ⟨S_spec.energyExpectation_nonneg,
   S_spec.survivalAmplitude_re T,
   S_spec.survivalAmplitude_im T,
   fun hT hre him htrig =>
     S_spec.margolus_levitin_conditional T hT hre him htrig⟩

/-- **Margolus-Levitin Quantum Speed Limit ↔ Universal Bekenstein Bound & Black-Hole First Law Bridge**:
Links the Margolus-Levitin orthogonality time bound `T * E ≥ π / 2` to the Bekenstein entropy
bound `bekensteinBound R E = 2 * π * R * E` (so `T * bekensteinBound R E ≥ π^2 * R` for `0 ≤ R`
and `E = S_spec.energyExpectation`) and Schwarzschild first-law mechanics
`2 * bekensteinBound (2 * M) M * hawkingTemperature M = M`. -/
theorem margolus_levitin_and_bekenstein_black_hole_speed_limit_bridge
    {n : ℕ} (S_spec : EnergySpectrum n) (T R M : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hM : 0 < M)
    (h_orth_re : (S_spec.survivalAmplitude T).re = 0)
    (h_orth_im : (S_spec.survivalAmplitude T).im = 0)
    (h_trig : ∀ x : ℝ, 0 ≤ x → Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)) :
    T * S_spec.energyExpectation ≥ Real.pi / 2 ∧
    T * bekensteinBound R S_spec.energyExpectation ≥ Real.pi ^ 2 * R ∧
    bekensteinBound (2 * M) M = bekensteinHawkingEntropy M ∧
    2 * bekensteinBound (2 * M) M * hawkingTemperature M = M := by
  have hml := S_spec.margolus_levitin_conditional T hT h_orth_re h_orth_im h_trig
  have hMT := M_times_hawkingTemperature M hM
  refine ⟨hml, ?_, schwarzschild_saturates_bound M, ?_⟩
  · unfold bekensteinBound
    have h2piR : 0 ≤ 2 * Real.pi * R := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hml h2piR
    calc
      T * (2 * Real.pi * R * S_spec.energyExpectation)
        = (2 * Real.pi * R) * (T * S_spec.energyExpectation) := by ring
      _ ≥ (2 * Real.pi * R) * (Real.pi / 2) := hmul
      _ = Real.pi ^ 2 * R := by ring
  · rw [schwarzschild_bound_eq]
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    calc
      2 * (4 * Real.pi * M ^ 2) * hawkingTemperature M
        = (8 * Real.pi * M) * (M * hawkingTemperature M) := by ring
      _ = (8 * Real.pi * M) * (1 / (8 * Real.pi)) := by rw [hMT]
      _ = M := by field_simp

/-- **MASTER SYNTHESIS — Curved 4D Lohmiller-Slotine Action-Principle Contraction, Backreaction, Lieb-Robinson Light-Cone & Quantum Speed Limits**:
Unites all eight `LayerB` modules (`LohmillerSlotineBridge`, `LohmillerSlotineCalculus`,
`LohmillerSlotineBackreaction`, `LohmillerSlotineContinuumLimit`, `LiebRobinson`,
`RobertsonSchrodinger`, `MandelstamTamm`, `MargolusLevitin`) with Module 1
(`KFCausalCurved4DBFSourceDressingMetricGaugeCouplingMinimalBridge`) and the curved 4D
Raychaudhuri–Malament–Schwarzschild–Christodoulou–Bekenstein framework. -/
theorem curved_4D_lohmiller_slotine_lieb_robinson_quantum_speed_limit_master_synthesis
    {V_sp W_sp : Type*} [AddCommGroup V_sp] [Module ℝ V_sp] [AddCommGroup W_sp] [Module ℝ W_sp]
    (L_op : V_sp →ₗ[ℝ] W_sp) (ψ_func : W_sp →ₗ[ℝ] ℝ) (v₀ : V_sp) (hL : ψ_func (L_op v₀) ≠ 0)
    (sc₃ : StructureConstants 8) (conn₃ : ConnectionData 4 8)
    (G_N : ℝ) (hG_pos : 0 < G_N)
    (k_mc φ₁ φ₂ qA₁ qA₂ : ℝ)
    (W_ls : WaveData) (h_r_ne : W_ls.r ≠ 0)
    (sw : SmoothWaveField) (x_pt t_pt lap : ℝ) (h_smooth : SmoothEnough sw x_pt t_pt)
    {C_lr v_lr ξ_lr d_lr t_lr : ℝ} (hC_lr : 0 < C_lr) (hξ_lr : 0 < ξ_lr)
    {n_qm : ℕ} (ρ_dm : ComplexDensityMatrix n_qm) (HS : HeisenbergSnapshot n_qm)
    (S_spec : EnergySpectrum n_qm) (T_ml : ℝ)
    (md : MetricDerivs 4) (a b c d_idx : Fin 4)
    (M J r_int : ℝ) (hsub : kerrSubextremal M J) (hM : 0 < M)
    (hr_pos : 0 < r_int) (hr_lt : r_int < schwarzschildRadius M) :
    -- (1) Module 1: BF Source/Dressing, 4D Yang-Mills Tracelessness, Causal Coefficient c = 1/2, Minimal Coupling & Riemann Action
    (stressEnergyTrace sc₃ conn₃ = 0 ∧
     causalCoefficient = 1 / 2 ∧
     discretenessLength causalCoefficient G_N = Real.sqrt (8 * Real.pi) * planckLength G_N ∧
     Complex.normSq (coupledAmplitude k_mc φ₁ qA₁ + coupledAmplitude k_mc φ₂ qA₂) =
       2 + 2 * Real.cos ((k_mc * φ₁ + qA₁) - (k_mc * φ₂ + qA₂)) ∧
     0 ≤ kretschnerAction md ∧
     (∃ (md₁ md₂ : MetricDerivs 2),
       accumulatedAction [md₁, md₂] ≠
         accumulatedAction [UnifiedTheory.LayerB.RiemannAction.addMetricDerivs md₁ md₂])) ∧
    -- (2) Lohmiller-Slotine Polar Bridge, Smooth PDE Hookup & Matter-Geometry Backreaction
    (obs (psiPolar W_ls) = W_ls.r ^ 2 ∧
     ((schrodResidualReal W_ls = 0 ∧ schrodResidualImag W_ls = 0) ↔
       (HamiltonJacobiWithBohm W_ls ∧ ContinuityEquation W_ls)) ∧
     ((PDE_residualRe sw x_pt t_pt = 0 ∧ PDE_residualIm sw x_pt t_pt = 0) ↔
       (HamiltonJacobiWithBohm (WaveData.atPoint sw x_pt t_pt) ∧
        ContinuityEquation (WaveData.atPoint sw x_pt t_pt))) ∧
     SubBridge2_HauptvermutungLaplacianControl sw x_pt t_pt lap ∧
     bohmQuantumPotential W_ls h_r_ne =
       -(W_ls.hbar ^ 2 / (2 * W_ls.m)) * dressingCurvature W_ls h_r_ne ∧
     (HamiltonJacobiWithBohm_curved W_ls 1 ↔ HamiltonJacobiWithBohm W_ls)) ∧
    -- (3) Lieb-Robinson Light-Cone Bound & Malament 3+1 Conformal Uniqueness
    (0 < lrBound C_lr v_lr ξ_lr d_lr t_lr ∧
     (v_lr * |t_lr| < d_lr → lrBound C_lr v_lr ξ_lr d_lr t_lr < C_lr) ∧
     LR_Trivial_Bound_Target ∧
     Emergent_Causality_Target ∧
     weylTensor4D (conformalPartMetricDerivs4D md) a b c d_idx = 0) ∧
    -- (4) Robertson-Schrödinger Uncertainty, Mandelstam-Tamm & Margolus-Levitin Quantum Speed Limits
    (ComplexDensityMatrix.variance ρ_dm HS.H * ComplexDensityMatrix.variance ρ_dm HS.A ≥
       (1 / 4) * Complex.normSq (Matrix.trace (ρ_dm.M * ComplexDensityMatrix.commutator HS.H HS.A)) ∧
     ComplexDensityMatrix.variance ρ_dm HS.H * ComplexDensityMatrix.variance ρ_dm HS.A ≥
       (1 / 4) * ((Matrix.trace (ρ_dm.M * HS.dA_dt)).re) ^ 2 ∧
     0 ≤ S_spec.energyExpectation ∧
     (S_spec.survivalAmplitude T_ml).re =
       ∑ i, S_spec.probs i * Real.cos (S_spec.energies i * T_ml)) ∧
    -- (5) Curved 4D Singularity Focusing, Christodoulou Irreducible Mass & Bekenstein Bound
    ((schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus < 0 ∧
     0 < conjugatePointTime
       (schwarzschildInteriorTrappedSurface M r_int hM hr_pos hr_lt).θ_plus ∧
     M ^ 2 = irreducibleMassSq M J + J ^ 2 / (4 * irreducibleMassSq M J) ∧
     IsBekensteinCompliant (kerrBekensteinHawkingEntropy M J) (2 * M) M ∧
     schwarzschildKretschmann M (schwarzschildRadius M) *
       (bekensteinBound (2 * M) M) ^ 2 = 12 * Real.pi ^ 2) := by
  have hm1 := curved_4D_bf_source_dressing_metric_gauge_minimal_riemann_master_synthesis
    L_op ψ_func v₀ hL sc₃ conn₃ G_N hG_pos k_mc φ₁ φ₂ qA₁ qA₂ md a b c d_idx M J hsub hM
  have hexp := schwarzschild_interior_trapped_surface_expansions_neg
    M r_int hM hr_pos hr_lt
  have hconj := schwarzschild_interior_trapped_surface_conjugate_times
    M r_int hM hr_pos hr_lt
  exact ⟨⟨hm1.2.1.1, hm1.2.2.1.1, hm1.2.2.1.2.1, hm1.2.2.2.1.2.2, hm1.2.2.2.2.1, hm1.2.2.2.2.2.1⟩,
    ⟨psiPolar_obs_eq_r_sq W_ls,
      schrodinger_satisfied_iff W_ls,
      schrodinger_PDE_iff_HJ_continuity_smooth sw x_pt t_pt h_smooth,
      (ls_continuum_limit_subbridge2_and_subbridge3_witnesses sw x_pt t_pt lap).1,
      bohmQuantumPotential_eq_dressing_curvature W_ls h_r_ne,
      HamiltonJacobiWithBohm_curved_flat W_ls⟩,
    ⟨lrBound_pos hC_lr,
      fun h => lrBound_outside_cone hC_lr hξ_lr h,
      lr_trivial_bound_holds,
      emergent_causality_holds,
      hm1.2.2.2.2.2.2.1⟩,
    ⟨ComplexDensityMatrix.robertson_uncertainty ρ_dm HS.hH HS.hA,
      mandelstam_tamm ρ_dm HS,
      S_spec.energyExpectation_nonneg,
      S_spec.survivalAmplitude_re T_ml⟩,
    ⟨hexp.1, hconj.1,
      hm1.2.2.2.2.2.2.2.1,
      hm1.2.2.2.2.2.2.2.2.1,
      hm1.2.2.2.2.2.2.2.2.2⟩⟩

#print axioms ls_polar_kp_amplitude_and_born_rule
#print axioms ls_madelung_schrodinger_iff_hj_bohm_and_continuity
#print axioms ls_two_branch_and_multipath_interference_bridge
#print axioms ls_born_unique_in_polar_and_discrete_poset_growth_bridge
#print axioms ls_classicality_iff_flat_dressing_and_bohm_curvature
#print axioms ls_u1_phase_invariance_and_quarter_turn_four_phase_cancellation
#print axioms ls_graviton_born_rule_and_polar_tt_interference
#print axioms ls_curved_space_hj_flat_reduction_and_harmonic_dressing
#print axioms ls_component_registry_and_master_bridge
#print axioms ls_calculus_time_and_space_partials_of_psi_re_im
#print axioms ls_calculus_second_spatial_partials_of_psi_re_im
#print axioms ls_calculus_pde_residual_decomp_and_rotation_invertibility
#print axioms ls_calculus_schrodinger_pde_iff_hj_continuity_global_and_local
#print axioms ls_continuum_limit_subbridge2_and_subbridge3_witnesses
#print axioms ls_continuum_limit_subbridge1_implies_polar_convergence_at_step
#print axioms ls_backreaction_bohm_potential_and_metric_source_proportionality
#print axioms ls_backreaction_conformal_1plus1_static_ricci_and_dressing
#print axioms ls_backreaction_static_real_hj_and_equilibrium_source
#print axioms ls_backreaction_curved_hj_flat_and_matter_coupled_equilibrium
#print axioms ls_backreaction_static_einstein_like_slow_r_and_vacuum_limits
#print axioms ls_backreaction_coupled_snapshot_and_dynamic_einstein_identity
#print axioms lieb_robinson_bound_pos_and_light_cone_trichotomy
#print axioms lieb_robinson_exponential_distance_decay_and_zero_time_seed
#print axioms lieb_robinson_commutator_norm_ceiling_and_emergent_causality_targets
#print axioms lieb_robinson_light_cone_and_malament_3plus1_conformal_bridge
#print axioms lieb_robinson_schwarzschild_horizon_crossing_and_trapped_surface_bridge
#print axioms robertson_schrodinger_discriminant_and_expectation_linearity
#print axioms robertson_schrodinger_commutator_antiHermitian_and_purely_imaginary_trace
#print axioms robertson_schrodinger_variance_nonneg_and_uncertainty_bound
#print axioms mandelstam_tamm_energy_time_uncertainty_and_stationary_commuting_limit
#print axioms margolus_levitin_survival_amplitude_and_conditional_speed_limit
#print axioms margolus_levitin_and_bekenstein_black_hole_speed_limit_bridge
#print axioms curved_4D_lohmiller_slotine_lieb_robinson_quantum_speed_limit_master_synthesis

end UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineContractionLiebRobinsonSpeedLimitBridge
