/- Lohmiller–Slotine SubBridge2 Discrete-to-Continuum 1D & `n`D Smooth Laplacian Convergence
(`C³` Taylor Remainder), Conformal / Diagonal / Chartwise SPD Laplace–Beltrami Convergence,
and Gaussian Width Backreaction Dynamics (`σ σ'' + (σ - 1) (σ')² = 0`, Conserved First Integral
`σ' e^σ / σ = C`, Exponential Doubling-Time Bounds `e^{σ₀}/(2C) ≤ ∫ ≤ e^{2σ₀}/C`, and Exact
`Ei` Time Parameterization `∫_{σ(0)}^{σ(t)} (e^s / s) ds = C t`) Bridged with Curved 4D Gravity:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerB.LohmillerSlotineSubBridge2`
   and `UnifiedTheory.LayerB.LohmillerSlotineSubBridge2_Conformal`, certifying:
   - Exact finite-difference Laplacian evaluation on quadratics (`2 * a`), cubics (`6 * a * x`),
     and quartics (`12 * a * x^2 + 2 * a * h^2`),
   - Unconditional `C³` Taylor remainder theorem `centered_fd_exact_remainder`,
     `SmoothConvergenceTheorem_1D_proved`, and `n`-dimensional slice-sum convergence
     `fdLaplacianND_converges`,
   - 1D divergence-form conformal Laplace–Beltrami convergence `fdConformalLaplacianDiv1D_converges`,
     `n`-dimensional conformal Laplace–Beltrami convergence `fdLaplaceBeltrami_converges_conformalND`,
     diagonal-metric Laplace–Beltrami convergence `fdLaplaceBeltrami_converges_diagonalMetric`,
     and chartwise SPD divergence-form Laplace–Beltrami convergence
     `fdLaplaceBeltrami_converges_chartwise`.
2. Bridges `UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics`, certifying:
   - Factorization `firstIntegralRate = (exp σ / σ²) * gaussianWidthODE_residual`,
     conservation `firstIntegralRate = 0` along solutions, and implicit ODE
     `firstIntegral σ σ' = C ↔ σ' = C * σ * exp(-σ)`,
   - Sign invariance (`gaussian_width_no_oscillation`), large-`σ` exponential slowing
     `Tendsto (fun σ => C * σ * exp(-σ)) atTop (𝓝 0)`, small-`σ` limit `C`, frozen solution
     `gaussianWidthODE_residual σ_const 0 0 = 0` vs. free-Schrödinger dispersion
     `0 ≠ ħ² / (m² * σ_const³)`,
   - Two-sided exponential doubling-time bounds
     `exp σ₀ / (2 * C) ≤ ∫ σ in σ₀..(2 * σ₀), doublingTimeIntegrand C σ ≤ exp (2 * σ₀) / C`,
     maximal spreading rate `C * σ * exp(-σ) ≤ C / exp 1` at `σ = 1`, and the exact
     fundamental-theorem-of-calculus time parameterization
     `∫ s in (σ 0)..(σ t), exp s / s = C * t`.
3. Unites the Lohmiller–Slotine conformal/chartwise Laplace–Beltrami and Gaussian width
   dynamics packages with the curved 4D gravitational plane waves (`ttModeCount 4 = 2`),
   Malament `3 + 1` null-cone conformal uniqueness, causal-set Hauptvermutung, Lieb–Robinson
   light-cone bound, and Robertson–Schrödinger / Mandelstam–Tamm speed limits. -/
import UnifiedTheory.LayerB.LohmillerSlotineSubBridge2
import UnifiedTheory.LayerB.LohmillerSlotineSubBridge2_Conformal
import UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics
import UnifiedTheory.Audit.KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge
import UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineContractionLiebRobinsonSpeedLimitBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineConformalLaplacianGaussianWidthBridge

noncomputable section

open Filter Topology Real Matrix
open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction
open UnifiedTheory.LayerA.Bianchi
open UnifiedTheory.LayerA.GravitationalPlaneWaves
open UnifiedTheory.LayerA.NullConeConformal
open UnifiedTheory.LayerA.Hauptvermutung
open UnifiedTheory.LayerA.Derived
open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.LohmillerSlotineBridge
open UnifiedTheory.LayerB.LohmillerSlotineCalculus
open UnifiedTheory.LayerB.LohmillerSlotineBackreaction
open UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit
open UnifiedTheory.LayerB.LohmillerSlotineSubBridge2
open UnifiedTheory.LayerB.LohmillerSlotineSubBridge2_Conformal
open UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics
open UnifiedTheory.LayerB.LiebRobinson
open UnifiedTheory.LayerB.RobertsonSchrodinger
open KFCausalCurved4DLinearizedMetricDecomposition (conformalPartMetricDerivs4D)
open KFCausalCurved4DLinearizedWeylRicciSplit (weylTensor4D)
open KFCausalCurved4DGravitationalPlaneWavesNullConeHauptvermutungBridge
  (curved_4d_gravitational_plane_waves_null_cone_hauptvermutung_master_synthesis)

/-! ### 1. Lohmiller–Slotine SubBridge2 Smooth 1D/`n`D & Conformal/Chartwise Laplace–Beltrami Convergence -/

/-- Exact polynomial finite-difference Laplacian identities (quadratic, cubic, quartic) and
unconditional `1`D and `n`D `C³` smooth convergence package
(`UnifiedTheory.LayerB.LohmillerSlotineSubBridge2`). -/
theorem lohmiller_slotine_subbridge2_polynomial_and_smooth_nd_convergence_package
    (a b c x h : ℝ) (h_ne : h ≠ 0)
    {n : ℕ} {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x_nd : Fin n → ℝ) (h_seq : ℕ → ℝ) (h_pos : ∀ k, 0 < h_seq k)
    (h_tendsto : Filter.Tendsto h_seq Filter.atTop (nhds 0))
    (sw : SmoothWaveField) (t lap : ℝ) :
    fdLaplacian1D h (fun y => a * y ^ 2 + b * y + c) x = 2 * a ∧
    laplacian1D (fun y => a * y ^ 2 + b * y + c) x = 2 * a ∧
    fdLaplacian1D h (fun y => a * y ^ 3) x = 6 * a * x ∧
    laplacian1D (fun y => a * y ^ 3) x = 6 * a * x ∧
    fdLaplacian1D h (fun y => a * y ^ 4) x = 12 * a * x ^ 2 + 2 * a * h ^ 2 ∧
    laplacian1D (fun y => a * y ^ 4) x = 12 * a * x ^ 2 ∧
    SmoothConvergenceTheorem_1D ∧
    Filter.Tendsto (fun k => fdLaplacianND (h_seq k) φ x_nd)
      Filter.atTop (nhds (laplacianND φ x_nd)) ∧
    SubBridge2_HauptvermutungLaplacianControl sw x t lap :=
  ⟨fdLaplacian1D_quadratic a b c h h_ne x,
   laplacian1D_quadratic a b c x,
   fdLaplacian1D_cubic a x h h_ne,
   laplacian1D_cubic a x,
   fdLaplacian1D_quartic a x h h_ne,
   laplacian1D_quartic a x,
   SmoothConvergenceTheorem_1D_proved,
   fdLaplacianND_converges hφ x_nd h_seq h_pos h_tendsto,
   SubBridge2_realizable sw x t lap⟩

/-- Conformal 1D, conformal `n`D, diagonal-metric `n`D, and chartwise SPD divergence-form
`n`D Laplace–Beltrami convergence package
(`UnifiedTheory.LayerB.LohmillerSlotineSubBridge2_Conformal`). -/
theorem lohmiller_slotine_conformal_diagonal_and_chartwise_laplace_beltrami_package
    (cf1 : ConformalFactor) {φ1 : ℝ → ℝ} (hφ1 : ContDiff ℝ 3 φ1) (x1 : ℝ)
    {n : ℕ} (cfN : ConformalFactorND n) (h_cfN : ContDiff ℝ 3 cfN.ρ)
    (g_diag : DiagonalMetric n) (h_diag : ∀ i, ContDiff ℝ 3 (g_diag.coef i))
    (g_chart : ChartwiseMetricCoefs n)
    {φN : (Fin n → ℝ) → ℝ} (hφN : ContDiff ℝ 3 φN)
    (h_wgrad : ∀ i, ContDiff ℝ 3 (g_chart.weightedGradient φN i))
    (xN : Fin n → ℝ) (i_idx : Fin n)
    (h_seq : ℕ → ℝ) (h_pos : ∀ k, 0 < h_seq k)
    (h_tendsto : Filter.Tendsto h_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => fdConformalLaplacianDiv1D cf1 (h_seq k) φ1 x1)
      Filter.atTop (nhds (conformalLaplaceBeltrami1D cf1 φ1 x1)) ∧
    conformalLaplaceBeltrami1D ConformalFactor.flat φ1 x1 = iteratedDeriv 2 φ1 x1 ∧
    Filter.Tendsto (fun k => fdConformalLaplacianND cfN (h_seq k) φN xN)
      Filter.atTop (nhds (conformalLaplaceBeltramiND cfN φN xN)) ∧
    conformalLaplaceBeltramiND (ConformalFactorND.flat n) φN xN = laplacianND φN xN ∧
    Filter.Tendsto (fun k => fdLaplaceBeltramiDiagonal g_diag (h_seq k) φN xN)
      Filter.atTop (nhds (laplaceBeltramiDiagonal g_diag φN xN)) ∧
    Filter.Tendsto (fun k => fdChartwiseLaplaceBeltrami g_chart (h_seq k) φN xN)
      Filter.atTop (nhds (chartwiseLaplaceBeltrami g_chart φN xN)) ∧
    (ChartwiseMetricCoefs.flat n).weightedGradient φN i_idx xN =
      gradientND_component φN i_idx xN :=
  ⟨fdConformalLaplacianDiv1D_converges cf1 hφ1 x1 h_seq h_pos h_tendsto,
   conformalLaplaceBeltrami1D_flat φ1 x1,
   fdLaplaceBeltrami_converges_conformalND cfN h_cfN hφN xN h_seq h_pos h_tendsto,
   conformalLaplaceBeltramiND_flat φN xN,
   fdLaplaceBeltrami_converges_diagonalMetric g_diag h_diag hφN xN h_seq h_pos h_tendsto,
   fdLaplaceBeltrami_converges_chartwise g_chart h_wgrad xN h_seq h_pos h_tendsto,
   ChartwiseMetricCoefs.flat_weightedGradient φN i_idx xN⟩

/-! ### 2. Lohmiller–Slotine Gaussian Width Backreaction Dynamics and Exponential Doubling Time -/

/-- Gaussian width ODE first-integral conservation, implicit solution `σ' = C σ e^{-σ}`,
sign invariance, asymptotic limits, and frozen-width contrast with free Schrödinger dispersion
(`UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics`). -/
theorem lohmiller_slotine_gaussian_width_first_integral_and_frozen_contrast_package
    (σ σ_prime σ_pp C hbar m : ℝ)
    (hσ_pos : 0 < σ) (hm : m ≠ 0) (hhbar : hbar ≠ 0) :
    firstIntegralRate σ σ_prime σ_pp =
      (Real.exp σ / σ ^ 2) * gaussianWidthODE_residual σ σ_prime σ_pp ∧
    (gaussianWidthODE_residual σ σ_prime σ_pp = 0 →
      firstIntegralRate σ σ_prime σ_pp = 0) ∧
    (firstIntegral σ σ_prime = C ↔ σ_prime = C * σ * Real.exp (-σ)) ∧
    (σ_prime = C * σ * Real.exp (-σ) →
      (0 < C → 0 < σ_prime) ∧ (C < 0 → σ_prime < 0) ∧ (C = 0 → σ_prime = 0)) ∧
    Tendsto (fun s : ℝ => C * s * Real.exp (-s)) atTop (𝓝 0) ∧
    Tendsto (fun s : ℝ => C * Real.exp (-s)) (𝓝 0) (𝓝 C) ∧
    (gaussianWidthODE_residual σ 0 0 = 0 ∧
     (0 : ℝ) ≠ hbar ^ 2 / (m ^ 2 * σ ^ 3)) :=
  ⟨firstIntegralRate_eq_factor_residual σ σ_prime σ_pp (ne_of_gt hσ_pos),
   gaussian_width_first_integral σ σ_prime σ_pp (ne_of_gt hσ_pos),
   gaussian_width_solution_implicit σ σ_prime C (ne_of_gt hσ_pos),
   gaussian_width_no_oscillation σ σ_prime C hσ_pos,
   gaussian_width_large_sigma_asymptotic C,
   gaussian_width_small_sigma_asymptotic C,
   gaussian_width_dynamics_differs_from_free_schrodinger σ hbar m (ne_of_gt hσ_pos) hm hhbar⟩

/-- Two-sided exponential doubling-time integral bounds, maximal spreading rate `C / e` at `σ = 1`,
and exact `Ei` time parameterization `∫_{σ(0)}^{σ(t)} (e^s / s) ds = C * t`. -/
theorem lohmiller_slotine_gaussian_width_doubling_time_and_exact_parameterization_package
    (C σ₀ : ℝ) (hC : 0 < C) (hσ₀ : 0 < σ₀)
    (σ_traj : ℝ → ℝ) (hσ_diff : Differentiable ℝ σ_traj)
    (hσ_traj_pos : ∀ t, 0 < σ_traj t)
    (h_ODE : ∀ t, deriv σ_traj t = C * σ_traj t * Real.exp (-(σ_traj t)))
    (t : ℝ) :
    (Real.exp σ₀ / (2 * C) ≤ ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C s ∧
     ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C s ≤ Real.exp (2 * σ₀) / C) ∧
    σ₀ * Real.exp (-σ₀) ≤ 1 * Real.exp (-1) ∧
    C * σ₀ * Real.exp (-σ₀) ≤ C / Real.exp 1 ∧
    ∫ s in (σ_traj 0)..(σ_traj t), Real.exp s / s = C * t :=
  ⟨doubling_time_two_sided_bound C σ₀ hC hσ₀,
   sigma_exp_neg_sigma_max_at_one σ₀,
   lsbridge_spreading_rate_max_at_one C σ₀ (le_of_lt hC),
   gaussian_width_exact_time_parameterization σ_traj C hσ_diff hσ_traj_pos h_ODE t⟩

/-! ### 3. Master Curved 4D Lohmiller–Slotine Conformal Laplacian, Gaussian Width, and Gravity Synthesis -/

/-- Master Curved 4D Lohmiller–Slotine Conformal/Chartwise Laplace–Beltrami Convergence,
Gaussian Width Backreaction & Doubling-Time Dynamics, Gravitational Plane Waves,
Malament `3 + 1` Null-Cone Uniqueness, Hauptvermutung, Lieb–Robinson Light Cone,
and Mandelstam–Tamm Speed Limit Synthesis. -/
theorem curved_4d_lohmiller_slotine_conformal_laplacian_gaussian_width_master_synthesis
    {n : ℕ} (cfN : ConformalFactorND n) (h_cfN : ContDiff ℝ 3 cfN.ρ)
    (g_chart : ChartwiseMetricCoefs n)
    {φN : (Fin n → ℝ) → ℝ} (hφN : ContDiff ℝ 3 φN)
    (h_wgrad : ∀ i, ContDiff ℝ 3 (g_chart.weightedGradient φN i))
    (xN : Fin n → ℝ)
    (h_seq : ℕ → ℝ) (h_pos : ∀ k, 0 < h_seq k)
    (h_tendsto : Filter.Tendsto h_seq Filter.atTop (nhds 0))
    (C_gw σ₀ hbar m_mass : ℝ) (hC_gw : 0 < C_gw) (hσ₀ : 0 < σ₀)
    (hm_mass : m_mass ≠ 0) (hhbar : hbar ≠ 0)
    (σ_traj : ℝ → ℝ) (hσ_diff : Differentiable ℝ σ_traj)
    (hσ_traj_pos : ∀ t, 0 < σ_traj t)
    (h_ODE : ∀ t, deriv σ_traj t = C_gw * σ_traj t * Real.exp (-(σ_traj t)))
    (t_gw : ℝ)
    (k₀ k₁ : ℝ) (hnull : IsNull k₀ k₁) (ε_pol : Matrix (Fin 2) (Fin 2) ℝ)
    (P_proc : SymmetricProcess) (ρ_hv V_hv Ω_hv : ℝ)
    (hρ_hv : 0 < ρ_hv) (hV_hv : 0 < V_hv) (hΩ_hv : 0 < Ω_hv) (hΩ4 : Ω_hv ^ 4 = 1)
    {C_lr v_lr ξ_lr d_lr t_lr : ℝ} (hC_lr : 0 < C_lr) (hξ_lr : 0 < ξ_lr)
    (hcone : v_lr * |t_lr| < d_lr)
    {n_q : ℕ} (ρ_q : ComplexDensityMatrix n_q) (HS : HeisenbergSnapshot n_q) :
    (SmoothConvergenceTheorem_1D ∧
     Filter.Tendsto (fun k => fdConformalLaplacianND cfN (h_seq k) φN xN)
       Filter.atTop (nhds (conformalLaplaceBeltramiND cfN φN xN)) ∧
     Filter.Tendsto (fun k => fdChartwiseLaplaceBeltrami g_chart (h_seq k) φN xN)
       Filter.atTop (nhds (chartwiseLaplaceBeltrami g_chart φN xN))) ∧
    ((gaussianWidthODE_residual σ₀ 0 0 = 0 ∧
      (0 : ℝ) ≠ hbar ^ 2 / (m_mass ^ 2 * σ₀ ^ 3)) ∧
     (Real.exp σ₀ / (2 * C_gw) ≤ ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C_gw s ∧
      ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C_gw s ≤ Real.exp (2 * σ₀) / C_gw) ∧
     C_gw * σ₀ * Real.exp (-σ₀) ≤ C_gw / Real.exp 1 ∧
     ∫ s in (σ_traj 0)..(σ_traj t_gw), Real.exp s / s = C_gw * t_gw) ∧
    (((∀ t x : ℝ, ∀ i j : Fin 2,
         -(-(k₀ ^ 2) * planeWaveTensor k₀ k₁ ε_pol t x i j) +
           (-(k₁ ^ 2) * planeWaveTensor k₀ k₁ ε_pol t x i j) = 0) ∧
      ttModeCount 4 = 2) ∧
     0 < lambdaSq ρ_hv V_hv ∧
     P_proc.variance ρ_hv V_hv = ρ_hv * V_hv ∧
     Ω_hv = 1 ∧
     lrBound C_lr v_lr ξ_lr d_lr t_lr < C_lr ∧
     ComplexDensityMatrix.variance ρ_q HS.H * ComplexDensityMatrix.variance ρ_q HS.A ≥
       (1 / 4) * ((Matrix.trace (ρ_q.M * HS.dA_dt)).re) ^ 2) :=
  ⟨⟨SmoothConvergenceTheorem_1D_proved,
    fdLaplaceBeltrami_converges_conformalND cfN h_cfN hφN xN h_seq h_pos h_tendsto,
    fdLaplaceBeltrami_converges_chartwise g_chart h_wgrad xN h_seq h_pos h_tendsto⟩,
   ⟨gaussian_width_dynamics_differs_from_free_schrodinger σ₀ hbar m_mass (ne_of_gt hσ₀) hm_mass hhbar,
    doubling_time_two_sided_bound C_gw σ₀ hC_gw hσ₀,
    lsbridge_spreading_rate_max_at_one C_gw σ₀ (le_of_lt hC_gw),
    gaussian_width_exact_time_parameterization σ_traj C_gw hσ_diff hσ_traj_pos h_ODE t_gw⟩,
   ⟨master_planeWave_vacuum k₀ k₁ hnull ε_pol,
    lambdaSq_pos ρ_hv V_hv hρ_hv hV_hv,
    poisson_derived P_proc ρ_hv V_hv (le_of_lt hV_hv),
    conformal_plus_volume_determines_metric Ω_hv hΩ_hv hΩ4,
    lrBound_outside_cone hC_lr hξ_lr hcone,
    mandelstam_tamm ρ_q HS⟩⟩

#print axioms lohmiller_slotine_subbridge2_polynomial_and_smooth_nd_convergence_package
#print axioms lohmiller_slotine_conformal_diagonal_and_chartwise_laplace_beltrami_package
#print axioms lohmiller_slotine_gaussian_width_first_integral_and_frozen_contrast_package
#print axioms lohmiller_slotine_gaussian_width_doubling_time_and_exact_parameterization_package
#print axioms curved_4d_lohmiller_slotine_conformal_laplacian_gaussian_width_master_synthesis

end

end UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineConformalLaplacianGaussianWidthBridge
