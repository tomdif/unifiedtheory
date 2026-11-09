/- Lohmiller–Slotine SubBridge1 Discrete-to-Continuum Polar Amplitude Convergence
(Bolzano–Weierstrass Extraction, Polar Gauge-Fixing, `SO(2)` Substrate Energy Bound,
and Refinement Control) and Phase E Static Curved-Schrödinger Equilibrium Classification
(Polynomial `η = 1` Cancellation, Gaussian `R = 2 / (σ² r²) > 0`, Sech Soliton Constant
`R = 2 / σ²`, Generalized Sech `R = 2 (B / A)²`, Exponential `R = 0`, `σ → ∞ / 0⁺` Asymptotic
Limits, and Local/Global `C²` Negative-`R` No-Go Theorem) Bridged with Curved 4D Gravity:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerB.LohmillerSlotineSubBridge1`,
   certifying `subBridge1_zero`, Bolzano–Weierstrass subsequence extraction
   `BoundedKPSequence_has_convergent_subsequence`, polar gauge-fixing `polar_gauge_fixing`,
   polar subsequence convergence `BoundedKPSequence_has_polar_convergent_subsequence`,
   full-sequence convergence from subsequence uniqueness `BoundedKPSequence_unique_limit_polar_form`,
   equivalence `BoundedKPField F ↔ SubstrateEnergyBounded F`, and purely substrate-derived
   boundedness and uniqueness from `SubstrateEvolutionLaw` / `SO2RotationEvolution` and
   `SubstrateRefinementControl` (`SB1_bounded_and_unique_from_substrate`,
   `SB1_bounded_and_unique_from_SO2Rotation`).
2. Bridges the complete 9-module Phase E static curved-Schrödinger equilibrium suite
   (`LohmillerSlotinePredictionE1`, `E2`, `E3`, `EExponential`, `EFamily`,
   `EGeneralizedSech`, `ELimits`, `ENegativityNoGo`, `EFullNoGo`), certifying:
   - Universal family law `derivedRicci r r_x r_xx = 2 * (r_x² - r * r_xx) / r⁴` and
     Liouville constant-`R` condition `derivedRicci r r_x r_xx = 2 * C ↔ r_x² - r * r_xx = C * r⁴`,
   - Polynomial profile `r(x) = 1 + x²` exact cancellation `Δ_geom(1) = 1 / 2 = (4m/ħ²) V(1)` (`R(1) = 0`),
   - Gaussian profile `r_σ(x) = exp(-x²/(2σ²))` non-vanishing curvature `R_σ(x) = 2 / (σ² r_σ(x)²) ≠ 0`,
   - Sech soliton `r_σ(x) = sech(x/σ)` homogeneous positive curvature `R_σ(x) = 2 / σ² > 0`
     and generalized 2-parameter sech `r_{A,B}(x) = A sech(B x)` curvature `R = 2 B² / A²`,
   - Exponential profile `r_{α,β}(x) = exp(α x + β)` vacuum curvature `R ≡ 0`,
   - Asymptotic `Filter.Tendsto` limits `2 / σ² → 0` (`σ → ∞`), `2 / σ² → ∞` (`σ → 0⁺`),
     and `2 * exp(x² / σ²) / σ² → 0` (`σ → ∞` at fixed `x`),
   - Local (`IsLocalMax` + `ContDiffAt ℝ 2`) and global (`ContDiff ℝ 2`, `m ≤ r x ≤ M`)
     impossibility of constant negative curvature (`LSBridge_no_global_smooth_bounded_negative_R`).
3. Unites SubBridge1 and the complete Phase E constant-`R` classification with SubBridge2
   conformal/chartwise Laplace–Beltrami convergence, Gaussian width `σ(t)` backreaction dynamics,
   and curved 4D Bianchi / trace-reversal / Lovelock / `Λ² N = 1` / Gauss–Bonnet / focusing gravity. -/
import UnifiedTheory.LayerB.LohmillerSlotineSubBridge1
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE2
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEExponential
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech
import UnifiedTheory.LayerB.LohmillerSlotinePredictionELimits
import UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEFullNoGo
import UnifiedTheory.Audit.KFCausalCurved4DBianchiLinearizedEinsteinLovelockWeylAntiGravityBridge
import UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineConformalLaplacianGaussianWidthBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineSubBridge1PredictionESechNoGoBridge

noncomputable section

open Filter Topology Real Matrix
open scoped BigOperators
open UnifiedTheory.LayerA
open UnifiedTheory.LayerA.Bianchi
open UnifiedTheory.LayerA.MetricConstruction
open UnifiedTheory.LayerA.LinearizedEinstein
open UnifiedTheory.LayerA.LinearizedFieldEqs
open UnifiedTheory.LayerA.CosmologicalConstantN
open UnifiedTheory.LayerA.GaussBonnetExpansion
open UnifiedTheory.LayerA.Graviton
open UnifiedTheory.LayerA.GravitationalPlaneWaves
open UnifiedTheory.LayerA.Hauptvermutung
open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.SignedSource
open UnifiedTheory.LayerB.MetricDefects
open UnifiedTheory.LayerB.SourceFocusing
open UnifiedTheory.LayerB.FocusingBridge
open UnifiedTheory.LayerB.FocusingCoupling
open UnifiedTheory.LayerB.PosetGrowthIsQuantum
open UnifiedTheory.LayerB.LohmillerSlotineContinuumLimit
open UnifiedTheory.LayerB.LohmillerSlotineSubBridge1
open UnifiedTheory.LayerB.LohmillerSlotineSubBridge2
open UnifiedTheory.LayerB.LohmillerSlotineSubBridge2_Conformal
open UnifiedTheory.LayerB.LohmillerSlotineGaussianWidthDynamics
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE2
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEExponential
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech
open UnifiedTheory.LayerB.LohmillerSlotinePredictionELimits
open UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEFullNoGo
open KFCausalCurved4DBianchiLinearizedEinsteinLovelockWeylAntiGravityBridge
  (bianchi_trace_reversal_and_linearized_superposition_package)
open KFCausalCurved4DLohmillerSlotineConformalLaplacianGaussianWidthBridge
  (curved_4d_lohmiller_slotine_conformal_laplacian_gaussian_width_master_synthesis)

/-! ### 1. Lohmiller–Slotine SubBridge1 Discrete-to-Continuum Polar Amplitude & Substrate Dynamics -/

/-- Lohmiller–Slotine SubBridge1 Bolzano–Weierstrass extraction, polar gauge-fixing,
full-sequence polar convergence from subsequence uniqueness, and `SO(2)` substrate energy /
refinement control package (`UnifiedTheory.LayerB.LohmillerSlotineSubBridge1`). -/
theorem lohmiller_slotine_subbridge1_polar_and_substrate_refinement_package
    (seq_zero seq : DiscreteKPSequence)
    (hzero : IsZeroKPSequence seq_zero) (hb : BoundedKPSequence seq)
    (qLim pLim s_phase : ℝ)
    (huniq : ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ q' p' : ℝ,
       Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds q') →
       Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds p') →
       q' = qLim ∧ p' = pLim)
    (F : KPField) (M_E : ℝ) (hM_E_nn : 0 ≤ M_E)
    (h_rot : SO2RotationEvolution F)
    (h_init : InitialEnergyBound F M_E)
    (h_refine : SubstrateRefinementControl F) :
    SubBridge1_DiscreteAmplitudeToContinuum seq_zero 0 s_phase ∧
    (∃ r s : ℝ, 0 ≤ r ∧ r * Real.cos s = qLim ∧ r * Real.sin s = pLim) ∧
    (∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ r s : ℝ, 0 ≤ r ∧
        Tendsto (fun n => (seq.growth (ψ n)).Q) atTop (nhds (r * Real.cos s)) ∧
        Tendsto (fun n => (seq.growth (ψ n)).P) atTop (nhds (r * Real.sin s))) ∧
    (∃ r s : ℝ, 0 ≤ r ∧
      Tendsto (fun n => (seq.growth n).Q) atTop (nhds (r * Real.cos s)) ∧
      Tendsto (fun n => (seq.growth n).P) atTop (nhds (r * Real.sin s))) ∧
    (BoundedKPField F ↔ SubstrateEnergyBounded F) ∧
    (BoundedKPField F ∧
     ∃ qLimF pLimF : ℝ → ℝ → ℝ, KPFieldHasUniqueSubseqLimits F qLimF pLimF) :=
  ⟨subBridge1_zero seq_zero hzero s_phase,
   polar_gauge_fixing qLim pLim,
   BoundedKPSequence_has_polar_convergent_subsequence seq hb,
   BoundedKPSequence_unique_limit_polar_form seq hb qLim pLim huniq,
   boundedKPField_iff_substrateEnergyBounded F,
   SB1_bounded_and_unique_from_SO2Rotation h_rot hM_E_nn h_init h_refine⟩

/-! ### 2. Phase E1–E4 Polynomial Cancellation, Gaussian, Sech Soliton, Generalized Sech, and Exponential Profiles -/

/-- Phase E1–E3 polynomial `η = 1` cancellation (`R(1) = 0`), Gaussian profile
`R_σ(x) = 2 / (σ² r_σ(x)²) ≠ 0`, and sech soliton homogeneous positive curvature
`R_σ(x) = 2 / σ² > 0` package (`LohmillerSlotinePredictionE1`, `E2`, `E3`). -/
theorem lohmiller_slotine_prediction_e1_e2_e3_polynomial_gaussian_sech_package
    (σ x x₂ hbar m : ℝ) (hm : 0 < m) (hhbar : 0 < hbar) (hσ : σ ≠ 0)
    (R_poly R_gauss R_sech1 R_sech2 : ℝ)
    (h_id_poly :
      let r := polyProfile 1
      let r_x := polyProfile_x 1
      let r_xx := polyProfile_xx 1
      let V_x1 := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
      R_poly + (4 * m / hbar ^ 2) * V_x1 = einsteinCorrection r r_x)
    (h_id_gauss :
      R_gauss + (4 * m / hbar ^ 2) * gaussianMatterPotential σ x hbar m =
        einsteinCorrection (gaussianProfile σ x) (gaussianProfile_x σ x))
    (h_id_sech1 :
      R_sech1 + (4 * m / hbar ^ 2) * sechMatterPotential σ x hbar m =
        einsteinCorrection (sechProfile σ x) (sechProfile_x σ x))
    (h_id_sech2 :
      R_sech2 + (4 * m / hbar ^ 2) * sechMatterPotential σ x₂ hbar m =
        einsteinCorrection (sechProfile σ x₂) (sechProfile_x σ x₂)) :
    (0 ≤ einsteinCorrection (polyProfile x) (polyProfile_x x) ∧
     einsteinCorrection (polyProfile 1) (polyProfile_x 1) = 1 / 2 ∧
     R_poly = 0) ∧
    (0 < gaussianProfile σ x ∧
     R_gauss = 2 / (σ ^ 2 * (gaussianProfile σ x) ^ 2) ∧
     R_gauss ≠ 0) ∧
    (0 < sechProfile σ x ∧
     R_sech1 = 2 / σ ^ 2 ∧
     R_sech1 = R_sech2 ∧
     0 < R_sech1) :=
  ⟨⟨einsteinCorrection_nonneg (polyProfile x) (polyProfile_x x),
    polyProfile_correction_at_one,
    polyProfile_R_zero_at_x_one hbar m hm hhbar R_poly h_id_poly⟩,
   ⟨gaussianProfile_pos σ x,
    gaussianRicci_from_identity σ x hbar m hσ (ne_of_gt hm) (ne_of_gt hhbar) R_gauss h_id_gauss,
    gaussianRicci_never_zero σ x hbar m hσ (ne_of_gt hm) (ne_of_gt hhbar) R_gauss h_id_gauss⟩,
   ⟨sechProfile_pos σ x,
    sechRicci_from_identity σ x hbar m hσ (ne_of_gt hm) (ne_of_gt hhbar) R_sech1 h_id_sech1,
    sechRicci_constant σ x x₂ hbar m hσ (ne_of_gt hm) (ne_of_gt hhbar) R_sech1 R_sech2 h_id_sech1 h_id_sech2,
    sechRicci_positive σ x hbar m hσ (ne_of_gt hm) (ne_of_gt hhbar) R_sech1 h_id_sech1⟩⟩

/-- Phase E-Family, E4 Exponential (`R ≡ 0`), Generalized Sech (`R = 2 B² / A²`),
and `Filter.Tendsto` `σ → ∞ / 0⁺` asymptotic limits package
(`LohmillerSlotinePredictionEFamily`, `EExponential`, `EGeneralizedSech`, `ELimits`). -/
theorem lohmiller_slotine_prediction_efamily_exponential_gensech_and_limits_package
    (r r_x r_xx C σ x α β A B hbar m : ℝ)
    (hr : r ≠ 0) (hσ : σ ≠ 0) (hA : A ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0) :
    (derivedRicci r r_x r_xx + (4 * m / hbar ^ 2) * staticMatterPotential r r_xx hbar m =
       einsteinCorrection r r_x ∧
     (derivedRicci r r_x r_xx = 2 * C ↔ r_x ^ 2 - r * r_xx = C * r ^ 4) ∧
     derivedRicci (gaussianProfile σ x) (gaussianProfile_x σ x) (gaussianProfile_xx σ x) =
       2 / (σ ^ 2 * (gaussianProfile σ x) ^ 2) ∧
     derivedRicci (sechProfile σ x) (sechProfile_x σ x) (sechProfile_xx σ x) = 2 / σ ^ 2) ∧
    (derivedRicci (expProfile α β x) (expProfile_x α β x) (expProfile_xx α β x) = 0 ∧
     (4 * m / hbar ^ 2) * expMatterPotential α β x hbar m =
       einsteinCorrection (expProfile α β x) (expProfile_x α β x) ∧
     derivedRicci (gSechProfile A B x) (gSechProfile_x A B x) (gSechProfile_xx A B x) =
       2 * B ^ 2 / A ^ 2 ∧
     0 ≤ derivedRicci (gSechProfile A B x) (gSechProfile_x A B x) (gSechProfile_xx A B x) ∧
     gSechProfile 1 (1 / σ) x = sechProfile σ x) ∧
    (Tendsto (fun s : ℝ => 2 / s ^ 2) atTop (𝓝 0) ∧
     Tendsto (fun s : ℝ => 2 / s ^ 2) (𝓝[>] (0 : ℝ)) atTop ∧
     Tendsto (fun s : ℝ => 2 * Real.exp (x ^ 2 / s ^ 2) / s ^ 2) atTop (𝓝 0)) :=
  ⟨⟨derivedRicci_satisfies_einstein_identity r r_x r_xx hbar m hr hm hhbar,
    derivedRicci_eq_const_iff r r_x r_xx C hr,
    derivedRicci_gaussian σ x hσ,
    derivedRicci_sech σ x hσ⟩,
   ⟨derivedRicci_expProfile_zero α β x,
    expProfile_einstein_cancellation α β x hbar m hm hhbar,
    derivedRicci_gSech A B x hA,
    derivedRicci_gSech_nonneg A B x hA,
    gSechProfile_specializes_to_sechProfile σ x hσ⟩,
   ⟨sech_Ricci_atTop,
    sech_Ricci_nhdsGT_zero,
    gaussian_Ricci_atFixedX_atTop x⟩⟩

/-! ### 3. Phase E5 Local (`IsLocalMax`) and Global (`C²` Bounded) Constant Negative-`R` No-Go Theorem -/

/-- Phase E5 local (`IsLocalMax` + `ContDiffAt ℝ 2`) and global (`ContDiff ℝ 2` bounded on `ℝ`)
constant-negative-`R` impossibility and constant-`R` classification completion package
(`LohmillerSlotinePredictionENegativityNoGo`, `LohmillerSlotinePredictionEFullNoGo`). -/
theorem lohmiller_slotine_prediction_e5_local_and_global_negative_r_nogo_package
    (r_loc : ℝ → ℝ) (x₀ : ℝ)
    (h_max : IsLocalMax r_loc x₀)
    (h_diff_loc : ContDiffAt ℝ 2 r_loc x₀)
    (h_pos_loc : 0 < r_loc x₀)
    (r_glob : ℝ → ℝ) (m_lb M_ub d_conv y_nonneg : ℝ)
    (hm_lb : 0 < m_lb) (hmM : m_lb ≤ M_ub)
    (hd_conv : 0 < d_conv) (hy_nonneg : 0 ≤ y_nonneg)
    (h_diff_glob : ContDiff ℝ 2 r_glob)
    (h_lower : ∀ x, m_lb ≤ r_glob x)
    (h_upper : ∀ x, r_glob x ≤ M_ub)
    (f_conv : ℝ → ℝ) (hf_diff : ContDiff ℝ 2 f_conv)
    (hf_dd : ∀ x, d_conv ≤ deriv (deriv f_conv) x) :
    (¬ ∃ (r r_x r_xx : ℝ), 0 < r ∧ r_x = 0 ∧ r_xx ≤ 0 ∧ derivedRicci r r_x r_xx < 0) ∧
    (deriv r_loc x₀ = 0 ∧ deriv (deriv r_loc) x₀ ≤ 0) ∧
    0 ≤ derivedRicci (r_loc x₀) (deriv r_loc x₀) (deriv (deriv r_loc) x₀) ∧
    (derivedRicci (r_loc x₀) (deriv r_loc x₀) (deriv (deriv r_loc) x₀) = 0 ∨
     0 < derivedRicci (r_loc x₀) (deriv r_loc x₀) (deriv (deriv r_loc) x₀)) ∧
    f_conv 0 + deriv f_conv 0 * y_nonneg + (d_conv / 2) * y_nonneg ^ 2 ≤ f_conv y_nonneg ∧
    (¬ ∃ C : ℝ, C < 0 ∧
      ∀ x, (deriv r_glob x) ^ 2 - r_glob x * deriv (deriv r_glob) x = C * (r_glob x) ^ 4) :=
  ⟨no_max_like_with_negative_R,
   deriv_and_deriv_deriv_at_isLocalMax r_loc x₀ h_max h_diff_loc,
   derivedRicci_nonneg_at_isLocalMax r_loc x₀ h_max h_diff_loc h_pos_loc,
   LSBridge_constant_R_classification_isLocalMax r_loc x₀ h_max h_diff_loc h_pos_loc,
   quadratic_lower_bound_of_unif_convex hd_conv hf_diff hf_dd hy_nonneg,
   LSBridge_no_global_smooth_bounded_negative_R r_glob m_lb M_ub hm_lb hmM h_diff_glob h_lower h_upper⟩

/-! ### 4. Master Curved 4D Lohmiller–Slotine SubBridge1, Phase E Constant-`R` Classification & No-Go, and Gravity Synthesis -/

/-- Master Curved 4D Lohmiller–Slotine SubBridge1 Polar Amplitude & Substrate Refinement,
Phase E Universal Family Law (`R = 2(r_x² - r r_xx)/r⁴`), Sech Soliton (`R = 2/σ²`),
Generalized Sech (`R = 2 B²/A²`), Exponential (`R = 0`), Global `C²` Negative-`R` No-Go,
SubBridge2 Conformal/Chartwise Laplace–Beltrami Convergence, Gaussian Width `σ(t)` Dynamics,
and 4D Trace-Reversal / Lovelock / `Λ² N = 1` / Gauss–Bonnet / Focusing Synthesis. -/
theorem curved_4d_lohmiller_slotine_subbridge1_prediction_e_sech_nogo_master_synthesis
    (F : KPField) (M_E : ℝ) (hM_E_nn : 0 ≤ M_E)
    (h_rot : SO2RotationEvolution F)
    (h_init : InitialEnergyBound F M_E)
    (h_refine : SubstrateRefinementControl F)
    (σ x α β A B : ℝ) (hσ : σ ≠ 0) (hA : A ≠ 0)
    (r_glob : ℝ → ℝ) (m_lb M_ub : ℝ)
    (hm_lb : 0 < m_lb) (hmM : m_lb ≤ M_ub)
    (h_diff_glob : ContDiff ℝ 2 r_glob)
    (h_lower : ∀ y, m_lb ≤ r_glob y) (h_upper : ∀ y, r_glob y ≤ M_ub)
    {n : ℕ} (cfN : ConformalFactorND n) (h_cfN : ContDiff ℝ 3 cfN.ρ)
    (g_chart : ChartwiseMetricCoefs n)
    {φN : (Fin n → ℝ) → ℝ} (hφN : ContDiff ℝ 3 φN)
    (h_wgrad : ∀ i, ContDiff ℝ 3 (g_chart.weightedGradient φN i))
    (xN : Fin n → ℝ)
    (h_seq : ℕ → ℝ) (h_pos : ∀ k, 0 < h_seq k)
    (h_tendsto : Filter.Tendsto h_seq Filter.atTop (nhds 0))
    (C_gw σ₀ : ℝ) (hC_gw : 0 < C_gw) (hσ₀ : 0 < σ₀)
    (σ_traj : ℝ → ℝ) (hσ_diff : Differentiable ℝ σ_traj)
    (hσ_traj_pos : ∀ t, 0 < σ_traj t)
    (h_ODE : ∀ t, deriv σ_traj t = C_gw * σ_traj t * Real.exp (-(σ_traj t)))
    (t_gw : ℝ)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ)
    (md₁ : MetricDerivs 4) (k_null : Fin 4 → ℝ) (φ_conf : ℝ)
    (h_pos_foc : Perturbation 4) (hq_pos : 0 < Q h_pos_foc) :
    ((BoundedKPField F ↔ SubstrateEnergyBounded F) ∧
     BoundedKPField F ∧
     (∃ qLimF pLimF : ℝ → ℝ → ℝ, KPFieldHasUniqueSubseqLimits F qLimF pLimF)) ∧
    (einsteinCorrection (polyProfile 1) (polyProfile_x 1) = 1 / 2 ∧
     derivedRicci (gaussianProfile σ x) (gaussianProfile_x σ x) (gaussianProfile_xx σ x) =
       2 / (σ ^ 2 * (gaussianProfile σ x) ^ 2) ∧
     derivedRicci (sechProfile σ x) (sechProfile_x σ x) (sechProfile_xx σ x) = 2 / σ ^ 2 ∧
     derivedRicci (gSechProfile A B x) (gSechProfile_x A B x) (gSechProfile_xx A B x) =
       2 * B ^ 2 / A ^ 2 ∧
     derivedRicci (expProfile α β x) (expProfile_x α β x) (expProfile_xx α β x) = 0 ∧
     Tendsto (fun s : ℝ => 2 / s ^ 2) atTop (𝓝 0) ∧
     Tendsto (fun s : ℝ => 2 / s ^ 2) (𝓝[>] (0 : ℝ)) atTop ∧
     (¬ ∃ C : ℝ, C < 0 ∧
       ∀ y, (deriv r_glob y) ^ 2 - r_glob y * deriv (deriv r_glob) y = C * (r_glob y) ^ 4)) ∧
    (SmoothConvergenceTheorem_1D ∧
     Filter.Tendsto (fun k => fdConformalLaplacianND cfN (h_seq k) φN xN)
       Filter.atTop (nhds (conformalLaplaceBeltramiND cfN φN xN)) ∧
     Filter.Tendsto (fun k => fdChartwiseLaplaceBeltrami g_chart (h_seq k) φN xN)
       Filter.atTop (nhds (chartwiseLaplaceBeltrami g_chart φN xN)) ∧
     (Real.exp σ₀ / (2 * C_gw) ≤ ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C_gw s ∧
      ∫ s in σ₀..(2 * σ₀), doublingTimeIntegrand C_gw s ≤ Real.exp (2 * σ₀) / C_gw) ∧
     ∫ s in (σ_traj 0)..(σ_traj t_gw), Real.exp s / s = C_gw * t_gw) ∧
    (traceReversal 4 (traceReversal 4 h4) = h4 ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) = (10 : ℝ) ^ (244 : ℕ) ∧
     Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
       (BHArea ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ))) ^ 2 ∧
     4 * gbStandard (riemannFromMetric md₁) =
       4 * kretschner (riemannFromMetric md₁) -
         16 * ricciNorm (riemannFromMetric md₁) +
         4 * scalarR (riemannFromMetric md₁) ^ 2 ∧
     gravitonPolarizations 3 = 2 ∧
     nullFocusing (conformalMD 4 φ_conf) k_null =
       φ_conf * nullFocusing (conformalMD 4 1) k_null ∧
     0 < focusing grFocusingHypothesis h_pos_foc) := by
  have hsb1 := SB1_bounded_and_unique_from_SO2Rotation h_rot hM_E_nn h_init h_refine
  exact ⟨⟨boundedKPField_iff_substrateEnergyBounded F, hsb1.1, hsb1.2⟩,
         ⟨polyProfile_correction_at_one,
          derivedRicci_gaussian σ x hσ,
          derivedRicci_sech σ x hσ,
          derivedRicci_gSech A B x hA,
          derivedRicci_expProfile_zero α β x,
          sech_Ricci_atTop,
          sech_Ricci_nhdsGT_zero,
          LSBridge_no_global_smooth_bounded_negative_R r_glob m_lb M_ub hm_lb hmM h_diff_glob h_lower h_upper⟩,
         ⟨SmoothConvergenceTheorem_1D_proved,
          fdLaplaceBeltrami_converges_conformalND cfN h_cfN hφN xN h_seq h_pos h_tendsto,
          fdLaplaceBeltrami_converges_chartwise g_chart h_wgrad xN h_seq h_pos h_tendsto,
          doubling_time_two_sided_bound C_gw σ₀ hC_gw hσ₀,
          gaussian_width_exact_time_parameterization σ_traj C_gw hσ_diff hσ_traj_pos h_ODE t_gw⟩,
         ⟨traceReversal_involutive_4d h4,
          cosmological_constant_N_summary.2.1,
          Nsub_is_BHArea_squared,
          gb_scalar_identity (riemannFromMetric md₁),
          graviton_2_polarizations,
          conformal_focusing_proportional φ_conf k_null,
          gr_signed_focusing.1 h_pos_foc hq_pos⟩⟩

#print axioms lohmiller_slotine_subbridge1_polar_and_substrate_refinement_package
#print axioms lohmiller_slotine_prediction_e1_e2_e3_polynomial_gaussian_sech_package
#print axioms lohmiller_slotine_prediction_efamily_exponential_gensech_and_limits_package
#print axioms lohmiller_slotine_prediction_e5_local_and_global_negative_r_nogo_package
#print axioms curved_4d_lohmiller_slotine_subbridge1_prediction_e_sech_nogo_master_synthesis

end

end UnifiedTheory.Audit.KFCausalCurved4DLohmillerSlotineSubBridge1PredictionESechNoGoBridge
