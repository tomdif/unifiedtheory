/- Quantitative vanishing of the actual kinetic and ordered matter energies
on the concentrating trial. No unbounded-observable limit is inferred from
weak convergence of the initial probability law. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary (dampedProfile)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

theorem trial_momentum_rate (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (v : Transverse) (g : Hilbert)
    (hg : (trialState ε a hbar hε ha hh,g) ∈ (clockMomentum ε hbar v).graph) :
    ‖g‖^2 ≤ |hbar| *kineticMass ε a v*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have he := (clockMomentum ε hbar v).mem_graph_snd_inj' hg
    (trialState_clockMomentum_graph ε a hbar hε ha hh v) rfl
  dsimp only [Prod.snd] at he
  have hn : ‖g‖^2 = hbar^2*(∫ z : Configuration, ‖derivative v (dampedProfile ε a hbar) z‖^2) := by
    rw [he,norm_smul,mul_pow,toLp_square_integral]
    simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hp : (∫ z : Configuration, ‖derivative v (dampedProfile ε a hbar) z‖^2) =
      dampedMass ε a*(∫ x : Transverse, ‖gradient (groundWidth hbar) (neutralWidth hbar) v x‖^2) := by
    simp_rw [dampedProfile_eq,configurationProfile_derivative]
    exact product_square_integral _ _ (dampedClockFunction_memLp ε a hε ha)
      (gradient_memLp _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) v)
  have hb := mul_le_mul_of_nonneg_left (ground_gradient_mass_bound hbar hh v) (dampedMass_nonnegative ε a)
  rw [hn,hp]
  unfold kineticMass
  nlinarith only [hb]

theorem scaled_linear_field_bound (l : Transverse →L[ℝ] ℝ) (f g q : Hilbert)
    (hg : (f,g) ∈ (physicalField l).graph) (hq : (f,q) ∈ (fieldSquare l).graph)
    (r : ℝ) (hr : 0 < r) : ‖g‖^2 ≤ r*‖f‖^2+‖q‖^2/r := by
  have hf2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f)
  have hg2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
  have hq2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp q).1).mp (Lp.memLp q)
  have hb : (∫ x, ‖g x‖^2) ≤ ∫ x, r*‖f x‖^2+‖q x‖^2/r := by
    apply integral_mono_ae hg2 ((hf2.const_mul r).add (hq2.div_const r))
    filter_upwards [(physicalField_graph l _ _).mp hg,(fieldSquare_graph l _ _).mp hq] with x hx hy
    change ‖g x‖^2 ≤ r*‖f x‖^2+‖q x‖^2/r
    rw [hx,hy]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    have hs : (l x.2)^2 ≤ r+((l x.2)^2)^2/r := by
      calc
        _ ≤ (r^2+((l x.2)^2)^2)/r := (le_div_iff₀ hr).mpr (by
          nlinarith only [sq_nonneg ((l x.2)^2-r),mul_nonneg hr.le (sq_nonneg (l x.2))])
        _ = _ := by field_simp
    convert mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f x‖) using 1
    ring
  rw [integral_add (hf2.const_mul r) (hq2.div_const r),integral_const_mul,integral_div] at hb
  simpa only [← l2_norm_square] using hb

theorem shifted_fieldSquare_rate (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (q : Hilbert)
    (hq : (shiftedOutput ε a hbar hε ha hh hb,q) ∈ (fieldSquare l).graph) :
    ‖q‖^2 ≤ hbar^2*quadraticMass ε a l*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hn := gaussianState_fieldSquare_mass ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hb) l q hq
  have he := quadratic_mass_bound ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hb) l
  rw [ground_moment hbar hh] at he
  rw [hn]
  convert he using 1
  unfold quadraticMass
  simp only [mul_pow,sq_abs]
  ring

theorem trial_quadraticMatter_rate (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (q : Hilbert)
    (hq : (trialState ε a hbar hε ha hh,q) ∈ (matterFactor ε hε hbar (fieldSquare l)).graph) :
    ‖q‖^2 ≤ hbar^2*quadraticMass ε a l*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  obtain ⟨f,hf,hfq⟩ := (composition_graph _ _ _ _).mp hq
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' hf
    (trialState_shifted_graph ε a hbar hε ha hh hb) rfl
  dsimp only [Prod.snd] at he
  exact shifted_fieldSquare_rate ε a hbar hε ha hh hb l q (he ▸ hfq)

theorem trial_linearMatter_rate (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (trialState ε a hbar hε ha hh,g) ∈ (matterFactor ε hε hbar (physicalField l)).graph) :
    ‖g‖^2 ≤ |hbar| *(stripMass ε a+quadraticMass ε a l)*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  obtain ⟨f,hf,hfg⟩ := (composition_graph _ _ _ _).mp hg
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' hf
    (trialState_shifted_graph ε a hbar hε ha hh hb) rfl
  dsimp only [Prod.snd] at he
  let q := fieldSquare l ⟨shiftedOutput ε a hbar hε ha hh hb,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hb l⟩
  have hq := (fieldSquare l).mem_graph ⟨shiftedOutput ε a hbar hε ha hh hb,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hb l⟩
  have h1 := scaled_linear_field_bound l _ g q (he ▸ hfg) hq |hbar| (abs_pos.mpr hh)
  have h2 := add_le_add (mul_le_mul_of_nonneg_left
    (shiftedOutput_mass_bound ε a hbar hε ha hh hb) (abs_nonneg hbar))
    (div_le_div_of_nonneg_right (shifted_fieldSquare_rate ε a hbar hε ha hh hb l q hq) (abs_nonneg hbar))
  apply h1.trans (h2.trans_eq _)
  rw [← sq_abs hbar]
  field_simp

#print axioms trial_momentum_rate
#print axioms scaled_linear_field_bound
#print axioms shifted_fieldSquare_rate
#print axioms trial_quadraticMatter_rate
#print axioms trial_linearMatter_rate

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay
