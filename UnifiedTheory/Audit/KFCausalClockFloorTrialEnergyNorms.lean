/- Physical norm and energy-factor bounds for the actual charge-zero trial.
All constants below are independent of the Planck parameter. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
import UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities (configurationProfile)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
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
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (line)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)

def clockMass (ε a : ℝ) : ℝ := ∫ s : ℝ, ‖clockFunction ε a s‖^2
def halfMass (ε a : ℝ) : ℝ := ∫ s : ℝ, ‖halfClockFunction ε a s‖^2
def dampedMass (ε a : ℝ) : ℝ := ∫ s : ℝ, ‖dampedClockFunction ε a s‖^2

theorem norm_square_of_representative (f : Hilbert) (g : Configuration → ℂ)
    (hg : MemLp g 2 volume) (he : f =ᵐ[volume] g) : ‖f‖^2 = ∫ z, ‖g z‖^2 := by
  have hf : f = hg.toLp g := Lp.ext (he.trans hg.coeFn_toLp.symm)
  exact (congrArg (fun u : Hilbert => ‖u‖^2) hf).trans (toLp_square_integral g hg)

theorem trial_norm_square (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖trialState ε a hbar hε ha hh‖^2 =
      clockMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hm := KFCausalPhysicalGaussianCharge.configurationProfile_memLp _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) _
    (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)
  exact (norm_square_of_representative _ _ hm (trialState_coe ε a hbar hε ha hh)).trans
    (profile_square_integral _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
      _ (clockFunction_memLp ε a hε ha))

theorem clockMass_positive (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : 0 < clockMass ε a := by
  have hn := norm_pos_iff.mpr (trialState_ne_zero ε a 1 hε ha one_ne_zero)
  have he := trial_norm_square ε a 1 hε ha one_ne_zero
  have hp := gaussianMass_positive _ _ (groundWidth_positive 1 one_ne_zero)
    (neutralWidth_positive 1 one_ne_zero)
  exact (mul_pos_iff_of_pos_right hp).mp (he ▸ sq_pos_of_pos hn)

theorem halfMass_nonnegative (ε a : ℝ) : 0 ≤ halfMass ε a := integral_nonneg (fun _ => sq_nonneg _)
theorem dampedMass_nonnegative (ε a : ℝ) : 0 ≤ dampedMass ε a := integral_nonneg (fun _ => sq_nonneg _)

theorem trial_clockHalf_mass (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (g : Hilbert) (hg : (trialState ε a hbar hε ha hh,g) ∈ (clockHalf ε).graph) :
    ‖g‖^2 = halfMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hm := KFCausalPhysicalGaussianCharge.configurationProfile_memLp _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) _
    (halfClockFunction_continuous ε a) (halfClockFunction_memLp ε a hε ha)
  have he : g =ᵐ[volume] configurationProfile (groundWidth hbar) (neutralWidth hbar) (halfClockFunction ε a) := by
    filter_upwards [(clockHalf_graph ε _ _).mp hg,trialState_coe ε a hbar hε ha hh] with z hz ht
    rw [hz,ht]
    simp only [configurationProfile,halfClockFunction,halfWeight,mul_assoc]
  exact (norm_square_of_representative g _ hm he).trans
    (profile_square_integral _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
      _ (halfClockFunction_memLp ε a hε ha))

def kineticMass (ε a : ℝ) (v : Transverse) : ℝ := 80*dampedMass ε a*(∑ i : Fin 5, (v i)^2)

theorem kineticMass_nonnegative (ε a : ℝ) (v : Transverse) : 0 ≤ kineticMass ε a v := by
  have := dampedMass_nonnegative ε a
  unfold kineticMass
  positivity

theorem trial_momentum_mass (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hh1 : |hbar| ≤ 1) (v : Transverse) (g : Hilbert)
    (hg : (trialState ε a hbar hε ha hh,g) ∈ (clockMomentum ε hbar v).graph) :
    ‖g‖^2 ≤ kineticMass ε a v*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
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
  have hstep : 80*|hbar| *(∑ i : Fin 5, (v i)^2) ≤ 80*(∑ i : Fin 5, (v i)^2) := by
    nlinarith only [mul_le_mul_of_nonneg_right hh1 (show 0 ≤ 80*(∑ i : Fin 5, (v i)^2) by positivity)]
  have hc := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep
    (gaussianMass_positive _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)).le)
    (dampedMass_nonnegative ε a)
  rw [hn,hp]
  unfold kineticMass
  nlinarith only [hb,hc]

theorem gaussianState_mass (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    ‖gaussianState ε a α β y hε ha hα hβ hw hy‖^2 =
      ∫ z : ℝ × Grouped, ‖line ε a α β y z‖^2 := by
  let f := configurationLine ε a α β y
  have hf := configurationLine_memLp ε a α β y hε ha hα hβ hw hy
  have hn := (coordinates ε hε).norm_map (hf.toLp f)
  exact (congrArg (fun r : ℝ => r^2) hn).trans ((toLp_square_integral f hf).trans
    (grouping_preserves_volume.integral_comp grouping.measurableEmbedding
      (fun z : ℝ × Grouped => ‖line ε a α β y z‖^2)))

theorem shiftedOutput_mass_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖shiftedOutput ε a hbar hε ha hh hbound‖^2 ≤
      stripMass ε a*gaussianMass (groundWidth hbar) (neutralWidth hbar) :=
  (gaussianState_mass ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hbound)).le.trans
      (line_mass_bound ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
        (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hbound))

#print axioms norm_square_of_representative
#print axioms trial_norm_square
#print axioms clockMass_positive
#print axioms halfMass_nonnegative
#print axioms dampedMass_nonnegative
#print axioms trial_clockHalf_mass
#print axioms kineticMass_nonnegative
#print axioms trial_momentum_mass
#print axioms gaussianState_mass
#print axioms shiftedOutput_mass_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
