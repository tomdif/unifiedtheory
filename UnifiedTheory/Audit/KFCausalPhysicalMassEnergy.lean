/- Regularized physical energies along the constructed eight-factor weak
solution. Their derivatives have a cutoff-independent local bound and
converge to zero, while the energies converge to the physical norm squared. -/
import UnifiedTheory.Audit.KFCausalPhysicalWeakFormContinuity
import UnifiedTheory.Audit.KFCausalMassEnergyIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalMassEnergy
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
open UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
open UnifiedTheory.Audit.KFCausalPhysicalCountableLimit
open UnifiedTheory.Audit.KFCausalPhysicalWeakTrajectory
open UnifiedTheory.Audit.KFCausalPhysicalWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalPhysicalWeakFormContinuity
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalLocalWeakContinuity
open UnifiedTheory.Audit.KFCausalMassRegularization
open UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative
open UnifiedTheory.Audit.KFCausalMassEnergyIdentities

theorem mass_inner_symm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (x y : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ (massOperator ε hε hbar hh mass2 quartic vacuum x) y = inner ℂ x (massOperator ε hε hbar hh mass2 quartic vacuum y) :=
  gram_inner_symm _ x y

theorem mass_positive (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (x : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : 0 ≤ (inner ℂ (massOperator ε hε hbar hh mass2 quartic vacuum x) x).re := by
  rw [mass_left_pairing,complex_inner_square,Complex.ofReal_re]
  positivity

theorem massSlope_window_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (T t : ℝ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖massSlope ε hε hbar hh mass2 quartic vacuum s w V t‖ ≤ massLipschitzBound ε hε hbar hh mass2 quartic vacuum s T w := by
  have hf : ‖referenceFormOperator ε hε hbar hh mass2 quartic vacuum t‖ ≤ 1+Real.exp (2*T) :=
    (referenceForm_norm_le ε hε hbar hh mass2 quartic vacuum t).trans
      (add_le_add le_rfl (Real.exp_le_exp.mpr (by linarith [(abs_le.mp ht).2])))
  have hpair := (ContinuousLinearMap.le_opNorm (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t) (V.formState t)).trans
    (mul_le_mul hf (formState_window_bound ε hε hbar hh mass2 quartic vacuum s w V T t hT ht)
      (norm_nonneg _) (by positivity))
  have he := mul_le_mul_of_nonneg_left hpair (abs_nonneg (1/hbar))
  unfold massSlope massLipschitzBound
  simp only [norm_smul,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
  convert he using 1
  ring

theorem massSlope_weakly_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) :
    ∀ y, Continuous (fun t => inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s w V t) y) := by
  intro y
  simpa only [massSlope_pairing] using limitSlope_continuous ε hε hbar hh mass2 quartic vacuum s w V y

def massEnergy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (δ t : ℝ) : ℝ :=
  energy (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massInverse (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ) (massState ε hε hbar hh mass2 quartic vacuum s w V t)

def massEnergyDerivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (δ t : ℝ) : ℝ :=
  2*(inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s w V t)
    (massInverse (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ (massState ε hε hbar hh mass2 quartic vacuum s w V t))).re

theorem massEnergy_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (massEnergy ε hε hbar hh mass2 quartic vacuum s w V δ)
      (massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V δ t) t := by
  have hs := massInverse_symmetric (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (massOperator ε hε hbar hh mass2 quartic vacuum) (mass_inner_symm ε hε hbar hh mass2 quartic vacuum)
    (mass_positive ε hε hbar hh mass2 quartic vacuum) δ hδ
  apply energy_derivative_of_weak (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (massInverse (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ) hs
    (massState ε hε hbar hh mass2 quartic vacuum s w V) (massSlope ε hε hbar hh mass2 quartic vacuum s w V t)
    t (massLipschitzBound ε hε hbar hh mass2 quartic vacuum s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε hbar hh mass2 quartic vacuum s (|t|+1) w)
  · have he : ∀ᶠ h in 𝓝 (0:ℝ), |h| < 1 := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hpair
    have ht : |t| ≤ |t|+1 := by linarith
    have hsum : |t+h| ≤ |t|+|h| := by
      simpa only [sub_zero,zero_sub,sub_neg_eq_add,abs_neg,zero_add] using abs_sub_le t 0 (-h)
    have hth : |t+h| ≤ |t|+1 := hsum.trans (by linarith)
    simpa only [add_sub_cancel_left] using massState_window_lipschitz ε hε hbar hh mass2 quartic vacuum s w V
      (|t|+1) t (t+h) (by positivity) ht hth
  · exact mass_pairing_derivative ε hε hbar hh mass2 quartic vacuum s w V t

theorem massEnergyDerivative_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) (δ : ℝ) :
    Continuous (massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V δ) := by
  have hp := (massInverse (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ).continuous
  have hg := massState_continuous ε hε hbar hh mass2 quartic vacuum s w V
  have hpg := hp.comp hg
  have hpair := weak_strong_pairing_continuous (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massSlope ε hε hbar hh mass2 quartic vacuum s w V)
    (fun t => massInverse (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ (massState ε hε hbar hh mass2 quartic vacuum s w V t))
    (fun T => massLipschitzBound ε hε hbar hh mass2 quartic vacuum s T w)
    (massSlope_window_bound ε hε hbar hh mass2 quartic vacuum s w V)
    (massSlope_weakly_continuous ε hε hbar hh mass2 quartic vacuum s w V)
    hpg
  exact continuous_const.mul (Complex.continuous_re.comp hpair)

theorem massSlope_diagonal_zero (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) (t : ℝ) :
    (inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s w V t) (V.formState t)).re = 0 := by
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (staticMap ε hε hbar hh mass2 quartic vacuum) (growingMap ε hε hbar hh mass2 quartic vacuum) t
  have hpair := schrodinger_diagonal_zero (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t) hs hbar (V.formState t)
  exact hpair

theorem massEnergyDerivative_error (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (δ t : ℝ) (hδ : 0 < δ) :
    massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V δ t =
      -2*(inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s w V t)
        (damping (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) δ (V.formState t))).re :=
  regularized_slope_error (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) _ (mass_inner_symm ε hε hbar hh mass2 quartic vacuum) (mass_positive ε hε hbar hh mass2 quartic vacuum)
    δ hδ (V.formState t) _ (massSlope_diagonal_zero ε hε hbar hh mass2 quartic vacuum s w V t)

theorem massEnergyDerivative_window_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (δ T t : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V δ t‖ ≤
      2*massLipschitzBound ε hε hbar hh mass2 quartic vacuum s T w * windowRadius ε hε hbar hh mass2 quartic vacuum s T w := by
  rw [massEnergyDerivative_error ε hε hbar hh mass2 quartic vacuum s w V δ t hδ]
  apply (energy_error_norm_bound _ _).trans
  have hd := (damping_contraction (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) (mass_inner_symm ε hε hbar hh mass2 quartic vacuum)
    (mass_positive ε hε hbar hh mass2 quartic vacuum) δ hδ (V.formState t)).trans
    (formState_window_bound ε hε hbar hh mass2 quartic vacuum s w V T t hT ht)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (massSlope_window_bound ε hε hbar hh mass2 quartic vacuum s w V T t hT ht)
    (by norm_num)) hd (norm_nonneg _) (by have := massLipschitzBound_nonneg ε hε hbar hh mass2 quartic vacuum s T w; positivity)

def massScale (n : ℕ) : ℝ := (cutoff n)⁻¹

theorem massScale_pos (n : ℕ) : 0 < massScale n := inv_pos.mpr (cutoff_pos n)

theorem massScale_tendsto : Tendsto massScale atTop (𝓝 0) := tendsto_inv_atTop_zero.comp cutoff_tendsto

theorem massEnergy_tendsto (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) (t : ℝ) :
    Tendsto (fun n => massEnergy ε hε hbar hh mass2 quartic vacuum s w V (massScale n) t) atTop
      (𝓝 (‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V.formState t)‖^2)) := by
  have hpair := embedded_energy_limit (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh mass2 quartic vacuum 0)
    massScale massScale_pos massScale_tendsto (V.formState t)
  exact hpair

theorem massEnergyDerivative_tendsto_zero (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) (t : ℝ) :
    Tendsto (fun n => massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V (massScale n) t) atTop (𝓝 0) := by
  have hr := embedded_damping_pairing_limit (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh mass2 quartic vacuum 0)
    massScale massScale_pos massScale_tendsto (V.formState t) (massSlope ε hε hbar hh mass2 quartic vacuum s w V t)
  have he : (fun n => massEnergyDerivative ε hε hbar hh mass2 quartic vacuum s w V (massScale n) t) =
      (fun n => -2*(inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s w V t)
        (damping (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (massOperator ε hε hbar hh mass2 quartic vacuum) (massScale n) (V.formState t))).re) := by
    funext n
    exact massEnergyDerivative_error ε hε hbar hh mass2 quartic vacuum s w V _ t (massScale_pos n)
  rw [he]
  exact hr

#print axioms mass_positive
#print axioms massSlope_window_bound
#print axioms massEnergy_derivative
#print axioms massEnergyDerivative_continuous
#print axioms massSlope_diagonal_zero
#print axioms massEnergyDerivative_error
#print axioms massEnergyDerivative_window_bound
#print axioms massEnergy_tendsto
#print axioms massEnergyDerivative_tendsto_zero

end
end UnifiedTheory.Audit.KFCausalPhysicalMassEnergy
