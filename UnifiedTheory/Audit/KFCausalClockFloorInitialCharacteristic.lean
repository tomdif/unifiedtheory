/- Joint initial position/momentum characteristic convergence of the actual
uniform-energy physical family. The clock floor is fixed. This is not a
propagation theorem or a joint limit removing that floor. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration
open UnifiedTheory.Audit.KFCausalGaussianPhaseSpaceLimit
open UnifiedTheory.Audit.KFCausalLpPhaseTranslation
open UnifiedTheory.Audit.KFCausalProductPhaseTranslation
open UnifiedTheory.Audit.KFCausalClockFloorInitialProduct
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Ordered modulation followed on the input by a canonical translation.
There are six position frequencies and six momentum frequencies. -/
def observable (hbar r u : ℝ) (ξ η : Transverse) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  phaseTranslation volume (fun z : Configuration => r*z.1+dot ξ z.2)
    ((measurable_const.mul measurable_fst).add ((dot_continuous ξ).measurable.comp measurable_snd))
    (hbar*u,hbar • η)

def transverseCharacteristic (hbar : ℝ) (hh : hbar ≠ 0) (ξ η : Transverse) : ℂ :=
  inner ℂ (unitGaussian hbar hh)
    (phaseTranslation volume (dot ξ) (dot_continuous ξ).measurable (hbar • η) (unitGaussian hbar hh))

theorem transverseCharacteristic_bound (hbar : ℝ) (hh : hbar ≠ 0) (ξ η : Transverse) :
    ‖transverseCharacteristic hbar hh ξ η-1‖ ≤ errorBound hbar ξ η := by
  have he : inner ℂ (unitGaussian hbar hh) (unitGaussian hbar hh) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,unitGaussian_norm]; norm_num
  rw [transverseCharacteristic,← he,← inner_sub_right]
  have hb := norm_inner_le_norm (𝕜 := ℂ) (unitGaussian hbar hh)
    (phaseTranslation volume (dot ξ) (dot_continuous ξ).measurable (hbar • η)
      (unitGaussian hbar hh)-unitGaussian hbar hh)
  rw [unitGaussian_norm,one_mul] at hb
  exact hb.trans (phaseTranslation_bound hbar hh ξ η)

theorem transverseCharacteristic_tendsto (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0)
    (hlim : Tendsto h atTop (𝓝 0)) (ξ η : Transverse) :
    Tendsto (fun n => transverseCharacteristic (h n) (hh n) ξ η) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => transverseCharacteristic_bound (h n) (hh n) ξ η)
    ((errorBound_tendsto ξ η).comp hlim)

def translatedClockCharacteristic (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbar r u : ℝ) : ℂ :=
  inner ℂ (unitClock ε a hε ha)
    (phaseTranslation volume (fun s : ℝ => r*s) (measurable_const.mul measurable_id)
      (hbar*u) (unitClock ε a hε ha))

theorem translatedClockCharacteristic_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (r u : ℝ) :
    Tendsto (fun hbar => translatedClockCharacteristic ε a hε ha hbar r u) (𝓝 0)
      (𝓝 (clockCharacteristic ε a hε ha r)) := by
  have hc : Continuous (fun hbar : ℝ => translatedClockCharacteristic ε a hε ha hbar r u) := by
    exact continuous_const.inner ((modulation volume (fun s : ℝ => r*s)
      (measurable_const.mul measurable_id)).continuous.comp
        ((translation_continuous volume (unitClock ε a hε ha)).comp (continuous_id.mul continuous_const)))
  have hz : translatedClockCharacteristic ε a hε ha 0 r u = clockCharacteristic ε a hε ha r := by
    change inner ℂ _ (modulation volume (fun s : ℝ => r*s) (measurable_const.mul measurable_id)
      (translation volume (0*u) (unitClock ε a hε ha))) = _
    rw [zero_mul,translation_zero]
    rfl
  exact hz ▸ hc.tendsto 0

def quantumCharacteristic (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (r u : ℝ) (ξ η : Transverse) : ℂ :=
  inner ℂ (unitTrial ε a hbar hε ha hh) (observable hbar r u ξ η (unitTrial ε a hbar hε ha hh))

theorem quantumCharacteristic_product (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (r u : ℝ) (ξ η : Transverse) :
    quantumCharacteristic ε a hbar hε ha hh r u ξ η =
      translatedClockCharacteristic ε a hε ha hbar r u*transverseCharacteristic hbar hh ξ η := by
  rw [quantumCharacteristic,unitTrial_product]
  exact product_characteristic volume volume (fun s : ℝ => r*s) (measurable_const.mul measurable_id)
    (dot ξ) (dot_continuous ξ).measurable (hbar*u) (hbar • η) (unitClock ε a hε ha) (unitGaussian hbar hh)

theorem quantumCharacteristic_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0)) (r u : ℝ) (ξ η : Transverse) :
    Tendsto (fun n => quantumCharacteristic ε a (h n) hε ha (hh n) r u ξ η) atTop
      (𝓝 (∫ z, classicalPhase r u ξ η z ∂classicalLaw ε a)) := by
  simp_rw [quantumCharacteristic_product]
  rw [classicalLaw_characteristic ε a hε ha]
  simpa only [mul_one] using
    (((translatedClockCharacteristic_tendsto ε a hε ha r u).comp hlim).mul
      (transverseCharacteristic_tendsto h hh hlim ξ η))

/-- An explicit admissible sequence, to make the limiting family non-vacuous. -/
def parameter (ε : ℝ) (n : ℕ) : ℝ := min 1 (2*Real.pi*ε/3)/((n:ℝ)+1)

theorem parameter_positive (ε : ℝ) (hε : 0 < ε) (n : ℕ) : 0 < parameter ε n := by
  unfold parameter
  apply div_pos (lt_min zero_lt_one (by positivity))
  positivity

theorem parameter_bound (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    |parameter ε n| ≤ min 1 (2*Real.pi*ε/3) := by
  rw [abs_of_pos (parameter_positive ε hε n)]
  exact div_le_self (le_of_lt (lt_min zero_lt_one (by positivity)))
    (le_add_of_nonneg_left (Nat.cast_nonneg n))

theorem parameter_tendsto (ε : ℝ) : Tendsto (parameter ε) atTop (𝓝 0) := by
  simpa only [parameter,div_eq_mul_inv,one_mul,mul_zero] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
      Tendsto (fun n : ℕ => min 1 (2*Real.pi*ε/3)*(1/((n:ℝ)+1))) atTop (𝓝 (_*0)))

theorem exists_admissible_sequence (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ → ℝ, (∀ n, h n ≠ 0) ∧ (∀ n, |h n| ≤ 2*Real.pi*ε/3) ∧
      (∀ n, |h n| ≤ 1) ∧ Tendsto h atTop (𝓝 0) :=
  ⟨parameter ε,fun n => (parameter_positive ε hε n).ne',
    fun n => (parameter_bound ε hε n).trans (min_le_right _ _),
    fun n => (parameter_bound ε hε n).trans (min_le_left _ _),parameter_tendsto ε⟩

/-- The convergence theorem applies to the same states already proved to lie
in the actual averaged energy form with a uniform energy bound. -/
theorem physical_state_characteristic_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hh1 : ∀ n, |h n| ≤ 1) (hlim : Tendsto h atTop (𝓝 0))
    (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (r u : ℝ) (ξ η : Transverse) :
    Tendsto (fun n =>
      let f := KFCausalClockFloorAveragedFormTransport.embedding ε hε (h n) (hh n) (hb n)
        mass2 quartic vacuum 0
        (state ε a hε ha (h n) (hh n) (hb n) (hh1 n) mass2 quartic vacuum s hm hq hv)
      inner ℂ f (observable (h n) r u ξ η f)) atTop
      (𝓝 (∫ z, classicalPhase r u ξ η z ∂classicalLaw ε a)) := by
  simp_rw [state_embedding]
  exact quantumCharacteristic_tendsto ε a hε ha h hh hlim r u ξ η

#print axioms transverseCharacteristic_bound
#print axioms transverseCharacteristic_tendsto
#print axioms translatedClockCharacteristic_tendsto
#print axioms quantumCharacteristic_product
#print axioms quantumCharacteristic_tendsto
#print axioms parameter_positive
#print axioms parameter_bound
#print axioms parameter_tendsto
#print axioms exists_admissible_sequence
#print axioms physical_state_characteristic_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
