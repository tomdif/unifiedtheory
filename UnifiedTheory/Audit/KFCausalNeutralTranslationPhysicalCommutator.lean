/- The actual averaged energy form obeys a neutral-translation commutator
bound. At the canonical displacement r=hbar*v its normalized bound is
uniform over nonzero hbar in a bounded interval. No trajectory derivative
or classical transport identification is assumed or asserted here. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationAveragedForm
import UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalNeutralTranslationMatter (shiftValue)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
open UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph (energyWeight_ne_zero)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalNeutralTranslationAveragedForm (formAction formAction_output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem pointField_shift (r : ℝ) : shiftValue pointField r = (r : ℂ) := by
  simp [shiftValue,KFCausalMatterOrderedDomain.pointField]

def speedBound (w : Fin 8 → ℂ) (H v : ℝ) : ℝ :=
  2*(|v| *‖weightedLinear w‖+H*|v|^2*‖weightedQuadratic w‖)

theorem errorBound_scaled (w : Fin 8 → ℂ) (h v H : ℝ) (hh : |h| ≤ H) :
    2*errorBound w ((h*v : ℝ) : ℂ) ≤ |h| *speedBound w H v := by
  simp only [errorBound,Complex.norm_real,Real.norm_eq_abs,abs_mul,mul_pow,speedBound]
  have hn := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 2*|h| *|v|^2*‖weightedQuadratic w‖)
  nlinarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε) (hne : h ≠ 0)
  (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
local notation "𝒱" => AveragedSpace ε hε h hh hne m g k t
local notation "E" => energyOutput ε hε h hh hne m g k t
local notation "F" => formAction ε hε h hh hne m g k t hm hg hk
local notation "w" => energyWeight m g k t

def formCommutator (r : ℝ) (u z : 𝒱) : ℂ :=
  inner ℂ (E u) (E (F r z))-inner ℂ (E (F (-r) u)) (E z)

theorem form_commutator_bound (r : ℝ) (u z : 𝒱) :
    ‖formCommutator ε hε h hh hne m g k t hm hg hk r u z‖ ≤
      (2*errorBound w (r:ℂ))*‖E u‖*‖E z‖ := by
  have hb := outputLp_commutator angleMeasure w (energyWeight_ne_zero m g k t hm hg hk) (r:ℂ) r (E u) (E z)
  simpa only [formCommutator,formAction_output,pointField_shift,Complex.ofReal_neg] using hb

theorem canonical_commutator_bound (v H : ℝ) (hH : |h| ≤ H) (u z : 𝒱) :
    ‖formCommutator ε hε h hh hne m g k t hm hg hk (h*v) u z‖ ≤
      |h| *speedBound w H v*‖E u‖*‖E z‖ := by
  apply (form_commutator_bound ε hε h hh hne m g k t hm hg hk (h*v) u z).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (errorBound_scaled w h v H hH) (norm_nonneg _)) (norm_nonneg _)

theorem normalized_commutator_bound (v H : ℝ) (hH : |h| ≤ H) (u z : 𝒱) :
    ‖formCommutator ε hε h hh hne m g k t hm hg hk (h*v) u z‖/|h| ≤
      speedBound w H v*‖E u‖*‖E z‖ := by
  have divide (a b c d x : ℝ) (hx : 0 < x) (ha : a ≤ x*b*c*d) : a/x ≤ b*c*d := by
    apply (div_le_iff₀ hx).mpr
    nlinarith only [ha]
  exact divide _ _ _ _ _ (abs_pos.mpr hne)
    (canonical_commutator_bound ε hε h hh hne m g k t hm hg hk v H hH u z)

#print axioms pointField_shift
#print axioms errorBound_scaled
#print axioms form_commutator_bound
#print axioms canonical_commutator_bound
#print axioms normalized_commutator_bound

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator
