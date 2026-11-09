/- The neutral translation is precisely the existing canonical momentum
phase test. Hence its complete averaged form-domain preservation applies
to that test, rather than to a substitute observable. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralCanonicalForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (Frequency operator operator_coe scalar)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalNeutralTranslationAveragedForm (formAction formAction_embedding energy_domain_action_iff)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def frequency (v : ℝ) : Frequency (X := Configuration) := (0,vector v)

theorem vector_smul (h v : ℝ) : h • vector v = vector (h*v) := by
  apply Prod.ext
  · simp [vector]
  · funext i
    fin_cases i <;> simp [vector,smul_eq_mul]

theorem operator_action (h v : ℝ) (f : Hilbert) :
    operator volume h (frequency v) f = action (h*v) f := by
  apply Lp.ext
  filter_upwards [operator_coe volume h (frequency v) f,action_coe (h*v) f] with x hw ht
  rw [hw,ht]
  simp only [frequency,ContinuousLinearMap.zero_apply,scalar,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_mul,vector_smul]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ Real.pi*ε) (hne : h ≠ 0)
  (m g k t : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)

theorem canonical_form_embedding (v : ℝ) (u : AveragedSpace ε hε h hh hne m g k t) :
    embedding ε hε h hh hne m g k t (formAction ε hε h hh hne m g k t hm hg hk (h*v) u) =
      operator volume h (frequency v) (embedding ε hε h hh hne m g k t u) := by
  exact (formAction_embedding ε hε h hh hne m g k t hm hg hk (h*v) u).trans
    (operator_action h v _).symm

include hm hg hk in
theorem canonical_energy_domain (v : ℝ) (f : Hilbert) :
    operator volume h (frequency v) f ∈ (energyOperator ε hε h hh hne m g k t).domain ↔
      f ∈ (energyOperator ε hε h hh hne m g k t).domain := by
  simpa only [operator_action] using
    energy_domain_action_iff ε hε h hh hne m g k t hm hg hk (h*v) f

#print axioms vector_smul
#print axioms operator_action
#print axioms canonical_form_embedding
#print axioms canonical_energy_domain

end
end UnifiedTheory.Audit.KFCausalNeutralCanonicalForm
