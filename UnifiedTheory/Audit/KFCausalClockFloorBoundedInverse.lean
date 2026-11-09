/- The actual inverse half-clock is bounded and commutes with the defect.
Consequently the natural ordered exponential is closed, since its right
factor is everywhere defined and bounded. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

variable (ε : ℝ) (hε : 0 < ε)

def inverseLinear : Hilbert →ₗ[ℂ] Hilbert where
  toFun := inverseAction ε hε
  map_add' f g := (inverseClockHalf ε).map_add
    ⟨f,inverseClockHalf_domain ε hε f⟩ ⟨g,inverseClockHalf_domain ε hε g⟩
  map_smul' c f := (inverseClockHalf ε).map_smul c ⟨f,inverseClockHalf_domain ε hε f⟩

theorem inverseAction_norm_bound (f : Hilbert) :
    ‖inverseAction ε hε f‖ ≤ (Real.sqrt ε)⁻¹*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [inverseAction_coe ε hε f] with x hx
  rw [hx,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (inverseWeight_bound ε hε x) (norm_nonneg _)

def inverseL : Hilbert →L[ℂ] Hilbert :=
  (inverseLinear ε hε).mkContinuous ((Real.sqrt ε)⁻¹) (inverseAction_norm_bound ε hε)

theorem inverseL_eq (f : Hilbert) : inverseL ε hε f = inverseAction ε hε f := rfl

theorem inverseL_graph (f g : Hilbert) :
    (f,g) ∈ (inverseClockHalf ε).graph ↔ g = inverseL ε hε f := by
  have hg := (inverseClockHalf ε).mem_graph ⟨f,inverseClockHalf_domain ε hε f⟩
  constructor
  · intro h
    exact (inverseClockHalf ε).mem_graph_snd_inj' h hg rfl
  · intro h
    rw [h]
    exact hg

theorem inverseL_defect (f : Hilbert) :
    inverseL ε hε (defectOperator ε hε f) = defectOperator ε hε (inverseL ε hε f) := by
  apply Lp.ext
  filter_upwards [inverseAction_coe ε hε (defectOperator ε hε f),defectOperator_coe ε hε f,
    defectOperator_coe ε hε (inverseL ε hε f),inverseAction_coe ε hε f] with x hs hd ht hf
  change (inverseL ε hε (defectOperator ε hε f)) x = _ at hs
  change (inverseL ε hε f) x = _ at hf
  rw [hs,ht,hd,hf]
  ring

theorem ordered_graph_iff (hbar : ℝ) (f g : Hilbert) :
    (f,g) ∈ (orderedExponential ε hε hbar).graph ↔
      (inverseL ε hε f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph := by
  rw [orderedExponential,composition_graph]
  constructor
  · rintro ⟨y,hy,hg⟩
    rw [(inverseL_graph ε hε f y).mp hy] at hg
    exact hg
  · intro h
    exact ⟨_,(inverseL_graph ε hε f _).mpr rfl,h⟩

theorem orderedExponential_closed (hbar : ℝ) :
    (orderedExponential ε hε hbar).IsClosed := by
  let T := (inverseL ε hε).prodMap (ContinuousLinearMap.id ℂ Hilbert)
  have he : ((orderedExponential ε hε hbar).graph : Set (Hilbert × Hilbert)) =
      T ⁻¹' ((longitudinalExponential ε hε hbar (1/2)).graph : Set (Hilbert × Hilbert)) := by
    ext z
    exact ordered_graph_iff ε hε hbar z.1 z.2
  change IsClosed ((orderedExponential ε hε hbar).graph : Set (Hilbert × Hilbert))
  rw [he]
  exact (longitudinal_exponential_closed ε hε hbar (1/2)).preimage T.continuous

#print axioms inverseAction_norm_bound
#print axioms inverseL_eq
#print axioms inverseL_graph
#print axioms inverseL_defect
#print axioms ordered_graph_iff
#print axioms orderedExponential_closed

end
end UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
