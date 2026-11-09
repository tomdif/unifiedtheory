/- Every bounded measurable clock multiplier preserves the actual
clock-half and transverse kinetic graphs. Transverse commutation follows
from translations and the strong generator, including maximal domains. -/
import UnifiedTheory.Audit.KFCausalBoundedClockCharge
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalBoundedClockFactorGraphs
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalBoundedClockCharge (multiplier multiplier_coe)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

variable (m : ℝ → ℂ) (hm : Measurable m) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ s, ‖m s‖ ≤ C)
local notation "M" => multiplier m hm C hC hb

def euclideanMultiplier : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  (euclideanPullback : Hilbert →L[ℂ] FrequencyHilbert).comp
    ((M).comp (euclideanPullback.symm : FrequencyHilbert →L[ℂ] Hilbert))

theorem euclideanMultiplier_coe (f : FrequencyHilbert) :
    euclideanMultiplier m hm C hC hb f =ᵐ[volume] fun x => m (x 0)*f x := by
  have he : euclideanPullback (euclideanPullback.symm f) = f := euclideanPullback.apply_symm_apply f
  filter_upwards [euclideanPullback_coe (M (euclideanPullback.symm f)),
    euclideanPullback_coe (euclideanPullback.symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (multiplier_coe m hm C hC hb (euclideanPullback.symm f))]
    with x hM hf hm'
  change (euclideanPullback (M (euclideanPullback.symm f))) x = _
  rw [hM]
  change (M (euclideanPullback.symm f)) (split x) = _
  rw [hm']
  rw [he] at hf
  rw [hf,split_apply]
  rfl

theorem euclideanMultiplier_translation (v : Transverse) (t : ℝ) (f : FrequencyHilbert) :
    euclideanMultiplier m hm C hC hb (KFCausalFourierTranslation.translation (t • transverseVector v) f) =
      KFCausalFourierTranslation.translation (t • transverseVector v) (euclideanMultiplier m hm C hC hb f) := by
  apply Lp.ext
  filter_upwards [euclideanMultiplier_coe m hm C hC hb (KFCausalFourierTranslation.translation (t • transverseVector v) f),
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) f,
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) (euclideanMultiplier m hm C hC hb f),
    (KFCausalFourierTranslation.shift_preserves_volume (t • transverseVector v)).quasiMeasurePreserving.ae
      (euclideanMultiplier_coe m hm C hC hb f)] with x hM ht hm' hs
  rw [hM,ht,hm']
  change (euclideanMultiplier m hm C hC hb f) (x+t • transverseVector v) = _ at hs
  rw [hs]
  change m (x 0)*f (x+t • transverseVector v) = m ((x+t • transverseVector v) 0)*f (x+t • transverseVector v)
  simp [transverseVector]

theorem transverse_graph (h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g : Hilbert)
    (hg : (f,g) ∈ (transverseMomentum h v).graph) :
    (M f,M g) ∈ (transverseMomentum h v).graph := by
  have he := KFCausalDirectionalTranslationMomentum.bounded_commutation h hh (transverseVector v)
    (euclideanMultiplier m hm C hC hb) (euclideanMultiplier_translation m hm C hC hb v) _ _
      ((transverse_graph_iff h v f g).mp hg)
  apply (transverse_graph_iff h v _ _).mpr
  change (euclideanPullback (M (euclideanPullback.symm (euclideanPullback f))),
    euclideanPullback (M (euclideanPullback.symm (euclideanPullback g)))) ∈ _ at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

theorem half_graph (ε : ℝ) (f g : Hilbert) (hg : (f,g) ∈ (clockHalf ε).graph) :
    (M f,M g) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [multiplier_coe m hm C hC hb f,multiplier_coe m hm C hC hb g,
    (clockHalf_graph ε f g).mp hg] with x hf hg' he
  rw [hf,hg',he]
  ring

theorem inverse_half_graph (ε : ℝ) (f g : Hilbert) (hg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (M f,M g) ∈ (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_graph ε _ _).mpr
  filter_upwards [multiplier_coe m hm C hC hb f,multiplier_coe m hm C hC hb g,
    (inverseClockHalf_graph ε f g).mp hg] with x hf hg' he
  rw [hf,hg',he]
  ring

theorem kinetic_graph (ε h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g : Hilbert)
    (hg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (M f,M g) ∈ (clockMomentum ε h v).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hg
  exact (composition_graph _ _ _ _).mpr ⟨M u,inverse_half_graph m hm C hC hb ε f u hu,
    transverse_graph m hm C hC hb h hh v u g hg⟩

#print axioms euclideanMultiplier_coe
#print axioms euclideanMultiplier_translation
#print axioms transverse_graph
#print axioms half_graph
#print axioms inverse_half_graph
#print axioms kinetic_graph
end
end UnifiedTheory.Audit.KFCausalBoundedClockFactorGraphs
