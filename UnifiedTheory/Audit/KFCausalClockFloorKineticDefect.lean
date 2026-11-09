/- The real clock defect commutes on the full natural graphs of clock
energy and all transverse kinetic factors. Transverse momentum domain
preservation follows from actual translations and their strong generator. -/
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
import UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum multiplier spectralMomentum_graph_derivative)

variable (ε : ℝ) (hε : 0 < ε)

def euclideanDefect : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  (euclideanPullback : Hilbert →L[ℂ] FrequencyHilbert).comp
    ((defectOperator ε hε).comp (euclideanPullback.symm : FrequencyHilbert →L[ℂ] Hilbert))

theorem euclideanDefect_coe (f : FrequencyHilbert) :
    euclideanDefect ε hε f =ᵐ[volume] fun x => (defect ε (x 0):ℂ)*f x := by
  have he : euclideanPullback (euclideanPullback.symm f) = f := euclideanPullback.apply_symm_apply f
  filter_upwards [euclideanPullback_coe (defectOperator ε hε (euclideanPullback.symm f)),
    euclideanPullback_coe (euclideanPullback.symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (defectOperator_coe ε hε (euclideanPullback.symm f))] with x hb hf hd
  change (euclideanPullback (defectOperator ε hε (euclideanPullback.symm f))) x = _
  rw [hb]
  change (defectOperator ε hε (euclideanPullback.symm f)) (split x) = _
  rw [hd]
  rw [he] at hf
  rw [hf,split_apply]
  rfl

theorem euclideanDefect_translation (v : Transverse) (t : ℝ) (f : FrequencyHilbert) :
    euclideanDefect ε hε (KFCausalFourierTranslation.translation (t • transverseVector v) f) =
      KFCausalFourierTranslation.translation (t • transverseVector v) (euclideanDefect ε hε f) := by
  apply Lp.ext
  filter_upwards [euclideanDefect_coe ε hε (KFCausalFourierTranslation.translation (t • transverseVector v) f),
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) f,
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) (euclideanDefect ε hε f),
    (KFCausalFourierTranslation.shift_preserves_volume (t • transverseVector v)).quasiMeasurePreserving.ae
      (euclideanDefect_coe ε hε f)] with x hb ht hd hs
  rw [hb,ht,hd]
  change (euclideanDefect ε hε f) (x+t • transverseVector v) = _ at hs
  rw [hs]
  change (defect ε (x 0):ℂ)*f (x+t • transverseVector v) =
    (defect ε ((x+t • transverseVector v) 0):ℂ)*f (x+t • transverseVector v)
  simp [transverseVector]

theorem transverse_graph_iff (hbar : ℝ) (v : Transverse) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum hbar v).graph ↔
      (euclideanPullback f,euclideanPullback g) ∈ (spectralMomentum hbar (transverseVector v)).graph := by
  rw [transverseMomentum_graph,spectralMomentum,realPullback_graph]
  rfl

theorem transverse_graph_defect (hbar : ℝ) (v : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum hbar v).graph) :
    (defectOperator ε hε f,defectOperator ε hε g) ∈ (transverseMomentum hbar v).graph := by
  by_cases hn : hbar = 0
  · subst hbar
    have hg : g = 0 := by
      apply fourierCoordinates.injective
      rw [map_zero]
      apply Lp.ext
      filter_upwards [(transverseMomentum_graph 0 v f g).mp hfg,
        Lp.coeFn_zero ℂ 2 (volume : Measure Space)] with k hk hz
      simpa only [transverseSymbol,mul_zero,zero_mul,Complex.ofReal_zero,hz] using hk
    rw [hg,map_zero]
    apply (transverseMomentum_graph 0 v _ _).mpr
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Space)] with k hk
    simp only [hk,Pi.zero_apply,transverseSymbol,mul_zero,zero_mul,Complex.ofReal_zero]
  · have h := KFCausalDirectionalTranslationMomentum.bounded_commutation hbar hn (transverseVector v)
      (euclideanDefect ε hε) (euclideanDefect_translation ε hε v) _ _ ((transverse_graph_iff hbar v f g).mp hfg)
    apply (transverse_graph_iff hbar v _ _).mpr
    change (euclideanPullback (defectOperator ε hε (euclideanPullback.symm (euclideanPullback f))),
      euclideanPullback (defectOperator ε hε (euclideanPullback.symm (euclideanPullback g)))) ∈ _ at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h

theorem clockHalf_graph_defect (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (defectOperator ε hε f,defectOperator ε hε g) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [defectOperator_coe ε hε f,defectOperator_coe ε hε g,(clockHalf_graph ε f g).mp hfg] with x hf hg hm
  rw [hg,hf,hm]
  ring

theorem clockMomentum_graph_defect (hbar : ℝ) (v : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε hbar v).graph) :
    (defectOperator ε hε f,defectOperator ε hε g) ∈ (clockMomentum ε hbar v).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hfg
  apply (composition_graph _ _ _ _).mpr
  refine ⟨defectOperator ε hε u,?_,transverse_graph_defect ε hε hbar v u g hg⟩
  apply (inverseL_graph ε hε _ _).mpr
  rw [inverseL_defect,← (inverseL_graph ε hε f u).mp hu]

#print axioms euclideanDefect_coe
#print axioms euclideanDefect_translation
#print axioms transverse_graph_iff
#print axioms transverse_graph_defect
#print axioms clockHalf_graph_defect
#print axioms clockMomentum_graph_defect

end
end UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
