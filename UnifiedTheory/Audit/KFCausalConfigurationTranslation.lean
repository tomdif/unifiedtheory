/- Clock translation on the full configuration Hilbert space, with actual
unitary maps, group composition and strong continuity. This parameter is
longitudinal transport, not the physical Hamiltonian evolution time. -/
import UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalConfigurationTranslation
noncomputable section
open MeasureTheory Filter
open scoped CompactlySupported ENNReal
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

def clockShift (t : ℝ) : Configuration ≃ₜ Configuration := Homeomorph.addRight (t,0)

theorem clockShift_apply (t : ℝ) (x : Configuration) : clockShift t x = (x.1+t,x.2) := by
  change (x.1+t,x.2+0) = _
  rw [add_zero]

theorem clockShift_compose (t u : ℝ) (x : Configuration) :
    clockShift u (clockShift t x) = clockShift (t+u) x := by
  simp only [clockShift_apply,add_assoc]

theorem clockShift_measurePreserving (t : ℝ) :
    MeasurePreserving (clockShift t) (volume : Measure Configuration) volume := by
  have hh := (measurePreserving_add_right (volume : Measure ℝ) t).prod
    (MeasurePreserving.id (volume : Measure KFCausalTransverseDilationFlow.Transverse))
  convert hh using 1
  funext x
  simp [clockShift_apply,Prod.map]

theorem clockShift_continuousFamily : Continuous (fun t : ℝ => (clockShift t : C(Configuration, Configuration))) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : ℝ×Configuration => z.2+(z.1,0))
  fun_prop

def translationTests (t : ℝ) : Test ≃ₗ[ℂ] Test :=
  weightedEquiv (clockShift t) (fun _ => 1) continuous_const (fun _ => one_ne_zero)

theorem translationTests_apply (t : ℝ) (f : Test) (x : Configuration) :
    translationTests t f x = f (clockShift t x) := by
  simp only [translationTests,weightedEquiv_apply,one_mul]

theorem translationTests_initial (f : Test) : translationTests 0 f = f := by
  apply DFunLike.ext
  intro x
  simp only [translationTests_apply,clockShift_apply,add_zero,Prod.mk.eta]

theorem translationTests_compose (t u : ℝ) (f : Test) :
    translationTests u (translationTests t f) = translationTests (t+u) f := by
  apply DFunLike.ext
  intro x
  simp only [translationTests_apply,clockShift_compose,add_comm u t]

theorem translationTests_norm (t : ℝ) (f : Test) :
    ‖embedding (translationTests t f)‖ = ‖embedding f‖ := by
  have he : ‖embedding (translationTests t f)‖^2 = ‖embedding f‖^2 := by
    rw [embedding_norm_square,embedding_norm_square]
    simp_rw [translationTests_apply]
    exact (clockShift_measurePreserving t).integral_comp
      (clockShift t).toMeasurableEquiv.measurableEmbedding (fun x => ‖f x‖^2)
  nlinarith [norm_nonneg (embedding (translationTests t f)),norm_nonneg (embedding f)]

def translation (t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension embedding embedding_dense (translationTests t) (translationTests_norm t)

theorem translation_embedding (t : ℝ) (f : Test) :
    translation t (embedding f) = embedding (translationTests t f) :=
  extension_embedding _ _ _ _ f

theorem translation_initial (f : Hilbert) : translation 0 f = f := by
  have he : (fun u : Hilbert => translation 0 u) = (fun u : Hilbert => u) := by
    apply embedding_dense.equalizer (translation 0).continuous continuous_id
    funext g
    simp only [Function.comp_apply]
    rw [translation_embedding,translationTests_initial,id_eq]
  exact congrFun he f

theorem translation_compose (t u : ℝ) (f : Hilbert) :
    translation u (translation t f) = translation (t+u) f := by
  have he : (fun v : Hilbert => translation u (translation t v)) =
      (fun v : Hilbert => translation (t+u) v) := by
    apply embedding_dense.equalizer ((translation u).continuous.comp (translation t).continuous)
      (translation (t+u)).continuous
    funext g
    simp only [Function.comp_apply]
    rw [translation_embedding,translation_embedding,translation_embedding,translationTests_compose]
  exact congrFun he f

theorem translation_reverse (t : ℝ) (f : Hilbert) : translation (-t) (translation t f) = f := by
  rw [translation_compose,add_neg_cancel,translation_initial]

theorem translation_eq_compMeasurePreserving (t : ℝ) (f : Hilbert) :
    translation t f = Lp.compMeasurePreserving (clockShift t) (clockShift_measurePreserving t) f := by
  have he : (fun v : Hilbert => translation t v) =
      (fun v : Hilbert => Lp.compMeasurePreserving (clockShift t) (clockShift_measurePreserving t) v) := by
    apply embedding_dense.equalizer (translation t).continuous
      (Lp.compMeasurePreservingₗᵢ ℂ (clockShift t) (clockShift_measurePreserving t)).continuous
    funext g
    simp only [Function.comp_apply]
    rw [translation_embedding]
    apply Lp.ext
    filter_upwards [embedding_coe (translationTests t g),
      Lp.coeFn_compMeasurePreserving (embedding g) (clockShift_measurePreserving t),
      (clockShift_measurePreserving t).quasiMeasurePreserving.ae (embedding_coe g)]
      with x hx hc hg
    change (embedding (translationTests t g) : Hilbert) x =
      (Lp.compMeasurePreserving (clockShift t) (clockShift_measurePreserving t) (embedding g)) x
    rw [hx,hc]
    simpa only [translationTests_apply,Function.comp_apply] using hg.symm
  exact congrFun he f

theorem translation_strong_continuous (f : Hilbert) : Continuous (fun t : ℝ => translation t f) := by
  have hh := (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    clockShift_continuousFamily clockShift_measurePreserving (by norm_num : (2:ℝ≥0∞) ≠ ∞)
  simpa only [translation_eq_compMeasurePreserving] using hh

#print axioms clockShift_measurePreserving
#print axioms translationTests_norm
#print axioms translation
#print axioms translation_embedding
#print axioms translation_initial
#print axioms translation_compose
#print axioms translation_reverse
#print axioms translation_eq_compMeasurePreserving
#print axioms translation_strong_continuous

end
end UnifiedTheory.Audit.KFCausalConfigurationTranslation
