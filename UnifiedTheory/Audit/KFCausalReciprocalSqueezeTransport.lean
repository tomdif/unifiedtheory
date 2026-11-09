/- The reciprocal squeeze is an actual unitary group on the full physical L2
space. Its representative, normalization, inverse and clock-translation
commutation are established without operator-domain assumptions. -/
import UnifiedTheory.Audit.KFCausalReciprocalSqueezePullback
import UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
import UnifiedTheory.Audit.KFCausalCoupledCoordinateNullSets
import UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
import UnifiedTheory.Audit.KFCausalClockFourierDiagonalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalReciprocalSqueezeTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeFlow
open UnifiedTheory.Audit.KFCausalReciprocalSqueezePullback
open UnifiedTheory.Audit.KFCausalWeightedConfigurationTests
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension
open UnifiedTheory.Audit.KFCausalConfigurationTranslation
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization (clock_translation_coe)

def configurationEquiv (a : ℝ) : Configuration ≃L[ℝ] Configuration :=
  ((LinearEquiv.refl ℝ ℝ).prodCongr (squeezeEquiv (-a))).toContinuousLinearEquiv

def squeezeFlow (a : ℝ) : Configuration ≃ₜ Configuration :=
  (configurationEquiv a).toHomeomorph

theorem squeezeFlow_apply (a : ℝ) (x : Configuration) :
    squeezeFlow a x = (x.1,squeeze (-a) x.2) := rfl

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem squeezeFlow_quasiMeasurePreserving (a : ℝ) :
    Measure.QuasiMeasurePreserving (squeezeFlow a) volume volume :=
  KFCausalCoupledCoordinateNullSets.homeomorph_quasiMeasurePreserving volume _
    (configurationEquiv a).symm.differentiable

theorem squeezeFlow_compose (a b : ℝ) (x : Configuration) :
    squeezeFlow b (squeezeFlow a x) = squeezeFlow (a+b) x := by
  simp only [squeezeFlow_apply,squeeze_compose,neg_add]

def testPullback (a : ℝ) : Test ≃ₗ[ℂ] Test :=
  weightedEquiv (squeezeFlow a) (fun _ => (Real.exp (-a/2):ℂ)) continuous_const
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem testPullback_apply (a : ℝ) (f : Test) (x : Configuration) :
    testPullback a f x = (Real.exp (-a/2):ℂ)*f (squeezeFlow a x) := rfl

theorem testPullback_square_integral (a : ℝ) (f : Test) :
    (∫ x : Configuration, ‖testPullback a f x‖^2) = ∫ x : Configuration, ‖f x‖^2 := by
  rw [Measure.volume_eq_prod ℝ Transverse]
  rw [integral_prod _ (test_square_integrable (testPullback a f)),
    integral_prod _ (test_square_integrable f)]
  apply integral_congr_ae
  filter_upwards [] with s
  exact pullback_square_integral a (fun y => f (s,y))

theorem testPullback_physical_norm (a : ℝ) (f : Test) :
    ‖embedding (testPullback a f)‖ = ‖embedding f‖ := by
  have he : ‖embedding (testPullback a f)‖^2 = ‖embedding f‖^2 := by
    rw [embedding_norm_square,embedding_norm_square,testPullback_square_integral]
  nlinarith [norm_nonneg (embedding (testPullback a f)),norm_nonneg (embedding f)]

def transport (a : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension embedding embedding_dense (testPullback a) (testPullback_physical_norm a)

theorem transport_embedding (a : ℝ) (f : Test) :
    transport a (embedding f) = embedding (testPullback a f) :=
  extension_embedding _ _ _ _ f

theorem transport_coe (a : ℝ) (f : Hilbert) :
    transport a f =ᵐ[volume] fun x => (Real.exp (-a/2):ℂ)*f (squeezeFlow a x) := by
  apply KFCausalWeightedLpRepresentative.dense_weighted_representative
    embedding embedding_dense (transport a) (transport a).continuous (squeezeFlow a)
    (squeezeFlow_quasiMeasurePreserving a) (fun _ => (Real.exp (-a/2):ℂ)) _ f
  intro d
  rw [transport_embedding]
  filter_upwards [embedding_coe (testPullback a d),
    (squeezeFlow_quasiMeasurePreserving a).ae (embedding_coe d)] with x hx hd
  rw [hx,testPullback_apply,hd]

theorem transport_initial (f : Hilbert) : transport 0 f = f := by
  apply Lp.ext
  filter_upwards [transport_coe 0 f] with x hx
  simpa only [neg_zero,zero_div,Real.exp_zero,Complex.ofReal_one,one_mul,
    squeezeFlow_apply,squeeze_initial,Prod.mk.eta] using hx

theorem transport_compose (a b : ℝ) (f : Hilbert) :
    transport b (transport a f) = transport (a+b) f := by
  apply Lp.ext
  filter_upwards [transport_coe b (transport a f),transport_coe (a+b) f,
    (squeezeFlow_quasiMeasurePreserving b).ae (transport_coe a f)] with x hb hsum ha
  rw [hb,hsum,ha,squeezeFlow_compose,add_comm b a]
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  congr 2
  ring

theorem transport_reverse (a : ℝ) (f : Hilbert) : transport (-a) (transport a f) = f := by
  rw [transport_compose,add_neg_cancel,transport_initial]

theorem transport_unitary (a : ℝ) :
    (transport a : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  (Unitary.linearIsometryEquiv.symm (transport a)).property

theorem transport_translation (a u : ℝ) (f : Hilbert) :
    transport a (translation u f) = translation u (transport a f) := by
  apply Lp.ext
  filter_upwards [transport_coe a (translation u f),clock_translation_coe u (transport a f),
    (squeezeFlow_quasiMeasurePreserving a).ae (clock_translation_coe u f),
    (clockShift_measurePreserving u).quasiMeasurePreserving.ae (transport_coe a f)] with x hs ht hf hg
  rw [hs,ht,hf,hg]
  simp only [clockShift_apply,squeezeFlow_apply]

#print axioms squeezeFlow_apply
#print axioms squeezeFlow_quasiMeasurePreserving
#print axioms squeezeFlow_compose
#print axioms testPullback_apply
#print axioms testPullback_square_integral
#print axioms testPullback_physical_norm
#print axioms transport_embedding
#print axioms transport_coe
#print axioms transport_initial
#print axioms transport_compose
#print axioms transport_reverse
#print axioms transport_unitary
#print axioms transport_translation

end
end UnifiedTheory.Audit.KFCausalReciprocalSqueezeTransport
