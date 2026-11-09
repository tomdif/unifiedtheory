/- Strong continuity of the actual paired squeeze. Compact test pairings
are continuous by integration over the fixed support of the second test.
The unitary norm identity upgrades this to strong continuity; physical
density extends it to every L2 state. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeTransport
import UnifiedTheory.Audit.KFCausalNormPairingStrongLimit
import UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPairedSqueezeFlow
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport

theorem squeeze_joint_continuous : Continuous (fun p : ℝ × Transverse => squeeze p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [squeeze,Matrix.cons_val_zero',Matrix.cons_val_succ',
    KFCausalPairedSqueezeFlow.diagonal,offDiagonal]
  all_goals fun_prop

theorem flow_joint_continuous : Continuous (fun p : ℝ × Configuration => squeezeFlow p.1 p.2) := by
  simp only [squeezeFlow_apply]
  exact (continuous_fst.comp continuous_snd).prodMk
    (squeeze_joint_continuous.comp
      (continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd)))

theorem test_pairing_continuous (f g : Test) :
    Continuous (fun a : ℝ => inner ℂ (transport a (embedding f)) (embedding g)) := by
  let F : ℝ → Configuration → ℂ := fun a x =>
    inner ℂ ((Real.exp (-a/2):ℂ)*f (squeezeFlow a x)) (g x)
  have hF : Continuous F.uncurry := by
    change Continuous (fun p : ℝ × Configuration =>
      inner ℂ ((Real.exp (-p.1/2):ℂ)*f (squeezeFlow p.1 p.2)) (g p.2))
    exact (((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_fst.neg.div_const 2))).mul
        (f.continuous.comp flow_joint_continuous)).inner
      (g.continuous.comp continuous_snd))
  have hI : Continuous (fun a => ∫ x : Configuration, F a x) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support g.hasCompactSupport hF.continuousOn
    intro a x _ hx
    simp only [F,image_eq_zero_of_notMem_tsupport hx,inner_zero_right]
  have he (a : ℝ) : inner ℂ (transport a (embedding f)) (embedding g) = ∫ x, F a x := by
    rw [transport_embedding,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [embedding_coe (testPullback a f),embedding_coe g] with x hf hg
    rw [hf,hg,testPullback_apply]
  simpa only [he] using hI

theorem test_strong_continuous (f : Test) : Continuous (fun a : ℝ => transport a (embedding f)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply KFCausalNormPairingStrongLimit.strong_of_norm_and_pairing
  · simpa only [LinearIsometryEquiv.norm_map] using
      (tendsto_const_nhds (x := ‖embedding f‖) :
        Tendsto (fun _ : ℝ => ‖embedding f‖) (𝓝 a) (𝓝 ‖embedding f‖))
  · simpa only [← transport_embedding] using
      (test_pairing_continuous f (testPullback a f)).tendsto a

theorem transport_strong_continuous (f : Hilbert) : Continuous (fun a : ℝ => transport a f) :=
  KFCausalDenseUnitaryExtension.continuous_of_dense_isometries embedding embedding_dense
    (fun a f => transport a f) (fun a => (transport a).isometry) test_strong_continuous f

theorem transport_joint_continuous : Continuous (fun p : ℝ × Hilbert => transport p.1 p.2) :=
  KFCausalStrongUnitaryContinuity.joint_evaluation_continuous transport transport_strong_continuous

#print axioms squeeze_joint_continuous
#print axioms flow_joint_continuous
#print axioms test_pairing_continuous
#print axioms test_strong_continuous
#print axioms transport_strong_continuous
#print axioms transport_joint_continuous

end
end UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity
