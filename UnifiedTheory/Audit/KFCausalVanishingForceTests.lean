/- All continuous tests vanishing at infinity extend by zero to the
arctangent compactification. This identifies the local force limit on C₀. -/
import UnifiedTheory.Audit.KFCausalLocalForceMeasure
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalVanishingForceTests
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction Classical
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
open UnifiedTheory.Audit.KFCausalLocalForceMeasure
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)

theorem embed_interior (p : ℝ) : embed p ∈ interior :=
  ⟨Real.neg_pi_div_two_lt_arctan p, Real.arctan_lt_pi_div_two p⟩

theorem embed_tangent (x : Spectrum) (hx : x ∈ interior) :
    embed (Real.tan (x:ℝ)) = x :=
  Subtype.ext (Real.arctan_tan hx.1 hx.2)

def extensionValue (f : C₀(ℝ, ℂ)) (x : Spectrum) : ℂ :=
  if x ∈ interior then f (Real.tan (x:ℝ)) else 0

theorem extension_continuous (f : C₀(ℝ, ℂ)) : Continuous (extensionValue f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ interior
  · have hi : IsOpen interior := isOpen_Ioo.preimage continuous_subtype_val
    have ht : ContinuousAt (fun z : Spectrum => Real.tan (z:ℝ)) x := by
      simpa only [Real.tan_eq_sin_div_cos] using
        (Real.continuous_sin.continuousAt.comp continuous_subtype_val.continuousAt).div
          (Real.continuous_cos.continuousAt.comp continuous_subtype_val.continuousAt)
          (ne_of_gt (Real.cos_pos_of_mem_Ioo hx))
    apply (f.continuous.continuousAt.comp ht).congr_of_eventuallyEq
    filter_upwards [hi.mem_nhds hx] with z hz
    simp [extensionValue, hz]
  · change Tendsto (extensionValue f) (𝓝 x) (𝓝 (extensionValue f x))
    rw [extensionValue, if_neg hx]
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    obtain ⟨K,hK,hsmall⟩ := mem_cocompact.mp
      ((zero_at_infty f) (Metric.ball_mem_nhds (0:ℂ) hδ))
    have hS : IsClosed (embed '' K) := (hK.image embed_continuous).isClosed
    have hxS : x ∈ (embed '' K)ᶜ := by
      rintro ⟨p,_,rfl⟩
      exact hx (embed_interior p)
    filter_upwards [hS.isOpen_compl.mem_nhds hxS] with z hz
    by_cases hzI : z ∈ interior
    · have hzK : Real.tan (z:ℝ) ∉ K := by
        intro h
        exact hz ⟨Real.tan (z:ℝ),h,embed_tangent z hzI⟩
      simpa [extensionValue,hzI] using hsmall hzK
    · simpa [extensionValue,hzI] using hδ

def extension (f : C₀(ℝ, ℂ)) : Spectrum →ᵇ ℂ :=
  mkOfCompact ⟨extensionValue f,extension_continuous f⟩

theorem extension_boundary (f : C₀(ℝ, ℂ)) (x : Spectrum) (hx : x ∉ interior) :
    extension f x = 0 := by
  change extensionValue f x = 0
  simp [extensionValue,hx]

theorem extension_pullback (f : C₀(ℝ, ℂ)) : pullback (extension f) = f.toBCF := by
  ext p
  change extensionValue f (embed p) = f p
  rw [extensionValue, if_pos (embed_interior p)]
  exact congrArg f (Real.tan_arctan p)

theorem finitePair_test_zero (P N : FiniteMeasure Spectrum) (f : C₀(ℝ, ℂ)) :
    (finitePair P N).evaluate f.toBCF =
      ((∫ x, extension f x ∂(P : Measure Spectrum))-
        (∫ x, extension f x ∂(N : Measure Spectrum)))/2 := by
  rw [← extension_pullback f]
  exact finitePair_test P N (extension f) (extension_boundary f)

theorem zero_test_of_compact_limits (F : ℕ → FluxPair) (P N : FiniteMeasure Spectrum)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (f : C₀(ℝ, ℂ)) :
    Tendsto (fun n => (F n).evaluate f.toBCF) atTop
      (𝓝 ((finitePair P N).evaluate f.toBCF)) := by
  have hp := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hP (extension f)
  have hn := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hN (extension f)
  rw [finitePair_test_zero]
  simpa only [compactify_test,extension_pullback,FluxPair.evaluate] using (hp.sub hn).div_const 2

#print axioms extension_continuous
#print axioms extension_boundary
#print axioms extension_pullback
#print axioms finitePair_test_zero
#print axioms zero_test_of_compact_limits
end
end UnifiedTheory.Audit.KFCausalVanishingForceTests
