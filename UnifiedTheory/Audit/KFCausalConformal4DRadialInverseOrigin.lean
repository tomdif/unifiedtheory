import UnifiedTheory.Audit.KFCausalConformal4DRadialInverse

/- Actual origin value and derivative of the constructed inverse chart. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialInverseOrigin
noncomputable section
open Set Filter Topology
open scoped ContDiff
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DRadialScale
open KFCausalConformal4DRadialJacobian KFCausalConformal4DRadialInverse

theorem inverse_origin (c : ℝ) (hc : |c|≤1/54) : inverse c hc 0=0 := by
  have h := inverse_left c hc 0 (by norm_num [closedBox])
    (by rw [radialMap_origin]; norm_num [targetBox])
  simpa only [radialMap_origin] using h

private theorem mapDerivative_origin (c : ℝ) :
    mapDerivative c 0=ContinuousLinearMap.id ℝ (ℝ×ℝ) := by
  have hz : (scaleDerivative c 0).smulRight (0:ℝ×ℝ)=0 := by
    apply ContinuousLinearMap.ext
    intro p
    simp
  simpa only [mapDerivative,Prod.fst_zero,Prod.snd_zero,scale_origin,one_smul,add_zero] using
    congrArg (fun L => ContinuousLinearMap.id ℝ (ℝ×ℝ)+L) hz

theorem inverse_origin_fderiv (c : ℝ) (hc : |c|≤1/54) :
    fderiv ℝ (inverse c hc) 0=ContinuousLinearMap.id ℝ (ℝ×ℝ) := by
  have hy : (0:ℝ×ℝ)∈targetBox := by norm_num [targetBox]
  have hi := ((inverse_smoothAt c hc 0 hy).differentiableAt (by simp)).hasFDerivAt
  have hf : HasFDerivAt (radialMap c) (ContinuousLinearMap.id ℝ (ℝ×ℝ))
      (inverse c hc 0) := by
    rw [inverse_origin]
    simpa only [mapDerivative_origin] using radialMap_hasFDerivAt c 0
      (by change 0<normalized c 0 0; rw [normalized_origin]; norm_num)
  have hcomp := hf.comp 0 hi
  have he : (radialMap c ∘ inverse c hc)=ᶠ[𝓝 (0:ℝ×ℝ)] id := by
    filter_upwards [targetBox_open.mem_nhds hy] with y hyt
    exact inverse_right c hc y hyt
  have hid : HasFDerivAt (radialMap c ∘ inverse c hc)
      (ContinuousLinearMap.id ℝ (ℝ×ℝ)) 0 :=
    (hasFDerivAt_id (0:ℝ×ℝ)).congr_of_eventuallyEq he
  have h := hcomp.unique hid
  simpa only [ContinuousLinearMap.id_comp] using h

theorem inverse_origin_hasFDerivAt (c : ℝ) (hc : |c|≤1/54) :
    HasFDerivAt (inverse c hc) (ContinuousLinearMap.id ℝ (ℝ×ℝ)) 0 := by
  have h := ((inverse_smoothAt c hc 0 (by norm_num [targetBox])).differentiableAt
    (by simp)).hasFDerivAt
  rw [inverse_origin_fderiv] at h
  exact h

#print axioms inverse_origin
#print axioms inverse_origin_fderiv
#print axioms inverse_origin_hasFDerivAt
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialInverseOrigin
