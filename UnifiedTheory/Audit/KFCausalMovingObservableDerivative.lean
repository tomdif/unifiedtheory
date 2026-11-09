/- A time-dependent bounded observable can be differentiated along a merely
continuous physical trajectory when the frozen-observable derivative is
known. The additional term is derived from the operator-norm derivative. -/
import UnifiedTheory.Audit.KFCausalComplexFormObservableDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalMovingObservableDerivative
noncomputable section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem increment (D E : H →L[ℂ] H) (x y : H) :
    inner ℂ y (E y)-inner ℂ x (D x) =
      (inner ℂ y (D y)-inner ℂ x (D x))+inner ℂ y ((E-D) y) := by
  simp only [ContinuousLinearMap.sub_apply,inner_sub_right]
  ring

theorem expectation_derivative (u : ℝ → H) (D : ℝ → H →L[ℂ] H)
    (D' : H →L[ℂ] H) (x : ℝ) (v : ℂ) (hu : ContinuousAt u x)
    (hD : HasDerivAt D D' x)
    (hf : HasDerivAt (fun t => inner ℂ (u t) (D x (u t))) v x) :
    HasDerivAt (fun t => inner ℂ (u t) (D t (u t)))
      (v+inner ℂ (u x) (D' (u x))) x := by
  have ht : Tendsto (fun h : ℝ => x+h) (𝓝[≠] 0) (𝓝 x) := by
    have hi : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [add_zero] using hi.const_add x
  have hU := hu.tendsto.comp ht
  have happly : Continuous (fun p : (H →L[ℂ] H) × H => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hchange := hU.inner (𝕜 := ℂ)
    ((happly.tendsto (D',u x)).comp (hD.tendsto_slope_zero.prodMk_nhds hU))
  have hs := hf.tendsto_slope_zero.add hchange
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert hs using 1
  funext h
  rw [increment,smul_add]
  congr 1
  simp only [Function.comp_apply,ContinuousLinearMap.smul_apply,inner_smul_right_eq_smul]

#print axioms increment
#print axioms expectation_derivative
end
end UnifiedTheory.Audit.KFCausalMovingObservableDerivative
