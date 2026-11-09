/- Time differentiation of a resolvent with its bounded perturbation
included. Only invertibility at the differentiation point is required. -/
import UnifiedTheory.Audit.KFCausalPartialResolventPerturbation
import UnifiedTheory.Audit.KFCausalInverseCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPerturbedResolventCurve
noncomputable section
open UnifiedTheory.Audit.KFCausalPartialResolventPerturbation (resolvent)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def derivative (R C D E : V →L[ℂ] V) : V →L[ℂ] V :=
  D*Ring.inverse (1-C*R)+R*(-(Ring.inverse (1-C*R)*(-(E*R+C*D))*Ring.inverse (1-C*R)))

theorem resolvent_derivative (R C : ℝ → V →L[ℂ] V) (D E : V →L[ℂ] V) (t : ℝ)
    (hR : HasDerivAt R D t) (hC : HasDerivAt C E t) (hu : IsUnit (1-C t*R t)) :
    HasDerivAt (fun r => resolvent (R r) (C r)) (derivative (R t) (C t) D E) t := by
  exact hR.mul (KFCausalInverseCurve.inverseCurve_hasDerivAt (fun r => 1-C r*R r)
    (-(E*R t+C t*D)) t ((hC.mul hR).const_sub 1) hu)

theorem derivative_continuousOn (R C D E : ℝ → V →L[ℂ] V) (s : Set ℝ)
    (hR : Continuous R) (hC : Continuous C) (hD : Continuous D) (hE : Continuous E)
    (hu : ∀ t ∈ s, IsUnit (1-C t*R t)) :
    ContinuousOn (fun t => derivative (R t) (C t) (D t) (E t)) s := by
  have hi : ContinuousOn (fun t => Ring.inverse (1-C t*R t)) s := by
    intro t ht
    have hp : ContinuousAt (fun r => 1-C r*R r) t := (continuous_const.sub (hC.mul hR)).continuousAt
    have hh : ContinuousAt (Ring.inverse : (V →L[ℂ] V) → (V →L[ℂ] V)) (1-C t*R t) :=
      (differentiableAt_inverse (𝕜 := ℝ) (hu t ht)).continuousAt
    exact (ContinuousAt.comp (f := fun r : ℝ => 1-C r*R r) hh hp).continuousWithinAt
  exact (hD.continuousOn.mul hi).add
    (hR.continuousOn.mul (((hi.mul ((hE.mul hR).add (hC.mul hD)).neg.continuousOn).mul hi).neg))

#print axioms resolvent_derivative
#print axioms derivative_continuousOn
end
end UnifiedTheory.Audit.KFCausalPerturbedResolventCurve
