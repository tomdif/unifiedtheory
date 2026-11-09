/- Time differentiability of the constructed complex mass resolvent
and its bounded generator approximation. -/
import UnifiedTheory.Audit.KFCausalMassResolventStability
import UnifiedTheory.Audit.KFCausalInverseCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalComplexMassCurve
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexMassPencil
open UnifiedTheory.Audit.KFCausalComplexMassResolvent
open UnifiedTheory.Audit.KFCausalMassResolventStability
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def derivative (M : V →L[ℂ] V) (Q D : ℝ → V →L[ℂ] V) (h b t : ℝ) : V →L[ℂ] V :=
  -(Ring.inverse (pencil M (Q t) h b)*(-(phase h • D t))*
    Ring.inverse (pencil M (Q t) h b))*M

omit [CompleteSpace V] in
theorem pencil_derivative (M : V →L[ℂ] V) (Q D : ℝ → V →L[ℂ] V) (h b t : ℝ)
    (hd : HasDerivAt Q (D t) t) :
    HasDerivAt (fun r => pencil M (Q r) h b) (-(phase h • D t)) t :=
  (hd.const_smul (phase h)).const_sub (b • M)

theorem resolvent_derivative (M : V →L[ℂ] V) (Q D : ℝ → V →L[ℂ] V) (h b t : ℝ)
    (hd : HasDerivAt Q (D t) t) (hu : IsUnit (pencil M (Q t) h b)) :
    HasDerivAt (fun r => resolvent M (Q r) h b) (derivative M Q D h b t) t :=
  (KFCausalInverseCurve.inverseCurve_hasDerivAt (fun r => pencil M (Q r) h b)
    (-(phase h • D t)) t (pencil_derivative M Q D h b t hd) hu).mul_const M

theorem derivative_continuous (M : V →L[ℂ] V) (Q D : ℝ → V →L[ℂ] V) (h b : ℝ)
    (hq : Continuous Q) (hd : Continuous D) (hu : ∀ t, IsUnit (pencil M (Q t) h b)) :
    Continuous (derivative M Q D h b) := by
  have hp : Continuous (fun t => pencil M (Q t) h b) := continuous_const.sub (hq.const_smul (phase h))
  have hi := KFCausalInverseCurve.inverseCurve_continuous _ hp hu
  exact (((hi.mul (hd.const_smul (phase h)).neg).mul hi).neg).mul continuous_const

theorem approximation_derivative (M : V →L[ℂ] V) (Q D : ℝ → V →L[ℂ] V) (h b t : ℝ)
    (hd : HasDerivAt Q (D t) t) (hu : IsUnit (pencil M (Q t) h b)) :
    HasDerivAt (fun r => approximation M (Q r) h b) (b • (b • derivative M Q D h b t)) t :=
  (((resolvent_derivative M Q D h b t hd hu).const_smul b).sub_const 1).const_smul b

#print axioms pencil_derivative
#print axioms resolvent_derivative
#print axioms derivative_continuous
#print axioms approximation_derivative
end
end UnifiedTheory.Audit.KFCausalComplexMassCurve
