/- Residual estimates for unitary evolution on resolvent-smoothed curves.
Only strong orbit continuity and the proved derivative on resolvent
ranges are required; the generator need not be bounded. -/
import UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
import UnifiedTheory.Audit.KFCausalStrongIsometryDerivative
import UnifiedTheory.Audit.KFCausalStrongResidualCalculus

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalResolventUnitaryResidual
noncomputable section
open Set
open KFCausalUnitaryOrbitAverage (StrongUnitaryGroup)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem moving_derivative (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => U t x))
    (f : ℝ → H) (p q : H) (s : ℝ) (hf : HasDerivAt f q s)
    (hu : HasDerivAt (fun t => U t (f s)) p s) :
    HasDerivAt (fun t => U t (f t)) (U s q+p) s := by
  have hd := KFCausalStrongIsometryDerivative.derivative_at_zero_vector U hc
    (fun t => f t-f s) q s (hf.sub_const (f s)) (sub_self _)
  convert hd.add hu using 1
  funext t
  change U t (f t)=U t (f t-f s)+U t (f s)
  rw [map_sub,sub_add_cancel]

theorem interaction_derivative (U : StrongUnitaryGroup H) (R : H →L[ℂ] H) (c : ℂ)
    (hr : ∀ f t, HasDerivAt (fun u => U.action u (R f)) (c • U.action t (f-R f)) t)
    (f : ℝ → H) (q : H) (s : ℝ) (hf : HasDerivAt f q s) :
    HasDerivAt (fun t => U.action (-t) (R (f t)))
      (U.action (-s) (R q-c • (f s-R (f s)))) s := by
  have hp : HasDerivAt (fun t : ℝ => U.action (-t) (R (f s)))
      (-(c • U.action (-s) (f s-R (f s)))) s := by
    simpa only [neg_smul,one_smul] using (hr (f s) (-s)).scomp s (hasDerivAt_id s).neg
  have hq := (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hf
  have hd := moving_derivative (fun t => U.action (-t))
    (fun x => (U.continuous_orbit x).comp continuous_neg) (fun t => R (f t)) _ _ s hq hp
  exact hd.congr_deriv (by
    change U.action (-s) (R q)+ -(c • U.action (-s) (f s-R (f s)))=_
    simp only [map_sub,map_smul]
    simp only [sub_eq_add_neg])

theorem error_bound (U : StrongUnitaryGroup H) (R : H →L[ℂ] H) (c : ℂ)
    (hr : ∀ f t, HasDerivAt (fun u => U.action u (R f)) (c • U.action t (f-R f)) t)
    (f q : ℝ → H) (hf : ∀ t, HasDerivAt f (q t) t) (t C : ℝ)
    (hb : ∀ s ∈ uIcc 0 t, ‖R (q s)-c • (f s-R (f s))‖ ≤ C) :
    ‖U.action t (R (f 0))-R (f t)‖ ≤ C*|t| := by
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ uIcc 0 t) => (interaction_derivative U R c hr f (q s) s (hf s)).hasDerivWithinAt)
    (fun s (hs : s ∈ uIcc 0 t) => by rw [(U.action (-s)).norm_map]; exact hb s hs)
    (convex_uIcc 0 t) (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 t) (right_mem_uIcc : t ∈ uIcc 0 t)
  have hreverse (y : H) : U.action t (U.action (-t) y)=y := by
    rw [U.compose,neg_add_cancel,U.initial]
  have he : U.action t (R (f 0))-R (f t)=U.action t (R (f 0)-U.action (-t) (R (f t))) := by
    rw [map_sub,hreverse]
  rw [he,(U.action t).norm_map,norm_sub_rev]
  simpa only [neg_zero,U.initial,sub_zero,Real.norm_eq_abs] using hd

#print axioms moving_derivative
#print axioms interaction_derivative
#print axioms error_bound
end
end UnifiedTheory.Audit.KFCausalResolventUnitaryResidual
