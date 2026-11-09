/- Actual positive-quadrant integrability, truncation and Euler identity.
Upper support is required only at the high edges; no negative-coordinate
vanishing is imposed. The exact identity is at every finite parameter. -/
import UnifiedTheory.Audit.KFCausalMinkowski4DEulerIBP

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalMinkowski4DEulerQuadrant
noncomputable section
open MeasureTheory Set
open KFCausalMinkowski4DEulerIBP
open KFCausalMinkowski4DMoments (f4D)

def UpperSupport (A B : ℝ) (F : ℝ × ℝ → ℝ) : Prop :=
  ∀ p, A ≤ p.1 ∨ B ≤ p.2 → F p=0

def quadrantIntegral (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ), F p

theorem upper_support_integrable (A B : ℝ) (F : ℝ × ℝ → ℝ)
    (hc : Continuous F) (hs : UpperSupport A B F) :
    IntegrableOn F (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
  apply IntegrableOn.of_inter_support (measurableSet_Ioi.prod measurableSet_Ioi)
  apply (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  have hu : p.1 < A := by
    by_contra hn
    exact hp.2 (hs p (Or.inl (not_lt.mp hn)))
  have hv : p.2 < B := by
    by_contra hn
    exact hp.2 (hs p (Or.inr (not_lt.mp hn)))
  exact ⟨⟨hp.1.1.le,hu.le⟩,⟨hp.1.2.le,hv.le⟩⟩

theorem quadrant_eq_box (A B : ℝ) (F : ℝ × ℝ → ℝ)
    (hs : UpperSupport A B F) :
    quadrantIntegral F=boxIntegral A B F := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioi)
    (prod_mono Ioc_subset_Ioi_self Ioc_subset_Ioi_self)
  intro p hp
  by_cases hu : p.1 ≤ A
  · by_cases hv : p.2 ≤ B
    · exact False.elim (hp.2 ⟨⟨hp.1.1,hu⟩,⟨hp.1.2,hv⟩⟩)
    · exact hs p (Or.inr (not_le.mp hv).le)
  · exact hs p (Or.inl (not_le.mp hu).le)

theorem quadrant_eq_iterated (A B : ℝ) (F : ℝ × ℝ → ℝ)
    (hc : Continuous F) (hs : UpperSupport A B F) :
    quadrantIntegral F=∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), F (u,v) := by
  have hi := upper_support_integrable A B F hc hs
  change Integrable F ((volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) at hi
  rw [← Measure.prod_restrict] at hi
  change (∫ p, F p ∂(volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)))=_
  rw [← Measure.prod_restrict]
  exact integral_prod_symm F hi

theorem kernel_quadrant_integrable (a A B : ℝ) (F : ℝ × ℝ → ℝ)
    (hc : Continuous F) (hs : UpperSupport A B F) :
    IntegrableOn (fun p => kernel a p.1 p.2*F p) (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
  apply upper_support_integrable A B
  · dsimp [kernel,f4D]; fun_prop
  · intro p hp; dsimp only; rw [hs p hp,mul_zero]

theorem variation_quadrant_integrable (a A B : ℝ) (F : ℝ × ℝ → ℝ)
    (hc : Continuous F) (hs : UpperSupport A B F) :
    IntegrableOn (fun p => variation a p.1 p.2*F p) (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) := by
  apply upper_support_integrable A B
  · dsimp [variation,fd]; fun_prop
  · intro p hp; dsimp only; rw [hs p hp,mul_zero]

theorem quadrant_euler_identity (a A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (F Fu Fv : ℝ × ℝ → ℝ) (hF : Continuous F)
    (hFu : Continuous Fu) (hFv : Continuous Fv)
    (hdu : ∀ v u, HasDerivAt (fun x => F (x,v)) (Fu (u,v)) u)
    (hdv : ∀ u v, HasDerivAt (fun x => F (u,x)) (Fv (u,v)) v)
    (hsF : UpperSupport A B F) (hsFu : UpperSupport A B Fu) (hsFv : UpperSupport A B Fv) :
    quadrantIntegral (fun p => variation a p.1 p.2*F p) =
      -(1/4)*quadrantIntegral (fun p => kernel a p.1 p.2*
        (4*F p+p.1*Fu p+p.2*Fv p)) := by
  have hs1 : UpperSupport A B (fun p => variation a p.1 p.2*F p) := by
    intro p hp; dsimp only; rw [hsF p hp,mul_zero]
  have hs2 : UpperSupport A B (fun p => kernel a p.1 p.2*(4*F p+p.1*Fu p+p.2*Fv p)) := by
    intro p hp
    dsimp only
    rw [hsF p hp,hsFu p hp,hsFv p hp]
    ring
  rw [quadrant_eq_box A B _ hs1,quadrant_eq_box A B _ hs2]
  exact compact_euler_identity a A B hA hB F Fu Fv hF hFu hFv hdu hdv
    (fun v => hsF (A,v) (Or.inl le_rfl)) (fun u => hsF (u,B) (Or.inr le_rfl))

#print axioms upper_support_integrable
#print axioms quadrant_eq_box
#print axioms quadrant_eq_iterated
#print axioms kernel_quadrant_integrable
#print axioms variation_quadrant_integrable
#print axioms quadrant_euler_identity
end
end UnifiedTheory.Audit.KFCausalMinkowski4DEulerQuadrant
