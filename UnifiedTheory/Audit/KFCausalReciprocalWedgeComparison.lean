/- Global comparison of the positive wedge weights. Nesting eliminates
the moving-boundary term by comparison of zero-extended densities. The
physical kernel representation and its integrability are still separate. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeComparison
noncomputable section
open Set
open KFCausalReciprocalWedgeGeometry (wedge)
open KFCausalReciprocalWedgeWeight (weight)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry

theorem scalar_growth (f : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hf : Differentiable ℝ f) (hd : ∀ u ∈ Icc a b, deriv f u ≤ C*f u) :
    f b ≤ Real.exp (C*(b-a))*f a := by
  have hg (u : ℝ) : HasDerivAt (fun x => Real.exp (-C*x)*f x)
      (Real.exp (-C*u)*(deriv f u-C*f u)) u := by
    convert (((hasDerivAt_id u).const_mul (-C)).exp).mul (hf u).hasDerivAt using 1
    dsimp
    ring
  have hcont : Continuous (fun u => Real.exp (-C*u)*f u) :=
    (fun u => (hg u).continuousAt) |> continuous_iff_continuousAt.mpr
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont.continuousOn
    (fun u _ => (hg u).differentiableAt.differentiableWithinAt) (fun u hu => by
      rw [(hg u).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hd u (interior_subset hu))))
  have h := mul_le_mul_of_nonneg_left (hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) (Real.exp_pos (C*b)).le
  have he : Real.exp (C*b)*Real.exp (-C*b) = 1 := by rw [← Real.exp_add]; simp
  have he' : Real.exp (C*b)*Real.exp (-C*a) = Real.exp (C*(b-a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,he,he',one_mul] using h

theorem actual_weight_differentiable (α β η c0 c1 c2 ε y : ℝ) (z : ℂ)
    (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/6) (hy0 : y ≠ 0) :
    Differentiable ℝ (fun s => weight α β η c0 c1 c2 (scale ε y s) z) := by
  intro s
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  have hA := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy'
  have ht := fraction_bounds ε s hε
  have hD := normalized_denominator_positive _ _ ⟨ht.1.le,ht.2.le⟩ hA
  have hf := KFCausalReciprocalWedgePrefactor.region_field_positive _
    (KFCausalReciprocalWedgePrefactor.actual_mem_region ε y s hε hy)
  exact (KFCausalReciprocalWedgeWeight.weight_derivative (scale ε y) α β η c0 c1 c2 (fraction ε s) s z
    (actual_normalized_velocity ε y s hε hy') hα.ne' hA.ne'
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy').ne'
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy' hy0) hD.ne' hf.ne').differentiableAt

theorem exists_uniform_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α β η c0 c1 c2 ε y s t : ℝ,
      0 < α → 0 ≤ β → 0 ≤ η → 0 ≤ c0 → 0 ≤ c1 → 0 ≤ c2 →
      0 < ε → |y| ≤ Real.pi*ε/6 → y ≠ 0 → s ≤ t → ∀ z ∈ wedge α (scale ε y t),
      weight α β η c0 c1 c2 (scale ε y t) z ≤
        Real.exp (C*(t-s))*weight α β η c0 c1 c2 (scale ε y s) z := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalWedgeWeight.exists_uniform_weight_bound
  refine ⟨C,hC,?_⟩
  intro α β η c0 c1 c2 ε y s t hα hβ hη h0 h1 h2 hε hy hy0 hst z hz
  apply scalar_growth _ C s t hst (actual_weight_differentiable α β η c0 c1 c2 ε y z hα hε hy hy0)
  intro u hu
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  exact hbound α β η c0 c1 c2 ε y u hα hβ hη h0 h1 h2 hε hy hy0 z
    (KFCausalReciprocalWedgeNesting.actual_wedge_nested α ε y u t hα hε hy' hy0 hu.2 hz)

def extendedWeight (α β η c0 c1 c2 ε y s : ℝ) (z : ℂ) : ℝ :=
  (wedge α (scale ε y s)).indicator (weight α β η c0 c1 c2 (scale ε y s)) z

theorem exists_uniform_extended_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α β η c0 c1 c2 ε y s t : ℝ,
      0 < α → 0 ≤ β → 0 ≤ η → 0 ≤ c0 → 0 ≤ c1 → 0 ≤ c2 →
      0 < ε → |y| ≤ Real.pi*ε/6 → y ≠ 0 → s ≤ t → ∀ z : ℂ,
      extendedWeight α β η c0 c1 c2 ε y t z ≤
        Real.exp (C*(t-s))*extendedWeight α β η c0 c1 c2 ε y s z := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_uniform_comparison
  refine ⟨C,hC,?_⟩
  intro α β η c0 c1 c2 ε y s t hα hβ hη h0 h1 h2 hε hy hy0 hst z
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  by_cases hz : z ∈ wedge α (scale ε y t)
  · have hs := KFCausalReciprocalWedgeNesting.actual_wedge_nested α ε y s t hα hε hy' hy0 hst hz
    simp only [extendedWeight,indicator_of_mem hz,indicator_of_mem hs]
    exact hbound α β η c0 c1 c2 ε y s t hα hβ hη h0 h1 h2 hε hy hy0 hst z hz
  · simp only [extendedWeight,indicator_of_notMem hz]
    by_cases hs : z ∈ wedge α (scale ε y s)
    · rw [indicator_of_mem hs]
      exact mul_nonneg (Real.exp_pos _).le
        (KFCausalReciprocalWedgeWeight.weight_nonnegative α β η c0 c1 c2 _ z hη h0 h1 h2 hs)
    · rw [indicator_of_notMem hs,mul_zero]

#print axioms scalar_growth
#print axioms actual_weight_differentiable
#print axioms exists_uniform_comparison
#print axioms exists_uniform_extended_comparison
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeComparison
