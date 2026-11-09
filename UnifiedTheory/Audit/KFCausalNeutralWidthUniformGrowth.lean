/- The neutral comparison constant can be chosen uniformly over all
charged Gaussian parameters above one positive floor. This follows from
the inverse-width dependence of the regular score, not from a compact
upper bound on the Gaussian parameter. -/
import UnifiedTheory.Audit.KFCausalNeutralFiniteResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralWidthUniformGrowth
noncomputable section
open MeasureTheory
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalNeutralPlaneUniformScore
open KFCausalNeutralPlaneActualBound
open KFCausalNeutralProfileMarginal
open KFCausalNeutralProfileGrowth
open KFCausalNeutralExponentialProfiles
open KFCausalNeutralFiniteResponse (realKernel realKernel_derivative)

theorem regularScore_antitone (α₀ α t : ℝ) (r : ℂ)
    (hα₀ : 0 < α₀) (hα : α₀ ≤ α) (ht : t ∈ Set.Icc 0 1)
    (hA : 0 < r.re^2-r.im^2) : regularScore α t r ≤ regularScore α₀ t r := by
  have hd := normalized_denominator_positive t r ht hA
  have ha : 0 < r.re^2 := by nlinarith [sq_nonneg r.im]
  have hS : 0 < r.re^2+r.im^2 := by positivity
  have hp : 0 < 8*α₀*r.re^2*(r.re^2+r.im^2)*
      KFCausalNeutralPlaneClockGeometry.denominator (1-t) t r := by positivity
  have hm : 8*α₀*r.re^2*(r.re^2+r.im^2)*
      KFCausalNeutralPlaneClockGeometry.denominator (1-t) t r ≤
      8*α*r.re^2*(r.re^2+r.im^2)*
      KFCausalNeutralPlaneClockGeometry.denominator (1-t) t r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hα)
      (show 0 ≤ 8*r.re^2*(r.re^2+r.im^2)*
        KFCausalNeutralPlaneClockGeometry.denominator (1-t) t r by positivity)]
  unfold regularScore
  exact add_le_add le_rfl (div_le_div_of_nonneg_left
    (mul_nonneg ht.1 (sq_nonneg _)) hp hm)

theorem exists_upper_width_score (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α ε y s : ℝ, α₀ ≤ α → 0 < ε →
      |y| ≤ Real.pi*ε/3 → y ≠ 0 → score α ε y s ≤ M := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_score α₀ hα₀
  refine ⟨M,hM,?_⟩
  intro α ε y s hα hε hy hy0
  have ht := fraction_bounds ε s hε
  rw [KFCausalNeutralPlanePrefactorScore.actual_score_regular α ε y s
    (lt_of_lt_of_le hα₀ hα) hε hy hy0]
  apply (regularScore_antitone α₀ α _ _ hα₀ hα ⟨ht.1.le,ht.2.le⟩
    (KFCausalNeutralPlaneClockGeometry.scale_square_re_positive ε y s hε hy)).trans
  rw [← KFCausalNeutralPlanePrefactorScore.actual_score_regular α₀ ε y s hα₀ hε hy hy0]
  exact hbound ε y s hε hy hy0

theorem exists_upper_width_density_growth (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α β ε y : ℝ, α₀ ≤ α → 0 < ε →
      |y| ≤ Real.pi*ε/3 → y ≠ 0 → ∀ (F : ℂ → ℂ) (s t x z : ℝ), s ≤ t →
      actualProfileDensity α β ε y t F x z ≤
        Real.exp (M*(t-s))*actualProfileDensity α β ε y s F x z := by
  obtain ⟨M,hM,hscore⟩ := exists_upper_width_score α₀ hα₀
  refine ⟨M,hM,?_⟩
  intro α β ε y hα hε hy hy0 F s t x z hst
  have hp : 0 < α := lt_of_lt_of_le hα₀ hα
  have hg := KFCausalNeutralPlaneUniformGrowth.exponential_comparison
    (fun u => actualDensity α β ε y u 1 x z) M
    (fun u => (actualDensity_derivative α β ε y u hp hε hy hy0 1 x z).differentiableAt)
    (fun u => (actualDensity_derivative_bound α β ε y u hp hε hy hy0 1 x z).trans
      (mul_le_mul_of_nonneg_right (hscore α ε y u hα hε hy hy0)
        (actualDensity_nonnegative α β ε y u hp hε hy hy0 1 x z))) s t hst
  rw [actualProfileDensity_factorization,actualProfileDensity_factorization]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hg
    (sq_nonneg ‖F ((x:ℂ)+(z:ℂ)*Complex.I)‖)

theorem exists_upper_width_profile_growth (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α β ε y : ℝ, α₀ ≤ α → 0 < ε →
      |y| ≤ Real.pi*ε/3 → y ≠ 0 → ∀ (F : ℂ → ℂ) (s t : ℝ), s ≤ t →
      Integrable (profileEnergyDensity α β (scale ε y s) F) →
      Integrable (profileEnergyDensity α β (scale ε y t) F) →
      (∫ q, profileEnergyDensity α β (scale ε y t) F q) ≤
        Real.exp (M*(t-s))*(∫ q, profileEnergyDensity α β (scale ε y s) F q) := by
  obtain ⟨M,hM,hg⟩ := exists_upper_width_density_growth α₀ hα₀
  refine ⟨M,hM,?_⟩
  intro α β ε y hα hε hy hy0 F s t hst hs ht
  have hp : 0 < α := lt_of_lt_of_le hα₀ hα
  rw [profileEnergy_plane_integral α β _
      (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y t hε hy hy0),
    profileEnergy_plane_integral α β _
      (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0)]
  change (∫ v : Fin 2 → ℝ, actualProfileDensity α β ε y t F (v 0) (v 1)) ≤
    Real.exp (M*(t-s))*(∫ v : Fin 2 → ℝ, actualProfileDensity α β ε y s F (v 0) (v 1))
  rw [← integral_const_mul]
  exact integral_mono (actualProfileDensity_integrable α β ε y t hp hε hy hy0 F ht)
    ((actualProfileDensity_integrable α β ε y s hp hε hy hy0 F hs).const_mul _)
    (fun v => hg α β ε y hα hε hy hy0 F s t (v 0) (v 1) hst)

theorem exists_upper_width_kernel_growth (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α β ε y : ℝ, α₀ ≤ α → 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b c : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s t : ℝ), s ≤ t →
      realKernel ε y α β N b c P t ≤ Real.exp (M*(t-s))*realKernel ε y α β N b c P s := by
  obtain ⟨M,hM,hg⟩ := exists_upper_width_profile_growth α₀ hα₀
  refine ⟨M,hM,?_⟩
  intro α β ε y hα hβ hw hε hy hy0 N b c P s t hst
  have hp : 0 < α := lt_of_lt_of_le hα₀ hα
  simp only [realKernel,KFCausalNeutralFiniteGram.energyKernel_re α β ε y t hp hβ hw hε hy,
    KFCausalNeutralFiniteGram.energyKernel_re α β ε y s hp hβ hw hε hy]
  exact hg α β ε y hα hε hy hy0 _ s t hst
    (finiteProfile_integrable Finset.univ b c P α β ε y s hp hβ hw hε hy)
    (finiteProfile_integrable Finset.univ b c P α β ε y t hp hβ hw hε hy)

theorem exists_upper_width_kernel_derivative (α₀ : ℝ) (hα₀ : 0 < α₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ α β ε y : ℝ, α₀ ≤ α → 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b c : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
      deriv (realKernel ε y α β N b c P) s ≤ M*realKernel ε y α β N b c P s := by
  obtain ⟨M,hM,hg⟩ := exists_upper_width_kernel_growth α₀ hα₀
  refine ⟨M,hM,?_⟩
  intro α β ε y hα hβ hw hε hy hy0 N b c P s
  exact KFCausalCenteredPolynomialResponseBound.derivative_le_of_exponential_growth _ M
    (fun u => (realKernel_derivative α β ε y u (lt_of_lt_of_le hα₀ hα) hβ hw hε hy N b c P).differentiableAt)
    (hg α β ε y hα hβ hw hε hy hy0 N b c P) s

#print axioms regularScore_antitone
#print axioms exists_upper_width_score
#print axioms exists_upper_width_density_growth
#print axioms exists_upper_width_profile_growth
#print axioms exists_upper_width_kernel_growth
#print axioms exists_upper_width_kernel_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralWidthUniformGrowth
