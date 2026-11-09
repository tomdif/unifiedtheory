/- Convexity of the unweighted norm along an actual complex-clock shear
path. Both real and imaginary parts of the clock coefficient are retained.
This is an auxiliary interpolation estimate, not Hamiltonian evolution. -/
import UnifiedTheory.Audit.KFCausalClockShearPositiveVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearNormConvexity
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (weighted_graph_pairing)

variable (C : Hilbert →L[ℂ] Hilbert) (c : ℝ → ℂ)
  (hC : ∀ f : Hilbert, C f =ᵐ[volume] fun x => c x.1*f x)

include hC in
theorem square_coe (f : Hilbert) : C (C f) =ᵐ[volume] fun x => (c x.1)^2*f x := by
  filter_upwards [hC (C f),hC f] with x hx hy
  rw [hx,hy]
  ring

include hC in
theorem curvature_nonnegative (f : Hilbert) :
    0 ≤ (inner ℂ f (C (C f))+inner ℂ (C f) (C f)).re := by
  have he := integral_re ((L2.integrable_inner (𝕜 := ℂ) f (C (C f))).add
    (L2.integrable_inner (𝕜 := ℂ) (C f) (C f)))
  change (∫ x, (inner ℂ (f x) (C (C f) x)+inner ℂ (C f x) (C f x)).re) =
    (∫ x, inner ℂ (f x) (C (C f) x)+inner ℂ (C f x) (C f x)).re at he
  rw [L2.inner_def,L2.inner_def,← integral_add (L2.integrable_inner (𝕜 := ℂ) f (C (C f)))
    (L2.integrable_inner (𝕜 := ℂ) (C f) (C f)),← he]
  apply integral_nonneg_of_ae
  filter_upwards [hC f,square_coe C c hC f] with x hx hy
  rw [hx,hy]
  change 0 ≤ (((c x.1)^2*f x)*star (f x)+(c x.1*f x)*star (c x.1*f x)).re
  simp only [Complex.star_def,pow_two,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.add_re]
  nlinarith [sq_nonneg ((c x.1).re*(f x).re),sq_nonneg ((c x.1).re*(f x).im)]

def tangent (U J : ℝ → Hilbert) (t : ℝ) : ℝ := (inner ℂ (U t) (C (J t))).re

theorem norm_derivative (U J : ℝ → Hilbert) (t : ℝ)
    (hd : HasDerivAt U (C (J t)) t) :
    HasDerivAt (fun r => ‖U r‖^2) (2*tangent C U J t) t := by
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd.inner ℂ hd)
  change HasDerivAt (fun r => (inner ℂ (U r) (U r)).re)
    (inner ℂ (U t) (C (J t))+inner ℂ (C (J t)) (U t)).re t at he
  have hi : (inner ℂ (C (J t)) (U t)).re = (inner ℂ (U t) (C (J t))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  convert he using 1
  · funext r
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (U r)).symm
  · rw [Complex.add_re,hi]
    unfold tangent
    ring

include hC in
theorem tangent_derivative (h : ℝ) (hh : h ≠ 0) (U J : ℝ → Hilbert) (k : Hilbert) (t : ℝ)
    (hdU : HasDerivAt U (C (J t)) t) (hdJ : HasDerivAt J (C k) t)
    (hgU : (U t,J t) ∈ (shearMomentum h).graph)
    (hgJ : (J t,k) ∈ (shearMomentum h).graph) :
    HasDerivAt (tangent C U J)
      (inner ℂ (J t) (C (C (J t)))+inner ℂ (C (J t)) (C (J t))).re t := by
  have he := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hdU.inner ℂ ((C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hdJ))
  have hp := weighted_graph_pairing (C.comp C) (ContinuousLinearMap.id ℂ Hilbert)
    (fun s => (c s)^2) (fun _ => 1) (square_coe C c hC)
    (fun f => Filter.Eventually.of_forall (fun _ => (one_mul _).symm)) h hh (U t) (J t) k hgU hgJ
  change inner ℂ (U t) (C (C k)) = inner ℂ (J t) (C (C (J t))) at hp
  change HasDerivAt (tangent C U J)
    (inner ℂ (U t) (C (C k))+inner ℂ (C (J t)) (C (J t))).re t at he
  rw [hp] at he
  exact he

include hC in
theorem tangent_monotone (h : ℝ) (hh : h ≠ 0) (U J : ℝ → Hilbert) (K : Interval → Hilbert)
    (hU : Continuous U) (hJ : Continuous J)
    (hdU : ∀ t (_ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt U (C (J t)) t)
    (hdJ : ∀ t (ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt J (C (K ⟨t,ht.1.le,ht.2.le⟩)) t)
    (hgU : ∀ t : Interval, (U t,J t) ∈ (shearMomentum h).graph)
    (hgJ : ∀ t : Interval, (J t,K t) ∈ (shearMomentum h).graph) :
    MonotoneOn (tangent C U J) (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (Complex.continuous_re.comp (hU.inner (C.continuous.comp hJ))).continuousOn
    (f' := fun t => (inner ℂ (J t) (C (C (J t)))+inner ℂ (C (J t)) (C (J t))).re)
  · intro t ht
    rw [interior_Icc] at ht
    exact (tangent_derivative C c hC h hh U J (K ⟨t,ht.1.le,ht.2.le⟩) t
      (hdU t ht) (hdJ t ht) (hgU ⟨t,ht.1.le,ht.2.le⟩)
      (hgJ ⟨t,ht.1.le,ht.2.le⟩)).hasDerivWithinAt
  · intro t _
    exact curvature_nonnegative C c hC (J t)

theorem initial_tangent_lower (U J : ℝ → Hilbert) (hU : Continuous U)
    (hd : ∀ t (_ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt U (C (J t)) t)
    (hm : MonotoneOn (tangent C U J) (Icc (0:ℝ) 1)) :
    ‖U 0‖^2+2*tangent C U J 0 ≤ ‖U 1‖^2 := by
  have hD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) := norm_derivative C U J t (hd t ht)
  have he := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv (hU.norm.pow 2).continuousOn
    (fun t ht => (hD t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt)
    (C := 2*tangent C U J 0) (fun t ht => by
      have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
      rw [(hD t ht').deriv]
      exact mul_le_mul_of_nonneg_left (hm ⟨le_rfl,zero_le_one⟩ ⟨ht'.1.le,ht'.2.le⟩ ht'.1.le)
        (by norm_num : (0:ℝ) ≤ 2))
    0 ⟨le_rfl,zero_le_one⟩ 1 ⟨zero_le_one,le_rfl⟩ zero_le_one
  norm_num only [sub_zero,mul_one] at he
  linarith

#print axioms square_coe
#print axioms curvature_nonnegative
#print axioms norm_derivative
#print axioms tangent_derivative
#print axioms tangent_monotone
#print axioms initial_tangent_lower
end
end UnifiedTheory.Audit.KFCausalImaginaryShearNormConvexity
