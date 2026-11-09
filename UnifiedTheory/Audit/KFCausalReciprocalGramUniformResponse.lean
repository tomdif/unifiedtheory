/- A uniform matrix response bound for the physical reciprocal kernel.
The positive representation and nested wedge comparison control every
finite interference direction without a Gram eigenvalue lower bound. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgeRepresentation
import UnifiedTheory.Audit.KFCausalReciprocalWedgeComparison
import UnifiedTheory.Audit.KFCausalReciprocalCrossResponse
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalGramUniformResponse
noncomputable section
open MeasureTheory Set
open scoped ENNReal ComplexConjugate
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalCrossGram (pairing)
open KFCausalReciprocalCrossResponse (actualKernel)
open KFCausalReciprocalWedgePlane (c0 c1)
open KFCausalReciprocalWedgeCartesian (normalizer)
open KFCausalReciprocalWedgeRepresentation (wedgeDensity)
open KFCausalReciprocalWedgeGeometry (wedge)
open KFCausalReciprocalWedgeComparison (extendedWeight)
open KFCausalReciprocalWedgeLaplace (laplaceSum)

def gram (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  (pairing n α β w (scale ε y s) c c).re
def slope (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  (∑ i, ∑ j, (conj (c i)*c j)*deriv (actualKernel α β ε y (w i) (w j)) s).re
def extendedDensity (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (s θ : ℝ) (z : ℂ) : ℝ :=
  extendedWeight α β (Real.sin θ^2) (c0 β) (c1 β) (1/4) ε y s z*‖laplaceSum n w c z‖^2
def total (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ : ℝ in Ioo (-Real.pi) Real.pi, ∫⁻ z : ℂ, ENNReal.ofReal (extendedDensity n α β ε y w c s θ z)

theorem extended_lintegral (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (s θ : ℝ) :
    (∫⁻ z : ℂ, ENNReal.ofReal (extendedDensity n α β ε y w c s θ z)) =
      ∫⁻ z in wedge α (scale ε y s), ENNReal.ofReal (wedgeDensity n α β w (scale ε y s) c θ z) := by
  have he : (fun z => ENNReal.ofReal (extendedDensity n α β ε y w c s θ z)) =
      (wedge α (scale ε y s)).indicator
        (fun z => ENNReal.ofReal (wedgeDensity n α β w (scale ε y s) c θ z)) := by
    funext z
    by_cases hz : z ∈ wedge α (scale ε y s)
    · simp only [extendedDensity,extendedWeight,wedgeDensity,indicator_of_mem hz]
    · simp only [extendedDensity,extendedWeight,indicator_of_notMem hz,zero_mul,ENNReal.ofReal_zero]
  rw [he,lintegral_indicator (KFCausalReciprocalWedgeMeasure.wedge_measurable α _)]

theorem gram_nonnegative (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) (s : ℝ) :
    0 ≤ gram n α β ε y w c s := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact KFCausalReciprocalCrossGram.pairing_nonneg n α β w _ c hw ha hc hβ

theorem gram_lintegral (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) (hw : ∀ i, 1 ≤ w i) (s : ℝ) :
    ENNReal.ofReal (gram n α β ε y w c s) = ENNReal.ofReal (normalizer β/2)*total n α β ε y w c s := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  unfold gram total
  simp_rw [extended_lintegral]
  exact KFCausalReciprocalWedgeRepresentation.pairing_lintegral n α β w _ c hw hα ha hc hβ
    (KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy).ne'
    (KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero ε y s hε hy hy0)

theorem exists_uniform_gram_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ),
      0 < α → 0 < β → 32*β ≤ α → 0 < ε → |y| ≤ Real.pi*ε/6 → y ≠ 0 →
      (∀ i, 1 ≤ w i) → ∀ s t : ℝ, s ≤ t →
        gram n α β ε y w c t ≤ Real.exp (C*(t-s))*gram n α β ε y w c s := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalWedgeComparison.exists_uniform_extended_comparison
  refine ⟨C,hC,?_⟩
  intro n α β ε y w c hα hβ hwidth hε hy hy0 hw s t hst
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  obtain ⟨h0,h1⟩ := KFCausalReciprocalWedgePlane.coefficients_nonneg β hβ
  have ht : total n α β ε y w c t ≤ ENNReal.ofReal (Real.exp (C*(t-s)))*total n α β ε y w c s := by
    unfold total
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro θ
    dsimp only
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    dsimp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    unfold extendedDensity
    have h := mul_le_mul_of_nonneg_right
      (hbound α β (Real.sin θ^2) (c0 β) (c1 β) (1/4) ε y s t hα hβ.le
        (sq_nonneg _) h0 h1 (by norm_num) hε hy hy0 hst z) (sq_nonneg ‖laplaceSum n w c z‖)
    simpa only [mul_assoc] using h
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.exp_pos _).le (gram_nonnegative n α β ε y w c hα hβ hwidth hε hy' hw s))).mp
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    gram_lintegral n α β ε y w c hα hβ hwidth hε hy' hy0 hw t,
    gram_lintegral n α β ε y w c hα hβ hwidth hε hy' hy0 hw s]
  calc
    _ ≤ ENNReal.ofReal (normalizer β/2)*(ENNReal.ofReal (Real.exp (C*(t-s)))*total n α β ε y w c s) :=
      mul_le_mul_right ht _
    _ = _ := by ac_rfl

theorem gram_derivative (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) (s : ℝ) :
    HasDerivAt (gram n α β ε y w c) (slope n α β ε y w c s) s := by
  have hd := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
    HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
      (KFCausalReciprocalCrossResponse.actual_derivative α β ε y (w i) (w j) s
        hα hβ hwidth hε hy (hw i) (hw j)).const_mul (conj (c i)*c j)))
  have hd' : HasDerivAt (fun u => pairing n α β w (scale ε y u) c c)
      (∑ i, ∑ j, (conj (c i)*c j)*deriv (actualKernel α β ε y (w i) (w j)) s) s := by
    convert hd using 1
    funext u
    simp only [pairing,Finset.sum_apply,actualKernel]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd'

theorem derivative_from_comparison (f f' : ℝ → ℝ) (C : ℝ)
    (hd : ∀ s, HasDerivAt f (f' s) s)
    (hcmp : ∀ s t, s ≤ t → f t ≤ Real.exp (C*(t-s))*f s) (s : ℝ) :
    f' s ≤ C*f s := by
  have hmono : Antitone (fun u => Real.exp (-C*u)*f u) := by
    intro a b hab
    calc
      _ ≤ Real.exp (-C*b)*(Real.exp (C*(b-a))*f a) :=
        mul_le_mul_of_nonneg_left (hcmp a b hab) (Real.exp_pos _).le
      _ = Real.exp (-C*a)*f a := by
        rw [← mul_assoc,← Real.exp_add]
        congr 2
        ring
  have hg : HasDerivAt (fun u => Real.exp (-C*u)*f u)
      (Real.exp (-C*s)*(f' s-C*f s)) s := by
    convert (((hasDerivAt_id s).const_mul (-C)).exp).mul (hd s) using 1
    dsimp
    ring
  have hn := hmono.deriv_nonpos (x := s)
  rw [hg.deriv] at hn
  nlinarith [Real.exp_pos (-C*s)]

theorem exists_uniform_matrix_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ),
      0 < α → 0 < β → 32*β ≤ α → 0 < ε → |y| ≤ Real.pi*ε/6 → y ≠ 0 →
      (∀ i, 1 ≤ w i) → ∀ s : ℝ, slope n α β ε y w c s ≤ C*gram n α β ε y w c s := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_gram_comparison
  refine ⟨C,hC,?_⟩
  intro n α β ε y w c hα hβ hwidth hε hy hy0 hw s
  have hy' : |y| ≤ Real.pi*ε/3 := by nlinarith [Real.pi_pos]
  exact derivative_from_comparison _ _ C
    (gram_derivative n α β ε y w c hα hβ hwidth hε hy' hw)
    (hbound n α β ε y w c hα hβ hwidth hε hy hy0 hw) s

#print axioms extended_lintegral
#print axioms gram_nonnegative
#print axioms gram_lintegral
#print axioms exists_uniform_gram_comparison
#print axioms gram_derivative
#print axioms derivative_from_comparison
#print axioms exists_uniform_matrix_response
end
end UnifiedTheory.Audit.KFCausalReciprocalGramUniformResponse
