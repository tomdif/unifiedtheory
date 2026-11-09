/- Local full-space Gaussian/Laplace domination under charged exponential
dilation. Constants may depend on the finite source family and degrees;
this is absolute domination, not a uniform energy-relative estimate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedDilationEnvelope
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalJointCompactPolynomialBounds (Controlled)
open KFCausalClusteredClockFactors (E)

def scale (ell t : ℝ) : ℝ := Real.exp (ell*t)
def geometry (ell : ℝ) (r : ℂ) (t : ℝ) : ℂ := (scale ell t:ℂ)*r

theorem geometry_area (ell : ℝ) (r : ℂ) (t : ℝ) :
    area (geometry ell r t) = scale ell t^2*area r := by
  simp only [geometry,area,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  ring

theorem scale_square_lower (ell t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Real.exp (-2*|ell|) ≤ scale ell t^2 := by
  have ht' : |t| ≤ 1 := abs_le.mpr ht
  have hm : |ell*t| ≤ |ell| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left ht' (abs_nonneg ell)).trans_eq (mul_one _)
  unfold scale
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  nlinarith [(abs_le.mp hm).1]

theorem width_floors (α β ell : ℝ) (r : ℂ) (hA : 0 < α*area r)
    (hC : 0 < α*area r-8*β*r.im^2) :
    ∃ q : ℝ, 0 < q ∧ ∀ t ∈ Set.Icc (-1:ℝ) 1,
      q ≤ α*area (geometry ell r t) ∧
      q ≤ α*area (geometry ell r t)-8*β*(geometry ell r t).im^2 := by
  let q := Real.exp (-2*|ell|)*min (α*area r) (α*area r-8*β*r.im^2)
  refine ⟨q,mul_pos (Real.exp_pos _) (lt_min hA hC),?_⟩
  intro t ht
  have hs := scale_square_lower ell t ht
  have he : α*area (geometry ell r t)-8*β*(geometry ell r t).im^2 =
      scale ell t^2*(α*area r-8*β*r.im^2) := by
    rw [geometry_area]
    simp only [geometry,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul]
    ring
  constructor
  · rw [geometry_area]
    change Real.exp (-2*|ell|)*min _ _ ≤ _
    calc
      _ ≤ Real.exp (-2*|ell|)*(α*area r) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.exp_pos _).le
      _ ≤ scale ell t^2*(α*area r) := mul_le_mul_of_nonneg_right hs hA.le
      _ = _ := by ring
  · rw [he]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right hs hC.le)

theorem prefactor_envelope (α β ell : ℝ) (r b : ℂ) (hβ : 0 < β)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2)
    (f : ℝ → Joint → ℂ) (hf : Controlled (Set.Icc (-1:ℝ) 1) f) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ t ∈ Set.Icc (-1:ℝ) 1, ∀ p, 0 ≤ p.2 →
        ‖Complex.exp (E α β (geometry ell r t) b p)*f t p‖^2 ≤ D p := by
  obtain ⟨q,hq,hbound⟩ := width_floors α β ell r hA hC
  obtain ⟨D,hDi,hD0,hD⟩ := KFCausalJointUniformWeightEnvelope.controlled_square_envelope
    (Set.Icc (-1:ℝ) 1) isCompact_Icc f hf
    (fun t => α*area (geometry ell r t))
    (fun t => α*area (geometry ell r t)-8*β*(geometry ell r t).im^2)
    (fun t => -4*b.im*(geometry ell r t).im) (by unfold geometry scale; fun_prop)
    (2*β) (2*b.re) q (by positivity) hq
    (fun t ht => (hbound t ht).1) (fun t ht => (hbound t ht).2)
  refine ⟨D,hDi,hD0,?_⟩
  intro t ht p hp
  rw [norm_mul,mul_pow,KFCausalClusteredClockDensity.base_norm,mul_comm]
  exact hD t ht p hp

theorem finite_pair_envelope (n : ℕ) (α : Fin n → ℝ) (β ell : ℝ) (r : ℂ)
    (b : Fin n → ℂ) (hβ : 0 < β) (hA : ∀ i, 0 < α i*area r)
    (hC : ∀ i, 0 < α i*area r-8*β*r.im^2)
    (f g : Fin n → ℝ → Joint → ℂ)
    (hf : ∀ i, Controlled (Set.Icc (-1:ℝ) 1) (f i))
    (hg : ∀ i, Controlled (Set.Icc (-1:ℝ) 1) (g i)) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ t ∈ Set.Icc (-1:ℝ) 1, ∀ p, 0 ≤ p.2 →
        ‖∑ i, Complex.exp (E (α i) β (geometry ell r t) (b i) p)*f i t p‖^2+
        ‖∑ i, Complex.exp (E (α i) β (geometry ell r t) (b i) p)*g i t p‖^2 ≤ D p := by
  choose A hAi hA0 hAf using fun i => prefactor_envelope (α i) β ell r (b i) hβ (hA i) (hC i) (f i) (hf i)
  choose B hBi hB0 hBg using fun i => prefactor_envelope (α i) β ell r (b i) hβ (hA i) (hC i) (g i) (hg i)
  refine ⟨fun p => (n:ℝ)*∑ i, (A i p+B i p),
    (integrable_finset_sum Finset.univ (fun i _ => (hAi i).add (hBi i))).const_mul _,?_,?_⟩
  · intro p
    exact mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg (fun i _ => add_nonneg (hA0 i p) (hB0 i p)))
  · intro t ht p hp
    have hb := KFCausalCorrelatedClusteredBounds.sum_pair_bound n (fun _ => 1)
      (fun i => Complex.exp (E (α i) β (geometry ell r t) (b i) p)*f i t p)
      (fun i => Complex.exp (E (α i) β (geometry ell r t) (b i) p)*g i t p)
      (fun i => A i p+B i p) (fun i => add_le_add (hAf i t ht p hp) (hBg i t ht p hp))
    simpa only [one_mul,norm_one,one_pow] using hb

#print axioms geometry_area
#print axioms scale_square_lower
#print axioms width_floors
#print axioms prefactor_envelope
#print axioms finite_pair_envelope
end
end UnifiedTheory.Audit.KFCausalCorrelatedDilationEnvelope
