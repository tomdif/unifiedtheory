/- A positive integral representation of the actual reciprocal Gram
form on a charged plane times a Laplace half-line. Absolute integrability
is proved termwise before exchanging finite interference sums. -/
import UnifiedTheory.Audit.KFCausalReciprocalWedgePlane
import UnifiedTheory.Audit.KFCausalReciprocalCrossGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalWedgeCartesian
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalWedgePlane (polynomial jointDensity jointMeasure)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalReciprocalCrossGeometry (B C)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalChargedPairCoordinates (fieldSlope)

def positiveDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  polynomial β (fieldSlope r) p.1.2*Real.exp (8*β*r.im^2*p.1.2^2)*
    ‖laplaceSum n w c (chart α r (p.1.1^2+p.1.2^2) p.2)‖^2

theorem positiveDensity_nonneg (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hβ : 0 < β) (p : (ℝ × ℝ) × ℝ) :
    0 ≤ positiveDensity n α β w r c p := by
  have hp := KFCausalReciprocalWedgePlane.polynomial_nonneg β (fieldSlope r) p.1.2 hβ
  unfold positiveDensity
  positivity

theorem joint_factor (α β w v : ℝ) (r : ℂ) (p : (ℝ × ℝ) × ℝ) :
    jointDensity (B α w v r) (C α β w v r) β (fieldSlope r) p =
      ((polynomial β (fieldSlope r) p.1.2*Real.exp (8*β*r.im^2*p.1.2^2):ℝ):ℂ)*
        Complex.exp (-B α w v r*((p.1.1^2+p.1.2^2:ℝ):ℂ)-conj (B α w v r)*(p.2:ℂ)) := by
  simp only [jointDensity,KFCausalReciprocalWedgePlane.density,C,
    Complex.ofReal_mul,Complex.ofReal_exp,mul_assoc,← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem density_expansion (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (p : (ℝ × ℝ) × ℝ) :
    (positiveDensity n α β w r c p:ℂ) =
      ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
        jointDensity (B α (w i) (w j) r) (C α β (w i) (w j) r) β (fieldSlope r) p := by
  unfold positiveDensity
  rw [Complex.ofReal_mul,KFCausalReciprocalWedgeLaplace.laplaceSum_norm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [joint_factor]
  ring

theorem positiveDensity_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    Integrable (positiveDensity n α β w r c) jointMeasure := by
  have hi : ∀ i j, Integrable (fun p => ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
      jointDensity (B α (w i) (w j) r) (C α β (w i) (w j) r) β (fieldSlope r) p) jointMeasure := by
    intro i j
    obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β (w i) (w j) r
      (hw i) (hw j) hA hC hβ
    exact (KFCausalReciprocalWedgePlane.joint_integrable _ _ hb hc β (fieldSlope r)).const_mul _
  have hs := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))
  have he : Integrable (fun p => (positiveDensity n α β w r c p:ℂ)) jointMeasure :=
    hs.congr (Filter.Eventually.of_forall (fun p => (density_expansion n α β w r c p).symm))
  exact he.re

theorem density_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    (∫ p, (positiveDensity n α β w r c p:ℂ) ∂jointMeasure) =
      ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
        ∫ p, jointDensity (B α (w i) (w j) r) (C α β (w i) (w j) r) β (fieldSlope r) p ∂jointMeasure := by
  have hi : ∀ i j, Integrable (fun p => ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
      jointDensity (B α (w i) (w j) r) (C α β (w i) (w j) r) β (fieldSlope r) p) jointMeasure := by
    intro i j
    obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β (w i) (w j) r
      (hw i) (hw j) hA hC hβ
    exact (KFCausalReciprocalWedgePlane.joint_integrable _ _ hb hc β (fieldSlope r)).const_mul _
  simp_rw [density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),integral_const_mul]

theorem gaussianValue_real (b : ℝ) (hb : 0 < b) :
    KFCausalComplexGaussianMoments.gaussianValue (b:ℂ) = (Real.sqrt (Real.pi/b):ℂ) := by
  rw [← KFCausalComplexGaussianMoments.value_zero (b:ℂ) (by simpa using hb)]
  unfold KFCausalComplexGaussianMoments.value KFCausalComplexGaussianMoments.moment
  simp only [pow_zero,one_mul]
  have he : (fun x : ℝ => Complex.exp (-(b:ℂ)*(x:ℂ)^2)) =
      fun x => (Real.exp (-b*x^2):ℂ) := by
    funext x
    simp only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_pow]
  rw [he,integral_complex_ofReal,integral_gaussian]

def normalizer (β : ℝ) : ℝ := (Real.pi/4)*Real.sqrt (Real.pi/(2*β))

theorem normalizer_pos (β : ℝ) (hβ : 0 < β) : 0 < normalizer β := by
  unfold normalizer
  positivity

theorem pairing_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    KFCausalReciprocalCrossGram.pairing n α β w r c c =
      ((normalizer β*∫ p, positiveDensity n α β w r c p ∂jointMeasure:ℝ):ℂ) := by
  have hg : KFCausalComplexGaussianMoments.gaussianValue (2*(β:ℂ)) =
      (Real.sqrt (Real.pi/(2*β)):ℂ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using gaussianValue_real (2*β) (by positivity)
  rw [Complex.ofReal_mul,← integral_complex_ofReal,density_integral n α β w r c hw hA hC hβ]
  unfold KFCausalReciprocalCrossGram.pairing
  simp_rw [KFCausalReciprocalWedgePlane.kernel_joint α β _ _ r (hw _) (hw _) hA hC hβ,hg]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold normalizer
  push_cast
  ring

#print axioms positiveDensity_nonneg
#print axioms joint_factor
#print axioms density_expansion
#print axioms positiveDensity_integrable
#print axioms density_integral
#print axioms gaussianValue_real
#print axioms normalizer_pos
#print axioms pairing_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalWedgeCartesian
