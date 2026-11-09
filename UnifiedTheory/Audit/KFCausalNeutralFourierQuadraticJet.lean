/- Exact degree-two Fourier field channels. Arbitrary neutral source
and polynomial degree enter only through three actual Fourier moments;
this is a representation identity, not a uniform matrix inequality. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierEnergy
import UnifiedTheory.Audit.KFCausalGaussianQuarticFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierQuadraticJet
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralFourierField (fieldPolynomial spectrum fieldLine)
open KFCausalNeutralFourierEnergy (frequencyDensity frequencyMoment)
open KFCausalNeutralLinePackets (entire)
open KFCausalGaussianQuarticFourier (fourier_const_mul)

private theorem fourier_add (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) (k : ℝ) :
    (𝓕 (fun x => f x+g x)) k = (𝓕 f) k+(𝓕 g) k := by
  simp only [Real.fourier_eq,smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff k).mpr hf)
    ((Real.fourierIntegral_convergent_iff k).mpr hg)

def packetMoment (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  (x:ℂ)^j*entire β b P (x:ℂ)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def momentLine (j : ℕ) (x : ℝ) : ℂ := (x:ℂ)^j*line n β b c P 0 x

theorem line_zero (j : ℕ) :
    line n β b c (fun i => fieldPolynomial j 0 (P i)) 0 = momentLine n β b c P j := by
  funext x
  simp only [line,KFCausalGaussianContourShift.horizontal,
    KFCausalNeutralFourierField.family_field,Complex.ofReal_zero,zero_mul,add_zero,momentLine]

theorem line_one (q : ℂ) :
    line n β b c (fun i => fieldPolynomial 1 q (P i)) 0 =
      fun x => momentLine n β b c P 1 x+q*momentLine n β b c P 0 x := by
  funext x
  simp only [line,KFCausalGaussianContourShift.horizontal,
    KFCausalNeutralFourierField.family_field,Complex.ofReal_zero,zero_mul,add_zero,
    momentLine,pow_zero,pow_one,one_mul]
  ring

theorem line_two (q : ℂ) :
    line n β b c (fun i => fieldPolynomial 2 q (P i)) 0 =
      fun x => momentLine n β b c P 2 x+(2*q)*momentLine n β b c P 1 x+
        q^2*momentLine n β b c P 0 x := by
  funext x
  simp only [line,KFCausalGaussianContourShift.horizontal,
    KFCausalNeutralFourierField.family_field,Complex.ofReal_zero,zero_mul,add_zero,
    momentLine,pow_zero,pow_one,one_mul]
  ring

theorem momentLine_integrable (hβ : 0 < β) (j : ℕ) :
    Integrable (momentLine n β b c P j) := by
  rw [← line_zero]
  exact KFCausalNeutralFourierShift.line_integrable n β hβ b c _ 0

theorem spectrum_zero (j : ℕ) (k : ℝ) :
    spectrum n β b c P j 0 k = (𝓕 (momentLine n β b c P j)) k := by
  unfold KFCausalNeutralFourierField.spectrum
  rw [line_zero]

theorem spectrum_one (hβ : 0 < β) (q : ℂ) (k : ℝ) :
    spectrum n β b c P 1 q k = spectrum n β b c P 1 0 k+q*spectrum n β b c P 0 0 k := by
  unfold KFCausalNeutralFourierField.spectrum
  rw [line_one,fourier_add _ _ (momentLine_integrable n β b c P hβ 1)
    ((momentLine_integrable n β b c P hβ 0).const_mul q),fourier_const_mul]
  simp only [line_zero]

theorem spectrum_two (hβ : 0 < β) (q : ℂ) (k : ℝ) :
    spectrum n β b c P 2 q k = spectrum n β b c P 2 0 k+
      2*q*spectrum n β b c P 1 0 k+q^2*spectrum n β b c P 0 0 k := by
  have hs : Integrable (fun x => momentLine n β b c P 2 x+(2*q)*momentLine n β b c P 1 x) :=
    (momentLine_integrable n β b c P hβ 2).add ((momentLine_integrable n β b c P hβ 1).const_mul (2*q))
  unfold KFCausalNeutralFourierField.spectrum
  rw [line_two,fourier_add _ _ hs
    ((momentLine_integrable n β b c P hβ 0).const_mul (q^2)),
    fourier_add _ _ (momentLine_integrable n β b c P hβ 2)
      ((momentLine_integrable n β b c P hβ 1).const_mul (2*q)),fourier_const_mul,fourier_const_mul]
  simp only [line_zero]

def jetEnergy (q G₀ G₁ G₂ : ℂ) : ℝ :=
  ‖G₀‖^2+‖G₁+q*G₀‖^2/2+‖G₂+2*q*G₁+q^2*G₀‖^2/4

theorem frequencyDensity_jet (hβ : 0 < β) (a y k : ℝ) :
    frequencyDensity n β b c P a y k = Real.exp (-4*Real.pi*k*y)*
      jetEnergy ((a:ℂ)-(y:ℂ)*Complex.I) (spectrum n β b c P 0 0 k)
        (spectrum n β b c P 1 0 k) (spectrum n β b c P 2 0 k) := by
  have hz (q : ℂ) : spectrum n β b c P 0 q = spectrum n β b c P 0 0 := by
    simp only [KFCausalNeutralFourierField.spectrum,fieldPolynomial,pow_zero,one_mul]
  unfold frequencyDensity frequencyMoment jetEnergy
  rw [hz,spectrum_one n β b c P hβ,spectrum_two n β b c P hβ]
  ring

omit n b c P in
theorem packetMoment_integrable (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ) (j : ℕ) :
    Integrable (packetMoment β b P j) := by
  have hi := KFCausalNeutralFourierShift.polynomial_translated_integrable β hβ b 0 P (Polynomial.X^j)
  simpa only [Polynomial.eval_pow,Polynomial.eval_X,add_zero,packetMoment] using hi

theorem momentLine_sum (j : ℕ) :
    momentLine n β b c P j = fun x => ∑ i, c i*packetMoment β (b i) (P i) j x := by
  funext x
  unfold momentLine line KFCausalGaussianContourShift.horizontal KFCausalNeutralLineDomain.family packetMoment
  simp only [Complex.ofReal_zero,zero_mul,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectrum_sum (hβ : 0 < β) (j : ℕ) (k : ℝ) :
    spectrum n β b c P j 0 k = ∑ i, c i*(𝓕 (packetMoment β (b i) (P i) j)) k := by
  rw [spectrum_zero,momentLine_sum]
  simp only [Real.fourier_eq,Finset.smul_sum]
  have hi (i : Fin n) : Integrable (fun x => Real.fourierChar (-inner ℝ x k) •
      (c i*packetMoment β (b i) (P i) j x)) :=
    (Real.fourierIntegral_convergent_iff k).mpr ((packetMoment_integrable β hβ (b i) (P i) j).const_mul (c i))
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Circle.smul_def,smul_eq_mul,mul_left_comm _ (c i),integral_const_mul]

#print axioms line_zero
#print axioms line_one
#print axioms line_two
#print axioms momentLine_integrable
#print axioms spectrum_zero
#print axioms spectrum_one
#print axioms spectrum_two
#print axioms frequencyDensity_jet
#print axioms packetMoment_integrable
#print axioms momentLine_sum
#print axioms spectrum_sum
end
end UnifiedTheory.Audit.KFCausalNeutralFourierQuadraticJet
