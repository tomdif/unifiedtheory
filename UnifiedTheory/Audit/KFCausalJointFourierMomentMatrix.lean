/- The full three-channel Fourier energy is the evaluated coherent
charged moment matrix. Every width and polynomial cross term is retained.
This identifies the matrix to be bounded; it does not bound its derivative. -/
import UnifiedTheory.Audit.KFCausalJointFourierQuadraticJet
import UnifiedTheory.Audit.KFCausalChargedFourierPolynomialGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalJointFourierMomentMatrix
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
open KFCausalNeutralFourierQuadraticJet (packetMoment jetEnergy)
open KFCausalJointFourierQuadraticJet (chargedJet complexShear jetSlice)
open KFCausalChargedFourierPolynomialGram (family atom gram)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalReciprocalWedgeGeometry (gamma chart)

def source (r : ℂ) (k : ℝ) : ℝ := -8*Real.pi*k*r.im

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

def amplitude (j : ℕ) (k : ℝ) (i : Fin n) : ℂ :=
  c i*(w i:ℂ)*(𝓕 (packetMoment β (b i) (P i) j)) k

def channelCoefficients (r : ℂ) (k : ℝ) (h : Fin 3) (i : Fin n) : Fin 3 → ℂ :=
  ![![amplitude n β w b c P 0 k i,0,0],
    ![amplitude n β w b c P 1 k i,complexShear r*amplitude n β w b c P 0 k i,0],
    ![amplitude n β w b c P 2 k i,2*complexShear r*amplitude n β w b c P 1 k i,
      complexShear r^2*amplitude n β w b c P 0 k i]] h

def channels (r z : ℂ) (v k : ℝ) : Fin 3 → ℂ :=
  ![chargedJet n β w b c P 0 z k,
    chargedJet n β w b c P 1 z k+complexShear r*(v:ℂ)*chargedJet n β w b c P 0 z k,
    chargedJet n β w b c P 2 z k+2*complexShear r*(v:ℂ)*chargedJet n β w b c P 1 z k+
      (complexShear r*(v:ℂ))^2*chargedJet n β w b c P 0 z k]

theorem chargedJet_amplitude (j : ℕ) (z : ℂ) (k : ℝ) :
    chargedJet n β w b c P j z k =
      ∑ i, Complex.exp (-(w i:ℂ)*z)*amplitude n β w b c P j k i := by
  unfold chargedJet KFCausalNeutralJointCurvatureForm.coefficients amplitude
  apply Finset.sum_congr rfl
  intro i _
  ring

omit n β w b c P in
theorem atom_chart (α : ℝ) (r : ℂ) (w c : ℝ) (m : ℕ) (u v Y : ℝ) :
    atom (gamma α r) w c m u v Y =
      Complex.exp ((c:ℂ)/2*(v:ℂ))*Complex.exp (-(w:ℂ)*chart α r (u^2+v^2) Y)*(v:ℂ)^m := by
  unfold atom chart
  rw [← Complex.exp_add]
  rw [mul_comm _ ((v:ℂ)^m)]
  congr 1
  congr 1
  push_cast
  ring

theorem family_channels (α : ℝ) (r : ℂ) (k u v Y : ℝ) (h : Fin 3) :
    family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k h) u v Y =
      Complex.exp ((source r k:ℂ)/2*(v:ℂ))*
        channels n β w b c P r (chart α r (u^2+v^2) Y) v k h := by
  unfold family
  rw [Fintype.sum_prod_type]
  simp_rw [atom_chart]
  fin_cases h <;>
    norm_num [channelCoefficients,channels,Fin.sum_univ_succ,chargedJet_amplitude,
      Finset.mul_sum,← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem family_density (α : ℝ) (r : ℂ) (k u v Y : ℝ) (h : Fin 3) :
    ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k h) u v Y‖^2 =
      Real.exp (source r k*v)*‖channels n β w b c P r (chart α r (u^2+v^2) Y) v k h‖^2 := by
  rw [family_channels,norm_mul,mul_pow,Complex.norm_exp,← Real.exp_nat_mul]
  congr 2
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.div_ofNat_re,Complex.div_ofNat_im,zero_div,zero_mul,sub_zero]
  ring

def matrixEnergy (α : ℝ) (r : ℂ) (k : ℝ) : ℝ :=
  (gram n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 0)).re+
    (gram n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 1)).re/2+
    (gram n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 2)).re/4

theorem slice_density (α : ℝ) (r : ℂ) (k u v Y : ℝ) :
    jetSlice n β w b c P r (chart α r (u^2+v^2) Y) v k =
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 0) u v Y‖^2+
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 1) u v Y‖^2/2+
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 2) u v Y‖^2/4 := by
  rw [family_density,family_density,family_density]
  change Real.exp (-8*Real.pi*k*r.im*v)*
      jetEnergy (complexShear r*(v:ℂ)) (chargedJet n β w b c P 0 (chart α r (u^2+v^2) Y) k)
        (chargedJet n β w b c P 1 (chart α r (u^2+v^2) Y) k)
        (chargedJet n β w b c P 2 (chart α r (u^2+v^2) Y) k) =
    Real.exp (-8*Real.pi*k*r.im*v)*‖chargedJet n β w b c P 0 (chart α r (u^2+v^2) Y) k‖^2+
    Real.exp (-8*Real.pi*k*r.im*v)*
      ‖chargedJet n β w b c P 1 (chart α r (u^2+v^2) Y) k+
        complexShear r*(v:ℂ)*chargedJet n β w b c P 0 (chart α r (u^2+v^2) Y) k‖^2/2+
    Real.exp (-8*Real.pi*k*r.im*v)*
      ‖chargedJet n β w b c P 2 (chart α r (u^2+v^2) Y) k+
        2*complexShear r*(v:ℂ)*chargedJet n β w b c P 1 (chart α r (u^2+v^2) Y) k+
        (complexShear r*(v:ℂ))^2*chargedJet n β w b c P 0 (chart α r (u^2+v^2) Y) k‖^2/4
  unfold jetEnergy
  ring

omit n β w b c P in
theorem real_gram_integral (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    (∫ x : Charged, ‖family n p w c a x.1.1 x.1.2 x.2‖^2 ∂chargedMeasure) =
      (gram n p w c a).re := by
  have hi := KFCausalChargedFourierPolynomialGram.family_square_integrable n p w c a hp hw
  have he := congrArg RCLike.re (KFCausalChargedFourierPolynomialGram.gram_integral n p w c a hp hw)
  rw [← integral_re hi] at he
  exact he

theorem slice_integrable (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) :
    Integrable (fun x : Charged => jetSlice n β w b c P r (chart α r (x.1.1^2+x.1.2^2) x.2) x.1.2 k)
      chargedMeasure := by
  simp_rw [slice_density]
  have hi (h : Fin 3) : Integrable (fun x : Charged =>
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k h)
        x.1.1 x.1.2 x.2‖^2) chargedMeasure := by
    simpa only [RCLike.ofReal_re] using
      (KFCausalChargedFourierPolynomialGram.family_square_integrable n (gamma α r) w (source r k)
        (channelCoefficients n β w b c P r k h) hp hw).re
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

theorem slice_matrix_integral (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) :
    (∫ x : Charged, jetSlice n β w b c P r (chart α r (x.1.1^2+x.1.2^2) x.2) x.1.2 k ∂chargedMeasure) =
      matrixEnergy n β w b c P α r k := by
  simp_rw [slice_density]
  have hi (h : Fin 3) : Integrable (fun x : Charged =>
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k h)
        x.1.1 x.1.2 x.2‖^2) chargedMeasure := by
    simpa only [RCLike.ofReal_re] using
      (KFCausalChargedFourierPolynomialGram.family_square_integrable n (gamma α r) w (source r k)
        (channelCoefficients n β w b c P r k h) hp hw).re
  have hsum : Integrable (fun x : Charged =>
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 0) x.1.1 x.1.2 x.2‖^2+
      ‖family n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k 1) x.1.1 x.1.2 x.2‖^2/2)
      chargedMeasure := (hi 0).add ((hi 1).div_const 2)
  rw [integral_add hsum ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2)]
  simp_rw [integral_div,real_gram_integral n (gamma α r) w (source r k) _ hp hw]
  rfl

theorem matrixEnergy_nonnegative (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) :
    0 ≤ matrixEnergy n β w b c P α r k := by
  rw [← slice_matrix_integral n β w b c P α r k hp hw]
  exact integral_nonneg (fun x => KFCausalJointFourierQuadraticJet.jetSlice_nonnegative n β w b c P r _ _ _)

#print axioms chargedJet_amplitude
#print axioms atom_chart
#print axioms family_channels
#print axioms family_density
#print axioms slice_density
#print axioms real_gram_integral
#print axioms slice_integrable
#print axioms slice_matrix_integral
#print axioms matrixEnergy_nonnegative
end
end UnifiedTheory.Audit.KFCausalJointFourierMomentMatrix
