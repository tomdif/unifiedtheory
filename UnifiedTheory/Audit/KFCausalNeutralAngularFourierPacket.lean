/- Exact angular-frequency Fourier transform of an arbitrary neutral
Gaussian-polynomial packet, and its charged Gaussian gauge. The frequency
is ξ=2πk. All source and polynomial dependence is retained explicitly. -/
import UnifiedTheory.Audit.KFCausalShiftedComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalNeutralFourierQuadraticJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralAngularFourierPacket
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralLinePackets (packet monomial entire)
open KFCausalShiftedComplexGaussianMoments (normalized mass value)

def momentPolynomial (β : ℝ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (1/(2*(β:ℂ)))*Polynomial.X
  | n+2 => Polynomial.C (1/(2*(β:ℂ)))*
      (Polynomial.C (n+1:ℂ)*momentPolynomial β n+
        Polynomial.X*momentPolynomial β (n+1))

theorem momentPolynomial_eval (β : ℝ) (z : ℂ) (n : ℕ) :
    (momentPolynomial β n).eval z = normalized (β:ℂ) z n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [momentPolynomial,normalized]
  | one => simp [momentPolynomial,normalized,div_eq_mul_inv,mul_comm]
  | more n h0 h1 =>
    simp only [momentPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_add,Polynomial.eval_X,h0,h1,normalized]
    ring

def angularTransform (f : ℝ → ℂ) (ξ : ℝ) : ℂ := (𝓕 f) (ξ/(2*Real.pi))

theorem angularTransform_integral (f : ℝ → ℂ) (ξ : ℝ) :
    angularTransform f ξ = ∫ x : ℝ, Complex.exp (-Complex.I*(ξ:ℂ)*(x:ℂ))*f x := by
  simp only [angularTransform,Real.fourier_eq,Circle.smul_def,Real.fourierChar_apply,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [RCLike.inner_apply,conj_trivial,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_div,Complex.ofReal_ofNat]
  field_simp

theorem monomial_transform (β : ℝ) (b : ℂ) (hβ : 0 < β) (n : ℕ) (ξ : ℝ) :
    angularTransform (monomial β b n) ξ =
      mass (β:ℂ) (b-Complex.I*(ξ:ℂ))*normalized (β:ℂ) (b-Complex.I*(ξ:ℂ)) n := by
  rw [angularTransform_integral]
  have he (x : ℝ) : Complex.exp (-Complex.I*(ξ:ℂ)*(x:ℂ))*monomial β b n x =
      KFCausalShiftedComplexGaussianMoments.moment (β:ℂ) (b-Complex.I*(ξ:ℂ)) n x := by
    unfold monomial KFCausalShiftedComplexGaussianMoments.moment
    rw [mul_left_comm,mul_assoc,← Complex.exp_add]
    congr 2
    ring
  simp_rw [he]
  exact KFCausalShiftedComplexGaussianMoments.value_all (β:ℂ) _ hβ n

def transformedPolynomial (β : ℝ) (b : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C (KFCausalComplexGaussianMoments.gaussianValue (β:ℂ)*
    Complex.exp (b^2/(4*(β:ℂ))))*
    ∑ n ∈ P.support, Polynomial.C (P.coeff n)*
      (momentPolynomial β n).comp (Polynomial.C b-Polynomial.C Complex.I*Polynomial.X)

theorem packet_transform (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (hβ : 0 < β) (ξ : ℝ) :
    angularTransform (packet β b P) ξ =
      packet (1/(4*β)) (-Complex.I*b/(2*(β:ℂ))) (transformedPolynomial β b P) ξ := by
  have he (x : ℝ) : Complex.exp (-Complex.I*(ξ:ℂ)*(x:ℂ))*packet β b P x =
      ∑ n ∈ P.support, P.coeff n*
        (Complex.exp (-Complex.I*(ξ:ℂ)*(x:ℂ))*monomial β b n x) := by
    rw [KFCausalNeutralLinePackets.packet_expansion]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi (n : ℕ) : Integrable (fun x : ℝ => Complex.exp (-Complex.I*(ξ:ℂ)*(x:ℂ))*
      monomial β b n x) := by
    convert KFCausalShiftedComplexGaussianMoments.moment_integrable
      (β:ℂ) (b-Complex.I*(ξ:ℂ)) hβ n using 1
    funext x
    unfold monomial KFCausalShiftedComplexGaussianMoments.moment
    rw [mul_left_comm,mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [angularTransform_integral]
  simp_rw [he]
  rw [integral_finset_sum P.support (fun n _ => (hi n).const_mul (P.coeff n))]
  simp_rw [integral_const_mul,← angularTransform_integral,monomial_transform β b hβ]
  simp only [packet,entire,transformedPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_finset_sum,Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_X,
    momentPolynomial_eval,mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hb : (β:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβ)
  have hex : (b-Complex.I*(ξ:ℂ))^2/(4*(β:ℂ)) =
      -((1/(4*β):ℝ):ℂ)*(ξ:ℂ)^2+(-Complex.I*b/(2*(β:ℂ)))*(ξ:ℂ)+
        b^2/(4*(β:ℂ)) := by
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hex,Complex.exp_add]
  ring

theorem angularTransform_derivative (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (ξ : ℝ) :
    HasDerivAt (angularTransform (packet β b P))
      (-Complex.I*angularTransform (packet β b (Polynomial.X*P)) ξ) ξ := by
  have hf := KFCausalNeutralFourierShift.packet_integrable β hβ b P
  have hx : Integrable (fun x : ℝ => x • packet β b P x) := by
    have hi := KFCausalNeutralFourierShift.packet_integrable β hβ b (Polynomial.X*P)
    convert hi using 1
    funext x
    simp only [Complex.real_smul,packet,entire,Polynomial.eval_mul,Polynomial.eval_X]
    ring
  have hd := (Real.hasDerivAt_fourier hf hx (ξ/(2*Real.pi))).scomp ξ
    ((hasDerivAt_id ξ).div_const (2*Real.pi))
  change HasDerivAt (angularTransform (packet β b P)) _ ξ at hd
  convert hd using 1
  have he : (fun x : ℝ => (-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)) • packet β b P x) =
      fun x => (-2*(Real.pi:ℂ)*Complex.I)*packet β b (Polynomial.X*P) x := by
    funext x
    simp only [smul_eq_mul,packet,entire,Polynomial.eval_mul,Polynomial.eval_X]
    ring
  rw [he,KFCausalGaussianQuarticFourier.fourier_const_mul]
  unfold angularTransform
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.real_smul]
  push_cast
  field_simp

theorem angular_moment_one (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (ξ : ℝ) :
    angularTransform (packet β b (Polynomial.X*P)) ξ =
      Complex.I*packet (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
        (KFCausalNeutralLinePackets.step (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
          (transformedPolynomial β b P)) ξ := by
  have he : angularTransform (packet β b P) =
      packet (1/(4*β)) (-Complex.I*b/(2*(β:ℂ))) (transformedPolynomial β b P) :=
    funext (packet_transform β b P hβ)
  have hd := angularTransform_derivative β b P hβ ξ
  rw [he] at hd
  have hu := hd.unique (KFCausalNeutralLinePackets.packet_derivative _ _ _ ξ)
  rw [← hu]
  ring_nf
  simp [Complex.I_sq]

theorem angular_moment_two (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (ξ : ℝ) :
    angularTransform (packet β b (Polynomial.X^2*P)) ξ =
      -packet (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
        (KFCausalNeutralLinePackets.step (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
          (KFCausalNeutralLinePackets.step (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
            (transformedPolynomial β b P))) ξ := by
  have he : angularTransform (packet β b (Polynomial.X*P)) =
      fun ξ => Complex.I*packet (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
        (KFCausalNeutralLinePackets.step (1/(4*β)) (-Complex.I*b/(2*(β:ℂ)))
          (transformedPolynomial β b P)) ξ := funext (angular_moment_one β b P hβ)
  have hd := angularTransform_derivative β b (Polynomial.X*P) hβ ξ
  rw [he] at hd
  have hu := hd.unique ((KFCausalNeutralLinePackets.packet_derivative _ _ _ ξ).const_mul Complex.I)
  have hx : Polynomial.X*(Polynomial.X*P) = Polynomial.X^2*P := by ring
  rw [hx] at hu
  have hh := congrArg (fun z : ℂ => Complex.I*z) hu
  simpa only [mul_neg,← mul_assoc,Complex.I_mul_I,neg_mul,one_mul,neg_neg] using hh

def gaugeWidth (β h η : ℝ) : ℝ := 1/(4*β)-η^2/(2*h)

theorem gaugeWidth_positive (β h η : ℝ) (hβ : 0 < β) (hh : 0 < h)
    (hfloor : 2*β*η^2 < h) : 0 < gaugeWidth β h η := by
  unfold gaugeWidth
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (by positivity : 0 < 2*h) (by positivity : 0 < 4*β)).mpr
  nlinarith

theorem gauged_packet_transform (β h η : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (ξ : ℝ) :
    (Real.exp (η^2*ξ^2/(2*h)):ℂ)*angularTransform (packet β b P) ξ =
      packet (gaugeWidth β h η) (-Complex.I*b/(2*(β:ℂ)))
        (transformedPolynomial β b P) ξ := by
  rw [packet_transform β b P hβ]
  simp only [packet,entire,Complex.ofReal_exp,← mul_assoc]
  rw [← Complex.exp_add]
  congr 2
  unfold gaugeWidth
  push_cast
  ring

#print axioms momentPolynomial_eval
#print axioms angularTransform_integral
#print axioms monomial_transform
#print axioms packet_transform
#print axioms angularTransform_derivative
#print axioms angular_moment_one
#print axioms angular_moment_two
#print axioms gaugeWidth_positive
#print axioms gauged_packet_transform
end
end UnifiedTheory.Audit.KFCausalNeutralAngularFourierPacket
