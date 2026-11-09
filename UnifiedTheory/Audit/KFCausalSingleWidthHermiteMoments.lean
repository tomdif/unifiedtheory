/- Gaussian Hermite moments for the linked neutral field channels at one
charged width. The frequency integration retains the covariant derivative;
independent pointwise jets are not assigned an uncertainty inequality. -/
import UnifiedTheory.Audit.KFCausalComplexGaussianMoments
import UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSingleWidthHermiteMoments
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLinePackets (packet step)
open KFCausalNeutralLineDomain

def gaussianMass (h : ℝ) : ℝ := Real.sqrt (Real.pi/h)
def variance (h L η : ℝ) : ℝ := (L^2+η^2)/(2*h)
def slope (L η : ℝ) : ℂ := (L:ℂ)-Complex.I*(η:ℂ)

private theorem moment_re (h : ℝ) (hh : 0 < h) (n : ℕ) :
    (KFCausalComplexGaussianMoments.value (h:ℂ) n).re =
      ∫ x : ℝ, x^n*Real.exp (-h*x^2) := by
  have hr : (∫ x, KFCausalComplexGaussianMoments.moment (h:ℂ) n x).re =
      ∫ x, (KFCausalComplexGaussianMoments.moment (h:ℂ) n x).re :=
    (integral_re (KFCausalComplexGaussianMoments.moment_integrable (h:ℂ) hh n)).symm
  unfold KFCausalComplexGaussianMoments.value
  rw [hr]
  apply integral_congr_ae
  filter_upwards [] with x
  have he : -(h:ℂ)*(x:ℂ)^2 = ((-h*x^2:ℝ):ℂ) := by push_cast; ring
  unfold KFCausalComplexGaussianMoments.moment
  rw [he,← Complex.ofReal_exp,← Complex.ofReal_pow,← Complex.ofReal_mul]
  rfl

private theorem real_moments (h : ℝ) (hh : 0 < h) (n : Fin 5) :
    (∫ x : ℝ, x^(n:ℕ)*Real.exp (-h*x^2)) =
      gaussianMass h * ![1,0,1/(2*h),0,3/(4*h^2)] n := by
  have h0 : (KFCausalComplexGaussianMoments.value (h:ℂ) 0).re = gaussianMass h := by
    rw [moment_re h hh]
    simp only [pow_zero,one_mul,gaussianMass,integral_gaussian]
  have h2 := congrArg Complex.re (KFCausalComplexGaussianMoments.recurrence (h:ℂ) hh 0)
  have h4 := congrArg Complex.re (KFCausalComplexGaussianMoments.recurrence (h:ℂ) hh 2)
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,zero_mul,sub_zero,Nat.cast_zero,Nat.cast_ofNat,zero_add,
    one_mul,Complex.one_re,Complex.one_im,add_zero] at h2 h4
  rw [h0] at h2
  have hm2 : (KFCausalComplexGaussianMoments.value (h:ℂ) 2).re = gaussianMass h/(2*h) := by
    apply (eq_div_iff (by positivity : 2*h ≠ 0)).mpr
    nlinarith only [h2]
  have hm4 : (KFCausalComplexGaussianMoments.value (h:ℂ) 4).re = 3*gaussianMass h/(4*h^2) := by
    rw [hm2] at h4
    apply (eq_div_iff (by positivity : 4*h^2 ≠ 0)).mpr
    have ht := congrArg (fun z : ℝ => z*(2*h)) h4
    field_simp at ht
    nlinarith only [ht]
  fin_cases n
  · change (∫ x : ℝ, x^0*Real.exp (-h*x^2)) = gaussianMass h*1
    simpa only [moment_re h hh,mul_one] using h0
  · change (∫ x : ℝ, x^1*Real.exp (-h*x^2)) = gaussianMass h*0
    rw [← moment_re h hh,KFCausalComplexGaussianMoments.value_one (h:ℂ) hh]
    simp
  · change (∫ x : ℝ, x^2*Real.exp (-h*x^2)) = gaussianMass h*(1/(2*h))
    simpa only [moment_re h hh,div_eq_mul_inv,one_mul] using hm2
  · change (∫ x : ℝ, x^3*Real.exp (-h*x^2)) = gaussianMass h*0
    rw [← moment_re h hh,KFCausalComplexGaussianMoments.value_three (h:ℂ) hh]
    simp
  · change (∫ x : ℝ, x^4*Real.exp (-h*x^2)) = gaussianMass h*(3/(4*h^2))
    rw [← moment_re h hh,hm4]
    ring

private theorem quadratic_norm_integral (h : ℝ) (hh : 0 < h) (A B C : ℂ) :
    (∫ x : ℝ, Real.exp (-h*x^2)*‖A+B*(x:ℂ)+C*(x:ℂ)^2‖^2) =
      gaussianMass h*(‖A‖^2+(‖B‖^2+2*(conj A*C).re)/(2*h)+
        3*‖C‖^2/(4*h^2)) := by
  let d : Fin 5 → ℝ := ![‖A‖^2,2*(conj A*B).re,
    ‖B‖^2+2*(conj A*C).re,2*(conj B*C).re,‖C‖^2]
  have he (x : ℝ) : Real.exp (-h*x^2)*‖A+B*(x:ℂ)+C*(x:ℂ)^2‖^2 =
      ∑ n : Fin 5, d n*(x^(n:ℕ)*Real.exp (-h*x^2)) := by
    simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    simp only [Complex.sq_norm,Complex.normSq_apply]
    simp only [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
    ring
  simp_rw [he]
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (KFCausalPolynomialGaussianIntegrals.scalar_moment_integrable h hh n.val).const_mul (d n))]
  simp_rw [integral_const_mul,real_moments h hh]
  simp only [d,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,mul_zero,zero_add,add_zero,mul_one]
  ring

theorem hermite_norm_integral (h : ℝ) (hh : 0 < h) (A B C : ℂ) :
    (∫ x : ℝ, Real.exp (-h*x^2)*
      ‖A+B*(x:ℂ)+C*((x:ℂ)^2-(1/(2*h):ℝ))‖^2) =
      gaussianMass h*(‖A‖^2+‖B‖^2/(2*h)+‖C‖^2/(2*h^2)) := by
  have he (x : ℝ) : A+B*(x:ℂ)+C*((x:ℂ)^2-(1/(2*h):ℝ)) =
      (A-(1/(2*h):ℝ)*C)+B*(x:ℂ)+C*(x:ℂ)^2 := by ring
  simp_rw [he]
  rw [quadratic_norm_integral h hh]
  congr 1
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  field_simp
  ring

theorem first_channel_integral (h L η : ℝ) (hh : 0 < h) (g x : ℂ) :
    (∫ t : ℝ, Real.exp (-h*t^2)*‖x+slope L η*(t:ℂ)*g‖^2) =
      gaussianMass h*(‖x‖^2+variance h L η*‖g‖^2) := by
  have he := hermite_norm_integral h hh x (slope L η*g) 0
  simp only [zero_mul,add_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),
    zero_div,add_zero] at he
  convert he using 1
  · congr 1
    funext t
    congr 2
    ring
  · unfold variance slope
    simp only [norm_mul,mul_pow,Complex.sq_norm,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    ring

theorem second_channel_integral (h L η : ℝ) (hh : 0 < h) (g x y : ℂ) :
    (∫ t : ℝ, Real.exp (-h*t^2)*
      ‖y+(variance h L η:ℂ)*g+2*slope L η*(t:ℂ)*x+
        (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*g‖^2) =
      gaussianMass h*(‖y+(variance h L η:ℂ)*g‖^2+
        4*variance h L η*‖x‖^2+2*(variance h L η)^2*‖g‖^2) := by
  have he := hermite_norm_integral h hh (y+(variance h L η:ℂ)*g)
    (2*slope L η*x) ((slope L η)^2*g)
  convert he using 1
  · congr 1
    funext t
    congr 2
    ring
  · have hs : ‖slope L η‖^2=L^2+η^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp only [slope,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
      ring
    rw [norm_mul,norm_mul,norm_mul,norm_pow]
    rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    rw [mul_pow,mul_pow,mul_pow,hs]
    unfold variance
    ring

def covariantStep (β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C Complex.I*step β b P-Polynomial.C (c:ℂ)*Polynomial.X*P

private theorem covariant_packet (β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ) (k : ℝ) :
    packet β b (covariantStep β b c P) k =
      Complex.I*packet β b (step β b P) k-(c:ℂ)*(k:ℂ)*packet β b P k := by
  simp only [packet,KFCausalNeutralLinePackets.entire,covariantStep,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  ring

private theorem cross_integrable (β : ℝ) (b : ℂ) (P Q : Polynomial ℂ) (hβ : 0 < β) :
    Integrable (fun k => conj (packet β b P k)*packet β b Q k) := by
  simpa only [Polynomial.eval_one,one_mul] using
    polynomial_cross_integrable _ _ (packet_regular β hβ b P) (packet_regular β hβ b Q) 1

private theorem packet_norm_integrable (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (hβ : 0 < β) :
    Integrable (fun k => ‖packet β b P k‖^2) :=
  (memLp_two_iff_integrable_sq_norm
    (KFCausalNeutralLinePackets.packet_memLp β hβ b P).aestronglyMeasurable).mp
      (KFCausalNeutralLinePackets.packet_memLp β hβ b P)

theorem covariant_symmetric (β : ℝ) (b : ℂ) (c : ℝ) (P Q : Polynomial ℂ)
    (hβ : 0 < β) :
    (∫ k, conj (packet β b P k)*packet β b (covariantStep β b c Q) k) =
      ∫ k, conj (packet β b (covariantStep β b c P) k)*packet β b Q k := by
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun k => (KFCausalNeutralLinePackets.packet_derivative β b P k).star)
    (KFCausalNeutralLinePackets.packet_derivative β b Q)
    (cross_integrable β b P (step β b Q) hβ)
    (cross_integrable β b (step β b P) Q hβ)
    (cross_integrable β b P Q hβ)
  have hk : Integrable (fun k : ℝ => (k:ℂ)*(conj (packet β b P k)*packet β b Q k)) := by
    simpa only [Polynomial.eval_X] using polynomial_cross_integrable _ _
      (packet_regular β hβ b P) (packet_regular β hβ b Q) Polynomial.X
  have hl (k : ℝ) : conj (packet β b P k)*packet β b (covariantStep β b c Q) k =
      Complex.I*(conj (packet β b P k)*packet β b (step β b Q) k)-
        (c:ℂ)*((k:ℂ)*(conj (packet β b P k)*packet β b Q k)) := by
    rw [covariant_packet]
    ring
  have hr (k : ℝ) : conj (packet β b (covariantStep β b c P) k)*packet β b Q k =
      -Complex.I*(conj (packet β b (step β b P) k)*packet β b Q k)-
        (c:ℂ)*((k:ℂ)*(conj (packet β b P k)*packet β b Q k)) := by
    rw [covariant_packet]
    simp only [map_sub,map_mul,Complex.conj_I,Complex.conj_ofReal]
    ring
  simp_rw [hl,hr]
  rw [integral_sub ((cross_integrable β b P (step β b Q) hβ).const_mul Complex.I)
      (hk.const_mul (c:ℂ)),
    integral_sub ((cross_integrable β b (step β b P) Q hβ).const_mul (-Complex.I))
      (hk.const_mul (c:ℂ))]
  simp only [integral_const_mul]
  change (∫ k, conj (packet β b P k)*packet β b (step β b Q) k) =
    -(∫ k, conj (packet β b (step β b P) k)*packet β b Q k) at hi
  rw [hi]
  ring

def firstEnergy (h L η β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ) : ℝ :=
  ∫ k, ∫ t : ℝ, Real.exp (-h*t^2)*
    ‖packet β b (covariantStep β b c P) k+slope L η*(t:ℂ)*packet β b P k‖^2

def secondEnergy (h L η β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ) : ℝ :=
  ∫ k, ∫ t : ℝ, Real.exp (-h*t^2)*
    ‖packet β b (covariantStep β b c (covariantStep β b c P)) k+
      (variance h L η:ℂ)*packet β b P k+
      2*slope L η*(t:ℂ)*packet β b (covariantStep β b c P) k+
      (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*packet β b P k‖^2

theorem linked_first_identity (h L η β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) :
    firstEnergy h L η β b c P = gaussianMass h*
      ((∫ k, ‖packet β b (covariantStep β b c P) k‖^2)+
        variance h L η*(∫ k, ‖packet β b P k‖^2)) := by
  unfold firstEnergy
  simp_rw [first_channel_integral h L η hh]
  rw [integral_const_mul,integral_add (packet_norm_integrable β b _ hβ)
    ((packet_norm_integrable β b P hβ).const_mul (variance h L η)),integral_const_mul]

theorem linked_second_identity (h L η β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) :
    secondEnergy h L η β b c P = gaussianMass h*
      ((∫ k, ‖packet β b (covariantStep β b c (covariantStep β b c P)) k‖^2)+
        6*variance h L η*(∫ k, ‖packet β b (covariantStep β b c P) k‖^2)+
        3*(variance h L η)^2*(∫ k, ‖packet β b P k‖^2)) := by
  let Q := covariantStep β b c P
  let R := covariantStep β b c Q
  have hs := covariant_symmetric β b c P Q hβ
  have hsre : (∫ k, (conj (packet β b P k)*packet β b R k).re) =
      ∫ k, ‖packet β b Q k‖^2 := by
    have hr : (∫ k, conj (packet β b P k)*packet β b R k).re =
        ∫ k, (conj (packet β b P k)*packet β b R k).re :=
      (integral_re (cross_integrable β b P R hβ)).symm
    rw [← hr]
    change (∫ k, conj (packet β b P k)*packet β b (covariantStep β b c Q) k).re = _
    rw [hs]
    have hi := integral_re (cross_integrable β b Q Q hβ)
    simpa only [Q,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re] using hi.symm
  have he (k : ℝ) : ‖packet β b R k+(variance h L η:ℂ)*packet β b P k‖^2 =
      ‖packet β b R k‖^2+2*variance h L η*(conj (packet β b P k)*packet β b R k).re+
        (variance h L η)^2*‖packet β b P k‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im]
    ring
  unfold secondEnergy
  simp_rw [second_channel_integral h L η hh]
  change (∫ k, gaussianMass h*(‖packet β b R k+(variance h L η:ℂ)*packet β b P k‖^2+
    4*variance h L η*‖packet β b Q k‖^2+2*(variance h L η)^2*‖packet β b P k‖^2)) = _
  simp_rw [he]
  have hi0 := packet_norm_integrable β b P hβ
  have hi1 := packet_norm_integrable β b Q hβ
  have hi2 := packet_norm_integrable β b R hβ
  have hix : Integrable (fun k => (conj (packet β b P k)*packet β b R k).re) :=
    (cross_integrable β b P R hβ).re
  have hs1 := integral_add hi2 (hix.const_mul (2*variance h L η))
  have hs2 := integral_add (hi2.add (hix.const_mul (2*variance h L η)))
    (hi0.const_mul ((variance h L η)^2))
  have hs3 := integral_add ((hi2.add (hix.const_mul (2*variance h L η))).add
    (hi0.const_mul ((variance h L η)^2))) (hi1.const_mul (4*variance h L η))
  have hs4 := integral_add (((hi2.add (hix.const_mul (2*variance h L η))).add
    (hi0.const_mul ((variance h L η)^2))).add (hi1.const_mul (4*variance h L η)))
    (hi0.const_mul (2*(variance h L η)^2))
  simp only [Pi.add_apply] at hs1 hs2 hs3 hs4
  rw [integral_const_mul,hs4,hs3,hs2,hs1]
  simp only [integral_const_mul,hsre]
  change gaussianMass h*((∫ k, ‖packet β b R k‖^2)+
    2*variance h L η*(∫ k, ‖packet β b Q k‖^2)+
    (variance h L η)^2*(∫ k, ‖packet β b P k‖^2)+
    4*variance h L η*(∫ k, ‖packet β b Q k‖^2)+
    2*(variance h L η)^2*(∫ k, ‖packet β b P k‖^2)) = _
  dsimp only [R,Q]
  ring

theorem linked_second_lower (h L η β : ℝ) (b : ℂ) (c : ℝ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) :
    3*variance h L η*firstEnergy h L η β b c P ≤ secondEnergy h L η β b c P := by
  rw [linked_first_identity h L η β b c P hh hβ,linked_second_identity h L η β b c P hh hβ]
  have h0 : 0 ≤ gaussianMass h := Real.sqrt_nonneg _
  have hv : 0 ≤ variance h L η := by unfold variance; positivity
  have h1 : 0 ≤ ∫ k, ‖packet β b (covariantStep β b c P) k‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have h2 : 0 ≤ ∫ k, ‖packet β b (covariantStep β b c (covariantStep β b c P)) k‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  nlinarith [mul_nonneg h0 h2,mul_nonneg h0 (mul_nonneg hv h1)]

/-- Exact polynomial normalization after completing the tilted Gaussian
square. Here g1 and g2 denote ordinary frequency derivatives of g0 when
this algebraic identity is applied to a genuine profile. -/
theorem gauged_channel_identities (h L η k t : ℝ) (g0 g1 g2 : ℂ) (hh : h ≠ 0) :
    let q := η^2/h
    let d := L*η/h
    let v := t-η*k/h
    let X1 := Complex.I*g1-(d:ℂ)*(k:ℂ)*g0
    let X2 := -g2-2*Complex.I*(d:ℂ)*(k:ℂ)*g1-
      Complex.I*(d:ℂ)*g0+(d:ℂ)^2*(k:ℂ)^2*g0
    (Complex.I*g1-Complex.I*(q:ℂ)*(k:ℂ)*g0+slope L η*(v:ℂ)*g0 =
      X1+slope L η*(t:ℂ)*g0) ∧
    (-g2+2*(q:ℂ)*(k:ℂ)*g1+(q:ℂ)*g0-(q:ℂ)^2*(k:ℂ)^2*g0+
      2*slope L η*(v:ℂ)*(Complex.I*g1-Complex.I*(q:ℂ)*(k:ℂ)*g0)+
      (slope L η)^2*(v:ℂ)^2*g0 =
      X2+(variance h L η:ℂ)*g0+2*slope L η*(t:ℂ)*X1+
        (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*g0) := by
  dsimp only
  constructor <;> apply Complex.ext <;>
    simp only [slope,variance,pow_two,Complex.add_re,Complex.add_im,Complex.sub_re,
      Complex.sub_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.re_ofNat,Complex.im_ofNat] <;>
    field_simp [hh] <;> ring

#print axioms hermite_norm_integral
#print axioms first_channel_integral
#print axioms second_channel_integral
#print axioms covariant_symmetric
#print axioms linked_first_identity
#print axioms linked_second_identity
#print axioms linked_second_lower
#print axioms gauged_channel_identities
end
end UnifiedTheory.Audit.KFCausalSingleWidthHermiteMoments
