/- Exact neutral Fourier contour translation for arbitrary finite
Gaussian exponential-polynomial families. All strip envelopes and L1
hypotheses are derived; the multiplier uses the actual 2*pi convention. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationEnvelope
import UnifiedTheory.Audit.KFCausalLocalStripContour

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierShift
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralLinePackets (entire packet monomial translatedPolynomial)
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralTranslationEnvelope (radius sourceCap)
open KFCausalGaussianContourShift (horizontal)
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)

theorem packet_integrable (β : ℝ) (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ) :
    Integrable (packet β b P) := by
  have hi := integrable_finset_sum P.support (fun j _ =>
    (KFCausalNeutralLinePackets.monomial_integrable β hβ b j).const_mul (P.coeff j))
  change Integrable (fun x => packet β b P x)
  simpa only [KFCausalNeutralLinePackets.packet_expansion] using hi

theorem translated_integrable (β : ℝ) (hβ : 0 < β) (b z : ℂ) (P : Polynomial ℂ) :
    Integrable (fun x : ℝ => entire β b P ((x:ℂ)+z)) := by
  simp_rw [KFCausalNeutralLinePackets.translated_packet]
  exact packet_integrable β hβ _ _

theorem polynomial_translated_integrable (β : ℝ) (hβ : 0 < β) (b z : ℂ) (P Q : Polynomial ℂ) :
    Integrable (fun x : ℝ => Q.eval (x:ℂ)*entire β b P ((x:ℂ)+z)) := by
  simp_rw [KFCausalNeutralLinePackets.translated_packet,KFCausalNeutralLinePackets.packet_polynomial]
  exact packet_integrable β hβ _ _

theorem family_polynomial_integrable (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z : ℂ) (Q : Polynomial ℂ) :
    Integrable (fun x : ℝ => Q.eval (x:ℂ)*family n β b c P ((x:ℂ)+z)) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    (polynomial_translated_integrable β hβ (b i) z (P i) Q).const_mul (c i))
  simpa only [family,Finset.mul_sum,mul_left_comm] using hi

theorem radius_power_bound (a : ℝ) (ha : 0 < a) (N : ℕ) (x : ℝ) :
    (radius x)^N ≤ ((N.factorial:ℝ)/a^N)*Real.exp (a*radius x) := by
  have hr : 0 ≤ radius x := by unfold radius; positivity
  have hn : (0:ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have he := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp (a*radius x) (mul_nonneg ha.le hr) N)
  rw [mul_pow] at he
  have ht : (radius x)^N ≤ (Real.exp (a*radius x)*(N.factorial:ℝ))/a^N := by
    apply (le_div_iff₀ (pow_pos ha N)).mpr
    simpa only [mul_comm] using he
  convert ht using 1
  ring

theorem packet_strip_bound (β : ℝ) (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ, |y| ≤ R →
      ‖horizontal (entire β b P) y x‖ ≤ B*Real.exp (-(β/4)*x^2) := by
  have hc : Continuous (sourceCap β b) := by unfold sourceCap; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  let C := |M| *evalCap P (R+1)
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg M) (evalCap_nonnegative P _ (by linarith))
  let K := (P.natDegree.factorial:ℝ)/(β/4)^P.natDegree
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨C*K*Real.exp (β/4),by positivity,?_⟩
  intro x y hy
  let z : ℂ := (y:ℂ)*Complex.I
  have hz : ‖z‖ ≤ R := by simpa only [z,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] using hy
  have hm : sourceCap β b z ≤ |M| := by
    have hb := hM z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    have hb' : |sourceCap β b z| ≤ M := by simpa only [Real.norm_eq_abs] using hb
    exact (le_abs_self _).trans (hb'.trans (le_abs_self M))
  have hp := eval_bound P (R+1) (radius x) (by linarith)
    (KFCausalNeutralTranslationEnvelope.radius_one_le x) ((x:ℂ)+z)
    (KFCausalNeutralTranslationEnvelope.translated_radius R hR z hz x)
  have he := (KFCausalNeutralTranslationEnvelope.exponential_bound β hβ b z x).trans
    (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le)
  have hprod := mul_le_mul he hp (norm_nonneg _) (by positivity : 0 ≤ |M| *Real.exp (-(β/2)*x^2))
  have hpow := radius_power_bound (β/4) (by positivity) P.natDegree x
  have hlast := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (Real.exp_pos (-(β/2)*x^2)).le)
  have hexp : Real.exp (-(β/2)*x^2)*Real.exp ((β/4)*radius x) =
      Real.exp (β/4)*Real.exp (-(β/4)*x^2) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    unfold radius
    ring
  change ‖Complex.exp (-(β:ℂ)*((x:ℂ)+z)^2+b*((x:ℂ)+z))*P.eval ((x:ℂ)+z)‖ ≤ _
  rw [norm_mul]
  apply hprod.trans
  calc
    _ = C*Real.exp (-(β/2)*x^2)*(radius x)^P.natDegree := by dsimp only [C]; ring
    _ ≤ C*Real.exp (-(β/2)*x^2)*((P.natDegree.factorial:ℝ)/(β/4)^P.natDegree*
        Real.exp ((β/4)*radius x)) := hlast
    _ = C*K*(Real.exp (-(β/2)*x^2)*Real.exp ((β/4)*radius x)) := by dsimp only [K]; ring
    _ = _ := by rw [hexp]; ring

theorem family_strip_bound (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : ℝ, |y| ≤ R →
      ‖horizontal (family n β b c P) y x‖ ≤ B*Real.exp (-(β/4)*x^2) := by
  choose B hB hb using fun i => packet_strip_bound β hβ (b i) (P i) R hR
  refine ⟨∑ i, ‖c i‖*B i,Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hB i)),?_⟩
  intro x y hy
  change ‖∑ i, c i*entire β (b i) (P i) ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ _
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb i x y hy) (norm_nonneg _)

def line (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (y : ℝ) : ℝ → ℂ :=
  horizontal (family n β b c P) y

theorem line_integrable (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (y : ℝ) :
    Integrable (line n β b c P y) := by
  simpa only [line,horizontal,Polynomial.eval_one,one_mul] using
    family_polynomial_integrable n β hβ b c P ((y:ℂ)*Complex.I) 1

theorem line_memLp (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (y : ℝ) :
    MemLp (line n β b c P y) 2 volume :=
  KFCausalNeutralLineDomain.regular_memLp _
    (KFCausalNeutralLineDomain.family_regular n β hβ b c P ((y:ℂ)*Complex.I))

theorem fourier_shift (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (y k : ℝ) :
    (𝓕 (line n β b c P y)) k =
      (Real.exp (-2*Real.pi*k*y):ℂ)*(𝓕 (line n β b c P 0)) k := by
  obtain ⟨B,_,hB⟩ := family_strip_bound n β hβ b c P |y| (abs_nonneg y)
  have he := KFCausalLocalStripContour.fourier_shift_strip (family n β b c P) (β/4) B y
    (fun z _ => (KFCausalNeutralLineDomain.family_derivative n β b c P z).differentiableAt)
    (by positivity) hB k
  have hm := congrArg (fun z : ℂ => (Real.exp (-2*Real.pi*k*y):ℂ)*z) he
  have hc : (Real.exp (-2*Real.pi*k*y):ℂ)*(Real.exp (2*Real.pi*k*y):ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    ring_nf
    simp
  simpa only [line,← mul_assoc,hc,one_mul] using hm.symm

#print axioms packet_integrable
#print axioms translated_integrable
#print axioms polynomial_translated_integrable
#print axioms family_polynomial_integrable
#print axioms radius_power_bound
#print axioms packet_strip_bound
#print axioms family_strip_bound
#print axioms line_integrable
#print axioms line_memLp
#print axioms fourier_shift
end
end UnifiedTheory.Audit.KFCausalNeutralFourierShift
