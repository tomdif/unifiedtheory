/- Nearby complex translations of a finite neutral profile have a
common Gaussian L2 envelope, also after multiplication by the quartic
weight. The envelope is derived from compactness and Gaussian decay. -/
import UnifiedTheory.Audit.KFCausalNeutralUniformDefect
import UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationEnvelope
noncomputable section
open MeasureTheory
open KFCausalNeutralLinePackets (entire packet)
open KFCausalNeutralLineDomain (family)
open KFCausalQuarticPlaneDomination (potential potential_positive)
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)

def radius (x : ℝ) : ℝ := 1+x^2
def radiusPolynomial (N : ℕ) : Polynomial ℂ := (1+Polynomial.X^2)^N
def gaussianRadius (β : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  (radius x)^N*Real.exp (-(β/2)*x^2)
def sourceCap (β : ℝ) (b z : ℂ) : ℝ :=
  Real.exp ((b-2*(β:ℂ)*z).re^2/(2*β)+(-(β:ℂ)*z^2+b*z).re)

theorem radius_one_le (x : ℝ) : 1 ≤ radius x := by unfold radius; nlinarith [sq_nonneg x]

theorem translated_radius (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (x : ℝ) :
    ‖(x:ℂ)+z‖ ≤ (R+1)*radius x := by
  have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hn := norm_add_le (x:ℂ) z
  rw [Complex.norm_real,Real.norm_eq_abs] at hn
  unfold radius
  nlinarith [mul_nonneg hR (sq_nonneg x)]

theorem radiusPolynomial_eval (N : ℕ) (x : ℝ) :
    (radiusPolynomial N).eval (x:ℂ) = ((radius x)^N:ℝ) := by
  simp [radiusPolynomial,radius]

theorem gaussianRadius_eq (β : ℝ) (N : ℕ) (x : ℝ) :
    gaussianRadius β N x = ‖packet (β/2) 0 (radiusPolynomial N) x‖ := by
  unfold packet entire
  rw [norm_mul,radiusPolynomial_eval,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by unfold radius; positivity) N),Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_im,Complex.add_re,zero_mul,Complex.zero_re]
  simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,add_zero]
  unfold gaussianRadius
  ring

theorem gaussianRadius_memLp (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    MemLp (gaussianRadius β N) 2 volume := by
  change MemLp (fun x => gaussianRadius β N x) 2 volume
  simpa only [gaussianRadius_eq] using
    (KFCausalNeutralLinePackets.packet_memLp (β/2) (by positivity) 0 (radiusPolynomial N)).norm

theorem weighted_gaussianRadius_memLp (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    MemLp (fun x => potential x*gaussianRadius β N x) 2 volume := by
  have hm := (KFCausalNeutralLineDomain.packet_regular (β/2) (by positivity) 0 (radiusPolynomial N)
    (KFCausalNeutralLineDomain.weightPolynomial 0)).norm
  change MemLp (fun x : ℝ => ‖(KFCausalNeutralLineDomain.weightPolynomial 0).eval (x:ℂ)*
    packet (β/2) 0 (radiusPolynomial N) x‖) 2 volume at hm
  simpa only [KFCausalNeutralLineDomain.weight_eval,KFCausalNeutralLineDomain.weight,
    Matrix.cons_val_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (potential_positive _),← gaussianRadius_eq] using hm

theorem exponential_bound (β : ℝ) (hβ : 0 < β) (b z : ℂ) (x : ℝ) :
    ‖Complex.exp (-(β:ℂ)*((x:ℂ)+z)^2+b*((x:ℂ)+z))‖ ≤
      sourceCap β b z*Real.exp (-(β/2)*x^2) := by
  have he : (-(β:ℂ)*((x:ℂ)+z)^2+b*((x:ℂ)+z)).re =
      -β*x^2+(b-2*(β:ℂ)*z).re*x+(-(β:ℂ)*z^2+b*z).re := by
    simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.neg_re,Complex.neg_im,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat]
    ring
  rw [Complex.norm_exp,he]
  unfold sourceCap
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb := KFCausalNeutralLinePackets.source_exponent_bound β hβ (b-2*(β:ℂ)*z).re x
  linarith

theorem packet_envelope (β : ℝ) (hβ : 0 < β) (b : ℂ) (P : Polynomial ℂ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ → ℝ, (∀ x, 0 ≤ A x) ∧ MemLp A 2 volume ∧
      MemLp (fun x => potential x*A x) 2 volume ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ x : ℝ, ‖entire β b P ((x:ℂ)+z)‖ ≤ A x := by
  have hc : Continuous (sourceCap β b) := by unfold sourceCap; fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  let C := |M| * evalCap P (R+1)
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg M) (evalCap_nonnegative P _ (by linarith))
  refine ⟨fun x => C*gaussianRadius β P.natDegree x, ?_,
    (gaussianRadius_memLp β hβ P.natDegree).const_mul C, ?_, ?_⟩
  · intro x
    unfold gaussianRadius radius
    positivity
  · simpa only [mul_left_comm] using (weighted_gaussianRadius_memLp β hβ P.natDegree).const_mul C
  · intro z hz x
    have hm : sourceCap β b z ≤ |M| := by
      have hb := hM z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
      have hb' : |sourceCap β b z| ≤ M := by simpa only [Real.norm_eq_abs] using hb
      exact (le_abs_self _).trans (hb'.trans (le_abs_self M))
    have hp := eval_bound P (R+1) (radius x) (by linarith) (radius_one_le x)
      ((x:ℂ)+z) (translated_radius R hR z hz x)
    unfold entire
    rw [norm_mul]
    have he := (exponential_bound β hβ b z x).trans
      (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le)
    have hh := mul_le_mul he hp (norm_nonneg _) (by positivity : 0 ≤ |M| * Real.exp (-(β/2)*x^2))
    convert hh using 1
    unfold C gaussianRadius
    ring

theorem family_envelope (n : ℕ) (β : ℝ) (hβ : 0 < β) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ A : ℝ → ℝ, (∀ x, 0 ≤ A x) ∧ MemLp A 2 volume ∧
      MemLp (fun x => potential x*A x) 2 volume ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ x : ℝ, ‖family n β b c P ((x:ℂ)+z)‖ ≤ A x := by
  choose A hA hLp hVLp hbound using fun i => packet_envelope β hβ (b i) (P i) R hR
  refine ⟨fun x => ∑ i, ‖c i‖*A i x, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hA i x))
  · exact memLp_finset_sum Finset.univ (fun i _ => (hLp i).const_mul ‖c i‖)
  · simpa only [Finset.mul_sum,mul_left_comm] using
      memLp_finset_sum Finset.univ (fun i _ => (hVLp i).const_mul ‖c i‖)
  · intro z hz x
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound i z hz x) (norm_nonneg _)

#print axioms radius_one_le
#print axioms translated_radius
#print axioms radiusPolynomial_eval
#print axioms gaussianRadius_eq
#print axioms gaussianRadius_memLp
#print axioms weighted_gaussianRadius_memLp
#print axioms exponential_bound
#print axioms packet_envelope
#print axioms family_envelope
end
end UnifiedTheory.Audit.KFCausalNeutralTranslationEnvelope
