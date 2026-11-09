/- Genuine simultaneous charged-width and neutral-source differences.
The coefficients use the harmless common phase (-1)^n relative to the
forward-difference convention. No width-uniform response bound is asserted. -/
import UnifiedTheory.Audit.KFCausalClusteredClockFactors
import UnifiedTheory.Audit.KFCausalGaussianSourceKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceProfiles
noncomputable section
open Filter
open scoped Topology
open KFCausalClusteredWidthProfiles (quotient)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalWedgeLaplace (laplaceSum)

def widths (n : ℕ) (w0 δ : ℝ) (i : Fin (n+1)) : ℝ := w0+(i.val:ℝ)*δ
def sources (n : ℕ) (δ : ℝ) (b ℓ : ℂ) (i : Fin (n+1)) : ℂ :=
  b+(i.val:ℂ)*(δ:ℂ)*ℓ
def coefficients (n : ℕ) (w0 δ : ℝ) (i : Fin (n+1)) : ℂ :=
  ((-1:ℂ)^i.val*(n.choose i.val:ℂ))/(δ:ℂ)^n/(widths n w0 δ i:ℂ)

theorem widths_admissible (n : ℕ) (w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 ≤ δ)
    (i : Fin (n+1)) : 1 ≤ widths n w0 δ i := by
  unfold widths
  have hp : 0 ≤ (i.val:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ
  linarith

theorem profileSum_exact (n : ℕ) (w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 < δ)
    (b ℓ z ζ : ℂ) (P : Polynomial ℂ) :
    profileSum (n+1) (widths n w0 δ) (coefficients n w0 δ)
      (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) z ζ =
      Complex.exp (-(w0:ℂ)*z+b*ζ)*quotient δ (z-ℓ*ζ)^n*P.eval ζ := by
  have hw (i : Fin (n+1)) : (widths n w0 δ i:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one
      (widths_admissible n w0 δ hw0 hδ.le i)))
  have he (i : Fin (n+1)) :
      Complex.exp (sources n δ b ℓ i*ζ)*Complex.exp (-(widths n w0 δ i:ℂ)*z) =
        Complex.exp (-(w0:ℂ)*z+b*ζ)*Complex.exp (-(δ:ℂ)*(z-ℓ*ζ))^i.val := by
    rw [← Complex.exp_nat_mul,← Complex.exp_add,← Complex.exp_add]
    congr 1
    unfold sources widths
    push_cast
    ring
  have hb : ∑ i : Fin (n+1), (-1:ℂ)^i.val*(n.choose i.val:ℂ)*
      Complex.exp (-(δ:ℂ)*(z-ℓ*ζ))^i.val =
        (1-Complex.exp (-(δ:ℂ)*(z-ℓ*ζ)))^n := by
    rw [show (1:ℂ)-Complex.exp (-(δ:ℂ)*(z-ℓ*ζ)) =
      -Complex.exp (-(δ:ℂ)*(z-ℓ*ζ))+1 by ring,add_pow,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (-Complex.exp (-(δ:ℂ)*(z-ℓ*ζ)))^i.val =
      (-1:ℂ)^i.val*Complex.exp (-(δ:ℂ)*(z-ℓ*ζ))^i.val from neg_pow _ _]
    simp only [one_pow,mul_one]
    ring
  unfold profileSum laplaceSum exponentialProfile coefficients
  simp only [one_mul]
  calc
    _ = Complex.exp (-(w0:ℂ)*z+b*ζ)/(δ:ℂ)^n*P.eval ζ *
        ∑ i : Fin (n+1), (-1:ℂ)^i.val*(n.choose i.val:ℂ)*
          Complex.exp (-(δ:ℂ)*(z-ℓ*ζ))^i.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show ((((-1:ℂ)^i.val*(n.choose i.val:ℂ))/(δ:ℂ)^n/
          (widths n w0 δ i:ℂ)*
          (Complex.exp (sources n δ b ℓ i*ζ)*P.eval ζ))*(widths n w0 δ i:ℂ))*
          Complex.exp (-(widths n w0 δ i:ℂ)*z) =
        (((-1:ℂ)^i.val*(n.choose i.val:ℂ))/(δ:ℂ)^n)*P.eval ζ*
          (Complex.exp (sources n δ b ℓ i*ζ)*Complex.exp (-(widths n w0 δ i:ℂ)*z)) by
            field_simp [hw i]]
      rw [he]
      ring
    _ = _ := by rw [hb]; unfold quotient; rw [div_pow]; ring

theorem profileSum_tendsto (n : ℕ) (w0 : ℝ) (hw0 : 1 ≤ w0)
    (b ℓ z ζ : ℂ) (P : Polynomial ℂ) :
    Tendsto (fun δ : ℝ => profileSum (n+1) (widths n w0 δ) (coefficients n w0 δ)
      (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) z ζ) (𝓝[>] 0)
      (𝓝 (Complex.exp (-(w0:ℂ)*z+b*ζ)*(z-ℓ*ζ)^n*P.eval ζ)) := by
  apply Tendsto.congr' _
    ((((KFCausalClusteredWidthProfiles.quotient_tendsto (z-ℓ*ζ)).pow n).const_mul
      (Complex.exp (-(w0:ℂ)*z+b*ζ))).mul_const (P.eval ζ))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (profileSum_exact n w0 δ hw0 hδ b ℓ z ζ P).symm

theorem quotient_norm_bound (δ : ℝ) (z : ℂ) (M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hz : -z.re ≤ M) :
    ‖quotient δ z‖ ≤ ‖z‖*Real.exp (δ*M) := by
  have hd (t : ℝ) (_ : t ∈ Set.Icc 0 δ) : HasDerivWithinAt
      (fun u : ℝ => Complex.exp (-(u:ℂ)*z))
      (Complex.exp (-(t:ℂ)*z)*(-z)) (Set.Icc 0 δ) t :=
    (KFCausalClusteredWidthProfiles.exponential_derivative z t).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Set.Ico 0 δ) :
      ‖Complex.exp (-(t:ℂ)*z)*(-z)‖ ≤ ‖z‖*Real.exp (δ*M) := by
    rw [norm_mul,norm_neg,Complex.norm_exp]
    have he : (-(t:ℂ)*z).re ≤ δ*M := by
      simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
        Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hz),mul_nonneg (sub_nonneg.mpr ht.2.le) hM]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (norm_nonneg z)).trans_eq (mul_comm _ _)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb δ (Set.right_mem_Icc.mpr hδ.le)
  simp only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,sub_zero] at hm
  rw [quotient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  simpa only [norm_sub_rev] using hm

theorem joint_quotient_norm_bound (δ : ℝ) (z ξ : ℂ) (hδ : 0 < δ) (hz : 0 ≤ z.re) :
    ‖quotient δ (z-ξ)‖ ≤ ‖z-ξ‖*Real.exp (δ*max 0 ξ.re) :=
  quotient_norm_bound δ (z-ξ) (max 0 ξ.re) hδ (le_max_left _ _)
    (by rw [Complex.sub_re]; linarith [le_max_right (0:ℝ) ξ.re])

theorem joint_exponential_norm_bound (δ : ℝ) (z ξ : ℂ)
    (hδ : 0 ≤ δ) (hz : 0 ≤ z.re) :
    ‖Complex.exp (-(δ:ℂ)*(z-ξ))‖ ≤ Real.exp (δ*max 0 ξ.re) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
    Complex.ofReal_im,neg_zero,zero_mul,sub_zero,Complex.sub_re]
  nlinarith [mul_nonneg hδ hz,mul_nonneg hδ (sub_nonneg.mpr (le_max_right (0:ℝ) ξ.re))]

#print axioms widths_admissible
#print axioms profileSum_exact
#print axioms profileSum_tendsto
#print axioms quotient_norm_bound
#print axioms joint_quotient_norm_bound
#print axioms joint_exponential_norm_bound
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceProfiles
