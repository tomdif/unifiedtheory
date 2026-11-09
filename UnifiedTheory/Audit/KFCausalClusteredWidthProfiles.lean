/- Closely spaced admissible reciprocal widths generate charged polynomial
profiles in a pointwise limit. The exact finite sums also have a spacing-
independent half-plane envelope. This does not identify an integrated or
Hamiltonian graph limit, and supplies no uniform response estimate. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveForm
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClusteredWidthProfiles
noncomputable section
open Filter
open scoped Topology
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalReciprocalNeutralPositiveForm (profileSum positiveDensity)
open KFCausalReciprocalNeutralLaplace (Joint weight)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalNeutralKernel (neutral)

def widths (n : ℕ) (δ : ℝ) (i : Fin (n+1)) : ℝ := 1+(i.val:ℝ)*δ
def coefficients (n : ℕ) (δ : ℝ) (i : Fin (n+1)) : ℂ :=
  ((-1:ℂ)^i.val*(n.choose i.val:ℂ))/(δ:ℂ)^n/(widths n δ i:ℂ)
def quotient (δ : ℝ) (z : ℂ) : ℂ := (1-Complex.exp (-(δ:ℂ)*z))/(δ:ℂ)

theorem widths_admissible (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (i : Fin (n+1)) :
    1 ≤ widths n δ i := by
  unfold widths
  have hp : 0 ≤ (i.val:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ
  linarith

theorem laplaceSum_exact (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    laplaceSum (n+1) (widths n δ) (coefficients n δ) z =
      Complex.exp (-z)*quotient δ z^n := by
  have hw (i : Fin (n+1)) : (widths n δ i:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (widths_admissible n δ hδ.le i)))
  have he (i : Fin (n+1)) : Complex.exp (-(widths n δ i:ℂ)*z) =
      Complex.exp (-z)*Complex.exp (-(δ:ℂ)*z)^i.val := by
    rw [← Complex.exp_nat_mul]
    rw [← Complex.exp_add]
    congr 1
    unfold widths
    push_cast
    ring
  have hb : ∑ i : Fin (n+1), (-1:ℂ)^i.val*(n.choose i.val:ℂ)*
      Complex.exp (-(δ:ℂ)*z)^i.val = (1-Complex.exp (-(δ:ℂ)*z))^n := by
    rw [show (1:ℂ)-Complex.exp (-(δ:ℂ)*z) = -Complex.exp (-(δ:ℂ)*z)+1 by ring,
      add_pow,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (-Complex.exp (-(δ:ℂ)*z))^i.val =
      (-1:ℂ)^i.val*Complex.exp (-(δ:ℂ)*z)^i.val from neg_pow _ _]
    simp only [one_pow,mul_one]
    ring
  unfold laplaceSum coefficients
  simp only [div_mul_cancel₀ _ (hw _),he]
  calc
    _ = Complex.exp (-z)/(δ:ℂ)^n *
        ∑ i : Fin (n+1), (-1:ℂ)^i.val*(n.choose i.val:ℂ)*Complex.exp (-(δ:ℂ)*z)^i.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = Complex.exp (-z)*quotient δ z^n := by rw [hb]; unfold quotient; rw [div_pow]; ring

theorem exponential_derivative (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-(u:ℂ)*z))
      (Complex.exp (-(t:ℂ)*z)*(-z)) t := by
  convert (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).neg.mul_const z).cexp) using 1
  simp

theorem quotient_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => quotient δ z) (𝓝[>] 0) (𝓝 z) := by
  have ht := (exponential_derivative z 0).tendsto_slope_zero_right.neg
  simpa [quotient,Complex.real_smul,div_eq_mul_inv,mul_comm,← mul_neg,neg_sub] using ht

theorem laplaceSum_tendsto (n : ℕ) (z : ℂ) :
    Tendsto (fun δ : ℝ => laplaceSum (n+1) (widths n δ) (coefficients n δ) z)
      (𝓝[>] 0) (𝓝 (Complex.exp (-z)*z^n)) := by
  apply Tendsto.congr' _ (tendsto_const_nhds.mul ((quotient_tendsto z).pow n))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (laplaceSum_exact n δ hδ z).symm

theorem quotient_norm_le (δ : ℝ) (z : ℂ) (hδ : 0 < δ) (hz : 0 ≤ z.re) :
    ‖quotient δ z‖ ≤ ‖z‖ := by
  have hd (t : ℝ) (_ : t ∈ Set.Icc 0 δ) : HasDerivWithinAt
      (fun u : ℝ => Complex.exp (-(u:ℂ)*z)) (Complex.exp (-(t:ℂ)*z)*(-z)) (Set.Icc 0 δ) t :=
    (exponential_derivative z t).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Set.Ico 0 δ) :
      ‖Complex.exp (-(t:ℂ)*z)*(-z)‖ ≤ ‖z‖ := by
    rw [norm_mul,norm_neg,Complex.norm_exp]
    have he : (-(t:ℂ)*z).re ≤ 0 := by simp only [Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,neg_zero,zero_mul,sub_zero]; nlinarith [ht.1]
    have hx := Real.exp_le_one_iff.mpr he
    nlinarith [norm_nonneg z]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment' hd hb δ (Set.right_mem_Icc.mpr hδ.le)
  simp only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,sub_zero] at hm
  rw [quotient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  simpa only [norm_sub_rev] using hm

theorem laplaceSum_norm_le (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖laplaceSum (n+1) (widths n δ) (coefficients n δ) z‖ ≤
      Real.exp (-z.re)*‖z‖^n := by
  rw [laplaceSum_exact n δ hδ z,norm_mul,norm_pow,Complex.norm_exp,Complex.neg_re]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (quotient_norm_le δ z hδ hz) n)
    (Real.exp_pos _).le

theorem profileSum_factor (n : ℕ) (δ : ℝ) (F : ℂ → ℂ) (z ζ : ℂ) :
    profileSum (n+1) (widths n δ) (coefficients n δ) (fun _ => F) z ζ =
      laplaceSum (n+1) (widths n δ) (coefficients n δ) z*F ζ := by
  unfold profileSum laplaceSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem profileSum_tendsto (n : ℕ) (F : ℂ → ℂ) (z ζ : ℂ) :
    Tendsto (fun δ : ℝ => profileSum (n+1) (widths n δ) (coefficients n δ) (fun _ => F) z ζ)
      (𝓝[>] 0) (𝓝 (Complex.exp (-z)*z^n*F ζ)) := by
  simpa only [profileSum_factor] using (laplaceSum_tendsto n z).mul_const (F ζ)

theorem profileSum_norm_le (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (F : ℂ → ℂ)
    (z ζ : ℂ) (hz : 0 ≤ z.re) :
    ‖profileSum (n+1) (widths n δ) (coefficients n δ) (fun _ => F) z ζ‖ ≤
      ‖Complex.exp (-z)*z^n*F ζ‖ := by
  rw [profileSum_factor,norm_mul,norm_mul,norm_mul,norm_pow,Complex.norm_exp,Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (laplaceSum_norm_le n δ hδ z hz) (norm_nonneg _)

def limitDensity (n : ℕ) (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (p : Joint) : ℝ :=
  let z := chart α r (p.1.1^2+(p.1.2 0)^2) p.2
  weight β r p*‖Complex.exp (-z)*z^n*F (neutral r (p.1.2 0) (p.1.2 1))‖^2

theorem positiveDensity_tendsto (n : ℕ) (α β : ℝ) (r : ℂ) (F : ℂ → ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => positiveDensity (n+1) α β (widths n δ) r (coefficients n δ) (fun _ => F) p)
      (𝓝[>] 0) (𝓝 (limitDensity n α β r F p)) := by
  exact ((profileSum_tendsto n F (chart α r (p.1.1^2+(p.1.2 0)^2) p.2)
    (neutral r (p.1.2 0) (p.1.2 1))).norm.pow 2).const_mul (weight β r p)

theorem positiveDensity_le_limit (n : ℕ) (α β δ : ℝ) (r : ℂ) (F : ℂ → ℂ)
    (hδ : 0 < δ) (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r)
    (p : Joint) (hp : 0 ≤ p.2) :
    positiveDensity (n+1) α β (widths n δ) r (coefficients n δ) (fun _ => F) p ≤
      limitDensity n α β r F p := by
  have hz : 0 ≤ (chart α r (p.1.1^2+(p.1.2 0)^2) p.2).re := by
    rw [KFCausalReciprocalWedgeGeometry.chart_re]
    positivity
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (profileSum_norm_le n δ hδ F _ _ hz) 2)
    (KFCausalReciprocalNeutralLaplace.weight_positive β r p).le

#print axioms widths_admissible
#print axioms laplaceSum_exact
#print axioms exponential_derivative
#print axioms quotient_tendsto
#print axioms laplaceSum_tendsto
#print axioms quotient_norm_le
#print axioms laplaceSum_norm_le
#print axioms profileSum_factor
#print axioms profileSum_tendsto
#print axioms profileSum_norm_le
#print axioms positiveDensity_tendsto
#print axioms positiveDensity_le_limit
end
end UnifiedTheory.Audit.KFCausalClusteredWidthProfiles
