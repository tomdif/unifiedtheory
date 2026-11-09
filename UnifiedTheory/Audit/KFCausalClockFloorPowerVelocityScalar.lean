/- Uniform power-velocity estimates for the actual analytic clock shift.
The order is fixed before hbar tends to zero; constants may grow with it. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)

def remainderConstant : ℕ → ℝ
  | 0 => 0
  | n+1 => 2*remainderConstant n+(n+1)

theorem remainderConstant_nonnegative (n : ℕ) : 0 ≤ remainderConstant n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [remainderConstant]; positivity

theorem power_remainder (z d : ℂ) (hz : ‖z‖ ≤ 2) (hd : ‖d‖ ≤ 1) (n : ℕ) :
    ‖z^(n+1)-d^(n+1)-(n+1:ℂ)*d^n*(z-d)‖ ≤ remainderConstant n*‖z-d‖^2 := by
  induction n with
  | zero => simp [remainderConstant]
  | succ n ih =>
    have he : z^(n+1+1)-d^(n+1+1)-(n+1+1:ℂ)*d^(n+1)*(z-d) =
        z*(z^(n+1)-d^(n+1)-(n+1:ℂ)*d^n*(z-d))+(n+1:ℂ)*d^n*(z-d)^2 := by
      simp only [pow_succ]
      ring
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    have hc : ‖(n+1:ℂ)‖ = (n+1:ℝ) := by
      exact_mod_cast Complex.norm_natCast (n+1)
    have hd' : ‖d^n‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hd
    calc
      _ ≤ ‖z‖*‖z^(n+1)-d^(n+1)-(n+1:ℂ)*d^n*(z-d)‖+
          ‖(n+1:ℂ)‖*‖d^n‖*‖z-d‖^2 := by
        have ht := norm_add_le
          (z*(z^(n+1)-d^(n+1)-(n+1:ℂ)*d^n*(z-d))) ((n+1:ℂ)*d^n*(z-d)^2)
        rw [norm_mul z _,norm_mul ((n+1:ℂ)*d^n) _,norm_mul (n+1:ℂ) _,norm_pow (z-d) 2] at ht
        exact ht
      _ ≤ 2*(remainderConstant n*‖z-d‖^2)+(n+1:ℝ)*1*‖z-d‖^2 := by
        rw [hc]
        exact add_le_add (mul_le_mul hz ih (norm_nonneg _) (by norm_num))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd' (by positivity)) (sq_nonneg _))
      _ = _ := by simp only [remainderConstant]; ring

def powerDrift (ε : ℝ) (n : ℕ) (d : ℝ) : ℝ := (n+1)*d^n*drift ε d

def powerVelocity (ε h : ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  (-2/h)*(complexDefect ε ((q:ℂ)+(-h/2:ℝ)*Complex.I)^(n+1)).im

def errorConstant (ε : ℝ) (n : ℕ) : ℝ := (8*remainderConstant n+20*(n+1))/ε^2

theorem errorConstant_nonnegative (ε : ℝ) (n : ℕ) : 0 ≤ errorConstant ε n := by
  have := remainderConstant_nonnegative n
  unfold errorConstant
  positivity

theorem powerDrift_nonpositive (ε : ℝ) (hε : 0 < ε) (n : ℕ) (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    powerDrift ε n d ≤ 0 := by
  have hg : drift ε d ≤ 0 := by
    unfold drift
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hd.2))) hε.le
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity) (pow_nonneg hd.1 n)) hg

theorem powerVelocity_error (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ) (q : ℝ) :
    |powerVelocity ε h n q-powerDrift ε n (realDefect ε hε q)| ≤ errorConstant ε n*|h| := by
  let d := realDefect ε hε q
  let z := complexDefect ε ((q:ℂ)+(-h/2:ℝ)*Complex.I)
  have hy : |-h/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hd : 0 ≤ d ∧ d ≤ 1 := ⟨(realDefect_positive ε hε q).le,realDefect_le_one ε hε q⟩
  have hdNorm : ‖(d:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd.1] using hd.2
  have hzNorm : ‖z‖ ≤ 2 := complexDefect_norm_le_two ε hε _ (by simpa using hy)
  have hdiff : ‖z-(d:ℂ)‖ ≤ 2*|h|/ε := by
    have he := complexDefect_vertical_difference ε hε ((q:ℂ)+(-h/2:ℝ)*Complex.I) (by simpa using hy)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,zero_add,abs_div,abs_neg] at he
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    have hs : d^2 ≤ 1 := pow_le_one₀ hd.1 hd.2
    calc
      _ ≤ (2*|h|/ε)*d^2 := by convert he using 1; ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*|h|/ε)
  have hr := (Complex.abs_im_le_norm (z^(n+1)-(d:ℂ)^(n+1)-(n+1:ℂ)*(d:ℂ)^n*(z-(d:ℂ)))).trans
    (power_remainder z (d:ℂ) hzNorm hdNorm n)
  have he : (z^(n+1)-(d:ℂ)^(n+1)-(n+1:ℂ)*(d:ℂ)^n*(z-(d:ℂ))).im =
      (z^(n+1)).im-(n+1:ℝ)*d^n*z.im := by
    simp only [← Complex.ofReal_pow,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_im,Complex.ofReal_re,Complex.natCast_im,Complex.natCast_re,
      Complex.add_im,Complex.add_re,Complex.one_im,Complex.one_re,mul_zero,zero_mul,sub_zero,add_zero]
  rw [he] at hr
  have hrem : |(-2/h)*((z^(n+1)).im-(n+1:ℝ)*d^n*z.im)| ≤
      (8*remainderConstant n/ε^2)*|h| := by
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left hr (abs_nonneg (-2/h))).trans
    apply (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdiff 2) (remainderConstant_nonnegative n))
      (abs_nonneg (-2/h))).trans
    have hn := abs_ne_zero.mpr hne
    rw [abs_div,abs_neg]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply le_of_eq
    field_simp
    ring
  have hv : |quantumVelocity ε h q-drift ε d| ≤ (20*|h|/ε^2) := by
    apply (quantumVelocity_error ε hε h hne hb q).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hd.1 hd.2 (n := 3))
      (by positivity : 0 ≤ 20*|h|/ε^2)
  have hcoef : |(n+1:ℝ)*d^n| ≤ n+1 := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hd.1 n))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hd.1 hd.2 (n := n)) (by positivity : (0:ℝ) ≤ n+1)
  have hsplit : powerVelocity ε h n q-powerDrift ε n d =
      (-2/h)*((z^(n+1)).im-(n+1:ℝ)*d^n*z.im)+
        ((n+1:ℝ)*d^n)*(quantumVelocity ε h q-drift ε d) := by
    unfold powerVelocity powerDrift quantumVelocity z
    ring
  rw [hsplit]
  apply (abs_add_le _ _).trans
  have hb' := mul_le_mul hcoef hv (abs_nonneg _) (by positivity : (0:ℝ) ≤ n+1)
  rw [← abs_mul] at hb'
  exact (add_le_add hrem hb').trans_eq (by unfold errorConstant; ring)

#print axioms remainderConstant_nonnegative
#print axioms power_remainder
#print axioms errorConstant_nonnegative
#print axioms powerDrift_nonpositive
#print axioms powerVelocity_error

end
end UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityScalar
