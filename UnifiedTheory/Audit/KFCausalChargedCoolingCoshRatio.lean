/- Positive definiteness of the concrete normalized B and C shifted-cosh ratios. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingLogCosh

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingCoshRatio
noncomputable section
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingLevyLaplace
open KFCausalChargedCoolingLogCosh

theorem shifted_cosh_zero (s : ℝ) :
    Complex.cosh (shifted s 0) = (Real.cos (s/2):ℂ) := by
  rw [shifted,Complex.ofReal_zero,zero_add,
    show (s:ℂ)*Complex.I/2 = ((s/2:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.cosh_mul_I,← Complex.ofReal_cos]

private theorem cosh_ne (s z : ℝ) (hs : |s| < Real.pi) :
    Complex.cosh (shifted s z) ≠ 0 := Complex.slitPlane_ne_zero (shifted_cosh_slitPlane s z hs)

private theorem cosHalf_ne (s : ℝ) (hs : |s| < Real.pi) : (Real.cos (s/2):ℂ) ≠ 0 := by
  simpa only [shifted_cosh_zero] using cosh_ne s 0 hs

private theorem exp_difference (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    Complex.exp (Complex.log u-Complex.log v) = u/v := by
  rw [Complex.exp_sub,Complex.exp_log hu,Complex.exp_log hv]

private theorem exp_half_difference (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    Complex.exp ((Complex.log u-Complex.log v)/2) = u^(1/2:ℂ)/v^(1/2:ℂ) := by
  rw [Complex.cpow_def_of_ne_zero hu,Complex.cpow_def_of_ne_zero hv,← Complex.exp_sub]
  congr 1
  ring

private theorem exp_two (u : ℂ) : Complex.exp (2*u) = (Complex.exp u)^2 := by
  rw [two_mul,Complex.exp_add,pow_two]

/-- The square-root factor is the principal complex half-power. -/
def ratioB (θ z : ℝ) : ℂ :=
  (Complex.cosh (shifted θ z)/(Real.cos (θ/2):ℂ))*
    ((Real.cos θ:ℂ)^(1/2:ℂ)/(Complex.cosh (shifted (2*θ) z))^(1/2:ℂ))*
    ((Real.cos θ:ℂ)/Complex.cosh (shifted (-2*θ) z))

def ratioC (θ z : ℝ) : ℂ :=
  (Complex.cosh (shifted (-θ) z)/(Real.cos (θ/2):ℂ))*
    ((Real.cos θ:ℂ)^(1/2:ℂ)/(Complex.cosh (shifted (2*θ) z))^(1/2:ℂ))*
    ((Real.cos θ:ℂ)/Complex.cosh (shifted (-2*θ) z))^2

theorem exp_logRatio_B (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    Complex.exp (logRatio false θ z) = ratioB θ z := by
  have h2 : (2*θ)/2 = θ := by ring
  have hs : |θ| < Real.pi := by linarith [Real.pi_pos]
  have hs2 : |2*θ| < Real.pi := by rw [abs_mul]; norm_num; linarith
  have hsn2 : |-2*θ| < Real.pi := by simpa only [show -2*θ = -(2*θ) by ring,abs_neg] using hs2
  have hc : (Real.cos θ:ℂ) ≠ 0 := by simpa only [h2] using cosHalf_ne (2*θ) hs2
  have he : logRatio false θ z =
      (Complex.log (Complex.cosh (shifted θ z))-Complex.log (Real.cos (θ/2):ℂ))+
      (Complex.log (Real.cos θ:ℂ)-Complex.log (Complex.cosh (shifted (2*θ) z)))/2+
      (Complex.log (Real.cos θ:ℂ)-Complex.log (Complex.cosh (shifted (-2*θ) z))) := by
    simp [logRatio,Fin.sum_univ_three,coefficient,mode,shifted_cosh_zero]
    ring_nf
    simp only [Complex.cos_neg]
    ring
  rw [he,Complex.exp_add,Complex.exp_add,
    exp_difference _ _ (cosh_ne θ z hs) (cosHalf_ne θ hs),
    exp_half_difference _ _ hc (cosh_ne (2*θ) z hs2),
    exp_difference _ _ hc (cosh_ne (-2*θ) z hsn2)]
  rfl

theorem exp_logRatio_C (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    Complex.exp (logRatio true θ z) = ratioC θ z := by
  have h2 : (2*θ)/2 = θ := by ring
  have hs : |θ| < Real.pi := by linarith [Real.pi_pos]
  have hsn : |-θ| < Real.pi := by simpa only [abs_neg] using hs
  have hs2 : |2*θ| < Real.pi := by rw [abs_mul]; norm_num; linarith
  have hsn2 : |-2*θ| < Real.pi := by simpa only [show -2*θ = -(2*θ) by ring,abs_neg] using hs2
  have hc : (Real.cos θ:ℂ) ≠ 0 := by simpa only [h2] using cosHalf_ne (2*θ) hs2
  have he : logRatio true θ z =
      (Complex.log (Complex.cosh (shifted (-θ) z))-Complex.log (Real.cos (θ/2):ℂ))+
      (Complex.log (Real.cos θ:ℂ)-Complex.log (Complex.cosh (shifted (2*θ) z)))/2+
      2*(Complex.log (Real.cos θ:ℂ)-Complex.log (Complex.cosh (shifted (-2*θ) z))) := by
    simp [logRatio,Fin.sum_univ_three,coefficient,mode,shifted_cosh_zero]
    ring_nf
    simp only [show (θ:ℂ)*(-1/2) = -((θ:ℂ)*(1/2)) by ring,Complex.cos_neg]
    ring
  rw [he,Complex.exp_add,Complex.exp_add,
    exp_difference _ _ (cosh_ne (-θ) z hsn) (cosHalf_ne θ hs),
    exp_half_difference _ _ hc (cosh_ne (2*θ) z hs2),
    exp_two,exp_difference _ _ hc (cosh_ne (-2*θ) z hsn2)]
  rfl

theorem ratioB_positive {n : Type*} [Fintype n] (θ : ℝ) (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => ratioB θ (x j-x i)) := by
  simpa only [exp_logRatio_B θ _ hθ] using logRatio_kernel_positive false θ hθ x

theorem ratioC_positive {n : Type*} [Fintype n] (θ : ℝ) (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => ratioC θ (x j-x i)) := by
  simpa only [exp_logRatio_C θ _ hθ] using logRatio_kernel_positive true θ hθ x

#print axioms shifted_cosh_zero
#print axioms exp_logRatio_B
#print axioms exp_logRatio_C
#print axioms ratioB_positive
#print axioms ratioC_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingCoshRatio
