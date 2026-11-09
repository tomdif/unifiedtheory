/- The target reciprocal Gaussian and the broader paired Gaussian in
the actual physical charge coordinates. Their weighted normalization
retains both reciprocal widths and the neutral shear coefficient. -/
import UnifiedTheory.Audit.KFCausalTwoShearTransverseQuotient
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStates
import UnifiedTheory.Audit.KFCausalChargeShearJointFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalReciprocalNormalization
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexQuadraticPerturbation (mass weightedQuadratic)
open KFCausalPairedModeCoordinates (scale scale_square)

def normalize (α w c : ℝ) (x : Joint 2 4) : Space := WithLp.toLp 2
  ![((Real.sqrt (α/w)*c*x (.inl 0):ℝ):ℂ),
    ((Real.sqrt (α*w)*c*x (.inl 1):ℝ):ℂ),
    ((Real.sqrt (α/w)*x (.inr 1):ℝ):ℂ),
    ((Real.sqrt (α*w)*x (.inr 2):ℝ):ℂ),
    ((Real.sqrt (α/32)*x (.inr 3):ℝ):ℂ)]

def weights (W w : ℝ) : Fin 5 → ℝ :=
  ![w/(4*W),1/(4*W*w),w/(4*W),1/(4*W*w),1/(16*W)]

def coupling (α w : ℝ) : ℝ := 2*scale*Real.sqrt (α/32)/Real.sqrt (α*w)

theorem normalize_real (α w c : ℝ) (x : Joint 2 4) :
    ∀ i, (normalize α w c x i).im=0 := by
  intro i
  fin_cases i <;> simp [normalize]

theorem weights_bound (W w : ℝ) (hw : 1 ≤ w) (hW : w ≤ W) :
    ∀ i, 0 ≤ weights W w i ∧ weights W w i ≤ 1/4 := by
  have hp : 0 < w := by linarith
  have hP : 0 < W := by linarith
  have hww : 1 ≤ W*w := by nlinarith
  intro i
  fin_cases i <;> dsimp [weights]
  all_goals constructor
  all_goals first | positivity | (apply (div_le_iff₀ (by positivity)).mpr; nlinarith)

theorem normalize_mass (α w c : ℝ) (hα : 0 < α) (hw : 0 < w) (x : Joint 2 4) :
    mass (fun i => normalize α w c x i)=
      α*KFCausalReciprocalGaussianStates.coordinateQuadratic w c x+(α/32)*(x (.inr 3))^2 := by
  have h₁ := Real.sq_sqrt (div_nonneg hα.le hw.le)
  have h₂ := Real.sq_sqrt (mul_nonneg hα.le hw.le)
  have h₃ := Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  simp only [mass,Fin.sum_univ_succ,Fin.sum_univ_zero,normalize,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    KFCausalReciprocalGaussianStates.coordinateQuadratic_coordinates]
  simp only [mul_pow,h₁,h₂,h₃]
  ring

theorem baseline_quadratic (α W w c : ℝ) (hα : 0 < α) (hw : 0 < w)
    (hW : 0 < W) (x : Joint 2 4) :
    weightedQuadratic (weights W w) (fun i => normalize α w c x i)=
      (((α/(4*W))*KFCausalChargeGaussianGeometry.radius c x+
        (α/(512*W))*(x (.inr 3))^2:ℝ):ℂ) := by
  have h₁ := Real.sq_sqrt (div_nonneg hα.le hw.le)
  have h₂ := Real.sq_sqrt (mul_nonneg hα.le hw.le)
  have h₃ := Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero,normalize,weights,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    ← Complex.ofReal_pow,← Complex.ofReal_mul]
  norm_cast
  rw [KFCausalChargeGaussianGeometry.radius_coordinates]
  simp only [mul_pow,h₁,h₂,h₃]
  field_simp
  ring

theorem coupling_square (α w : ℝ) (hα : 0 < α) (hw : 0 < w) :
    (coupling α w)^2=1/(16*w) := by
  have h₁ := Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  have h₂ := Real.sq_sqrt (mul_nonneg hα.le hw.le)
  simp only [coupling,div_pow,mul_pow,h₁,h₂,scale_square]
  field_simp
  ring

theorem coupling_bound (α w : ℝ) (hα : 0 < α) (hw : 1 ≤ w) :
    |coupling α w| ≤ 1/4 := by
  have hp : 0 < w := by linarith
  have hs := coupling_square α w hα hp
  have hb : 1/(16*w) ≤ (1/4:ℝ)^2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)).mp (by simpa only [sq_abs] using hs.le.trans hb)

theorem normalize_shear (α w c t : ℝ) (hα : 0 < α) (hw : 0 < w) (x : Joint 2 4) :
    normalize α w c (KFCausalChargeShearJointFlow.flow t x)=
      flow (coupling α w) (t:ℂ) (normalize α w c x) := by
  have hb : Real.sqrt (α*w) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos hα hw))
  have he₁ : Complex.exp (-(t:ℂ)/2)=(Real.exp (-t/2):ℝ) := by
    rw [show -(t:ℂ)/2=((-t/2:ℝ):ℂ) by push_cast; rfl,Complex.ofReal_exp]
  have he₂ : Complex.exp ((t:ℂ)/2)=(Real.exp (t/2):ℝ) := by
    rw [show (t:ℂ)/2=((t/2:ℝ):ℂ) by push_cast; rfl,Complex.ofReal_exp]
  ext i
  fin_cases i <;> simp only [normalize,flow,Matrix.cons_val_zero,
    KFCausalChargeShearJointFlow.flow_first,
    KFCausalChargeShearJointFlow.flow_second,he₁,he₂]
  all_goals push_cast
  all_goals try ring
  simp only [coupling]
  push_cast
  have hbc : (Real.sqrt (α*w):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp [hbc]
  ring

#print axioms normalize_real
#print axioms weights_bound
#print axioms normalize_mass
#print axioms baseline_quadratic
#print axioms coupling_square
#print axioms coupling_bound
#print axioms normalize_shear
end
end UnifiedTheory.Audit.KFCausalPhysicalReciprocalNormalization
