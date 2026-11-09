/- The physical shear and its complex bilinear transpose give the actual
pulled Laplacian metric. Small complex clock shifts yield a uniform
Euclidean perturbation estimate; the transpose is not a Hermitian adjoint. -/
import UnifiedTheory.Audit.KFCausalComplexShearGroup
import UnifiedTheory.Audit.KFCausalPairedModeCoordinates

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalComplexShearMetric
noncomputable section
open KFCausalComplexShearPerturbation (Space flow diagonal diagonal_bound exp_half_bound)
open KFCausalPairedModeCoordinates (scale)

def transposeFlow (σ : ℝ) (z : ℂ) (x : Space) : Space := WithLp.toLp 2
  ![Complex.exp (-z/2)*x 0,Complex.exp (-z/2)*x 1,
    Complex.exp (z/2)*x 2,
    Complex.exp (z/2)*x 3+2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 4,x 4]

theorem transpose_pairing (σ : ℝ) (z : ℂ) (x y : Space) :
    (∑i,x i*flow σ z y i)=∑i,transposeFlow σ z x i*y i := by
  simp only [flow,transposeFlow,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  change x 0*(Complex.exp (-z/2)*y 0)+
    (x 1*(Complex.exp (-z/2)*y 1)+(x 2*(Complex.exp (z/2)*y 2)+
    (x 3*(Complex.exp (z/2)*y 3)+x 4*(y 4+2*(σ:ℂ)*(Complex.exp (z/2)-1)*y 3))))=
    (Complex.exp (-z/2)*x 0)*y 0+
    ((Complex.exp (-z/2)*x 1)*y 1+((Complex.exp (z/2)*x 2)*y 2+
    ((Complex.exp (z/2)*x 3+2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 4)*y 3+x 4*y 4)))
  ring

private theorem half_small (z : ℂ) (hz : ‖z‖≤1/20) :
    ‖Complex.exp (z/2)-1‖≤1/39 := by
  have h := exp_half_bound z (by linarith)
  have hp := mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz)
  nlinarith [norm_nonneg z]

private theorem coefficient_bound : |2*scale|≤3/2 := by
  have h := KFCausalPairedModeCoordinates.scale_square
  have hn := abs_nonneg (2*scale)
  nlinarith [sq_abs (2*scale)]

private theorem difference_bounds (σ : ℝ) (hσ : |σ|≤3/2)
    (z : ℂ) (hz : ‖z‖≤1/20) (x : Space) :
    ‖flow σ z x-x‖≤(4/39:ℝ)*‖x‖ ∧
      ‖transposeFlow σ z x-x‖≤(4/39:ℝ)*‖x‖ := by
  let c : Fin 5→ℂ := ![Complex.exp (-z/2)-1,Complex.exp (-z/2)-1,
    Complex.exp (z/2)-1,Complex.exp (z/2)-1,0]
  have hp := half_small z hz
  have hm := half_small (-z) (by simpa only [norm_neg] using hz)
  have hc : ∀i,‖c i‖≤1/39 := by
    intro i
    fin_cases i <;> norm_num [c] <;> assumption
  have hd := diagonal_bound c x (1/39) (by norm_num) hc
  have he (j : Fin 5) :
      ‖2*(σ:ℂ)*(Complex.exp (z/2)-1)*x j‖≤(3/39:ℝ)*‖x‖ := by
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ 2*(3/2)*(1/39)*‖x‖ := by
        gcongr
        exact PiLp.norm_apply_le x j
      _ = _ := by ring
  have hf : flow σ z x-x=diagonal c x+
      (WithLp.toLp 2 (Pi.single (4:Fin 5) (2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 3)):Space) := by
    ext i
    fin_cases i <;> simp [flow,diagonal,c] <;> ring
  have ht : transposeFlow σ z x-x=diagonal c x+
      (WithLp.toLp 2 (Pi.single (3:Fin 5) (2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 4)):Space) := by
    ext i
    fin_cases i <;> simp [transposeFlow,diagonal,c] <;> ring
  constructor
  · rw [hf]
    have h := norm_add_le (diagonal c x)
      (WithLp.toLp 2 (Pi.single (4:Fin 5) (2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 3)):Space)
    rw [PiLp.norm_toLp_single] at h
    linarith [he 3]
  · rw [ht]
    have h := norm_add_le (diagonal c x)
      (WithLp.toLp 2 (Pi.single (3:Fin 5) (2*(σ:ℂ)*(Complex.exp (z/2)-1)*x 4)):Space)
    rw [PiLp.norm_toLp_single] at h
    linarith [he 4]

theorem physical_difference (z : ℂ) (hz : ‖z‖≤1/20) (x : Space) :
    ‖flow (2*scale) z x-x‖≤(4/39:ℝ)*‖x‖ ∧
      ‖transposeFlow (2*scale) z x-x‖≤(4/39:ℝ)*‖x‖ :=
  difference_bounds (2*scale) coefficient_bound z hz x

def gram (δ : ℂ) (x : Space) : Space :=
  flow (2*scale) (-δ) (transposeFlow (2*scale) (-δ) x)

theorem gram_difference (δ : ℂ) (hδ : ‖δ‖≤1/20) (x : Space) :
    ‖gram δ x-x‖≤(328/1521:ℝ)*‖x‖ := by
  have hd : ‖-δ‖≤1/20 := by simpa only [norm_neg] using hδ
  let y := transposeFlow (2*scale) (-δ) x
  have hy := (physical_difference (-δ) hd x).2
  have hn := norm_add_le (y-x) x
  rw [sub_add_cancel] at hn
  have hf := (physical_difference (-δ) hd y).1
  have hh := norm_add_le (flow (2*scale) (-δ) y-y) (y-x)
  rw [sub_add_sub_cancel] at hh
  change ‖gram δ x-x‖≤‖gram δ x-y‖+‖y-x‖ at hh
  change ‖y-x‖≤_ at hy
  change ‖gram δ x-y‖≤_ at hf
  have hm := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤4/39)
  nlinarith only [hy,hf,hh,hm]

def normalizedMetric (δ z : ℂ) (x : Space) : Space := z • gram δ x

theorem normalized_difference (δ z : ℂ) (hδ : ‖δ‖≤1/20)
    (hz : ‖z-1‖≤1/18) (x : Space) :
    ‖normalizedMetric δ z x-x‖≤(7753/27378:ℝ)*‖x‖ := by
  have hn : ‖z‖≤19/18 := by
    have h := norm_add_le (z-1) 1
    rw [sub_add_cancel,norm_one] at h
    linarith
  have he : normalizedMetric δ z x-x=z • (gram δ x-x)+(z-1) • x := by
    simp only [normalizedMetric,smul_sub,sub_smul,one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖z • (gram δ x-x)‖+‖(z-1) • x‖ := norm_add_le _ _
    _ = ‖z‖*‖gram δ x-x‖+‖z-1‖*‖x‖ := by rw [norm_smul,norm_smul]
    _ ≤ (19/18)*(328/1521)*‖x‖+(1/18)*‖x‖ := by
      have hg := gram_difference δ hδ x
      nlinarith [mul_le_mul hn hg (norm_nonneg _) (by norm_num : (0:ℝ)≤19/18),
        mul_le_mul_of_nonneg_right hz (norm_nonneg x)]
    _ = _ := by ring

#print axioms transpose_pairing
#print axioms physical_difference
#print axioms gram_difference
#print axioms normalized_difference
end
end UnifiedTheory.Audit.KFCausalPhysicalComplexShearMetric
