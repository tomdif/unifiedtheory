/- Exact positive-width transport of the normalized charged cooling ratios. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingCoshRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingWidthGeometry
noncomputable section
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingLevyLaplace KFCausalChargedCoolingLogCosh
open KFCausalChargedCoolingCoshRatio

def phaseKernel (ρ θ x y : ℝ) : ℂ :=
  (ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)*(Real.exp (2*x):ℂ)+
  (ρ:ℂ)*Complex.exp (-(θ:ℂ)*Complex.I)*(Real.exp (2*y):ℂ)

theorem phaseKernel_cosh (ρ θ x y : ℝ) :
    phaseKernel ρ θ x y = (2*ρ*Real.exp (x+y):ℂ)*
      Complex.cosh (shifted (2*θ) (x-y)) := by
  unfold phaseKernel shifted
  rw [Complex.cosh]
  push_cast
  have h₁ : Complex.exp ((x:ℂ)+y)*Complex.exp ((x:ℂ)-y+2*θ*Complex.I/2) =
      Complex.exp ((θ:ℂ)*Complex.I)*Complex.exp (2*(x:ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  have h₂ : Complex.exp ((x:ℂ)+y)*Complex.exp (-((x:ℂ)-y+2*θ*Complex.I/2)) =
      Complex.exp (-(θ:ℂ)*Complex.I)*Complex.exp (2*(y:ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  linear_combination -(ρ:ℂ)*h₁-(ρ:ℂ)*h₂

private theorem cos_pos (θ : ℝ) (hθ : |θ| < Real.pi/2) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ],by linarith [le_abs_self θ]⟩

private theorem double_strip (θ : ℝ) (hθ : |θ| < Real.pi/2) : |2*θ| < Real.pi := by
  rw [abs_mul]; norm_num; linarith

theorem phaseKernel_ne (ρ θ x y : ℝ) (hρ : 0 < ρ) (hθ : |θ| < Real.pi/2) :
    phaseKernel ρ θ x y ≠ 0 := by
  rw [phaseKernel_cosh]
  exact mul_ne_zero (by exact_mod_cast ne_of_gt (mul_pos (mul_pos (by norm_num) hρ)
    (Real.exp_pos (x+y))))
    (Complex.slitPlane_ne_zero (shifted_cosh_slitPlane (2*θ) (x-y) (double_strip θ hθ)))

theorem phaseKernel_log (ρ θ x y : ℝ) (hρ : 0 < ρ) (hθ : |θ| < Real.pi/2) :
    Complex.log (phaseKernel ρ θ x y) =
      ((Real.log (2*ρ)+x+y:ℝ):ℂ)+Complex.log (Complex.cosh (shifted (2*θ) (x-y))) := by
  rw [phaseKernel_cosh]
  rw [show (2:ℂ)*ρ*(Real.exp (x+y):ℂ) = ((2*ρ*Real.exp (x+y):ℝ):ℂ) by push_cast; rfl]
  rw [Complex.log_ofReal_mul
    (mul_pos (mul_pos (by norm_num) hρ) (Real.exp_pos (x+y)))
    (Complex.slitPlane_ne_zero (shifted_cosh_slitPlane (2*θ) (x-y) (double_strip θ hθ))),
    Real.log_mul (ne_of_gt (mul_pos (by norm_num) hρ)) (Real.exp_ne_zero _),Real.log_exp]
  push_cast
  ring

def widthB (ρ σ θ x y : ℝ) : ℂ :=
  phaseKernel σ (θ/2) x y /
    (phaseKernel ρ θ x y ^ (1/2:ℂ)*phaseKernel ρ (-θ) x y)

def widthC (ρ σ θ x y : ℝ) : ℂ :=
  phaseKernel σ (-θ/2) x y /
    (phaseKernel ρ θ x y ^ (1/2:ℂ)*phaseKernel ρ (-θ) x y ^ 2)

def normalization (kind : Bool) (ρ σ θ : ℝ) : ℝ :=
  Real.log (2*σ)+Real.log (Real.cos (θ/2))-
    (if kind then 5/2 else 3/2)*(Real.log (2*ρ)+Real.log (Real.cos θ))

private theorem half_strip (θ : ℝ) (hθ : |θ| < Real.pi/2) : |θ/2| < Real.pi/2 := by
  rw [abs_div]; norm_num; linarith [abs_nonneg θ,Real.pi_pos]

private theorem negative_strip (θ : ℝ) (hθ : |θ| < Real.pi/2) : |-θ| < Real.pi/2 := by
  simpa only [abs_neg] using hθ

private theorem logRatio_B_expand (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    logRatio false θ z =
      Complex.log (Complex.cosh (shifted θ z))-((Real.log (Real.cos (θ/2)):ℝ):ℂ)-
      (Complex.log (Complex.cosh (shifted (2*θ) z))-((Real.log (Real.cos θ):ℝ):ℂ))/2-
      (Complex.log (Complex.cosh (shifted (-2*θ) z))-((Real.log (Real.cos θ):ℝ):ℂ)) := by
  rw [Complex.ofReal_log (cos_pos (θ/2) (half_strip θ hθ)).le,
    Complex.ofReal_log (cos_pos θ hθ).le]
  simp [logRatio,Fin.sum_univ_three,coefficient,mode,shifted_cosh_zero]
  ring_nf
  simp only [Complex.cos_neg]
  ring

private theorem logRatio_C_expand (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    logRatio true θ z =
      Complex.log (Complex.cosh (shifted (-θ) z))-((Real.log (Real.cos (θ/2)):ℝ):ℂ)-
      (Complex.log (Complex.cosh (shifted (2*θ) z))-((Real.log (Real.cos θ):ℝ):ℂ))/2-
      2*(Complex.log (Complex.cosh (shifted (-2*θ) z))-((Real.log (Real.cos θ):ℝ):ℂ)) := by
  rw [Complex.ofReal_log (cos_pos (θ/2) (half_strip θ hθ)).le,
    Complex.ofReal_log (cos_pos θ hθ).le]
  simp [logRatio,Fin.sum_univ_three,coefficient,mode,shifted_cosh_zero]
  ring_nf
  simp only [show (θ:ℂ)*(-1/2) = -((θ:ℂ)*(1/2)) by ring,Complex.cos_neg]
  ring

theorem widthB_transport (ρ σ θ x y : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : |θ| < Real.pi/2) :
    widthB ρ σ θ x y = (Real.exp (normalization false ρ σ θ-(x+y)/2):ℂ)*ratioB θ (x-y) := by
  have hn := phaseKernel_ne σ (θ/2) x y hσ (half_strip θ hθ)
  have hs := phaseKernel_ne ρ θ x y hρ hθ
  have ht := phaseKernel_ne ρ (-θ) x y hρ (negative_strip θ hθ)
  have he : widthB ρ σ θ x y = Complex.exp
      (Complex.log (phaseKernel σ (θ/2) x y)-
        Complex.log (phaseKernel ρ θ x y)/2-Complex.log (phaseKernel ρ (-θ) x y)) := by
    rw [Complex.exp_sub,Complex.exp_sub,Complex.exp_log hn,Complex.exp_log ht]
    unfold widthB
    rw [Complex.cpow_def_of_ne_zero hs]
    rw [show Complex.log (phaseKernel ρ θ x y)*(1/2:ℂ) =
      Complex.log (phaseKernel ρ θ x y)/2 by ring]
    exact (div_div _ _ _).symm
  rw [he,← exp_logRatio_B θ (x-y) hθ,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  rw [phaseKernel_log σ (θ/2) x y hσ (half_strip θ hθ),
    phaseKernel_log ρ θ x y hρ hθ,
    phaseKernel_log ρ (-θ) x y hρ (negative_strip θ hθ),logRatio_B_expand θ (x-y) hθ]
  simp only [normalization,Bool.false_eq_true,ite_false]
  rw [show 2*(θ/2)=θ by ring,show 2*(-θ) = -2*θ by ring]
  push_cast
  ring

theorem widthC_transport (ρ σ θ x y : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : |θ| < Real.pi/2) :
    widthC ρ σ θ x y = (Real.exp (normalization true ρ σ θ-3*(x+y)/2):ℂ)*ratioC θ (x-y) := by
  have hn := phaseKernel_ne σ (-θ/2) x y hσ (by simpa only [neg_div,abs_neg] using half_strip θ hθ)
  have hs := phaseKernel_ne ρ θ x y hρ hθ
  have ht := phaseKernel_ne ρ (-θ) x y hρ (negative_strip θ hθ)
  have he : widthC ρ σ θ x y = Complex.exp
      (Complex.log (phaseKernel σ (-θ/2) x y)-
        Complex.log (phaseKernel ρ θ x y)/2-2*Complex.log (phaseKernel ρ (-θ) x y)) := by
    rw [Complex.exp_sub,Complex.exp_sub,Complex.exp_log hn,two_mul,Complex.exp_add,
      Complex.exp_log ht,← pow_two]
    unfold widthC
    rw [Complex.cpow_def_of_ne_zero hs]
    rw [show Complex.log (phaseKernel ρ θ x y)*(1/2:ℂ) =
      Complex.log (phaseKernel ρ θ x y)/2 by ring]
    exact (div_div _ _ _).symm
  rw [he,← exp_logRatio_C θ (x-y) hθ,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  rw [phaseKernel_log σ (-θ/2) x y hσ (by simpa only [neg_div,abs_neg] using half_strip θ hθ),
    phaseKernel_log ρ θ x y hρ hθ,
    phaseKernel_log ρ (-θ) x y hρ (negative_strip θ hθ),logRatio_C_expand θ (x-y) hθ]
  simp only [normalization,ite_true]
  rw [show 2*(-θ/2)= -θ by ring,show 2*(-θ) = -2*θ by ring]
  push_cast
  ring

#print axioms phaseKernel_cosh
#print axioms phaseKernel_ne
#print axioms phaseKernel_log
#print axioms widthB_transport
#print axioms widthC_transport
end
end UnifiedTheory.Audit.KFCausalChargedCoolingWidthGeometry
