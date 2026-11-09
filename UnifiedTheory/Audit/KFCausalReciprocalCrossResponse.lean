/- The off-diagonal kernel is continuously differentiable along the actual
clock scale. The exact finite-interval response identity retains both
boundary values and the full complex kernel derivative. No matrix
inequality or vanishing boundary limit is assumed here. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossGram
import UnifiedTheory.Audit.KFCausalClockResponseTransport
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalCrossResponse
noncomputable section
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalReciprocalCrossKernel (kernel formula)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockResponseTransport (clock pair weakPair reduced)

private theorem nonzero_of_re_pos (b : ℂ) (hb : 0 < b.re) : b ≠ 0 := by
  intro hz
  simp only [hz,Complex.zero_re,lt_self_iff_false] at hb

theorem gaussianValue_smooth (b : ℂ) (hb : 0 < b.re) :
    ContDiffAt ℝ ⊤ gaussianValue b := by
  have hz := nonzero_of_re_pos b hb
  have hd : AnalyticAt ℂ (fun z : ℂ => (Real.pi:ℂ)/z) b :=
    analyticAt_const.div analyticAt_id hz
  have hp : (Real.pi:ℂ)/b ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [Complex.div_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
    exact div_pos (mul_pos Real.pi_pos hb) (Complex.normSq_pos.mpr hz)
  exact ((hd.cpow (analyticAt_const (v := (1/2:ℂ))) hp).contDiffAt).restrict_scalars ℝ

theorem formula_smooth (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    ContDiffAt ℝ ⊤ (formula α β w v) r := by
  obtain ⟨ha,hb,hc,_⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v r hw hv hA hC hβ
  have hre : ContDiffAt ℝ ⊤ Complex.re r := Complex.reCLM.contDiff.contDiffAt
  have him : ContDiffAt ℝ ⊤ Complex.im r := Complex.imCLM.contDiff.contDiffAt
  have hconj : ContDiffAt ℝ ⊤ (starRingEnd ℂ) r := Complex.conjCLE.contDiff.contDiffAt
  have hga := (gaussianValue_smooth _ ha).comp r
    (show ContDiffAt ℝ ⊤ (A α w v) r by unfold A; fun_prop)
  have hgb := (gaussianValue_smooth _ hb).comp r
    (show ContDiffAt ℝ ⊤ (B α w v) r by unfold B; fun_prop)
  have hB' : ContDiffAt ℝ ⊤ (B α w v) r := by unfold B; fun_prop
  have hcorr : ContDiffAt ℝ ⊤ (fun z : ℂ => ((8*β*z.im^2:ℝ):ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (f := fun z : ℂ => 8*β*z.im^2) r (by fun_prop)
  have hc' : ContDiffAt ℝ ⊤ (C α β w v) r := hB'.sub hcorr
  have hgc := (gaussianValue_smooth _ hc).comp r hc' 
  have hn : 2*C α β w v r ≠ 0 := mul_ne_zero (by norm_num) (nonzero_of_re_pos _ hc)
  have hv' : ContDiffAt ℝ ⊤ (fun z => KFCausalComplexPotentialGaussian.variance
      (C α β w v z) (2*(β:ℂ)) (KFCausalChargedPairCoordinates.fieldSlope z)) r := by
    unfold KFCausalComplexPotentialGaussian.variance KFCausalChargedPairCoordinates.fieldSlope
    have hd : ContDiffAt ℝ ⊤ (fun z : ℂ => ((3-2*z.re:ℝ):ℂ)) r :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (f := fun z : ℂ => 3-2*z.re) r (by fun_prop)
    simp only [div_eq_mul_inv]
    exact contDiffAt_const.add ((hd.pow 2).mul ((contDiffAt_const.mul hc').inv hn))
  unfold formula KFCausalComplexPotentialGaussian.formula
  exact contDiffAt_const.mul
    (((((hga.pow 2).mul hgb).mul hgc).mul contDiffAt_const).mul
      ((contDiffAt_const.add (hv'.div_const 2)).add ((contDiffAt_const.mul (hv'.pow 2)).div_const 4)))

def actualKernel (α β ε y w v s : ℝ) : ℂ := kernel α β w v (scale ε y s)

theorem actual_smooth (α β ε y w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) : ContDiff ℝ 1 (actualKernel α β ε y w v) := by
  have he : actualKernel α β ε y w v = fun s => formula α β w v (scale ε y s) := by
    funext s
    exact KFCausalReciprocalCrossKernel.actual_formula α β ε y s w v hα hβ hwidth hε hy hw hv
  rw [he]
  apply contDiff_iff_contDiffAt.mpr
  intro s
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact ((formula_smooth α β w v _ hw hv ha hc hβ).of_le (by simp)).comp (f := scale ε y) s
    (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy).contDiffAt

theorem actual_derivative (α β ε y w v s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) :
    HasDerivAt (actualKernel α β ε y w v) (deriv (actualKernel α β ε y w v) s) s :=
  ((actual_smooth α β ε y w v hα hβ hwidth hε hy hw hv).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem actual_derivative_continuous (α β ε y w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) : Continuous (deriv (actualKernel α β ε y w v)) :=
  (actual_smooth α β ε y w v hα hβ hwidth hε hy hw hv).continuous_deriv_one

theorem interval_response (α β ε y w v a b l u : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) :
    (∫ s in l..u, actualKernel α β ε y w v s*weakPair ε a b 0 0 y s) =
      actualKernel α β ε y w v u*pair ε a b 0 0 y u/(clock ε u:ℂ)-
      actualKernel α β ε y w v l*pair ε a b 0 0 y l/(clock ε l:ℂ)+
      ∫ s in l..u, reduced ε a b 0 0 y
        (actualKernel α β ε y w v) (deriv (actualKernel α β ε y w v)) s :=
  KFCausalClockResponseTransport.interval_response ε a b 0 0 y hε hy _ _
    (actual_smooth α β ε y w v hα hβ hwidth hε hy hw hv).continuous
    (actual_derivative_continuous α β ε y w v hα hβ hwidth hε hy hw hv)
    (fun s => actual_derivative α β ε y w v s hα hβ hwidth hε hy hw hv) l u

#print axioms gaussianValue_smooth
#print axioms formula_smooth
#print axioms actual_smooth
#print axioms actual_derivative
#print axioms actual_derivative_continuous
#print axioms interval_response
end
end UnifiedTheory.Audit.KFCausalReciprocalCrossResponse
