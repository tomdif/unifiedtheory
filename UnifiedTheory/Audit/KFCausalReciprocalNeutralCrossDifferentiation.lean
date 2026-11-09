/- The full complex cross kernel is C1 by polarization of the already
differentiated complete energies. This keeps unequal reciprocal widths,
complex sources and arbitrary neutral polynomials. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossDifferentiation
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralKernel (kernel)
open KFCausalReciprocalNeutralPositiveForm (pairing)

theorem kernel_conj (α β w v : ℝ) (r b d : ℂ) (P Q : Polynomial ℂ) :
    conj (kernel α β w v r (exponentialProfile b 1 P) (exponentialProfile d 1 Q)) =
      kernel α β v w r (exponentialProfile d 1 Q) (exponentialProfile b 1 P) := by
  unfold kernel
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    simp only [KFCausalReciprocalNeutralSliceIntegrability.density_decomposition,
      map_add,map_div₀,map_mul,map_ofNat,starRingEnd_self_apply]
    ring)

def quadratic (M : Fin 2 → Fin 2 → ℂ) (c : Fin 2 → ℂ) : ℝ :=
  (∑ i, ∑ j, (conj (c i)*c j)*M i j).re

theorem matrix_polarization (M : Fin 2 → Fin 2 → ℂ) (hM : conj (M 0 1) = M 1 0) :
    M 0 1 = ((quadratic M ![1,1]-quadratic M ![1,-1])/4:ℝ)-
      Complex.I*((quadratic M ![1,Complex.I]-quadratic M ![1,-Complex.I])/4:ℝ) := by
  have h10 : M 1 0 = conj (M 0 1) := hM.symm
  apply Complex.ext <;>
    simp [quadratic,Fin.sum_univ_two,h10,Complex.mul_re,Complex.mul_im] <;> ring

def actual (ε y α β w v : ℝ) (b d : ℂ) (P Q : Polynomial ℂ) (s : ℝ) : ℂ :=
  kernel α β w v (scale ε y s) (exponentialProfile b 1 P) (exponentialProfile d 1 Q)

variable (ε y α β w v : ℝ) (b d : ℂ) (P Q : Polynomial ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : 1 ≤ w) (hv : 1 ≤ v)

include hε hy hα hβ hwidth hw hv in
theorem actual_contDiff : ContDiff ℝ 1 (actual ε y α β w v b d P Q) := by
  let W : Fin 2 → ℝ := ![w,v]
  let B : Fin 2 → ℂ := ![b,d]
  let R : Fin 2 → Polynomial ℂ := ![P,Q]
  let q (c : Fin 2 → ℂ) (s : ℝ) : ℝ :=
    (pairing 2 α β W (scale ε y s) c c (fun i => exponentialProfile (B i) 1 (R i))).re
  have hW (i : Fin 2) : 1 ≤ W i := by fin_cases i <;> assumption
  have hq (c : Fin 2 → ℂ) : ContDiff ℝ 1 (q c) :=
    KFCausalReciprocalNeutralKernelDerivative.pairing_contDiff 2 ε y α β W B R (fun _ => c)
      hε hy hα hβ hwidth hW (fun _ => contDiff_const)
  have he : actual ε y α β w v b d P Q = fun s =>
      ((q ![1,1] s-q ![1,-1] s)/4:ℝ)-
        Complex.I*((q ![1,Complex.I] s-q ![1,-Complex.I] s)/4:ℝ) := by
    funext s
    exact matrix_polarization
      (fun i j => kernel α β (W i) (W j) (scale ε y s)
        (exponentialProfile (B i) 1 (R i)) (exponentialProfile (B j) 1 (R j)))
      (kernel_conj α β w v (scale ε y s) b d P Q)
  rw [he]
  exact (Complex.ofRealCLM.contDiff.comp (((hq ![1,1]).sub (hq ![1,-1])).div_const 4)).sub
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (((hq ![1,Complex.I]).sub (hq ![1,-Complex.I])).div_const 4)))

include hε hy hα hβ hwidth hw hv in
theorem actual_derivative (s : ℝ) :
    HasDerivAt (actual ε y α β w v b d P Q) (deriv (actual ε y α β w v b d P Q) s) s :=
  ((actual_contDiff ε y α β w v b d P Q hε hy hα hβ hwidth hw hv).differentiable
    (by norm_num)).differentiableAt.hasDerivAt

include hε hy hα hβ hwidth hw hv in
theorem derivative_continuous : Continuous (deriv (actual ε y α β w v b d P Q)) :=
  (actual_contDiff ε y α β w v b d P Q hε hy hα hβ hwidth hw hv).continuous_deriv_one

#print axioms kernel_conj
#print axioms matrix_polarization
#print axioms actual_contDiff
#print axioms actual_derivative
#print axioms derivative_continuous
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossDifferentiation
