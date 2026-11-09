/- Exact differentiated cross kernels between distinct neutral
exponential-polynomial profiles. The complex coefficients and both
source parameters are retained. -/
import UnifiedTheory.Audit.KFCausalNeutralDisplacedResponseBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralCrossKernel
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles)

def crossKernel (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  star C*D*KFCausalPolynomialLocalKernel.integralValue ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n s
def crossDerivative (ε y α β : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  star C*D*KFCausalPolynomialLocalKernel.integralDerivative ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n s

theorem profileFactor_coefficient (α β : ℝ) (r b C : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (q : Transverse) :
    profileFactor α β r (exponentialProfile b C P) n q =
      C*profileFactor α β r (exponentialProfile b 1 P) n q := by
  unfold profileFactor exponentialProfile
  ring

theorem cross_integrable (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    Integrable (fun q : Transverse =>
      star (profileFactor α β (scale ε y s) (exponentialProfile b C P) n q)*
        profileFactor α β (scale ε y s) (exponentialProfile c D Q) n q) volume :=
  (exponentialProfile_factor_memLp α β ε y s hα hβ hw hε hy b C P n).star.integrable_mul
    (exponentialProfile_factor_memLp α β ε y s hα hβ hw hε hy c D Q n)

theorem unit_crossKernel_gram (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    KFCausalPolynomialLocalKernel.integralValue ε y α β
      (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
      P Q pointField n s =
      ∫ q : Transverse,
        star (profileFactor α β (scale ε y s) (exponentialProfile b 1 P) n q)*
          profileFactor α β (scale ε y s) (exponentialProfile c 1 Q) n q := by
  have hi := KFCausalPolynomialLocalKernel.value_integrable ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n hε hy continuous_const continuous_const continuous_const continuous_const
    (neutralSource b) (neutralSource c) hα hβ hw (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) s
  unfold KFCausalPolynomialLocalKernel.integralValue KFCausalPolynomialLocalKernel.measure
  rw [integral_prod_symm _ hi]
  simp [KFCausalPolynomialLocalKernel.value,exponentialProfile_factor]

theorem crossKernel_gram (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    crossKernel ε y α β b c C D P Q n s =
      ∫ q : Transverse,
        star (profileFactor α β (scale ε y s) (exponentialProfile b C P) n q)*
          profileFactor α β (scale ε y s) (exponentialProfile c D Q) n q := by
  rw [crossKernel,unit_crossKernel_gram α β ε y s hα hβ hw hε hy]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [profileFactor_coefficient α β _ b C,profileFactor_coefficient α β _ c D,star_mul]
  ring

theorem crossKernel_derivative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (b c C D : ℂ) (P Q : Polynomial ℂ) (n : ℕ) :
    HasDerivAt (crossKernel ε y α β b c C D P Q n)
      (crossDerivative ε y α β b c C D P Q n s) s :=
  (KFCausalPolynomialLocalKernel.integral_derivative ε y α β
    (fun _ => neutralSource b) (fun _ => neutralSource c) (fun _ => 1) (fun _ => 1)
    P Q pointField n hε hy continuous_const continuous_const continuous_const continuous_const
    (neutralSource b) (neutralSource c) hα hβ hw (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) s).const_mul (star C*D)

#print axioms profileFactor_coefficient
#print axioms cross_integrable
#print axioms unit_crossKernel_gram
#print axioms crossKernel_gram
#print axioms crossKernel_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralCrossKernel
