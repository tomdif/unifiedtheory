/- Pure-clock differentiation of a controlled physical multiplier times
a sourced shifted Gaussian. The source dependence is separated into a
finite linear sum, allowing graph outputs to vary continuously in L2. -/
import UnifiedTheory.Audit.KFCausalMixedFieldPureClockDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockCalculus
noncomputable section
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalRelativeGaussianDifferential (profile slope position direction)
open KFCausalClockFloorRelativeShift (scale argument)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open KFCausalShiftedGaussianPureDifferential
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalCanonicalClockDerivative (clockDerivative)

def baseCoefficient (ε α β p y : ℝ) (x : Configuration) : ℂ :=
  (p:ℂ)*Complex.I*inverseClock ε y x.1-realInverse ε x.1+
    (inverseClock ε y x.1-realInverse ε x.1)*slope (scale ε y) α β 0 x
def sourceCoefficient (ε y : ℝ) (i : Fin 5) (x : Configuration) : ℂ :=
  (inverseClock ε y x.1-realInverse ε x.1)*direction (scale ε y x.1) x.2 i

theorem baseCoefficient_controlled (ε α β p y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Controlled (baseCoefficient ε α β p y) :=
  controlled_add _ _
    (controlled_sub _ _ (controlled_mul _ _ (controlled_const ((p:ℂ)*Complex.I))
      (inverseClock_controlled ε y hε hy)) (realInverse_controlled ε hε))
    (controlled_mul _ _ (controlled_sub _ _ (inverseClock_controlled ε y hε hy)
      (realInverse_controlled ε hε)) (slope_controlled _ (scale_controlled ε y hε hy) α β 0))

theorem sourceCoefficient_controlled (ε y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (i : Fin 5) : Controlled (sourceCoefficient ε y i) :=
  controlled_mul _ _ (controlled_sub _ _ (inverseClock_controlled ε y hε hy)
    (realInverse_controlled ε hε)) (direction_controlled _ (scale_controlled ε y hε hy) i)

theorem slope_expansion (r : ℝ → ℂ) (α β : ℝ) (b : Fin 5 → ℂ) (x : Configuration) :
    slope r α β b x = slope r α β 0 x+∑ i, b i*direction (r x.1) x.2 i := by
  unfold KFCausalRelativeGaussianDifferential.slope
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.zero_apply]
  ring

theorem gaussian_differential (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (x : Configuration) :
    let F := profile (clockAmplitude ε a p y) (scale ε y) α β b
    differential ε F x = baseCoefficient ε α β p y x*F x+
      ∑ i, b i*(sourceCoefficient ε y i x*F x)-2*(a:ℂ)*(argument ε y x.1*F x) := by
  dsimp only
  rw [pure_differential ε a α β p y b hε hy,slope_expansion]
  unfold baseCoefficient sourceCoefficient
  simp only [add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
  ring

theorem product_differential (ε : ℝ) (m R f : Configuration → ℂ)
    (hm : Differentiable ℝ m) (hf : Differentiable ℝ f)
    (hR : ∀ x, realInverse ε x.1*clockDerivative m x = R x) (x : Configuration) :
    differential ε (fun x => m x*f x) x = R x*f x+m x*differential ε f x := by
  have hF := (hf x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have hM := (hm x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have hP := ((hm.mul hf) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => f (s,x.2)) (clockDerivative f x) x.1 at hF
  change HasDerivAt (fun s => m (s,x.2)) (clockDerivative m x) x.1 at hM
  change HasDerivAt (fun s => m (s,x.2)*f (s,x.2))
    (clockDerivative (fun x => m x*f x) x) x.1 at hP
  have he := hP.unique (hM.mul hF)
  unfold differential
  rw [he]
  change realInverse ε x.1*(clockDerivative m x*f x+m x*clockDerivative f x)+
    _*(m x*f x) = R x*f x+m x*(realInverse ε x.1*clockDerivative f x+_*f x)
  linear_combination f x*(hR x)

theorem weighted_differential (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (m R : Configuration → ℂ)
    (hm : Differentiable ℝ m) (hR : ∀ x, realInverse ε x.1*clockDerivative m x = R x)
    (x : Configuration) :
    let F := profile (clockAmplitude ε a p y) (scale ε y) α β b
    differential ε (fun x => m x*F x) x =
      (R x+m x*baseCoefficient ε α β p y x)*F x+
      ∑ i, b i*((m x*sourceCoefficient ε y i x)*F x)-
      2*(a:ℂ)*(m x*(argument ε y x.1*F x)) := by
  dsimp only
  rw [product_differential ε m R _ hm
    ((KFCausalRelativeGaussianDifferential.profile_smooth _ _
      (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p y hε hy)
      (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy) α β b).differentiable (by norm_num)) hR,
    gaussian_differential ε a α β p y b hε hy]
  simp only [mul_add,mul_sub,Finset.mul_sum,add_mul]
  ring

#print axioms baseCoefficient_controlled
#print axioms sourceCoefficient_controlled
#print axioms slope_expansion
#print axioms gaussian_differential
#print axioms product_differential
#print axioms weighted_differential
end
end UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockCalculus
