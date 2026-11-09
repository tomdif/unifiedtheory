/- Exact transverse derivatives of physical sourced Gaussians. The
derivative and the state are in L2 for arbitrary complex sources and
square-integrable clock factors. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
import UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
  (physicalGaussian_differentiable physicalGaussian_hasLineDerivAt configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)

theorem linearSource_hasLineDerivAt (b : Fin 5 → ℂ) (v x : Transverse) :
    HasLineDerivAt ℝ (linearSource b) (linearSource b v) x v := by
  have hl (i : Fin 5) : HasDerivAt (fun t : ℝ => x i+t*v i) (v i) 0 := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) => (hl i).ofReal_comp.const_mul (b i))
  change HasDerivAt (fun t : ℝ => linearSource b (x+t • v)) (linearSource b v) 0
  convert hsum using 1

def gradient (α β : ℝ) (b : Fin 5 → ℂ) (v x : Transverse) : ℂ :=
  linearSource b v*sourcedPacket α β b x+
    ∑ i : Fin 5, (-2*widths α β i*v i:ℝ)*(x i:ℂ)*sourcedPacket α β b x

theorem sourcedPacket_differentiable (α β : ℝ) (b : Fin 5 → ℂ) :
    Differentiable ℝ (sourcedPacket α β b) := by
  have hs : Differentiable ℝ (linearSource b) := by
    unfold linearSource
    apply Differentiable.fun_sum
    intro i _
    exact (Complex.ofRealCLM.differentiable.comp (differentiable_apply i)).const_mul (b i)
  exact hs.cexp.mul (physicalGaussian_differentiable α β)

theorem sourcedPacket_hasLineDerivAt (α β : ℝ) (b : Fin 5 → ℂ) (v x : Transverse) :
    HasLineDerivAt ℝ (sourcedPacket α β b) (gradient α β b v x) x v := by
  have hs := linearSource_hasLineDerivAt b v x
  have hg := physicalGaussian_hasLineDerivAt α β v x
  change HasDerivAt (fun t : ℝ => linearSource b (x+t • v)) (linearSource b v) 0 at hs
  change HasDerivAt (fun t : ℝ => physicalGaussian α β (x+t • v))
    (KFCausalPhysicalGaussianDerivative.gradient α β v x) 0 at hg
  have hmul : Complex.exp (linearSource b x)*KFCausalPhysicalGaussianDerivative.gradient α β v x =
      ∑ i : Fin 5, (-2*widths α β i*v i:ℝ)*(x i:ℂ)*sourcedPacket α β b x := by
    rw [KFCausalPhysicalGaussianDerivative.gradient,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold sourcedPacket
    ring
  change HasDerivAt (fun t : ℝ => sourcedPacket α β b (x+t • v)) (gradient α β b v x) 0
  convert hs.cexp.mul hg using 1
  simp only [zero_smul,add_zero,gradient]
  rw [← hmul]
  unfold sourcedPacket
  ring

theorem gradient_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (v : Transverse) : MemLp (gradient α β b v) 2 volume := by
  apply ((sourcedPacket_memLp α β hα hβ hw b).const_mul (linearSource b v)).add
  apply memLp_finset_sum
  intro i _
  simpa only [mul_assoc] using
    (sourcedPacket_coordinate_memLp α β hα hβ hw b i).const_mul ((-2*widths α β i*v i:ℝ):ℂ)

theorem clockPhase_real_norm (p s : ℝ) : ‖clockPhase p (s:ℂ)‖ = 1 := by
  rw [clockPhase,Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

def clockMultiplier (C : ℂ) (p : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ := C*clockPhase p (s:ℂ)*g s

theorem clockMultiplier_memLp (C : ℂ) (p : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    MemLp (clockMultiplier C p g) 2 volume := by
  have hc : Continuous (fun s : ℝ => C*clockPhase p (s:ℂ)) := by unfold clockPhase; fun_prop
  apply (hg.const_mul C).of_le (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with s
  change ‖C*clockPhase p (s:ℂ)*g s‖ ≤ ‖C*g s‖
  simp only [norm_mul,clockPhase_real_norm,mul_one,le_refl]

def physicalProfile (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (z : Configuration) : ℂ :=
  clockMultiplier C p g z.1*sourcedPacket α β b z.2

theorem physicalProfile_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    MemLp (physicalProfile C p α β b g) 2 volume :=
  configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg) (sourcedPacket_memLp α β hα hβ hw b)

theorem physicalProfile_derivative (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (v : Transverse) (z : Configuration) :
    derivative v (physicalProfile C p α β b g) z = clockMultiplier C p g z.1*gradient α β b v z.2 :=
  ((sourcedPacket_hasLineDerivAt α β b v z.2).const_mul (clockMultiplier C p g z.1)).deriv

theorem physicalProfile_transverse_differentiable (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (s : ℝ) :
    Differentiable ℝ (fun y : Transverse => physicalProfile C p α β b g (s,y)) :=
  (sourcedPacket_differentiable α β b).const_mul (clockMultiplier C p g s)

theorem physicalProfile_derivative_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    MemLp (derivative v (physicalProfile C p α β b g)) 2 volume := by
  have he := funext (physicalProfile_derivative C p α β b g v)
  rw [he]
  exact configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg) (gradient_memLp α β hα hβ hw b v)

#print axioms linearSource_hasLineDerivAt
#print axioms sourcedPacket_differentiable
#print axioms sourcedPacket_hasLineDerivAt
#print axioms gradient_memLp
#print axioms clockPhase_real_norm
#print axioms clockMultiplier_memLp
#print axioms physicalProfile_memLp
#print axioms physicalProfile_derivative
#print axioms physicalProfile_transverse_differentiable
#print axioms physicalProfile_derivative_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
