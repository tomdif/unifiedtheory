/- Two actual transverse-momentum actions on an unsourced Gaussian,
with arbitrary L2 clock profile. Polynomial Gaussian moments prove the
second output is in L2; no second-domain premise is introduced. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianStates
import UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalGaussianSecondMomentum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalPhysicalGaussianMoments (widths physicalGaussian_memLp)
open KFCausalPhysicalGaussianDerivative
  (physicalGaussian_differentiable physicalGaussian_hasLineDerivAt configuration_product_memLp)
open KFCausalDirectionalGaussianStates (linearForm direction_power_memLp)
open KFCausalTransverseTrialDerivative (derivative)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalTransverseMomentumDerivative (derivative_momentum_graph)

def direction (α β : ℝ) (v : Transverse) : Transverse := fun i => -2*widths α β i*v i

def profile (α β : ℝ) (g : ℝ → ℂ) (x : Configuration) : ℂ :=
  g x.1*physicalGaussian α β x.2

def first (α β : ℝ) (g : ℝ → ℂ) (v : Transverse) (x : Configuration) : ℂ :=
  g x.1*((linearForm (direction α β v) x.2:ℂ)*physicalGaussian α β x.2)

def second (α β : ℝ) (g : ℝ → ℂ) (v : Transverse) (x : Configuration) : ℂ :=
  g x.1*(((linearForm (direction α β v) x.2:ℂ)^2+
    (linearForm (direction α β v) v:ℂ))*physicalGaussian α β x.2)

theorem linearForm_hasLineDerivAt (d q v : Transverse) :
    HasLineDerivAt ℝ (fun q => (linearForm d q:ℂ)) (linearForm d v:ℂ) q v := by
  have hl (i : Fin 5) : HasDerivAt (fun t : ℝ => d i*(q i+t*v i)) (d i*v i) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (q i)).const_mul (d i) using 1
    simp
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hl i)
  exact hs.ofReal_comp

theorem gaussian_line_derivative (α β : ℝ) (v q : Transverse) :
    HasLineDerivAt ℝ (physicalGaussian α β)
      ((linearForm (direction α β v) q:ℂ)*physicalGaussian α β q) q v := by
  have hg := physicalGaussian_hasLineDerivAt α β v q
  convert hg using 1
  simp only [linearForm,direction,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,
    KFCausalPhysicalGaussianDerivative.gradient]

theorem profile_derivative (α β : ℝ) (g : ℝ → ℂ) (v : Transverse) :
    derivative v (profile α β g) = first α β g v := by
  funext x
  exact ((gaussian_line_derivative α β v x.2).const_mul (g x.1)).deriv

theorem first_derivative (α β : ℝ) (g : ℝ → ℂ) (v : Transverse) :
    derivative v (first α β g v) = second α β g v := by
  funext x
  have hd := ((linearForm_hasLineDerivAt (direction α β v) x.2 v).mul
    (gaussian_line_derivative α β v x.2)).const_mul (g x.1)
  convert hd.deriv using 1
  unfold second
  simp only [zero_smul,add_zero]
  ring

theorem profile_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) : MemLp (profile α β g) 2 volume :=
  configuration_product_memLp _ _ hg (physicalGaussian_memLp α β hα hβ)

theorem first_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    MemLp (first α β g v) 2 volume := by
  exact configuration_product_memLp _ _ hg
    (by simpa only [pow_one] using direction_power_memLp α β hα hβ (direction α β v) 1)

theorem second_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (v : Transverse) :
    MemLp (second α β g v) 2 volume := by
  have hm := (direction_power_memLp α β hα hβ (direction α β v) 2).add
    ((physicalGaussian_memLp α β hα hβ).const_mul (linearForm (direction α β v) v:ℂ))
  refine configuration_product_memLp g
    (fun q => ((linearForm (direction α β v) q:ℂ)^2+
      (linearForm (direction α β v) v:ℂ))*physicalGaussian α β q) hg ?_
  convert hm using 1
  funext q
  simp only [Pi.add_apply]
  ring

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
  (h : ℝ) (v : Transverse)

def state : Hilbert := (profile_memLp α β hα hβ g hg).toLp (profile α β g)
def firstOutput : Hilbert := (-Complex.I*(h:ℂ)) •
  (first_memLp α β hα hβ g hg v).toLp (first α β g v)
def secondOutput : Hilbert := (-Complex.I*(h:ℂ))^2 •
  (second_memLp α β hα hβ g hg v).toLp (second α β g v)

theorem first_graph : (state α β hα hβ g hg,firstOutput α β hα hβ g hg h v) ∈
    (transverseMomentum h v).graph := by
  have hd : MemLp (derivative v (profile α β g)) 2 volume := by
    rw [profile_derivative]
    exact first_memLp α β hα hβ g hg v
  have he := derivative_momentum_graph h _ v (profile_memLp α β hα hβ g hg) hd
    (fun s => (physicalGaussian_differentiable α β).const_mul (g s))
  simpa only [profile_derivative] using he

theorem second_graph :
    (firstOutput α β hα hβ g hg h v,secondOutput α β hα hβ g hg h v) ∈
      (transverseMomentum h v).graph := by
  have hd : MemLp (derivative v (first α β g v)) 2 volume := by
    rw [first_derivative]
    exact second_memLp α β hα hβ g hg v
  have hs (s : ℝ) : Differentiable ℝ (fun q : Transverse => first α β g v (s,q)) := by
    have hl : Differentiable ℝ (fun q : Transverse => (linearForm (direction α β v) q:ℂ)) := by
      have hr : Differentiable ℝ (linearForm (direction α β v)) := by
        unfold linearForm
        fun_prop
      exact Complex.ofRealCLM.differentiable.comp hr
    exact (hl.mul (physicalGaussian_differentiable α β)).const_mul (g s)
  have he := derivative_momentum_graph h _ v (first_memLp α β hα hβ g hg v) hd hs
  have he' := (transverseMomentum h v).graph.smul_mem (-Complex.I*(h:ℂ)) he
  simpa only [first_derivative,Prod.smul_mk,smul_smul,← pow_two] using he'

#print axioms linearForm_hasLineDerivAt
#print axioms gaussian_line_derivative
#print axioms profile_derivative
#print axioms first_derivative
#print axioms profile_memLp
#print axioms first_memLp
#print axioms second_memLp
#print axioms first_graph
#print axioms second_graph
end
end UnifiedTheory.Audit.KFCausalGaussianSecondMomentum
