/- Physical tensor products have exact transverse momentum and clock-power
graphs. The clock function need only satisfy the stated L2 conditions. -/
import UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
import UnifiedTheory.Audit.KFCausalPhysicalClockPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalTensorMomentum
noncomputable section
open MeasureTheory
open scoped LineDeriv ContDiff
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers

def tensorFunction (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (z : Configuration) : ℂ := g z.1*ψ z.2

theorem tensor_memLp (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (hg : MemLp g 2) :
    MemLp (tensorFunction g ψ) 2 := by
  have hm : AEStronglyMeasurable (tensorFunction g ψ) volume :=
    hg.aestronglyMeasurable.comp_fst.mul (ψ.memLp 2 volume).aestronglyMeasurable.comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have h₁ := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have h₂ := (memLp_two_iff_integrable_sq_norm (ψ.memLp 2 volume).aestronglyMeasurable).mp (ψ.memLp 2 volume)
  simpa only [tensorFunction,norm_mul,mul_pow] using h₁.mul_prod h₂

def tensorState (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (hg : MemLp g 2) : Hilbert :=
  (tensor_memLp g ψ hg).toLp (tensorFunction g ψ)

theorem tensorState_coe (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (hg : MemLp g 2) :
    tensorState g ψ hg =ᵐ[volume] tensorFunction g ψ := (tensor_memLp g ψ hg).coeFn_toLp

theorem tensor_derivative (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (v : Transverse) :
    derivative v (tensorFunction g ψ) = tensorFunction g (∂_{v} ψ) := by
  funext z
  change deriv (fun t : ℝ => g z.1*ψ (z.2+t • v)) 0 = g z.1*(∂_{v} ψ) z.2
  rw [deriv_const_mul_field,SchwartzMap.lineDerivOp_apply]
  rfl

theorem tensor_derivative_memLp (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ)
    (hg : MemLp g 2) (v : Transverse) : MemLp (derivative v (tensorFunction g ψ)) 2 := by
  rw [tensor_derivative]
  exact tensor_memLp g (∂_{v} ψ) hg

theorem tensor_momentum_graph (hbar : ℝ) (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ)
    (hg : MemLp g 2) (v : Transverse) :
    (tensorState g ψ hg,(-Complex.I*(hbar:ℂ)) • tensorState g (∂_{v} ψ) hg) ∈
      (transverseMomentum hbar v).graph := by
  have hs : ∀ s, Differentiable ℝ (fun y : Transverse => tensorFunction g ψ (s,y)) := by
    intro s
    simpa only [smul_eq_mul] using
      ((ψ.smooth (⊤ : ℕ∞)).differentiable (by simp)).const_smul (g s)
  have he : (tensor_derivative_memLp g ψ hg v).toLp (derivative v (tensorFunction g ψ)) =
      tensorState g (∂_{v} ψ) hg := by
    apply Lp.ext
    filter_upwards [(tensor_derivative_memLp g ψ hg v).coeFn_toLp,tensorState_coe g (∂_{v} ψ) hg] with z hz ht
    rw [hz,ht,tensor_derivative]
  have h := derivative_momentum_graph hbar (tensorFunction g ψ) v
    (tensor_memLp g ψ hg) (tensor_derivative_memLp g ψ hg v) hs
  rw [he] at h
  exact h

def clockWeight (b : ℝ) (g : ℝ → ℂ) (s : ℝ) : ℂ := (Real.exp (b*s):ℂ)*g s

theorem tensor_clock_graph (b : ℝ) (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ)
    (hg : MemLp g 2) (hb : MemLp (clockWeight b g) 2) :
    (tensorState g ψ hg,tensorState (clockWeight b g) ψ hb) ∈ (clockPower b).graph := by
  apply (clockPower_graph b _ _).mpr
  filter_upwards [tensorState_coe g ψ hg,tensorState_coe (clockWeight b g) ψ hb] with z hg' hb'
  rw [hg',hb']
  simp only [tensorFunction,clockWeight,mul_assoc]

#print axioms tensor_memLp
#print axioms tensorState_coe
#print axioms tensor_derivative
#print axioms tensor_derivative_memLp
#print axioms tensor_momentum_graph
#print axioms tensor_clock_graph

end
end UnifiedTheory.Audit.KFCausalPhysicalTensorMomentum
