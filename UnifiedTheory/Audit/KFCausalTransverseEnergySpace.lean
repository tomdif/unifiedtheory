/- A linear subspace of physical L2 states represented by functions smooth
in the transverse variables with finite first transverse derivative energy.
Its definition records actual functions and integrability, not certificates
about an unspecified differential operator. -/
import UnifiedTheory.Audit.KFCausalDampedProductJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseEnergySpace
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDerivativeScaling

def differential (f : Configuration → ℂ) (z : Configuration) : ℂ :=
  directionalDerivative (fun y => f (z.1,y)) z.2

theorem differential_zero : differential 0 = 0 := by
  funext z
  simp [differential,directionalDerivative]

theorem differential_add (f g : Configuration → ℂ)
    (hf : ∀ s, Differentiable ℝ (fun y : Transverse => f (s,y)))
    (hg : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    differential (f+g) = differential f+differential g := by
  funext z
  have hl : Differentiable ℝ (fun r : ℝ => z.2+r • direction) := by fun_prop
  exact deriv_add ((hf z.1).comp hl).differentiableAt ((hg z.1).comp hl).differentiableAt

theorem differential_smul (c : ℂ) (f : Configuration → ℂ) :
    differential (c • f) = c • differential f := by
  funext z
  exact partial_const_mul c (fun y => f (z.1,y)) z.2

def energyFunctions : Submodule ℂ (Configuration → ℂ) where
  carrier := {f | MemLp f 2 ∧ (∀ s, ContDiff ℝ ∞ (fun y : Transverse => f (s,y))) ∧ MemLp (differential f) 2}
  zero_mem' := ⟨MemLp.zero,fun _ => contDiff_const,by rw [differential_zero]; exact MemLp.zero⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1,fun s => (hf.2.1 s).add (hg.2.1 s),?_⟩
    rw [differential_add f g (fun s => (hf.2.1 s).differentiable (by simp))
      (fun s => (hg.2.1 s).differentiable (by simp))]
    exact hf.2.2.add hg.2.2
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c,fun s => (hf.2.1 s).const_smul c,?_⟩
    rw [differential_smul]
    exact hf.2.2.const_smul c

def embedding : energyFunctions →ₗ[ℂ] Hilbert where
  toFun f := f.property.1.toLp f
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

theorem embedding_coe (f : energyFunctions) : embedding f =ᵐ[volume] (f : Configuration → ℂ) :=
  f.property.1.coeFn_toLp

def energySpace : Submodule ℂ Hilbert := LinearMap.range embedding

theorem mem_energySpace_iff (f : Hilbert) : f ∈ energySpace ↔
    ∃ g : Configuration → ℂ, MemLp g 2 ∧
      (∀ s, ContDiff ℝ ∞ (fun y : Transverse => g (s,y))) ∧
      MemLp (differential g) 2 ∧ f =ᵐ[volume] g := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g,g.property.1,g.property.2.1,g.property.2.2,embedding_coe g⟩
  · rintro ⟨g,hg,hs,hd,he⟩
    refine ⟨⟨g,hg,hs,hd⟩,?_⟩
    apply Lp.ext
    exact (embedding_coe ⟨g,hg,hs,hd⟩).trans he.symm

#print axioms differential_zero
#print axioms differential_add
#print axioms differential_smul
#print axioms energyFunctions
#print axioms embedding_coe
#print axioms mem_energySpace_iff

end
end UnifiedTheory.Audit.KFCausalTransverseEnergySpace
