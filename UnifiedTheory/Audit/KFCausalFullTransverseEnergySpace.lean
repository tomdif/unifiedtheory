/- A linear physical L2 subspace with one common smooth representative
whose directional derivatives are in L2 for every transverse direction. -/
import UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
import UnifiedTheory.Audit.KFCausalTransverseEnergySpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative

theorem derivative_zero (v : Transverse) : derivative v 0=0 := by
  funext z
  simp [derivative,lineDeriv]

theorem derivative_add (v : Transverse) (f g : Configuration → ℂ)
    (hf : ∀ s, Differentiable ℝ (fun y : Transverse => f (s,y)))
    (hg : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    derivative v (f+g)=derivative v f+derivative v g := by
  funext z
  have hl : Differentiable ℝ (fun r : ℝ => z.2+r • v) := by fun_prop
  exact deriv_add ((hf z.1).comp hl).differentiableAt ((hg z.1).comp hl).differentiableAt

theorem derivative_smul (v : Transverse) (c : ℂ) (f : Configuration → ℂ) :
    derivative v (c • f)=c • derivative v f := by
  funext z
  exact deriv_const_mul_field c

def allEnergyFunctions : Submodule ℂ (Configuration → ℂ) where
  carrier := {f | MemLp f 2 ∧ (∀ s, ContDiff ℝ ∞ (fun y : Transverse => f (s,y))) ∧
    ∀ v : Transverse, MemLp (derivative v f) 2}
  zero_mem' := ⟨MemLp.zero,fun _ => contDiff_const,fun v => by rw [derivative_zero]; exact MemLp.zero⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1,fun s => (hf.2.1 s).add (hg.2.1 s),?_⟩
    intro v
    rw [derivative_add v f g (fun s => (hf.2.1 s).differentiable (by simp))
      (fun s => (hg.2.1 s).differentiable (by simp))]
    exact (hf.2.2 v).add (hg.2.2 v)
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c,fun s => (hf.2.1 s).const_smul c,?_⟩
    intro v
    rw [derivative_smul]
    exact (hf.2.2 v).const_smul c

def allEmbedding : allEnergyFunctions →ₗ[ℂ] Hilbert where
  toFun f := f.property.1.toLp f
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

theorem allEmbedding_coe (f : allEnergyFunctions) : allEmbedding f =ᵐ[volume] (f : Configuration → ℂ) :=
  f.property.1.coeFn_toLp

def allEnergySpace : Submodule ℂ Hilbert := LinearMap.range allEmbedding

theorem mem_allEnergySpace_iff (f : Hilbert) : f ∈ allEnergySpace ↔
    ∃ g : Configuration → ℂ, MemLp g 2 ∧ (∀ s, ContDiff ℝ ∞ (fun y : Transverse => g (s,y))) ∧
      (∀ v : Transverse, MemLp (derivative v g) 2) ∧ f =ᵐ[volume] g := by
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g,g.property.1,g.property.2.1,g.property.2.2,allEmbedding_coe g⟩
  · rintro ⟨g,hg,hs,hd,he⟩
    refine ⟨⟨g,hg,hs,hd⟩,?_⟩
    apply Lp.ext
    exact (allEmbedding_coe ⟨g,hg,hs,hd⟩).trans he.symm

theorem allEnergySpace_le_energySpace : allEnergySpace ≤ KFCausalTransverseEnergySpace.energySpace := by
  intro f hf
  rcases (mem_allEnergySpace_iff f).mp hf with ⟨g,hg,hs,hd,he⟩
  apply (KFCausalTransverseEnergySpace.mem_energySpace_iff f).mpr
  exact ⟨g,hg,hs,hd KFCausalTransverseDerivativeScaling.direction,he⟩

#print axioms derivative_zero
#print axioms derivative_add
#print axioms derivative_smul
#print axioms allEnergyFunctions
#print axioms allEmbedding_coe
#print axioms mem_allEnergySpace_iff
#print axioms allEnergySpace_le_energySpace

end
end UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
