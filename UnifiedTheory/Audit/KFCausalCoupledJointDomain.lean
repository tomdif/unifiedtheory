/- A proved dense common subspace for the actual longitudinal
half-exponential and the first transverse derivative energy condition.
This is Hilbert-norm density, not graph-core density or the full Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalCoupledTrialDensity
import UnifiedTheory.Audit.KFCausalTransverseEnergySpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledJointDomain
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalDampedProductJointEnergy
open UnifiedTheory.Audit.KFCausalCoupledTrialDensity
open UnifiedTheory.Audit.KFCausalTransverseEnergySpace
open UnifiedTheory.Audit.KFCausalLongitudinalExponential

theorem trialFunction_transverse_smooth (ε a p s : ℝ) (ψ : SchwartzMap TailSpace ℂ) :
    ContDiff ℝ ∞ (fun x : Transverse => trialFunction ε a p ψ (s,x)) := by
  have hp : ContDiff ℝ ∞ (fun x : Transverse =>
      (ψ ∘ transverseCoordinates) (flow (-phase ε s) x)) :=
    ((unflattenSchwartz ψ).smooth ⊤).comp (flowCLM (-phase ε s)).contDiff
  change ContDiff ℝ ∞ (fun x : Transverse =>
    (Real.sqrt (Real.exp s+ε):ℂ) *
      (modulate p (realTrial ε a) (chart ε s) *
        ((Real.exp (-phase ε s):ℂ) * (ψ ∘ transverseCoordinates) (flow (-phase ε s) x))))
  exact contDiff_const.mul (contDiff_const.mul (contDiff_const.mul hp))

theorem trialState_mem_energySpace (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) : trialState ε a p hε ha ψ (ψ.memLp 2 volume) ∈ energySpace := by
  apply (mem_energySpace_iff _).mpr
  exact ⟨trialFunction ε a p ψ,trialFunction_memLp ε a p hε ha ψ (ψ.memLp 2 volume),
    fun s => trialFunction_transverse_smooth ε a p s ψ,
    transverseDerivative_memLp ε a p hε ha ψ,trialState_coe ε a p hε ha ψ (ψ.memLp 2 volume)⟩

def jointSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ Hilbert :=
  energySpace ⊓ (longitudinalExponential ε hε hbar (1/2)).domain

theorem trialFamily_mem_jointSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (v : ℝ × SchwartzMap TailSpace ℂ) :
    trialFamily ε a hε ha v ∈ jointSpace ε hε hbar :=
  ⟨trialState_mem_energySpace ε a v.1 hε ha v.2,
    trialState_half_domain ε a v.1 hbar hε ha hh v.2 v.2.integrable (v.2.memLp 2 volume)⟩

theorem jointSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| < Real.pi*ε) :
    (jointSpace ε hε hbar).topologicalClosure = ⊤ := by
  have hs : Submodule.span ℂ (Set.range (trialFamily ε 1 hε zero_lt_one)) ≤ jointSpace ε hε hbar := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact trialFamily_mem_jointSpace ε 1 hbar hε zero_lt_one hh v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_trial_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem jointSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (f : Hilbert) :
    f ∈ jointSpace ε hε hbar ↔
      f ∈ (longitudinalExponential ε hε hbar (1/2)).domain ∧
        ∃ g : Configuration → ℂ, MemLp g 2 ∧
          (∀ s, ContDiff ℝ ∞ (fun y : Transverse => g (s,y))) ∧
          MemLp (differential g) 2 ∧ f =ᵐ[volume] g := by
  change (f ∈ energySpace ∧ _) ↔ _
  rw [mem_energySpace_iff]
  exact and_comm

#print axioms trialFunction_transverse_smooth
#print axioms trialState_mem_energySpace
#print axioms trialFamily_mem_jointSpace
#print axioms jointSpace_dense
#print axioms jointSpace_conditions

end
end UnifiedTheory.Audit.KFCausalCoupledJointDomain
