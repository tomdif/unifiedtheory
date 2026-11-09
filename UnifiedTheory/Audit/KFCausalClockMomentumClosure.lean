/- Every physical transverse momentum composed with a real clock power
is densely defined and closable. Explicit Gaussian tensor tests prove
density for both orders; no regulator or Planck-parameter bound is needed. -/
import UnifiedTheory.Audit.KFCausalPhysicalTensorDensity
import UnifiedTheory.Audit.KFCausalGaussianClockWeights
import UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockMomentumClosure
noncomputable section
open MeasureTheory
open scoped LineDeriv
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalPhysicalTensorMomentum
open UnifiedTheory.Audit.KFCausalPhysicalTensorDensity
open UnifiedTheory.Audit.KFCausalGaussianClockWeights

def clockMomentum (b hbar : ℝ) (v : Transverse) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (transverseMomentum hbar v) (clockPower b)

def momentumClock (b hbar : ℝ) (v : Transverse) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (clockPower b) (transverseMomentum hbar v)

theorem clockWeight_modulate (b p : ℝ) (g : ℝ → ℂ) :
    clockWeight b (modulate p g)=modulate p (clockWeight b g) := by
  funext s
  simp only [clockWeight,modulate]
  ring

theorem clockWeight_gaussian_memLp (b p : ℝ) : MemLp (clockWeight b (modulate p gaussian)) 2 := by
  rw [clockWeight_modulate]
  exact modulatedWeightedGaussian_memLp b p

theorem tensor_clockMomentum_graph (b hbar : ℝ) (v : Transverse)
    (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (hg : MemLp g 2)
    (hb : MemLp (clockWeight b g) 2) :
    (tensorState g ψ hg,(-Complex.I*(hbar:ℂ)) • tensorState (clockWeight b g) (∂_{v} ψ) hb) ∈
      (clockMomentum b hbar v).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨tensorState (clockWeight b g) ψ hb,tensor_clock_graph b g ψ hg hb,
    tensor_momentum_graph hbar (clockWeight b g) ψ hb v⟩

theorem tensor_momentumClock_graph (b hbar : ℝ) (v : Transverse)
    (g : ℝ → ℂ) (ψ : SchwartzMap Transverse ℂ) (hg : MemLp g 2)
    (hb : MemLp (clockWeight b g) 2) :
    (tensorState g ψ hg,(-Complex.I*(hbar:ℂ)) • tensorState (clockWeight b g) (∂_{v} ψ) hb) ∈
      (momentumClock b hbar v).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨(-Complex.I*(hbar:ℂ)) • tensorState g (∂_{v} ψ) hg,tensor_momentum_graph hbar g ψ hg v,
    (clockPower b).graph.smul_mem (-Complex.I*(hbar:ℂ)) (tensor_clock_graph b g (∂_{v} ψ) hg hb)⟩

theorem clockMomentum_dense (b hbar : ℝ) (v : Transverse) :
    Dense ((clockMomentum b hbar v).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (tensorFamily gaussian gaussian_memLp)) ≤
      (clockMomentum b hbar v).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨u,rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (tensor_clockMomentum_graph b hbar v
      (modulate u.1 gaussian) (unflattenSchwartz u.2) (modulatedGaussian_memLp u.1)
      (clockWeight_gaussian_memLp b u.1))
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_tensor_span gaussian gaussian_memLp gaussian_ne_zero] at hc
  exact top_unique hc

theorem momentumClock_dense (b hbar : ℝ) (v : Transverse) :
    Dense ((momentumClock b hbar v).domain : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hs : Submodule.span ℂ (Set.range (tensorFamily gaussian gaussian_memLp)) ≤
      (momentumClock b hbar v).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨u,rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (tensor_momentumClock_graph b hbar v
      (modulate u.1 gaussian) (unflattenSchwartz u.2) (modulatedGaussian_memLp u.1)
      (clockWeight_gaussian_memLp b u.1))
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_tensor_span gaussian gaussian_memLp gaussian_ne_zero] at hc
  exact top_unique hc

theorem clockMomentum_closable (b hbar : ℝ) (v : Transverse) : (clockMomentum b hbar v).IsClosable :=
  composition_closable _ _ (transverseMomentum_selfAdjoint hbar v) (clockPower_selfAdjoint b)
    (momentumClock_dense b hbar v)

theorem momentumClock_closable (b hbar : ℝ) (v : Transverse) : (momentumClock b hbar v).IsClosable :=
  composition_closable _ _ (clockPower_selfAdjoint b) (transverseMomentum_selfAdjoint hbar v)
    (clockMomentum_dense b hbar v)

def closedClockMomentum (b hbar : ℝ) (v : Transverse) : Hilbert →ₗ.[ℂ] Hilbert :=
  (clockMomentum b hbar v).closure

theorem clockMomentum_le_closure (b hbar : ℝ) (v : Transverse) :
    clockMomentum b hbar v ≤ closedClockMomentum b hbar v := (clockMomentum b hbar v).le_closure

theorem closedClockMomentum_graph (b hbar : ℝ) (v : Transverse) :
    (closedClockMomentum b hbar v).graph=(clockMomentum b hbar v).graph.topologicalClosure :=
  (clockMomentum_closable b hbar v).graph_closure_eq_closure_graph.symm

theorem closedClockMomentum_closed (b hbar : ℝ) (v : Transverse) :
    (closedClockMomentum b hbar v).IsClosed := (clockMomentum_closable b hbar v).closure_isClosed

theorem closedClockMomentum_dense (b hbar : ℝ) (v : Transverse) :
    Dense ((closedClockMomentum b hbar v).domain : Set Hilbert) :=
  (clockMomentum_dense b hbar v).mono (clockMomentum_le_closure b hbar v).1

#print axioms clockWeight_modulate
#print axioms clockWeight_gaussian_memLp
#print axioms tensor_clockMomentum_graph
#print axioms tensor_momentumClock_graph
#print axioms clockMomentum_dense
#print axioms momentumClock_dense
#print axioms clockMomentum_closable
#print axioms momentumClock_closable
#print axioms clockMomentum_le_closure
#print axioms closedClockMomentum_graph
#print axioms closedClockMomentum_closed
#print axioms closedClockMomentum_dense

end
end UnifiedTheory.Audit.KFCausalClockMomentumClosure
