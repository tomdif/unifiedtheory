/- The full propagator's strong initial derivative graph has precisely
the actual self-adjoint Hamiltonian graph as its closure. Strong initial
derivatives cannot give a different Hamiltonian or an extra operator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialSchrodinger
import UnifiedTheory.Audit.KFCausalUnitaryInitialGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorGeneratorIdentification
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorInitialSchrodinger

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "H" => hamiltonian ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "R" => shiftedResolvent ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

def coreGraph (a s : ℝ) : Set (Hilbert × Hilbert) :=
  range (fun f : Hilbert => (R a s (R a s f),R a s f-a • R a s (R a s f)))

def generatorGraph (s : ℝ) : Set (Hilbert × Hilbert) :=
  {p | HasDerivAt (fun t => U s t p.1) (c • p.2) s}

theorem resolvent_graph_core (a s : ℝ) (ha : 0 < a) :
    closure (coreGraph ε hε h hne hh m g k a s) = ((H s).graph : Set (Hilbert × Hilbert)) :=
  KFCausalResolventGraphCore.double_resolvent_graph_closure (H s) (R a s) a
    (averaged_resolves ε hε h hne hh m g k a s ha)
    (shiftedResolvent_left ε hε h hne hh m g k a s ha)
    (shiftedResolvent_dense ε hε h hne hh m g k a s ha)
    (hamiltonian_closed ε hε h hne hh m g k s)

theorem initial_derivative_graph_subset (s : ℝ) :
    generatorGraph ε hε h hne hh m g k s ⊆ ((H s).graph : Set (Hilbert × Hilbert)) := by
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (one_div_ne_zero hne))
  have hconj : starRingEnd ℂ c = -c := by
    simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg]
    ring
  have hu (f : Hilbert) : U s s f = f :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
      (evolution_initial ε hε h hne hh m g k s)
  have hd : ∀ p ∈ coreGraph ε hε h hne hh m g k 1 s,
      HasDerivAt (fun t => U s t p.1) (c • p.2) s := by
    rintro p ⟨f,rfl⟩
    exact double_resolvent_initial ε hε h hne hh m g k 1 s (by norm_num) f
  intro p hp
  exact KFCausalUnitaryInitialGenerator.derivative_mem_graph (H s)
    (hamiltonian_selfAdjoint ε hε h hne hh m g k s)
    (coreGraph ε hε h hne hh m g k 1 s)
    (resolvent_graph_core ε hε h hne hh m g k 1 s (by norm_num))
    (fun t f => U s t f) s (fun t f q => evolution_inner ε hε h hne hh m g k s t f q)
    hu c hc hconj hd p.1 p.2 hp

theorem initial_generator_graph_closure (s : ℝ) :
    closure (generatorGraph ε hε h hne hh m g k s) =
      ((H s).graph : Set (Hilbert × Hilbert)) := by
  apply Subset.antisymm
  · exact closure_minimal (initial_derivative_graph_subset ε hε h hne hh m g k s)
      (hamiltonian_closed ε hε h hne hh m g k s)
  · rw [← resolvent_graph_core ε hε h hne hh m g k 1 s (by norm_num)]
    apply closure_mono
    rintro p ⟨f,rfl⟩
    exact double_resolvent_initial ε hε h hne hh m g k 1 s (by norm_num) f

#print axioms resolvent_graph_core
#print axioms initial_derivative_graph_subset
#print axioms initial_generator_graph_closure
end
end UnifiedTheory.Audit.KFCausalClockFloorGeneratorIdentification
