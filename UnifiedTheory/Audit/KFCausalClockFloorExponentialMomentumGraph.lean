/- Exact interchange of the actual longitudinal momentum and its
positive exponential, including the two composition domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (a : ℝ)
local notation "L" => longitudinalMomentum ε hε h
local notation "E" => longitudinalExponential ε hε h a
include hne

theorem graph_interchange (f lf ef z : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (he : (f,ef) ∈ (E).graph) :
    (lf,z) ∈ (E).graph ↔ (ef,z) ∈ (L).graph := by
  rw [momentum_graph_fourier_iff ε hε h hne] at hl
  rw [longitudinal_exponential_graph] at he ⊢
  rw [momentum_graph_fourier_iff ε hε h hne]
  have hm : (fun k => (Real.exp (a*symbol h k):ℂ)*(coupledFourier ε hε lf) k) =ᵐ[volume]
      fun k => (symbol h k:ℂ)*(coupledFourier ε hε ef) k := by
    filter_upwards [hl,he] with k hk hj
    rw [hk,hj]
    ring
  exact ⟨fun hz => hz.trans hm,fun hz => hz.trans hm.symm⟩

theorem composition_domain_iff (f lf ef : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (he : (f,ef) ∈ (E).graph) :
    lf ∈ (E).domain ↔ ef ∈ (L).domain := by
  constructor
  · intro hz
    exact LinearPMap.mem_domain_of_mem_graph
      ((graph_interchange ε hε h hne a f lf ef _ hl he).mp ((E).mem_graph ⟨lf,hz⟩))
  · intro hz
    exact LinearPMap.mem_domain_of_mem_graph
      ((graph_interchange ε hε h hne a f lf ef _ hl he).mpr ((L).mem_graph ⟨ef,hz⟩))

theorem compositions_equal (f lf ef elf lef : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (he : (f,ef) ∈ (E).graph)
    (hel : (lf,elf) ∈ (E).graph) (hle : (ef,lef) ∈ (L).graph) : lef = elf :=
  (L).mem_graph_snd_inj' hle ((graph_interchange ε hε h hne a f lf ef elf hl he).mp hel) rfl

#print axioms graph_interchange
#print axioms composition_domain_iff
#print axioms compositions_equal
end
end UnifiedTheory.Audit.KFCausalClockFloorExponentialMomentumGraph
