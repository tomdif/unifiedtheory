/- The full free Hamiltonian is the sum of the two explicit maximal
operators, with equality of operator domains, not just equality of forms. -/
import UnifiedTheory.Audit.KFCausalClockFloorFreeFormSum
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorFreeOperatorSum
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)

private theorem data_ext
    (D E : KFCausalClosedGraphForm.Data Hilbert KFCausalAveragedOutputRescaling.EnergyOutputSpace)
    (ho : D.operator = E.operator) : D = E := by
  cases D
  cases E
  cases ho
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)

theorem residual_eq_static (hw : |h| ≤ 2*Real.pi*ε/3) (t : ℝ) :
    KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw 0 0 0 t =
      KFCausalClockFloorStaticOperator.operator ε hε h := by
  rw [← KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator ε hε h hh hw 0 0 0 0]
  unfold KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian
    KFCausalClockFloorStaticHamiltonian.hamiltonian
  congr 1
  apply data_ext
  exact KFCausalClockFloorFreeFormSum.residual_operator_eq_static ε hε h hh hw t

variable (hb : |h| ≤ Real.pi*ε/3) (t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw 0 0 0 t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticOperator.operator ε hε h

theorem operator_sum : (H) = (Real.exp (2*t):ℂ) • (K) + (S) := by
  rw [KFCausalClockFloorHamiltonianRadialSum.operator_sum ε hε h hh hb 0 0 0 t,
    residual_eq_static ε hε h hh hw t]

theorem domain_iff (f : Hilbert) : f ∈ (H).domain ↔ f ∈ (K).domain ∧ f ∈ (S).domain := by
  rw [operator_sum ε hε h hh hb t, LinearPMap.add_domain]
  rfl

theorem graph_from_components (f r s : Hilbert)
    (hr : (f, r) ∈ (K).graph) (hs : (f, s) ∈ (S).graph) :
    (f, (Real.exp (2*t):ℂ) • r+s) ∈ (H).graph := by
  rw [operator_sum ε hε h hh hb t]
  obtain ⟨u, hu, hur⟩ := (LinearPMap.mem_graph_iff _).mp hr
  obtain ⟨v, hv, hvs⟩ := (LinearPMap.mem_graph_iff _).mp hs
  have hfu : f ∈ (K).domain := LinearPMap.mem_domain_of_mem_graph hr
  have hfv : f ∈ (S).domain := LinearPMap.mem_domain_of_mem_graph hs
  refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨f, ⟨hfu, hfv⟩⟩, rfl, ?_⟩
  change (Real.exp (2*t):ℂ) • K ⟨f, hfu⟩ + S ⟨f, hfv⟩ = _
  congr 1
  · congr 1
    exact (K).mem_graph_snd_inj' ((K).mem_graph _) hr rfl
  · exact (S).mem_graph_snd_inj' ((S).mem_graph _) hs rfl

#print axioms residual_eq_static
#print axioms operator_sum
#print axioms domain_iff
#print axioms graph_from_components
end
end UnifiedTheory.Audit.KFCausalClockFloorFreeOperatorSum
