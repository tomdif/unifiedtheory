/- Defect stability and the signed exponential form pairing extend to the
closed span of actual coherent exponential graph pairs. Equality with the
entire exponential graph is not assumed or asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectGraphClosure
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds
open UnifiedTheory.Audit.KFCausalClockFloorExponential

abbrev PacketIndex := ℝ × (Fin 5 → ℂ) × ℕ

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
  (a α β : ℝ) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

def packetPair (i : PacketIndex) : Hilbert × Hilbert :=
  (state ε a α β i.1 i.2.1 hε ha hα hβ hw i.2.2 0 (by simp; positivity),
    state ε a α β i.1 i.2.1 hε ha hα hβ hw i.2.2 (-hbar/2) (shift_bound ε hbar hh))

def graphClosure : Submodule ℂ (Hilbert × Hilbert) :=
  (Submodule.span ℂ (Set.range (packetPair ε hε hbar hh a α β ha hα hβ hw))).topologicalClosure

def defectPair : (Hilbert × Hilbert) →L[ℂ] (Hilbert × Hilbert) :=
  (defectOperator ε hε).prodMap (shiftedDefect ε hε hbar hh)

theorem packetPair_mem_graph (i : PacketIndex) :
    packetPair ε hε hbar hh a α β ha hα hβ hw i ∈
      (longitudinalExponential ε hε hbar (1/2)).graph :=
  state_half_graph ε a α β i.1 i.2.1 hε ha hα hβ hw i.2.2 hbar hh _ _

theorem packetPair_mem_closure (i : PacketIndex) :
    packetPair ε hε hbar hh a α β ha hα hβ hw i ∈
      graphClosure ε hε hbar hh a α β ha hα hβ hw :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)

theorem graphClosure_le_graph :
    graphClosure ε hε hbar hh a α β ha hα hβ hw ≤
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply Submodule.topologicalClosure_minimal _ _ (longitudinal_exponential_closed ε hε hbar (1/2))
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact packetPair_mem_graph ε hε hbar hh a α β ha hα hβ hw i

theorem defectPair_packetPair (i : PacketIndex) :
    defectPair ε hε hbar hh (packetPair ε hε hbar hh a α β ha hα hβ hw i) =
      packetPair ε hε hbar hh a α β ha hα hβ hw (i.1,i.2.1,i.2.2+1) := by
  apply Prod.ext
  · exact (state_zero_successor ε a α β i.1 i.2.1 hε ha hα hβ hw i.2.2
      (by simp; positivity)).symm
  · exact shifted_state_successor ε hε hbar hh a α β i.1 i.2.1 ha hα hβ hw i.2.2
      (shift_bound ε hbar hh)

theorem graphClosure_defect_invariant (u : Hilbert × Hilbert)
    (hu : u ∈ graphClosure ε hε hbar hh a α β ha hα hβ hw) :
    defectPair ε hε hbar hh u ∈ graphClosure ε hε hbar hh a α β ha hα hβ hw := by
  let S := Submodule.span ℂ (Set.range (packetPair ε hε hbar hh a α β ha hα hβ hw))
  let T := defectPair ε hε hbar hh
  have hS : S ≤ S.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change defectPair ε hε hbar hh (packetPair ε hε hbar hh a α β ha hα hβ hw i) ∈ S
    rw [defectPair_packetPair]
    exact Submodule.subset_span ⟨(i.1,i.2.1,i.2.2+1),rfl⟩
  have hT : S ≤ S.topologicalClosure.comap T.toLinearMap :=
    fun x hx => S.le_topologicalClosure (hS hx)
  have hc : IsClosed (S.topologicalClosure.comap T.toLinearMap : Set (Hilbert × Hilbert)) :=
    S.isClosed_topologicalClosure.preimage T.continuous
  exact S.topologicalClosure_minimal hT hc hu

/-- Both images and the signed form estimate persist for finite coherent
superpositions and their limits in the actual exponential graph norm. -/
theorem graphClosure_control (f g : Hilbert)
    (hfg : (f,g) ∈ graphClosure ε hε hbar hh a α β ha hα hβ hw) :
    (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph ∧
    (defectOperator ε hε f,shiftedDefect ε hε hbar hh g) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph ∧
    (defectOperator ε hε (defectOperator ε hε f),
      shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g)) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph ∧
    ‖shiftedDefect ε hε hbar hh g-defectOperator ε hε g‖ ≤
      (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε g)‖ ∧
    0 ≤ hbar*(inner ℂ g (shiftedDefect ε hε hbar hh (shiftedDefect ε hε hbar hh g))).im := by
  have h1 := graphClosure_defect_invariant ε hε hbar hh a α β ha hα hβ hw (f,g) hfg
  have h2 := graphClosure_defect_invariant ε hε hbar hh a α β ha hα hβ hw _ h1
  exact ⟨graphClosure_le_graph ε hε hbar hh a α β ha hα hβ hw hfg,
    graphClosure_le_graph ε hε hbar hh a α β ha hα hβ hw h1,
    graphClosure_le_graph ε hε hbar hh a α β ha hα hβ hw h2,
    shiftedDefect_difference ε hε hbar hh g,shiftedDefect_square_form_sign ε hε hbar hh g⟩

#print axioms packetPair_mem_graph
#print axioms packetPair_mem_closure
#print axioms graphClosure_le_graph
#print axioms defectPair_packetPair
#print axioms graphClosure_defect_invariant
#print axioms graphClosure_control

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectGraphClosure
