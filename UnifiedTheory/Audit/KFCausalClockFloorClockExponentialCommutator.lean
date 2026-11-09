/- Actual clock/half-exponential compositions on their natural dense
Dom(E C). All domain conditions and the relative commutator bound are
derived from the existing full-domain defect theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator
import UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockExponentialCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator (commonDomain)

theorem commonDomain_dense (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Dense (commonDomain ε hε (longitudinalExponential ε hε h (1/2))) :=
  KFCausalClockFloorClockShiftCommutator.commonDomain_dense ε hε _
    (longitudinal_exponential_dense ε hε h (1/2))

theorem commonDomain_graphs (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert)
    (hf : f ∈ commonDomain ε hε (longitudinalExponential ε hε h (1/2))) :
    ∃ cf ef ecf cef : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧
      (f,ef) ∈ (longitudinalExponential ε hε h (1/2)).graph ∧
      (cf,ecf) ∈ (longitudinalExponential ε hε h (1/2)).graph ∧
      (ef,cef) ∈ (clockOperator ε hε).graph ∧
      cef-ecf = differenceOperator ε hε h hh ef ∧ ‖cef-ecf‖ ≤ |h| * ‖ef‖ :=
  KFCausalClockFloorClockShiftCommutator.commonDomain_graphs ε hε h hh _
    (KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh) f hf

theorem commutator_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f cf ef ecf cef : Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph)
    (he : (f,ef) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hec : (cf,ecf) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hce : (ef,cef) ∈ (clockOperator ε hε).graph) :
    cef-ecf = differenceOperator ε hε h hh ef ∧ ‖cef-ecf‖ ≤ |h| * ‖ef‖ :=
  KFCausalClockFloorClockShiftCommutator.commutator_graph ε hε h hh _
    (KFCausalClockFloorDefectFullDomain.graph_defect ε hε h hh) f cf ef ecf cef hc he hec hce

#print axioms commonDomain_dense
#print axioms commonDomain_graphs
#print axioms commutator_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorClockExponentialCommutator
