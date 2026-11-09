/- Multiplication by the actual clock defect preserves the full strong
longitudinal momentum domain, with its exact bounded commutator. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint

theorem defect_generator_derivative (ε : ℝ) (hε : 0 < ε)
    (f : (generator (coupledGroup ε hε)).domain) :
    HasDerivAt (fun t => transport ε hε t (defectOperator ε hε f))
      (driftOperator ε hε f+defectOperator ε hε (generator (coupledGroup ε hε) f)) 0 := by
  have hg := generator_derivative (coupledGroup ε hε) f
  change HasDerivAt (fun t => transport ε hε t (f:Hilbert)) _ 0 at hg
  have hd := (transportedOperator_derivative ε hε).clm_apply hg
  change HasDerivAt (fun t => transportedOperator ε hε t (transport ε hε t (f:Hilbert)))
    (driftOperator ε hε (transport ε hε 0 (f:Hilbert))+
      transportedOperator ε hε 0 (generator (coupledGroup ε hε) f)) 0 at hd
  simpa only [← transport_defect,transport_initial,transportedOperator_initial] using hd

theorem defect_generator_domain (ε : ℝ) (hε : 0 < ε)
    (f : (generator (coupledGroup ε hε)).domain) :
    defectOperator ε hε f ∈ (generator (coupledGroup ε hε)).domain :=
  (defect_generator_derivative ε hε f).differentiableAt

def defectState (ε : ℝ) (hε : 0 < ε)
    (f : (generator (coupledGroup ε hε)).domain) : (generator (coupledGroup ε hε)).domain :=
  ⟨defectOperator ε hε f,defect_generator_domain ε hε f⟩

theorem defect_generator (ε : ℝ) (hε : 0 < ε)
    (f : (generator (coupledGroup ε hε)).domain) :
    generator (coupledGroup ε hε) (defectState ε hε f) =
      driftOperator ε hε f+defectOperator ε hε (generator (coupledGroup ε hε) f) :=
  (defect_generator_derivative ε hε f).deriv

theorem defect_momentum_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : (longitudinalMomentum ε hε hbar).domain) :
    defectOperator ε hε f ∈ (longitudinalMomentum ε hε hbar).domain :=
  defect_generator_domain ε hε f

theorem defect_momentum (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : (longitudinalMomentum ε hε hbar).domain) :
    longitudinalMomentum ε hε hbar (defectState ε hε f) =
      defectOperator ε hε (longitudinalMomentum ε hε hbar f)+
      (Complex.I*(hbar:ℂ)/(ε:ℂ)) •
        defectOperator ε hε (defectOperator ε hε ((f:Hilbert)-defectOperator ε hε f)) := by
  change (-Complex.I*(hbar:ℂ)) • generator (coupledGroup ε hε) (defectState ε hε f) =
    defectOperator ε hε ((-Complex.I*(hbar:ℂ)) • generator (coupledGroup ε hε) f)+_
  rw [defect_generator]
  simp only [smul_add,map_smul,driftOperator,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,smul_smul]
  have he : (-Complex.I*(hbar:ℂ))*(-(1/(ε:ℂ))) = Complex.I*(hbar:ℂ)/(ε:ℂ) := by ring
  rw [he,add_comm]

theorem defect_momentum_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalMomentum ε hε hbar).graph) :
    (defectOperator ε hε f,defectOperator ε hε g+
      (Complex.I*(hbar:ℂ)/(ε:ℂ)) •
        defectOperator ε hε (defectOperator ε hε (f-defectOperator ε hε f))) ∈
      (longitudinalMomentum ε hε hbar).graph := by
  rw [LinearPMap.mem_graph_iff] at hfg
  rcases hfg with ⟨v,rfl,rfl⟩
  have hg := (longitudinalMomentum ε hε hbar).mem_graph (defectState ε hε v)
  rw [defect_momentum] at hg
  exact hg

#print axioms defect_generator_derivative
#print axioms defect_generator_domain
#print axioms defect_generator
#print axioms defect_momentum_domain
#print axioms defect_momentum
#print axioms defect_momentum_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum
