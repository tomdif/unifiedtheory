/- The bounded inverse half-clock preserves the actual maximal
pure-clock momentum domain and has an explicit bounded commutator. -/
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
local notation "R" => inverseL ε hε
local notation "L" => pureMomentum ε hε h
local notation "D" => defectOperator ε hε
local notation "Q" => responseOperator ε hε
omit h hne in
theorem transport_inverse (t : ℝ) (f : Hilbert) :
    transport ε hε t (R f) = operator ε hε t (transport ε hε t f) := by
  apply Lp.ext
  filter_upwards [transport_coe ε hε t (R f),
    operator_coe ε hε t (transport ε hε t f),transport_coe ε hε t f,
    (flow_quasiMeasurePreserving ε hε t).ae (inverseL_coe ε hε f)] with x hl hr hu hf
  rw [hl,hr]
  simp only [transportFunction]
  rw [hf,hu]
  dsimp only [transportFunction,KFCausalClockFloorInverseHalfTransportOperator.weight,KFCausalClockFloorInverseHalfTransportScalar.transported,pureFlow]
  ring

include hne

theorem inverse_momentum_drift (f g : Hilbert) (hfg : (f,g) ∈ (L).graph) :
    (R f,R g+(-Complex.I*(h:ℂ)) • driftOperator ε hε f) ∈ (L).graph := by
  have hd := (momentum_graph_iff (pureGroup ε hε) h hne f g).mp hfg
  have hp := (operator_derivative ε hε).clm_apply hd
  change HasDerivAt (fun t => operator ε hε t (transport ε hε t f))
    (driftOperator ε hε (transport ε hε 0 f)+operator ε hε 0 ((Complex.I/(h:ℂ)) • g)) 0 at hp
  apply (momentum_graph_iff (pureGroup ε hε) h hne _ _).mpr
  simpa only [← transport_inverse,transport_initial,operator_initial,map_smul,
    smul_add,smul_smul,inverse_coefficient h hne,one_smul,add_comm] using hp

theorem inverse_momentum_graph (f g : Hilbert) (hfg : (f,g) ∈ (L).graph) :
    (R f,R g+(Complex.I*(h:ℂ)/(2*(ε:ℂ))) • D (Q (R f))) ∈ (L).graph := by
  have he : (-Complex.I*(h:ℂ))*(-(1/(2*(ε:ℂ)))) = Complex.I*(h:ℂ)/(2*(ε:ℂ)) := by ring
  simpa only [driftOperator,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    smul_smul,he] using inverse_momentum_drift ε hε h hne f g hfg

theorem inverse_momentum_domain (f : Hilbert) (hf : f ∈ (L).domain) : R f ∈ (L).domain :=
  LinearPMap.mem_domain_of_mem_graph (inverse_momentum_graph ε hε h hne f _ ((L).mem_graph ⟨f,hf⟩))

omit hne in
theorem correction_bound (f : Hilbert) :
    ‖(Complex.I*(h:ℂ)/(2*(ε:ℂ))) • D (Q (R f))‖ ≤ (|h|/(2*ε))*‖R f‖ := by
  rw [norm_smul,norm_div,norm_mul,Complex.norm_I,one_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left
    ((defectOperator_norm_le ε hε _).trans (responseOperator_norm ε hε _)) (by positivity)

#print axioms transport_inverse
#print axioms inverse_momentum_drift
#print axioms inverse_momentum_graph
#print axioms inverse_momentum_domain
#print axioms correction_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf
