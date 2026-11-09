/- Constructed Schrodinger resolvents and uniform shifted-form estimates
for the actual lifted Hamiltonian. These are not yet evolution operators. -/
import UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
import UnifiedTheory.Audit.KFCausalMassResolventStability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorLiftedHamiltonian
open UnifiedTheory.Audit.KFCausalComplexMassPencil (phase pencil)
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => referenceShift ε hε h hne hh m g k
local notation "L" => liftedHamiltonian ε hε h hne hh m g k

def schrodingerResolvent (b t : ℝ) : V →L[ℂ] V :=
  KFCausalComplexMassResolvent.resolvent M (Q t) h b

def resolvedOutput (b t : ℝ) (f : V) : V :=
  KFCausalComplexMassResolvent.output M (Q t) h b f

theorem mass_symmetric : (M).toLinearMap.IsSymmetric :=
  KFCausalMassGram.gram_inner_symm J

theorem form_symmetric (t : ℝ) : (Q t).toLinearMap.IsSymmetric :=
  KFCausalShiftedForm.formOperator_symmetric
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) t

theorem shift_energy_coercive (a t : ℝ) (x : V) :
    KFCausalShiftedForm.lowerConstant a t*‖x‖^2 ≤ energy (F a t) x :=
  (KFCausalSplitTargetShiftedForm.shiftForm_coercive J
    (staticMap ε hε h hne hh m g k) (growingMap ε hε h hne hh m g k) a t
    (reference_decomposition ε hε h hne hh m g k) x).trans_eq (inner_re_symm (𝕜 := ℂ) (F a t x) x)

theorem shift_energy_nonnegative (a t : ℝ) (ha : 0 < a) (x : V) :
    0 ≤ energy (F a t) x :=
  (mul_nonneg (KFCausalShiftedForm.lowerConstant_positive a t ha).le (sq_nonneg ‖x‖)).trans
    (shift_energy_coercive ε hε h hne hh m g k a t x)

theorem complex_pencil_isUnit (b t : ℝ) (hb : 0 < b) : IsUnit (pencil M (Q t) h b) :=
  KFCausalComplexMassPencil.pencil_isUnit M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t)
    h b (KFCausalShiftedForm.lowerConstant b t) hne
    (KFCausalShiftedForm.lowerConstant_positive b t hb)
    (fun x => (shift_energy_coercive ε hε h hne hh m g k b t x).trans_eq
      (inner_re_symm (𝕜 := ℂ) x (F b t x)))

theorem resolvent_graph (b t : ℝ) (hb : 0 < b) (f : V) :
    (schrodingerResolvent ε hε h hne hh m g k b t f,resolvedOutput ε hε h hne hh m g k b t f)
      ∈ (L t).graph :=
  KFCausalComplexMassResolvent.resolvent_graph M (Q t)
    (mass_injective ε hε h hne hh m g k) h b hne
    (complex_pencil_isUnit ε hε h hne hh m g k b t hb) f

theorem resolvent_right (b t : ℝ) (f : V) :
    b • schrodingerResolvent ε hε h hne hh m g k b t f-
      phase h • resolvedOutput ε hε h hne hh m g k b t f = f :=
  KFCausalComplexMassResolvent.resolvent_right M (Q t) h b hne f

theorem resolvent_left (b t : ℝ) (hb : 0 < b) (x : (L t).domain) :
    schrodingerResolvent ε hε h hne hh m g k b t (b • (x:V)-phase h • L t x) = (x:V) :=
  KFCausalComplexMassResolvent.resolvent_left M (Q t) h b
    (complex_pencil_isUnit ε hε h hne hh m g k b t hb) (x:V) (L t x)
    ((lifted_graph_iff ε hε h hne hh m g k t _ _).mp ((L t).mem_graph x))

theorem energy_contraction (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : V) :
    energy (F a t) (b • schrodingerResolvent ε hε h hne hh m g k b t f) ≤ energy (F a t) f :=
  KFCausalMassResolventStability.energy_contraction M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t)
    h b a hne (complex_pencil_isUnit ε hε h hne hh m g k b t hb)
    (shift_energy_nonnegative ε hε h hne hh m g k a t ha) f

theorem scaled_norm_bound (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (f : V) :
    ‖b • schrodingerResolvent ε hε h hne hh m g k b t f‖ ≤
      Real.sqrt (‖F a t‖/KFCausalShiftedForm.lowerConstant a t)*‖f‖ :=
  KFCausalMassResolventStability.scaled_norm_bound M (Q t)
    (mass_symmetric ε hε h hne hh m g k) (form_symmetric ε hε h hne hh m g k t)
    h b a (KFCausalShiftedForm.lowerConstant a t) hne
    (complex_pencil_isUnit ε hε h hne hh m g k b t hb)
    (KFCausalShiftedForm.lowerConstant_positive a t ha)
    (shift_energy_coercive ε hε h hne hh m g k a t) f

#print axioms mass_symmetric
#print axioms form_symmetric
#print axioms shift_energy_coercive
#print axioms shift_energy_nonnegative
#print axioms complex_pencil_isUnit
#print axioms resolvent_graph
#print axioms resolvent_right
#print axioms resolvent_left
#print axioms energy_contraction
#print axioms scaled_norm_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorLiftedResolvent
