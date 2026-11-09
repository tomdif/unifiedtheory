/- A form-domain representative close to every bounded trajectory.
Its original form energy is uniformly bounded, and its squared physical
distance from the trajectory is O(1/a). The weak Schrodinger pairing is
exact. These statements still do not construct the unbounded limit. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
import UnifiedTheory.Audit.KFCausalPhysicalYosidaEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory
noncomputable section
open UnifiedTheory.Audit.KFCausalFormEnergyIdentities
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
open UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
open UnifiedTheory.Audit.KFCausalPhysicalShiftedResolvent
open UnifiedTheory.Audit.KFCausalPhysicalYosida
open UnifiedTheory.Audit.KFCausalPhysicalYosidaDynamics
open UnifiedTheory.Audit.KFCausalPhysicalYosidaEnergy

theorem timeEnergy_smul (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t r : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum t (r • w) = r^2*timeEnergy ε hε hbar hh mass2 quartic vacuum t w := by
  rw [← quadratic_eq_timeEnergy,← quadratic_eq_timeEnergy]
  exact quadratic_smul _ _ t r w

def smoothedLift (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  a • resolventFormLift ε hε hbar hh mass2 quartic vacuum a t (dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f)

def smoothedState (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) : Hilbert :=
  embedding ε hε hbar hh mass2 quartic vacuum 0 (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f)

theorem smoothedState_resolvent (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t f =
      a • shiftedResolvent ε hε hbar hh mass2 quartic vacuum a t (dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f) := by
  rw [smoothedState,smoothedLift,ContinuousLinearMap.map_smul_of_tower,shiftedResolvent_apply]

theorem smoothed_energy_split (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    trajectoryEnergy ε hε hbar hh mass2 quartic vacuum a ha s t f =
      a*‖dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f-smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t f‖^2 +
      timeEnergy ε hε hbar hh mass2 quartic vacuum t (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f) := by
  rw [trajectoryEnergy,boundedEnergy_split ε hε hbar hh mass2 quartic vacuum a t ha,
    smoothedState,smoothedLift,timeEnergy_smul,ContinuousLinearMap.map_smul_of_tower]

theorem smoothed_form_energy_le (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum t (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f) ≤
      trajectoryEnergy ε hε hbar hh mass2 quartic vacuum a ha s t f := by
  rw [smoothed_energy_split]
  have hn := mul_nonneg ha.le
    (sq_nonneg ‖dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f-smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t f‖)
  linarith

theorem smoothed_defect_energy_le (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) :
    a*‖dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f-smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t f‖^2 ≤
      trajectoryEnergy ε hε hbar hh mass2 quartic vacuum a ha s t f := by
  rw [smoothed_energy_split]
  have hq : 0 ≤ timeEnergy ε hε hbar hh mass2 quartic vacuum t (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f) := by
    rw [← quadratic_eq_timeEnergy]
    exact quadratic_nonneg _ _ _ _
  linarith

theorem smoothed_uniform_form_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum t
      (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) ≤
      Real.exp (2*|t-s|)*timeEnergy ε hε hbar hh mass2 quartic vacuum s w :=
  (smoothed_form_energy_le ε hε hbar hh mass2 quartic vacuum a ha s t _).trans
    (uniform_energy_bound ε hε hbar hh mass2 quartic vacuum a ha s t w)

theorem smoothed_uniform_defect_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖dynamics ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)-
      smoothedState ε hε hbar hh mass2 quartic vacuum a ha s t (embedding ε hε hbar hh mass2 quartic vacuum 0 w)‖^2 ≤
      (Real.exp (2*|t-s|)*timeEnergy ε hε hbar hh mass2 quartic vacuum s w)/a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm _ a]
  exact (smoothed_defect_energy_le ε hε hbar hh mass2 quartic vacuum a ha s t _).trans
    (uniform_energy_bound ε hε hbar hh mass2 quartic vacuum a ha s t w)

theorem smoothed_weak_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (s t : ℝ) (f : Hilbert) (v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f) (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) =
      inner ℂ (physicalYosida ε hε hbar hh mass2 quartic vacuum a t (dynamics ε hε hbar hh mass2 quartic vacuum a ha s t f))
        (embedding ε hε hbar hh mass2 quartic vacuum 0 v) := by
  rw [smoothedLift,inner_smul_left_eq_smul,
    shiftedResolvent_variational ε hε hbar hh mass2 quartic vacuum a t ha,yosida_action,inner_smul_left_eq_smul,
    shiftedResolvent_apply]

theorem smoothed_schrodinger_weak (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)
    (hhbar : hbar ≠ 0) (s t : ℝ) (f : Hilbert) :
    ∃ v' : Hilbert, HasDerivAt (fun z => dynamics ε hε hbar hh mass2 quartic vacuum a ha s z f) v' t ∧
      ∀ v : FormSpace ε hε hbar hh mass2 quartic vacuum 0,
        inner ℂ (smoothedLift ε hε hbar hh mass2 quartic vacuum a ha s t f) (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) =
          inner ℂ ((Complex.I*(hbar:ℂ)) • v') (embedding ε hε hbar hh mass2 quartic vacuum 0 v) := by
  refine ⟨_,dynamics_state_derivative ε hε hbar hh mass2 quartic vacuum a ha s t f,?_⟩
  intro v
  rw [generator_schrodinger ε hε hbar hh mass2 quartic vacuum a t hhbar]
  exact smoothed_weak_pairing ε hε hbar hh mass2 quartic vacuum a ha s t f v

#print axioms smoothed_energy_split
#print axioms smoothed_form_energy_le
#print axioms smoothed_defect_energy_le
#print axioms smoothed_uniform_form_bound
#print axioms smoothed_uniform_defect_bound
#print axioms smoothed_weak_pairing
#print axioms smoothed_schrodinger_weak

end
end UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory
