/- Charge covariance of the actual time-dependent propagator. Hamiltonian
domain invariance gives covariance of every positive resolvent cutoff;
the established strong limit transfers it to every physical Hilbert
state. No charge moment is required for this commutation statement. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargeHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeDynamics
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorChargeHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit (cutoff cutoff_pos)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence (cutoff_dynamics_strong_limit)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "H" => hamiltonian ε hε h hh hb m g k
local notation "U" => evolution ε hε h hh hb m g k

theorem shiftedResolvent_action (a : ℝ) (ha : 0 < a) (t θ : ℝ) (f : Hilbert) :
    shiftedResolvent ε hε h hh hb m g k a t (action h hh θ f) =
      action h hh θ (shiftedResolvent ε hε h hh hb m g k a t f) := by
  let x := resolventVector ε hε h hh hb m g k a t ha f
  let y : (H t).domain :=
    ⟨action h hh θ (x:Hilbert), action_mem_hamiltonian_domain ε hε h hh hb m g k t θ x⟩
  have hl := shiftedResolvent_left ε hε h hh hb m g k a t ha y
  have hr := shiftedResolvent_right ε hε h hh hb m g k a t ha f
  have he : H t y+a • (y:Hilbert) = action h hh θ f := by
    calc
      _ = action h hh θ (H t x)+a • action h hh θ (x:Hilbert) :=
        congrArg (fun z => z+a • action h hh θ (x:Hilbert))
          (hamiltonian_action ε hε h hh hb m g k t θ x)
      _ = action h hh θ (H t x+a • (x:Hilbert)) := by
        simp only [map_add, map_real_smul (action h hh θ) (action h hh θ).continuous]
      _ = action h hh θ f := congrArg (action h hh θ) hr
  exact (congrArg (shiftedResolvent ε hε h hh hb m g k a t) he).symm.trans hl

theorem yosida_action (a : ℝ) (ha : 0 < a) (t θ : ℝ) (f : Hilbert) :
    averagedYosida ε hε h hh hb m g k a t (action h hh θ f) =
      action h hh θ (averagedYosida ε hε h hh hb m g k a t f) := by
  simp only [averagedYosida, KFCausalYosidaApproximation.yosida_apply, map_sub,
    map_real_smul (action h hh θ) (action h hh θ).continuous,
    shiftedResolvent_action ε hε h hh hb m g k a ha]

theorem generator_action (a : ℝ) (ha : 0 < a) (t θ : ℝ) (f : Hilbert) :
    generator ε hε h hh hb m g k a t (action h hh θ f) =
      action h hh θ (generator ε hε h hh hb m g k a t f) := by
  simp only [generator, ContinuousLinearMap.smul_apply, map_smul,
    yosida_action ε hε h hh hb m g k a ha]

theorem dynamics_action (a : ℝ) (ha : 0 < a) (s t θ : ℝ) (f : Hilbert) :
    dynamics ε hε h hh hb m g k a ha s t (action h hh θ f) =
      action h hh θ (dynamics ε hε h hh hb m g k a ha s t f) := by
  let R : Hilbert →L[ℂ] Hilbert := action h hh θ
  have hinit : R (dynamics ε hε h hh hb m g k a ha s s f) = R f := by
    rw [dynamics_initial]
    rfl
  have hd (r : ℝ) : HasDerivAt (fun z => R (dynamics ε hε h hh hb m g k a ha s z f))
      (generator ε hε h hh hb m g k a r (R (dynamics ε hε h hh hb m g k a ha s r f))) r := by
    change HasDerivAt _ (generator ε hε h hh hb m g k a r
      (action h hh θ (dynamics ε hε h hh hb m g k a ha s r f))) r
    rw [generator_action ε hε h hh hb m g k a ha]
    exact (R.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (dynamics_state_derivative ε hε h hh hb m g k a ha s r f)
  exact (congrFun (dynamics_state_unique ε hε h hh hb m g k a ha s (R f)
    (fun z => R (dynamics ε hε h hh hb m g k a ha s z f)) hinit hd) t).symm

theorem evolution_action (s t θ : ℝ) (f : Hilbert) :
    U s t (action h hh θ f) = action h hh θ (U s t f) := by
  have hl := cutoff_dynamics_strong_limit ε hε h hh hb m g k s t (action h hh θ f)
  have hr := (action h hh θ).continuous.tendsto (U s t f) |>.comp
    (cutoff_dynamics_strong_limit ε hε h hh hb m g k s t f)
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun n =>
    (dynamics_action ε hε h hh hb m g k (cutoff n) (cutoff_pos n) s t θ f).symm)

theorem rotation_pairing_conserved (s t θ : ℝ) (f v : Hilbert) :
    inner ℂ (U s t f) (action h hh θ (U s t v)) = inner ℂ f (action h hh θ v) := by
  rw [← evolution_action ε hε h hh hb m g k s t θ v]
  exact (U s t).inner_map_map _ _

#print axioms shiftedResolvent_action
#print axioms yosida_action
#print axioms generator_action
#print axioms dynamics_action
#print axioms evolution_action
#print axioms rotation_pairing_conserved

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeDynamics
