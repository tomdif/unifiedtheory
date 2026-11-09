/- Resolvent smoothing of the actual full quantum trajectory has a
strong physical derivative. The unsmoothed trajectory is not assumed
to preserve the Hamiltonian operator domain. -/
import UnifiedTheory.Audit.KFCausalStrongResidualCalculus
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy (yosida_action)
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent
open UnifiedTheory.Audit.KFCausalStrongResidualCalculus
open UnifiedTheory.Audit.KFCausalHilbertStateEvolution (operator_apply_derivative)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "P" => referenceInverse ε hε h hne hh m g k
local notation "P'" => referenceInverseDerivative ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "S" => UnifiedTheory.Audit.KFCausalClockFloorMovingResolvent.derivative ε hε h hne hh m g k
local notation "Y" => averagedYosida ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem mass_derivative (s t : ℝ) (w : V) :
    HasDerivAt (fun z => M (F s z w)) (c • Q t (F s t w)) t := by
  have hQ : Continuous Q := continuous_iff_continuousAt.mpr
    (fun z => (referenceForm_derivative ε hε h hne hh m g k z).continuousAt)
  exact strong_of_continuous_weak_derivative (fun z => M (F s z w))
    (fun z => c • Q z (F s z w))
    ((hQ.clm_apply (formFlow_continuous ε hε h hne hh m g k s w)).const_smul c)
    (fun z y => mass_pairing_derivative ε hε h hne hh m g k s w
      (weakTrajectory ε hε h hne hh m g k s w) z y) t

theorem regularizer_mass (a t : ℝ) (x : V) :
    R a t (J x) = J (a • P a t (M x)) := by
  change a • J (P a t (M x)) = J (a • P a t (M x))
  exact ((J).map_smul_of_tower a _).symm

theorem derivative_mass (a t : ℝ) (x : V) :
    S a t (J x) = J (a • P' a t (M x)) := by
  change a • J (P' a t (M x)) = J (a • P' a t (M x))
  exact ((J).map_smul_of_tower a _).symm

theorem inverse_form_identity (a t : ℝ) (ha : 0 < a) (x : V) :
    P a t (Q t x) = x-a • P a t (M x) := by
  have he := referenceInverse_left ε hε h hne hh m g k a t ha x
  change P a t (a • M x+Q t x) = x at he
  simp only [map_add,ContinuousLinearMap.map_smul_of_tower] at he
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he)

theorem inverse_physical_identity (a t : ℝ) (ha : 0 < a) (x : V) :
    J (a • P a t (Q t x)) = Y a t (J x) := by
  have he := congrArg (fun v : V => J (a • v))
    (inverse_form_identity ε hε h hne hh m g k a t ha x)
  calc
    _ = J (a • (x-a • P a t (M x))) := he
    _ = a • (J x-J (a • P a t (M x))) :=
      ((J).map_smul_of_tower a _).trans
        (congrArg (fun f : Hilbert => a • f) (map_sub (J) x (a • P a t (M x))))
    _ = a • (J x-R a t (J x)) :=
      congrArg (fun f : Hilbert => a • (J x-f)) (regularizer_mass ε hε h hne hh m g k a t x).symm
    _ = _ := (yosida_action ε hε h hne hh m g k a t (J x)).symm

theorem inverse_generator_identity (a t : ℝ) (ha : 0 < a) (x : V) :
    J (a • P a t (c • Q t x)) = c • Y a t (J x) := by
  calc
    _ = J (a • (c • P a t (Q t x))) :=
      congrArg (fun v : V => J (a • v)) (map_smul (P a t) c (Q t x))
    _ = J (c • (a • P a t (Q t x))) := congrArg (J) (smul_comm a c _)
    _ = c • J (a • P a t (Q t x)) := map_smul (J) c _
    _ = _ := congrArg (fun f : Hilbert => c • f)
      (inverse_physical_identity ε hε h hne hh m g k a t ha x)

theorem smoothed_derivative (a : ℝ) (ha : 0 < a) (s t : ℝ) (w : V) :
    HasDerivAt (fun z => R a z (U s z (J w)))
      (S a t (U s t (J w))+c • Y a t (U s t (J w))) t := by
  have hd := operator_apply_derivative (P a) (fun z => M (F s z w))
    (P' a t) (c • Q t (F s t w)) t
    (referenceInverse_derivative ε hε h hne hh m g k a t ha)
    (mass_derivative ε hε h hne hh m g k s t w)
  have hp := ((J).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hd.const_smul a)
  convert hp using 1
  · funext z
    exact (congrArg (R a z) (evolution_embedding ε hε h hne hh m g k s z w)).trans
      (regularizer_mass ε hε h hne hh m g k a z (F s z w))
  · change S a t (U s t (J w))+c • Y a t (U s t (J w)) =
      J (a • (P' a t (M (F s t w))+P a t (c • Q t (F s t w))))
    rw [smul_add,map_add]
    exact congrArg₂ (fun f g : Hilbert => f+g)
      ((congrArg (S a t) (evolution_embedding ε hε h hne hh m g k s t w)).trans
        (derivative_mass ε hε h hne hh m g k a t (F s t w)))
      ((congrArg (fun f : Hilbert => c • Y a t f)
        (evolution_embedding ε hε h hne hh m g k s t w)).trans
        (inverse_generator_identity ε hε h hne hh m g k a t ha (F s t w)).symm)

#print axioms mass_derivative
#print axioms regularizer_mass
#print axioms derivative_mass
#print axioms inverse_form_identity
#print axioms inverse_physical_identity
#print axioms inverse_generator_identity
#print axioms smoothed_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
