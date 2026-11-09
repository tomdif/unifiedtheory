/- Energy smoothing and energy contraction for the actual scaled averaged
resolvent. The growing-output lift is controlled both on arbitrary physical
states and on the entire reference form domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorResolventTests
import UnifiedTheory.Audit.KFCausalFormResolventEnergyBounds
import UnifiedTheory.Audit.KFCausalMovingSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalMovingSandwichCalculus (weightedLift weightedLift_apply exp_smul_square)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "L" => referenceEnergyMap ε hε h hne hh m g k
local notation "A" => regularizerLift ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "G" => growingMap ε hε h hne hh m g k

theorem energy_variational (a t : ℝ) (ha : 0 < a) (f : Hilbert) (z : V₀) :
    inner ℂ (L t (A a t f)) (L t z) = (a:ℂ)*inner ℂ (f-J (A a t f)) (J z) :=
  ((referenceEnergyMap_pairing ε hε h hne hh m g k t (A a t f) z).trans
    (regularizer_variational ε hε h hne hh m g k a t ha f z)).trans
      (congrArg (fun v : Hilbert => (a:ℂ)*inner ℂ (f-v) (J z))
        (regularizerLift_embedding ε hε h hne hh m g k a t f).symm)

theorem regularizer_energy_square (a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    E t (A a t f) ≤ a/4*‖f‖^2 := by
  have hb := KFCausalFormResolventEnergyBounds.lift_energy_square J (L t) a ha f (A a t f)
    (energy_variational ε hε h hne hh m g k a t ha f (A a t f))
  exact (referenceEnergyMap_square ε hε h hne hh m g k t (A a t f)).symm.le.trans hb

theorem regularizer_energy_contraction (a t : ℝ) (ha : 0 < a) (x : V₀) :
    E t (A a t (J x)) ≤ E t x := by
  have hc := KFCausalFormResolventEnergyBounds.lift_energy_contraction J (L t) a ha x (A a t (J x))
    (energy_variational ε hε h hne hh m g k a t ha (J x))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
  simpa only [referenceEnergyMap_square] using hs

theorem growingMap_apply (x : V₀) :
    G x = growingPart ε hε h hne hh m g k x := ContinuousLinearMap.comp_apply _ _ x

theorem growing_energy_bound (t : ℝ) (x : V₀) :
    ‖Real.exp t • G x‖^2 ≤ E t x := by
  calc
    _ = Real.exp (2*t)*‖growingPart ε hε h hne hh m g k x‖^2 :=
      (exp_smul_square t (G x)).trans (congrArg (fun v : EnergyOutputSpace => Real.exp (2*t)*‖v‖^2)
        (growingMap_apply ε hε h hne hh m g k x))
    _ ≤ _ := le_add_of_nonneg_left (sq_nonneg ‖staticPart ε hε h hne hh m g k x‖)

def growingLift (a t : ℝ) : Hilbert →L[ℂ] EnergyOutputSpace :=
  weightedLift J (referenceInverse ε hε h hne hh m g k a t) G a t

theorem growingLift_apply (a t : ℝ) (f : Hilbert) :
    growingLift ε hε h hne hh m g k a t f = Real.exp t • G (A a t f) :=
  weightedLift_apply J (referenceInverse ε hε h hne hh m g k a t) G a t f

theorem growingLift_energy_bound (a t : ℝ) (f : Hilbert) :
    ‖growingLift ε hε h hne hh m g k a t f‖^2 ≤ E t (A a t f) :=
  (congrArg (fun v : EnergyOutputSpace => ‖v‖^2)
    (growingLift_apply ε hε h hne hh m g k a t f)).le.trans
      (growing_energy_bound ε hε h hne hh m g k t (A a t f))

theorem growingLift_square_bound (a t : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖growingLift ε hε h hne hh m g k a t f‖^2 ≤ a/4*‖f‖^2 :=
  (growingLift_energy_bound ε hε h hne hh m g k a t f).trans
    (regularizer_energy_square ε hε h hne hh m g k a t ha f)

theorem growingLift_form_bound (a t : ℝ) (ha : 0 < a) (x : V₀) :
    ‖growingLift ε hε h hne hh m g k a t (J x)‖^2 ≤ E t x :=
  (growingLift_energy_bound ε hε h hne hh m g k a t (J x)).trans
    (regularizer_energy_contraction ε hε h hne hh m g k a t ha x)

#print axioms energy_variational
#print axioms regularizer_energy_square
#print axioms regularizer_energy_contraction
#print axioms growingMap_apply
#print axioms growing_energy_bound
#print axioms growingLift_apply
#print axioms growingLift_energy_bound
#print axioms growingLift_square_bound
#print axioms growingLift_form_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
