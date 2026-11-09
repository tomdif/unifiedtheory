/- The dyadic cancellation controls the full completed Hamiltonian
form response, including the kinetic correction and the charge average.
This is a finite linear combination of existing physical observables. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicOutput
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse
import UnifiedTheory.Audit.KFCausalDyadicResponseChoice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicFullResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos)
open UnifiedTheory.Audit.KFCausalDyadicResponseChoice (width_mono)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm (OutputSpace correction correction_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound (outputAction)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing (reflectedOutput)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (commutator commutator_identity kineticConstant response response_eq_commutator)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicOutput (outputLp_mean_bound)

theorem kinetic_width_bound (ε δ v : ℝ) (N j : ℕ) (hδ : 0 ≤ δ) (hj : j ≤ N) :
    kineticConstant ε (width δ j) v ≤ kineticConstant ε (width δ N) v := by
  unfold kineticConstant KFCausalNeutralPositionRadialKineticGraph.responseConstant
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hs := Real.sqrt_le_sqrt (width_mono δ hδ j N hj)
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (N : ℕ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0)

theorem correction_mean_bound (hN : 0 < N) (f : Hilbert) :
    ‖mean N (fun j => correction ε hε h (width δ j) v (width_pos δ hδ j) hne f)‖ ≤
      |h| *kineticConstant ε (width δ N) v*‖f‖ := by
  apply mean_norm_le N hN
  intro j hj
  have hk := kinetic_width_bound ε δ v N j hδ.le (Nat.le_of_lt (Finset.mem_range.mp hj))
  exact (correction_bound ε hε h (width δ j) v (width_pos δ hδ j) hne f).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (abs_nonneg h)) (norm_nonneg f))

theorem commutator_mean_identity (f g : Hilbert) (x y : OutputSpace) :
    mean N (fun j => commutator ε hε h (width δ j) v (width_pos δ hδ j) hh hne f g x y) =
      inner ℂ x (mean N (fun j => (outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y-
        (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y))+
      (inner ℂ x (mean N (fun j => correction ε hε h (width δ j) v (width_pos δ hδ j) hne g))-
        inner ℂ (mean N (fun j => correction ε hε h (width δ j) (-v) (width_pos δ hδ j) hne f)) y) := by
  simp only [commutator_identity,mean_add,mean_sub,mean_inner_right,mean_inner_left]

theorem commutator_mean_bound (hN : 0 < N) (f g : Hilbert) (x y : OutputSpace) :
    ‖mean N (fun j => commutator ε hε h (width δ j) v (width_pos δ hδ j) hh hne f g x y)‖ ≤
      |h| *(responseConstant ε δ v N*‖x‖*‖y‖+
        kineticConstant ε (width δ N) v*(‖x‖*‖g‖+‖f‖*‖y‖)) := by
  have hm : ‖mean N (fun j => correction ε hε h (width δ j) (-v) (width_pos δ hδ j) hne f)‖ ≤
      |h| *kineticConstant ε (width δ N) v*‖f‖ := by
    simpa only [kineticConstant,KFCausalNeutralPositionRadialKineticGraph.responseConstant,abs_neg] using
      correction_mean_bound ε hε h δ (-v) N hδ hne hN f
  rw [commutator_mean_identity ε hε h δ v N hδ hh hne]
  calc
    _ ≤ ‖inner ℂ x (mean N (fun j => (outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y-
          (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y))‖+
        ‖inner ℂ x (mean N (fun j => correction ε hε h (width δ j) v (width_pos δ hδ j) hne g))-
          inner ℂ (mean N (fun j => correction ε hε h (width δ j) (-v) (width_pos δ hδ j) hne f)) y‖ := norm_add_le _ _
    _ ≤ ‖x‖*‖mean N (fun j => (outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y-
          (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y)‖+
        (‖x‖*‖mean N (fun j => correction ε hε h (width δ j) v (width_pos δ hδ j) hne g)‖+
          ‖mean N (fun j => correction ε hε h (width δ j) (-v) (width_pos δ hδ j) hne f)‖*‖y‖) :=
      add_le_add (norm_inner_le_norm _ _)
        ((norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)))
    _ ≤ ‖x‖*((|h| *responseConstant ε δ v N)*‖y‖)+
        (‖x‖*(|h| *kineticConstant ε (width δ N) v*‖g‖)+
          (|h| *kineticConstant ε (width δ N) v*‖f‖)*‖y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (outputLp_mean_bound ε hε h δ v N hδ hh hN y) (norm_nonneg _))
        (add_le_add (mul_le_mul_of_nonneg_left (correction_mean_bound ε hε h δ v N hδ hne hN g) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hm (norm_nonneg _)))
    _ = _ := by ring

open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
variable (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k t
local notation "J" => embedding ε hε h hne hh m g k t
local notation "A" => energyOutput ε hε h hne hh m g k t

theorem completed_form_mean_bound (hN : 0 < N) (u w : V) :
    ‖mean N (fun j => response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t u w)‖/|h| ≤
      responseConstant ε δ v N*‖A u‖*‖A w‖+
        kineticConstant ε (width δ N) v*(‖A u‖*‖J w‖+‖J u‖*‖A w‖) := by
  have he := congrArg (mean N) (funext (fun j =>
    response_eq_commutator ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t u w))
  apply (div_le_iff₀ (abs_pos.mpr hne)).mpr
  exact ((congrArg norm he).le.trans
    (commutator_mean_bound ε hε h δ v N hδ hh hne hN (J u) (J w) (A u) (A w))).trans_eq (by ring)

theorem completed_form_mean_diagonal (hN : 0 < N) (u : V) :
    ‖mean N (fun j => response ε hε h (width δ j) v (width_pos δ hδ j) hh hne m g k t u u)‖/|h| ≤
      responseConstant ε δ v N*‖A u‖^2+
        2*kineticConstant ε (width δ N) v*‖J u‖*‖A u‖ :=
  (completed_form_mean_bound ε hε h δ v N hδ hh hne m g k t hN u u).trans_eq (by ring)

#print axioms kinetic_width_bound
#print axioms correction_mean_bound
#print axioms commutator_mean_identity
#print axioms commutator_mean_bound
#print axioms completed_form_mean_bound
#print axioms completed_form_mean_diagonal

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicFullResponse
