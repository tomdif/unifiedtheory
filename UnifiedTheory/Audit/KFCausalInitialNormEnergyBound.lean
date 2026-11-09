/- A uniform energy bound for the unweighted initial interpolation map.
The full-energy statement keeps the vacuum coefficient, including zero.
No bound for the transported field maps or their terminal slopes follows. -/
import UnifiedTheory.Audit.KFCausalInitialNormVacuumComparison
import UnifiedTheory.Audit.KFCausalCoherentVacuumFormLift
import UnifiedTheory.Audit.KFCausalCoherentFullMomentumPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInitialNormEnergyBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator (input)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift (weightedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

theorem remove_positive_weight (t v A B : ℝ) (hv : 0 < v)
    (hbound : Real.exp (2*t)*v*A ≤ B) : A ≤ (Real.exp (-2*t)/v)*B := by
  have hx : Real.exp (-2*t)*Real.exp (2*t) = 1 := by
    rw [← Real.exp_add,show -2*t+2*t=0 by ring,Real.exp_zero]
  have hs : (Real.exp (-2*t)/v)*(Real.exp (2*t)*v) = 1 := by
    calc
      _ = (Real.exp (-2*t)*Real.exp (2*t))*(v/v) := by ring
      _ = 1 := by rw [hx,div_self hv.ne',mul_one]
  have hp := mul_le_mul_of_nonneg_left hbound (div_nonneg (Real.exp_pos (-2*t)).le hv.le)
  have he : (Real.exp (-2*t)/v)*(Real.exp (2*t)*v*A) = A := by
    rw [← mul_assoc,hs,one_mul]
  exact he.symm.trans_le hp

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => coherentSpan ε a h hε ha hh

theorem vacuum_form_bound (f : S)
    (u : KFCausalCoherentVacuumFormLift.FormSpace ε h hε hh hb)
    (hu : KFCausalCoherentVacuumFormLift.embedding ε h hε hh hb u = (f:Hilbert)) :
    ‖input ε a h hε ha hh hb 0 f‖^2 ≤
      ‖KFCausalCoherentVacuumFormLift.energyOutput ε h hε hh hb u‖^2 := by
  exact (KFCausalCoherentSpanVacuumSign.exists_nonnegative_actual_response ε a h hε ha hh hb f f.property).elim
    fun g hx => hx.elim fun j hx => by
      have hg := fun θ => (hx.2.2.1 θ).1
      have eu : KFCausalCoherentVacuumFormLift.lift ε h hε hh hb f g hx.1 hg = u :=
        KFCausalCoherentVacuumFormLift.embedding_injective ε h hε hh hb hu.symm
      have hrep := KFCausalCoherentVacuumFormLift.lift_output_coe ε h hε hh hb f g hx.1 hg
      have he : KFCausalCoherentVacuumFormLift.energyOutput ε h hε hh hb u =ᵐ[angleMeasure] g :=
        hrep.mono (fun θ hθ => (congrArg
          (fun v : KFCausalCoherentVacuumFormLift.FormSpace ε h hε hh hb =>
            (KFCausalCoherentVacuumFormLift.energyOutput ε h hε hh hb v) θ) eu.symm).trans hθ)
      have hnorm : ‖KFCausalCoherentVacuumFormLift.energyOutput ε h hε hh hb u‖^2 =
          ∫ θ, ‖g θ‖^2 ∂angleMeasure := by
        exact (l2_norm_square angleMeasure (KFCausalCoherentVacuumFormLift.energyOutput ε h hε hh hb u)).trans
          (integral_congr_ae (he.mono (fun _ he => congrArg (fun v : Hilbert => ‖v‖^2) he)))
      exact (KFCausalInitialNormVacuumComparison.actual_average_lower ε a h hε ha hh hb f g hg).2.2.trans_eq hnorm.symm

variable (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

omit a ha in
theorem actual_factor_energy (f : Hilbert) (u : Full) (hu : embed u = f)
    (g : Fin 8 → ℝ → Hilbert) (hc : ∀ i, Continuous (g i))
    (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph) (i : Fin 8) :
    ‖energyWeight mass2 quartic vacuum t i‖^2*(∫ θ, ‖g i θ‖^2 ∂angleMeasure) ≤ ‖out u‖^2 := by
  have eu : KFCausalCoherentMomentumEnergyLift.lift ε h hε hh hb mass2 quartic vacuum t f g hc hg = u :=
    embedding_injective ε hε h hp hh mass2 quartic vacuum t hu.symm
  have hrep := KFCausalCoherentMomentumEnergyLift.lift_output_coe ε h hε hh hb mass2 quartic vacuum t f g hc hg
  have he : out u =ᵐ[angleMeasure] weightedOutput mass2 quartic vacuum t g :=
    hrep.mono (fun θ hθ => (congrArg (fun v : Full => (out v) θ) eu.symm).trans hθ)
  have hi : Integrable (fun θ => ‖weightedOutput mass2 quartic vacuum t g θ‖^2) angleMeasure :=
    (continuous_angle_memLp _ ((KFCausalCoherentMomentumEnergyLift.weightedOutput_continuous
      mass2 quartic vacuum t g hc).norm.pow 2)).integrable (by norm_num)
  have hn : ‖out u‖^2 = ∫ θ, ‖weightedOutput mass2 quartic vacuum t g θ‖^2 ∂angleMeasure := by
    exact (l2_norm_square angleMeasure (out u)).trans
      (integral_congr_ae (he.mono (fun _ he => congrArg (fun v => ‖v‖^2) he)))
  have hbound := integral_mono
    (((continuous_angle_memLp _ ((hc i).norm.pow 2)).integrable (by norm_num)).const_mul
      (‖energyWeight mass2 quartic vacuum t i‖^2)) hi (fun θ => by
        have hb' := pow_le_pow_left₀ (norm_nonneg _)
          (PiLp.norm_apply_le (weightedOutput mass2 quartic vacuum t g θ) i) 2
        change ‖energyWeight mass2 quartic vacuum t i • g i θ‖^2 ≤ _ at hb'
        simpa only [norm_smul,mul_pow] using hb')
  exact (integral_const_mul _ _).symm.trans_le (hbound.trans_eq hn.symm)

theorem full_energy_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
    (f : S) (u : Full) (hu : embed u = (f:Hilbert)) :
    Real.exp (2*t)*vacuum*‖input ε a h hε ha hh hb 0 f‖^2 ≤ ‖out u‖^2 := by
  exact (KFCausalCoherentFullMomentumPairing.input_outputs ε h hε hh hb a ha f f.property).elim
    fun g hg => by
      have hi := (KFCausalInitialNormVacuumComparison.actual_average_lower ε a h hε ha hh hb f (g 7)
        (fun θ => hg.2.2 θ 7)).2.2
      have he := actual_factor_energy ε h hε hh hb mass2 quartic vacuum t f u hu g hg.1 hg.2.2 7
      have hw : ‖energyWeight mass2 quartic vacuum t 7‖^2 = Real.exp (2*t)*vacuum :=
        energyWeight_norm_square mass2 quartic vacuum t hm hq hv 7
      have he' := (congrArg (fun r : ℝ => r*(∫ θ, ‖g 7 θ‖^2 ∂angleMeasure)) hw).symm.trans_le he
      exact (mul_le_mul_of_nonneg_left hi (mul_nonneg (Real.exp_pos _).le hv)).trans he'

theorem positive_vacuum_norm_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 < vacuum)
    (f : S) (u : Full) (hu : embed u = (f:Hilbert)) :
    ‖input ε a h hε ha hh hb 0 f‖^2 ≤ (Real.exp (-2*t)/vacuum)*‖out u‖^2 := by
  exact remove_positive_weight t vacuum _ _ hv
    (full_energy_bound ε a h hε ha hh hb mass2 quartic vacuum t hm hq hv.le f u hu)

#print axioms remove_positive_weight
#print axioms vacuum_form_bound
#print axioms actual_factor_energy
#print axioms full_energy_bound
#print axioms positive_vacuum_norm_bound
end
end UnifiedTheory.Audit.KFCausalInitialNormEnergyBound
