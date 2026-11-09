/- An actual normalized, zero-charge family in the reference completed energy
form, with a bound independent of sufficiently small nonzero Planck parameter.
The positive clock floor and clock width are fixed. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
import UnifiedTheory.Audit.KFCausalAveragedFixedEnergy
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory (timeEnergy_smul)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)

def unitTrial (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) : Hilbert :=
  (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) • trialState ε a hbar hε ha hh

theorem unitTrial_norm (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    ‖unitTrial ε a hbar hε ha hh‖ = 1 := by
  rw [unitTrial,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (trialState_ne_zero ε a hbar hε ha hh))

theorem unitTrial_zeroSector (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    unitTrial ε a hbar hε ha hh ∈ zeroSector hbar hh :=
  ((zeroSector hbar hh).restrictScalars ℝ).smul_mem _ (trialState_mem_zeroSector ε a hbar hε ha hh)

def uniformEnergy (ε a mass2 quartic vacuum s : ℝ) : ℝ :=
  energyBudget ε a modelDirections pointField mass2 quartic vacuum s/clockMass ε a

theorem uniformEnergy_nonnegative (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ uniformEnergy ε a mass2 quartic vacuum s :=
  div_nonneg (energyBudget_nonnegative ε a modelDirections pointField mass2 quartic vacuum s hm hq hv)
    (clockMass_positive ε a hε ha).le

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbar : ℝ) (hh : hbar ≠ 0)
  (hb : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
  (mass2 quartic vacuum s : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum)
local notation "V₀" => FormSpace ε hε hbar hh hb mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hb mass2 quartic vacuum 0
local notation "E" => timeEnergy ε hε hbar hh hb mass2 quartic vacuum
local notation "f" => trialState ε a hbar hε ha hh
local notation "B" => energyBudget ε a modelDirections pointField mass2 quartic vacuum s
local notation "M" => gaussianMass (groundWidth hbar) (neutralWidth hbar)

include hh1 hm hq hv in
theorem exists_trial_form : ∃ w : V₀, J w = f ∧ E s w ≤ B*M := by
  let baseData := KFCausalClockFloorFormHamiltonian.formData ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
  let v := KFCausalClockFloorFormHamiltonian.commonFormVector ε hε hbar
    (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s
    (trialCommon ε a hbar hε ha hh hb modelDirections pointField)
  have hjv : KFCausalClosedGraphForm.embedding baseData v = f :=
    KFCausalClockFloorFormHamiltonian.commonFormVector_embedding ε hε hbar
      (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s _
  have hzv : KFCausalClosedGraphForm.embedding baseData v ∈ zeroSector hbar hh :=
    Eq.mpr (congrArg (fun z : Hilbert => z ∈ zeroSector hbar hh) hjv)
      (trialState_mem_zeroSector ε a hbar hε ha hh)
  have lift := KFCausalAveragedFixedEnergy.exists_fixed_lift
    (H := Hilbert) («E» := KFCausalClosedGraphForm.FormSpace baseData)
    (K := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (KFCausalPhysicalCircleAction.group hbar hh) (2*Real.pi)
    (KFCausalClosedGraphForm.embedding baseData) (KFCausalClosedGraphForm.energyOutput baseData)
    (KFCausalClosedGraphForm.embedding_injective baseData) (by positivity)
  have hl := lift v hzv
  let u := Classical.choose hl
  have hu := Classical.choose_spec hl
  let g := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε hbar hh hb mass2 quartic vacuum s u
  let w : V₀ := formTransfer ε hε hbar hh hb mass2 quartic vacuum s 0 g
  have hj : J w = f :=
    (transfer_embedding ε hε hbar hh hb mass2 quartic vacuum s 0 g).trans (hu.1.trans hjv)
  have he : E s w = KFCausalClockFloorJointEnergy.seedEnergy ε hε hbar modelDirections pointField
      mass2 quartic vacuum s (trialCommon ε a hbar hε ha hh hb modelDirections pointField) := by
    calc
      _ = ‖energyOutput ε hε hbar hh hb mass2 quartic vacuum s g‖^2 :=
        (timeEnergy_actual ε hε hbar hh hb mass2 quartic vacuum s w).symm.trans
          (congrArg (fun z => ‖energyOutput ε hε hbar hh hb mass2 quartic vacuum s z‖^2)
            (transfer_inverse ε hε hbar hh hb mass2 quartic vacuum s 0 g))
      _ = ‖KFCausalClosedGraphForm.energyOutput baseData v‖^2 := hu.2
      _ = _ := KFCausalClockFloorFormHamiltonian.commonFormVector_energy ε hε hbar
        (hamiltonian_bound ε hbar hb) mass2 quartic vacuum s hm hq hv _
  exact ⟨w,hj,he.le.trans (trial_seed_energy_bound ε a hbar hε ha hh hb hh1 modelDirections
    pointField mass2 quartic vacuum s hm hq hv)⟩

private theorem normalize_bound (n m q b e : ℝ) (hm : 0 < m) (hq : 0 < q)
    (hn2 : n^2 = m*q) (he : e ≤ b*q) : n⁻¹^2*e ≤ b/m := by
  calc
    _ = e/(n^2) := by rw [inv_pow]; ring
    _ ≤ (b*q)/(n^2) := div_le_div_of_nonneg_right he (sq_nonneg n)
    _ = b/m := by rw [hn2]; field_simp

include hh1 hm hq hv in
theorem exists_unit_trial_form :
    ∃ w : V₀, J w = unitTrial ε a hbar hε ha hh ∧ E s w ≤ uniformEnergy ε a mass2 quartic vacuum s := by
  let p := exists_trial_form ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv
  let w := Classical.choose p
  have hw := Classical.choose_spec p
  let r : ℝ := ‖f‖⁻¹
  have hj : J (r • w) = unitTrial ε a hbar hε ha hh :=
    ((J).map_smul_of_tower r w).trans (congrArg (fun x : Hilbert => r • x) hw.1)
  have he := normalize_bound ‖f‖ (clockMass ε a) M B (E s w)
    (clockMass_positive ε a hε ha)
    (gaussianMass_positive _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh))
    (trial_norm_square ε a hbar hε ha hh) hw.2
  exact ⟨r • w,hj,(timeEnergy_smul ε hε hbar hh hb mass2 quartic vacuum s r w).le.trans he⟩

def state : V₀ := Classical.choose (exists_unit_trial_form ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)

theorem state_embedding : J (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv) =
    unitTrial ε a hbar hε ha hh :=
  (Classical.choose_spec (exists_unit_trial_form ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)).1

theorem state_energy : E s (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv) ≤
    uniformEnergy ε a mass2 quartic vacuum s :=
  (Classical.choose_spec (exists_unit_trial_form ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)).2

theorem state_norm : ‖J (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)‖ = 1 :=
  (congrArg norm (state_embedding ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv)).trans
    (unitTrial_norm ε a hbar hε ha hh)

theorem state_zeroSector : J (state ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv) ∈ zeroSector hbar hh :=
  (state_embedding ε a hε ha hbar hh hb hh1 mass2 quartic vacuum s hm hq hv).symm ▸
    unitTrial_zeroSector ε a hbar hε ha hh

#print axioms unitTrial_norm
#print axioms unitTrial_zeroSector
#print axioms uniformEnergy_nonnegative
#print axioms exists_trial_form
#print axioms exists_unit_trial_form
#print axioms state_embedding
#print axioms state_energy
#print axioms state_norm
#print axioms state_zeroSector

end
end UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
