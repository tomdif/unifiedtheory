/- Normalized zero-charge single packets with uniformly bounded actual
projected eight-factor energy and unbounded actual pure-clock momentum.
This rules out energy-only momentum norm control on these admissible
packets. It does not assert propagator-domain invariance or a new dynamics. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyMomentum
import UnifiedTheory.Audit.KFCausalIndependentNeutralTestFamily
import UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_zero)
open UnifiedTheory.Audit.KFCausalIndependentNeutralTestFamily
  (positionParameter frequencyParameter packet parameter_fixed frequency_eq source_exact amplitude_exact)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (StructuredState input inputOrbit momentumOutput momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (amplitude clockFrequency source)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian
  (meanInput factorEnergy projectedEnergy energy_decomposition)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)

def structured (a h p : ℝ) (ha : 0 < a) : StructuredState where
  size := 1
  packet := fun _ => packet 0 0 0 a h p ha
  coefficient := fun _ => 1

theorem position_fixed (θ : ℝ) :
    parameter θ (positionParameter 0 0) = positionParameter 0 0 := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [parameter,KFCausalPairedRotation.rotate,positionParameter]

theorem source_parameters (h p θ : ℝ) (hh : h ≠ 0) :
    amplitude h (parameter θ (positionParameter 0 0)) (parameter θ (frequencyParameter 0 h p)) = 1 ∧
    clockFrequency h (parameter θ (frequencyParameter 0 h p)) = p ∧
    source h (parameter θ (positionParameter 0 0)) (parameter θ (frequencyParameter 0 h p)) = 0 := by
  refine ⟨?_,frequency_eq 0 h p θ,?_⟩
  · rw [amplitude_exact 0 0 0 h p θ hh]
    simp
  · rw [source_exact 0 0 0 h p θ hh]
    funext i
    fin_cases i <;> simp [KFCausalClockFloorCenteredGaussian.source,
      KFCausalIndependentNeutralTestFamily.position,KFCausalIndependentNeutralTestFamily.momentum]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "N" => (‖trialState ε a h hε ha hh‖⁻¹ : ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "S" p:arg => structured a h p ha
local notation "f" p:arg => input ε h hε hh (S p)
local notation "Bf" p:arg => momentumOutput ε h hε hh (S p)

theorem input_eq (p : ℝ) : f p =
    KFCausalClockFloorDisplacedStates.state ε a h hε ha hh
      (positionParameter 0 0) (frequencyParameter 0 h p) := by
  simp [input,structured,packet]

theorem input_norm (p : ℝ) : ‖f p‖ = 1 := by
  rw [input_eq]
  exact KFCausalClockFloorDisplacedStates.state_norm ε a h hε ha hh _ _

theorem input_fixed (p θ : ℝ) : action h hh θ (f p) = f p := by
  rw [input_eq,KFCausalClockFloorDisplacedStates.action_state,position_fixed,parameter_fixed]

theorem input_sourced (p : ℝ) : f p = N •
    KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw 1 p 0 := by
  rw [input_eq,KFCausalClockFloorDisplacedStates.state_normalization,
    KFCausalClockFloorDisplacedCommonDomain.rawState_eq_sourced ε a h hε ha hh _ _ rfl]
  have hs := source_parameters h p 0 hh
  simp only [parameter_zero] at hs
  rw [hs.1,hs.2.1,hs.2.2]

theorem momentum_sourced (p : ℝ) : Bf p = N •
    KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw 1 p 0 h := by
  simp only [momentumOutput,structured,packet,Fin.sum_univ_one,one_smul]
  unfold KFCausalDisplacedMomentumOrbit.pureOutput
  have hs := source_parameters h p 0 hh
  simp only [parameter_zero] at hs
  rw [hs.1,hs.2.1,hs.2.2]

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem inputOrbit_sourced (p : ℝ) (i : Fin 8) (θ : ℝ) :
    inputOrbit ε h hε hh hb (S p) i θ = N •
    KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
      1 p 0 h hb modelDirections pointField i := by
  simp only [inputOrbit,structured,packet,Fin.sum_univ_one,one_smul]
  unfold KFCausalClockFloorDisplacedCommonDomain.factorOutput
  have hs := source_parameters h p (2*Real.pi*θ) hh
  rw [hs.1,hs.2.1,hs.2.2]

theorem meanInput_sourced (p : ℝ) (i : Fin 8) :
    meanInput ε h hε hh hb (S p) i = N •
    KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
      1 p 0 h hb modelDirections pointField i := by
  unfold meanInput
  simp_rw [inputOrbit_sourced]
  simp

theorem energy_le (hp : 0 < h) (p : ℝ) (hpf : p ≤ 0) (mass2 quartic vacuum t : ℝ) :
    projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t ≤
      projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t := by
  rw [energy_decomposition,energy_decomposition]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  unfold factorEnergy
  rw [meanInput_sourced,meanInput_sourced]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (KFCausalNegativeFrequencyEnergy.factor_norm_le ε a α β hε ha hα hβ hw
      1 p 0 h hp hb hpf modelDirections pointField i) (norm_nonneg _)

def momentumScale : ℝ := |h| *‖clockInverse ε hε (f 0)‖

theorem momentumScale_pos : 0 < momentumScale ε a h hε ha hh := by
  apply mul_pos (abs_pos.mpr hh)
  apply norm_pos_iff.mpr
  apply KFCausalNegativeFrequencyMomentum.clockInverse_ne_zero ε hε
  exact norm_ne_zero_iff.mp (by rw [input_norm]; norm_num)

theorem momentum_lower (p : ℝ) :
    |p| *momentumScale ε a h hε ha hh ≤ ‖Bf p‖ := by
  unfold momentumScale
  rw [input_sourced,momentum_sourced,
    (clockInverse ε hε).map_smul_of_tower,norm_smul,norm_smul]
  have hb' := mul_le_mul_of_nonneg_left
    (KFCausalNegativeFrequencyMomentum.pureOutput_lower ε a α β hε ha hα hβ hw 1 p 0 h)
    (norm_nonneg N)
  convert hb' using 1
  ring

theorem bounded_energy_unbounded_momentum (hp : 0 < h) (mass2 quartic vacuum t M : ℝ) :
    ∃ n : ℕ,
      ‖f (-(n:ℝ))‖ = 1 ∧
      (∀ θ, action h hh θ (f (-(n:ℝ))) = f (-(n:ℝ))) ∧
      (f (-(n:ℝ)),Bf (-(n:ℝ))) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph ∧
      projectedEnergy ε h hε hh hb (S (-(n:ℝ))) mass2 quartic vacuum t ≤
        projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t ∧
      M < ‖Bf (-(n:ℝ))‖ := by
  have hd := momentumScale_pos ε a h hε ha hh
  obtain ⟨n,hn⟩ := exists_nat_gt (M/momentumScale ε a h hε ha hh)
  refine ⟨n,input_norm ε a h hε ha hh _,input_fixed ε a h hε ha hh _,
    momentum_graph ε h hε hh _,energy_le ε a h hε ha hh hb hp _ (neg_nonpos.mpr (Nat.cast_nonneg n))
      mass2 quartic vacuum t,?_⟩
  apply lt_of_lt_of_le ((div_lt_iff₀ hd).mp hn)
  simpa only [abs_neg,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))] using
    momentum_lower ε a h hε ha hh (-(n:ℝ))

theorem no_energy_momentum_bound (hp : 0 < h) (mass2 quartic vacuum t : ℝ) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, p ≤ 0 →
      ‖Bf p‖ ≤ K*(1+projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t) := by
  rintro ⟨K,hK,hbound⟩
  obtain ⟨n,_,_,_,he,hm⟩ := bounded_energy_unbounded_momentum ε a h hε ha hh hb hp
    mass2 quartic vacuum t (K*(1+projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t))
  have hb' := (hbound (-(n:ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) he) hK)
  exact (not_lt_of_ge hb') hm

theorem no_energy_form_momentum_bound (hp : 0 < h) (mass2 quartic vacuum t : ℝ) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, p ≤ 0 →
      ‖Bf p‖ ≤ K*Real.sqrt (1+projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t) := by
  rintro ⟨K,hK,hbound⟩
  obtain ⟨n,_,_,_,he,hm⟩ := bounded_energy_unbounded_momentum ε a h hε ha hh hb hp
    mass2 quartic vacuum t (K*Real.sqrt (1+projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t))
  have hb' := (hbound (-(n:ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl (1:ℝ)) he)) hK)
  exact (not_lt_of_ge hb') hm

theorem projected_input_embedding (p mass2 quartic vacuum t : ℝ) :
    KFCausalClockFloorAveragedEnergy.embedding ε hε h
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb) hh mass2 quartic vacuum t
      (KFCausalZeroChargeStructuredResponse.project ε h hε hh hb mass2 quartic vacuum t
        (KFCausalDisplacedStructuredResponse.inputLift ε h hε hh hb (S p) mass2 quartic vacuum t)) =
      f p := by
  change KFCausalStandingChargeOperator.zeroProjection h hh (f p) = f p
  exact KFCausalStandingChargeOperator.zeroProjection_fixes h hh _
    (input_fixed ε a h hε ha hh p)

#print axioms position_fixed
#print axioms source_parameters
#print axioms input_eq
#print axioms input_norm
#print axioms input_fixed
#print axioms input_sourced
#print axioms momentum_sourced
#print axioms inputOrbit_sourced
#print axioms meanInput_sourced
#print axioms energy_le
#print axioms momentumScale_pos
#print axioms momentum_lower
#print axioms bounded_energy_unbounded_momentum
#print axioms no_energy_momentum_bound
#print axioms no_energy_form_momentum_bound
#print axioms projected_input_embedding
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
