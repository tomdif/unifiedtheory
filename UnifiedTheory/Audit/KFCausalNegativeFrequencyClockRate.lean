/- Actual clock-defect rates on normalized zero-charge packets. Their
ordered outputs tend to zero along negative integer frequencies, while
the defect expectation stays fixed and positive. The rate is the exact
initial derivative under the constructed unbounded propagator. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyOutputDecay
import UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
import UnifiedTheory.Audit.KFCausalClockFloorDefectDissipationBudget

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyClockRate
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
open UnifiedTheory.Audit.KFCausalNegativeFrequencyOutputDecay
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (input inputLift)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (meanInput projectedEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean (comp_const mean_const)

private theorem const_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (x y : E) :
    inner ℂ (Lp.const 2 angleMeasure x) (Lp.const 2 angleMeasure y) = inner ℂ x y :=
  ((Lp.constL 2 angleMeasure ℂ : E →L[ℂ] Lp E 2 angleMeasure).adjoint_inner_right x
    (Lp.const 2 angleMeasure y)).symm.trans (congrArg (inner ℂ x) (mean_const angleMeasure y))

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hp : 0 < h)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "hh" => hp.ne'
local notation "S" p:arg => structured a h p ha
local notation "f" p:arg => input ε h hε hh (S p)
local notation "D" => defectOperator ε hε
local notation "J" => embedding ε hε h hh hb m g k 0
local notation "P" => KFCausalZeroChargeStructuredResponse.project ε h hε hh hb m g k t
local notation "u" p:arg => P (inputLift ε h hε hh hb (S p) m g k t)
local notation "A" => outputAction ε hε h hb

def packetForm (p : ℝ) : FormSpace ε hε h hh hb m g k 0 :=
  formTransfer ε hε h hh hb m g k t 0 (graphFormVector ε hε h hh hb m g k t (u p))

def packetOutput (p : ℝ) : Output (Fin 8) Hilbert :=
  WithLp.toLp 2 (fun i => energyWeight m g k t i • meanInput ε h hε hh hb (S p) i)

theorem packet_embedding (p : ℝ) : J (packetForm ε a h hε ha hp hb m g k t p) = f p := by
  rw [packetForm,transfer_embedding]
  exact projected_input_embedding ε a h hε ha hh hb p m g k t

theorem packet_output (p : ℝ) :
    evolvingOutput ε hε h hh hb m g k t t (packetForm ε a h hε ha hp hb m g k t p) =
      Lp.const 2 angleMeasure (packetOutput ε a h hε ha hp hb m g k t p) := by
  have hf := KFCausalClockFloorAveragedFormFlow.formFlow_initial ε hε h hh hb m g k t
    (packetForm ε a h hε ha hp hb m g k t p)
  have ht := transfer_inverse ε hε h hh hb m g k t 0 (graphFormVector ε hε h hh hb m g k t (u p))
  have he : evolvingOutput ε hε h hh hb m g k t t (packetForm ε a h hε ha hp hb m g k t p) =
      KFCausalZeroChargeStructuredResponse.output ε h hε hh hb m g k t (u p) :=
    (congrArg (fun z => energyOutput ε hε h hh hb m g k t
      (formTransfer ε hε h hh hb m g k 0 t z)) hf).trans
      (congrArg (energyOutput ε hε h hh hb m g k t) ht)
  have hm := KFCausalProjectedFactorMeans.lift_mean_output ε h hε hh hb m g k t _ _
    (KFCausalDisplacedStructuredResponse.inputOrbit_continuous ε h hε hh hb (S p))
    (KFCausalDisplacedStructuredResponse.inputOrbit_graph ε h hε hh hb (S p))
  exact he.trans ((KFCausalZeroChargeStructuredResponse.projected_output ε h hε hh hb m g k t
    (inputLift ε h hε hh hb (S p) m g k t)).trans (congrArg (Lp.const 2 angleMeasure) hm))

theorem packet_defect_constant (p : ℝ) :
    (inner ℂ (f p) (D (f p))).re = (inner ℂ (f 0) (D (f 0))).re := by
  rw [input_sourced,input_sourced,KFCausalClockFloorInitialDriftPairing.pairing_real_smul,
    KFCausalClockFloorInitialDriftPairing.pairing_real_smul]
  rw [defect_expectation_frequency ε a (groundWidth h) (neutralWidth h) hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) 1 0 p 0]

theorem packet_defect_positive : 0 < (inner ℂ (f 0) (D (f 0))).re := by
  apply KFCausalClockFloorStrictQuantumLimit.expectation_positive ε hε
  exact norm_ne_zero_iff.mp (by rw [input_norm]; norm_num)

theorem ordered_coordinate_limit (i : Fin 8) (hi : 5 ≤ i.val) :
    Tendsto (fun n : ℕ => packetOutput ε a h hε ha hp hb m g k t (-(n:ℝ)) i)
      atTop (𝓝 0) := by
  have hj : ∃ j : Fin 3, KFCausalSourcedResponseFactorBridge.index j = i := by
    fin_cases i
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · norm_num at hi
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨0,rfl⟩
  obtain ⟨j,rfl⟩ := hj
  have hz := ordered_output_tendsto_zero ε a (groundWidth h) (neutralWidth h) hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) 1 0
    h hp hb modelDirections pointField j
  have hs := (hz.const_smul (‖trialState ε a h hε ha hh‖⁻¹ : ℝ)).const_smul
    (energyWeight m g k t (KFCausalSourcedResponseFactorBridge.index j))
  simpa only [packetOutput,meanInput_sourced,smul_zero] using hs

theorem packet_rate_decomposition (p : ℝ) :
    exactRate ε hε h hh hb m g k t t (packetForm ε a h hε ha hp hb m g k t p) =
      ∑ i : Fin 8, (-2/h)*(inner ℂ (packetOutput ε a h hε ha hp hb m g k t p i)
        (factorAction ε hε h hb i (packetOutput ε a h hε ha hp hb m g k t p i))).im := by
  rw [exactRate,packet_output,comp_const,const_pairing,PiLp.inner_apply,Complex.im_sum,
    Finset.mul_sum]
  rfl

theorem exact_rate_tendsto_zero :
    Tendsto (fun n : ℕ => exactRate ε hε h hh hb m g k t t
      (packetForm ε a h hε ha hp hb m g k t (-(n:ℝ)))) atTop (𝓝 0) := by
  simp_rw [packet_rate_decomposition]
  have hs : ∀ i : Fin 8, Tendsto (fun n : ℕ => (-2/h)*
      (inner ℂ (packetOutput ε a h hε ha hp hb m g k t (-(n:ℝ)) i)
        (factorAction ε hε h hb i (packetOutput ε a h hε ha hp hb m g k t (-(n:ℝ)) i))).im)
        atTop (𝓝 0) := by
    intro i
    by_cases hi : i.val < 5
    · simpa only [factorAction,hi,if_true,
        KFCausalClockFloorQuantumVelocityPairing.defect_inner_im_zero,mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    · have hz := ordered_coordinate_limit ε a h hε ha hp hb m g k t i (Nat.le_of_not_gt hi)
      have hA := ((factorAction ε hε h hb i).continuous.tendsto 0).comp hz
      have hr := ((Complex.continuous_im.tendsto _).comp (hz.inner hA)).const_mul (-2/h)
      simpa only [map_zero,inner_zero_left,Complex.zero_im,mul_zero] using hr
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun i _ => hs i)

#print axioms packet_embedding
#print axioms packet_output
#print axioms packet_defect_constant
#print axioms packet_defect_positive
#print axioms ordered_coordinate_limit
#print axioms packet_rate_decomposition
#print axioms exact_rate_tendsto_zero
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyClockRate
