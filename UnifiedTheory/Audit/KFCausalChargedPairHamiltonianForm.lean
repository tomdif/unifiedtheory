/- Both paired and centered states lift into the completed averaged
Hamiltonian form. The exact full pairing separates into the unevaluated
kinetic pairing and the proved strictly nonzero potential contribution. -/
import UnifiedTheory.Audit.KFCausalChargedPairCharge
import UnifiedTheory.Audit.KFCausalChargedPairPotentialCoupling
import UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedPairHamiltonianForm
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargedPairPotentialCoupling (baseState potentialPairing potentialPairing_re_negative)
open KFCausalChargedPairDomain (state output output_graph)
open KFCausalChargedPairCharge (state_zeroSector state_outside_neutralClosure)
open KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound clockFunction trialState
    trialState_coe trialState_mem_zeroSector)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight energyWeight_norm_square)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorAveragedHamiltonian (graphFormVector)
open KFCausalFixedCommonEnergyPairing (fixedLift fixedLift_pairing)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "ψ" => state ε a h hε ha hh
local notation "ψ₀" => baseState ε a h hε ha hh

theorem baseState_eq_trial : ψ₀ = trialState ε a h hε ha hh := by
  apply Lp.ext
  filter_upwards [KFCausalClockFloorSourcedClockMomentum.state_coe
    ε a α β hε ha hα hβ hw 1 0 0,trialState_coe ε a h hε ha hh] with x hx hy
  change ψ₀ x = _ at hx
  rw [hx,hy]
  simp [KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,
    KFCausalClockFloorCoherentStrip.clockPhase,
    KFCausalChargeGaussianIdentities.configurationProfile]

theorem baseState_zeroSector : ψ₀ ∈ zeroSector h hh := by
  rw [baseState_eq_trial]
  exact trialState_mem_zeroSector ε a h hε ha hh

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def baseFactors (j : Fin 8) : Hilbert :=
  KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
    1 0 0 h hb modelDirections pointField j

def pairedFactors (j : Fin 8) : Hilbert :=
  output ε a h hε ha hh hb modelDirections pointField j

theorem baseFactors_graph (j : Fin 8) :
    (ψ₀,baseFactors ε a h hε ha hh hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hw
    1 0 0 h hb modelDirections pointField j

def baseLift (mass2 quartic vacuum t : ℝ) : FormSpace ε hε h hh hb mass2 quartic vacuum t :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t ψ₀
      (baseState_zeroSector ε a h hε ha hh) (baseFactors ε a h hε ha hh hb)
      (baseFactors_graph ε a h hε ha hh hb))

def pairedLift (mass2 quartic vacuum t : ℝ) : FormSpace ε hε h hh hb mass2 quartic vacuum t :=
  graphFormVector ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t ψ
      (state_zeroSector ε a h hε ha hh) (pairedFactors ε a h hε ha hh hb)
      (output_graph ε a h hε ha hh hb modelDirections pointField))

theorem baseLift_embedding (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (baseLift ε a h hε ha hh hb mass2 quartic vacuum t) = ψ₀ := rfl

theorem pairedLift_embedding (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t) = ψ := rfl

theorem pairedLift_outside_neutralClosure (mass2 quartic vacuum t : ℝ) :
    embedding ε hε h hh hb mass2 quartic vacuum t
      (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t) ∉
        closure (KFCausalNeutralSwapConstraint.neutralStates ε h hε hh) :=
  state_outside_neutralClosure ε a h hε ha hh

def formPairing (mass2 quartic vacuum t : ℝ) : ℂ :=
  inner ℂ (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (baseLift ε a h hε ha hh hb mass2 quartic vacuum t))
    (energyOutput ε hε h hh hb mass2 quartic vacuum t
      (pairedLift ε a h hε ha hh hb mass2 quartic vacuum t))

theorem formPairing_sum (mass2 quartic vacuum t : ℝ) :
    formPairing ε a h hε ha hh hb mass2 quartic vacuum t =
      ∑ j : Fin 8, inner ℂ (energyWeight mass2 quartic vacuum t j • baseFactors ε a h hε ha hh hb j)
        (energyWeight mass2 quartic vacuum t j • pairedFactors ε a h hε ha hh hb j) :=
  fixedLift_pairing ε h hε hh hb mass2 quartic vacuum t ψ₀
    (baseState_zeroSector ε a h hε ha hh) (baseFactors ε a h hε ha hh hb)
    (baseFactors_graph ε a h hε ha hh hb) ψ
    (state_zeroSector ε a h hε ha hh) (pairedFactors ε a h hε ha hh hb)
    (output_graph ε a h hε ha hh hb modelDirections pointField)

def factorPairing (j : Fin 8) : ℂ :=
  inner ℂ (baseFactors ε a h hε ha hh hb j) (pairedFactors ε a h hε ha hh hb j)

def kineticPairing (t : ℝ) : ℂ :=
  (factorPairing ε a h hε ha hh hb 0+factorPairing ε a h hε ha hh hb 1+
    factorPairing ε a h hε ha hh hb 2)/2+
    (Real.exp (2*t):ℂ)*(factorPairing ε a h hε ha hh hb 3+factorPairing ε a h hε ha hh hb 4)/2

private theorem weighted_pairing (w : ℂ) (f g : Hilbert) :
    inner ℂ (w • f) (w • g) = (‖w‖^2:ℝ)*inner ℂ f g := by
  rw [inner_smul_left,inner_smul_right,← mul_assoc]
  rw [Complex.conj_mul',Complex.ofReal_pow]

theorem unit_decomposition (t : ℝ) :
    formPairing ε a h hε ha hh hb 1 1 1 t =
      kineticPairing ε a h hε ha hh hb t+
        (Real.exp (2*t):ℂ)*potentialPairing ε a h hε ha hh hb := by
  have hp : potentialPairing ε a h hε ha hh hb =
      factorPairing ε a h hε ha hh hb 7+
        (1/2:ℂ)*factorPairing ε a h hε ha hh hb 5+
        (1/4:ℂ)*factorPairing ε a h hε ha hh hb 6 := rfl
  rw [formPairing_sum,hp]
  simp_rw [weighted_pairing,energyWeight_norm_square 1 1 1 t
    (by norm_num) (by norm_num) (by norm_num)]
  simp only [mul_one]
  change (∑ j : Fin 8, ((![1/2,1/2,1/2,Real.exp (2*t)/2,Real.exp (2*t)/2,
      Real.exp (2*t)/2,Real.exp (2*t)/4,Real.exp (2*t)] j:ℝ):ℂ)*
        factorPairing ε a h hε ha hh hb j) = _
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  unfold kineticPairing
  ring!

theorem potential_contribution_re_negative (t : ℝ) :
    ((Real.exp (2*t):ℂ)*potentialPairing ε a h hε ha hh hb).re < 0 := by
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (potentialPairing_re_negative ε a h hε ha hh hb)

#print axioms baseState_eq_trial
#print axioms baseState_zeroSector
#print axioms baseFactors_graph
#print axioms baseLift_embedding
#print axioms pairedLift_embedding
#print axioms pairedLift_outside_neutralClosure
#print axioms formPairing_sum
#print axioms unit_decomposition
#print axioms potential_contribution_re_negative
end
end UnifiedTheory.Audit.KFCausalChargedPairHamiltonianForm
