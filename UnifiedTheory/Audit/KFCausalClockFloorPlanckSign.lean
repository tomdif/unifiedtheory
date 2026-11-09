/- Exact sign identities for the actual longitudinal exponential and initial
boosted states. Reversing both hbar and canonical boost leaves the initial
state unchanged. This does not identify the two Hamiltonian evolutions. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPlanckSign
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (positionFrequency_smul)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalClockFloorExponential

theorem symbol_neg (h : ℝ) (k : KFCausalEuclideanConfiguration.Space) :
    symbol (-h) k = -symbol h k := by unfold symbol; ring

theorem exponential_sign_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f g : Hilbert) :
    (f,g) ∈ (longitudinalExponential ε hε (-h) a).graph ↔
      (f,g) ∈ (longitudinalExponential ε hε h (-a)).graph := by
  rw [longitudinal_exponential_graph,longitudinal_exponential_graph]
  simp only [symbol_neg,mul_neg,neg_mul]

theorem trialState_neg (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    trialState ε a (-h) hε ha (neg_ne_zero.mpr hh) = trialState ε a h hε ha hh := by
  apply Lp.ext
  filter_upwards [trialState_coe ε a (-h) hε ha (neg_ne_zero.mpr hh),
    trialState_coe ε a h hε ha hh] with x hn hp
  rw [hn,hp]
  simp only [groundWidth,neutralWidth,abs_neg]

theorem unitTrial_neg (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    unitTrial ε a (-h) hε ha (neg_ne_zero.mpr hh) = unitTrial ε a h hε ha hh := by
  exact congrArg (fun f : Hilbert => (‖f‖⁻¹:ℝ) • f) (trialState_neg ε a h hε ha hh)

theorem positionFrequency_neg (p : Configuration) :
    positionFrequency (-p).1 (-p).2 = -positionFrequency p.1 p.2 := by
  apply ContinuousLinearMap.ext
  intro x
  change (-p.1)*x.1+(∑ i, (-p.2 i)*x.2 i) = -(p.1*x.1+∑ i, p.2 i*x.2 i)
  simp only [neg_mul,Finset.sum_neg_distrib]
  ring

theorem boostedState_sign (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (p : Configuration) :
    boostedState ε a (-h) hε ha (neg_ne_zero.mpr hh) (positionFrequency (-p).1 (-p).2) =
      boostedState ε a h hε ha hh (positionFrequency p.1 p.2) := by
  simp only [boostedState,positionFrequency_neg,inv_neg,neg_smul,smul_neg,neg_neg]
  exact congrArg (KFCausalPhysicalMomentumModulation.modulation
    (h⁻¹ • positionFrequency p.1 p.2)) (unitTrial_neg ε a h hε ha hh)

#print axioms symbol_neg
#print axioms exponential_sign_graph
#print axioms trialState_neg
#print axioms unitTrial_neg
#print axioms positionFrequency_neg
#print axioms boostedState_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorPlanckSign
