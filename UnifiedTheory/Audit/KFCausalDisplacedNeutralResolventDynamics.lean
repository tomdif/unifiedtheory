/- The actual canonical neutral characteristic has a resolvent linear
response balance, with the explicit quadratic remainder retained. -/
import UnifiedTheory.Audit.KFCausalNeutralResolventContinuity
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalMovingBalance
import UnifiedTheory.Audit.KFCausalDisplacedNeutralDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalDisplacedNeutralResolventDynamics
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution_strong_continuous)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency operator_action)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalResolventBalance (test)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear weightedQuadratic)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

theorem test_action (h v : ℝ) (f : Hilbert) : test h (frequency v) f = action (h*v) f :=
  operator_action h v f

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
local notation "f" => evolvedState ε a h hε ha hne hh m g k s p
local notation "x" => trajectory ε a h hε ha hne hh m g k s p
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "X" => KFCausalDisplacedNeutralDynamics.characteristic ε a h hε ha hne hh m g k s p

def rate (r t v : ℝ) : ℂ :=
  KFCausalClockFloorCanonicalMovingBalance.rate ε a h hε ha hne hh m g k s p r t (frequency v)

def linearRate (r t v : ℝ) : ℂ :=
  KFCausalNeutralResolventResponse.linearRate ε hε h hne hh m g k r t v (f t)

def quadraticRate (r t v : ℝ) : ℂ :=
  KFCausalNeutralResolventResponse.quadraticRate ε hε h hne hh m g k r t v (f t)

def residual (r v b c : ℝ) : ℂ :=
  (∫ t in b..c, linearRate ε a h hε ha hne hh m g k s p r t v)-(X v c-X v b)

theorem rate_formula (r t v : ℝ) :
    rate ε a h hε ha hne hh m g k s p r t v =
      KFCausalNeutralResolventResponse.rate ε hε h hne hh m g k r t v (f t) := by
  simpa only [rate,test_action,KFCausalNeutralResolventResponse.rate,evolvedState] using
    KFCausalClockFloorCanonicalMovingBalance.rate_formula ε a h hε ha hne hh m g k s p r t (frequency v)

theorem linearRate_continuous (r v : ℝ) (hr : 0 < r) :
    Continuous (fun t => linearRate ε a h hε ha hne hh m g k s p r t v) :=
  KFCausalNeutralResolventContinuity.linearRate_continuous ε hε h hne hh m g k r v hr f
    (evolution_strong_continuous ε hε h hne hh m g k s _)

theorem quadraticRate_continuous (r v : ℝ) (hr : 0 < r) :
    Continuous (fun t => quadraticRate ε a h hε ha hne hh m g k s p r t v) :=
  KFCausalNeutralResolventContinuity.quadraticRate_continuous ε hε h hne hh m g k r v hr f
    (evolution_strong_continuous ε hε h hne hh m g k s _)

theorem linearRate_energy_bound (r t v : ℝ) (hr : 0 < r) :
    ‖linearRate ε a h hε ha hne hh m g k s p r t v‖ ≤
      2*|v| *‖weightedLinear (energyWeight m g k 0)‖*E t (x t) := by
  simpa only [trajectory_embedding,linearRate,evolvedState] using
    KFCausalNeutralResolventResponse.linearRate_energy_bound ε hε h hne hh m g k r t v hr (x t)

theorem quadraticRate_energy_bound (r t v : ℝ) (hr : 0 < r) :
    ‖quadraticRate ε a h hε ha hne hh m g k s p r t v‖ ≤
      2*|h| *|v|^2*‖weightedQuadratic (energyWeight m g k 0)‖*E t (x t) := by
  simpa only [trajectory_embedding,quadraticRate,evolvedState] using
    KFCausalNeutralResolventResponse.quadraticRate_energy_bound ε hε h hne hh m g k r t v hr (x t)

variable (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
include hm hg hk

theorem rate_polynomial (r t v : ℝ) (hr : 0 < r) :
    rate ε a h hε ha hne hh m g k s p r t v =
      linearRate ε a h hε ha hne hh m g k s p r t v+quadraticRate ε a h hε ha hne hh m g k s p r t v :=
  (rate_formula ε a h hε ha hne hh m g k s p r t v).trans
    (KFCausalNeutralResolventResponse.rate_polynomial ε hε h hne hh m g k hm hg hk r t v hr (f t))

theorem rate_energy_bound (r t v H : ℝ) (hr : 0 < r) (hH : |h| ≤ H) :
    ‖rate ε a h hε ha hne hh m g k s p r t v‖ ≤
      speedBound (energyWeight m g k 0) H v*E t (x t) := by
  have hb := KFCausalNeutralResolventResponse.rate_energy_bound ε hε h hne hh m g k hm hg hk r t v H hr hH (x t)
  exact (congrArg norm (rate_formula ε a h hε ha hne hh m g k s p r t v)).le.trans
    (by simpa only [trajectory_embedding,evolvedState] using hb)

theorem residual_decomposition (r v b c : ℝ) (hr : 0 < r) :
    residual ε a h hε ha hne hh m g k s p r v b c =
      KFCausalClockFloorCanonicalMovingBalance.residual ε a h hε ha hne hh m g k s p r (frequency v) b c-
        ∫ t in b..c, quadraticRate ε a h hε ha hne hh m g k s p r t v := by
  have hi : (∫ t in b..c, rate ε a h hε ha hne hh m g k s p r t v) =
      (∫ t in b..c, linearRate ε a h hε ha hne hh m g k s p r t v)+
      (∫ t in b..c, quadraticRate ε a h hε ha hne hh m g k s p r t v) := by
    calc
      _ = ∫ t in b..c, linearRate ε a h hε ha hne hh m g k s p r t v+
          quadraticRate ε a h hε ha hne hh m g k s p r t v :=
        intervalIntegral.integral_congr (fun t _ => rate_polynomial ε a h hε ha hne hh m g k s p hm hg hk r t v hr)
      _ = _ := intervalIntegral.integral_add
        ((linearRate_continuous ε a h hε ha hne hh m g k s p r v hr).intervalIntegrable b c)
        ((quadraticRate_continuous ε a h hε ha hne hh m g k s p r v hr).intervalIntegrable b c)
  change (∫ t in b..c, linearRate ε a h hε ha hne hh m g k s p r t v)-(X v c-X v b) =
    ((∫ t in b..c, rate ε a h hε ha hne hh m g k s p r t v)-(X v c-X v b))-
      ∫ t in b..c, quadraticRate ε a h hε ha hne hh m g k s p r t v
  rw [hi]
  ring

#print axioms test_action
#print axioms rate_formula
#print axioms linearRate_continuous
#print axioms quadraticRate_continuous
#print axioms linearRate_energy_bound
#print axioms quadraticRate_energy_bound
#print axioms rate_polynomial
#print axioms rate_energy_bound
#print axioms residual_decomposition
end
end UnifiedTheory.Audit.KFCausalDisplacedNeutralResolventDynamics
