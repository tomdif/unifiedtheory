/- The actual boosted initial states have both signs of longitudinal
exponential energy after the prescribed inverse-clock weight. The negative
output is constructed by exact Planck/boost sign identities; its bound and
classical initial limit are derived, not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPlanckSign
import UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
import UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialNegativeExponential
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorPlanckSign
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (boostedExponentialOutput boostedExponential_graph)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (exponentialMass boostedExponential_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

def input (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (p : Configuration) : Hilbert :=
  inverseL ε hε (boostedState ε a h hε ha hh (positionFrequency p.1 p.2))

def negativeOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : Hilbert :=
  boostedExponentialOutput ε a (-h) hε ha (neg_ne_zero.mpr hh) (by simpa only [abs_neg] using hb) (-p)

theorem positive_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (input ε a h hε ha hh p,boostedExponentialOutput ε a h hε ha hh hb p) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  (ordered_graph_iff ε hε h _ _).mp (boostedExponential_graph ε a h hε ha hh hb p)

theorem negative_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (input ε a h hε ha hh p,negativeOutput ε a h hε ha hh hb p) ∈
      (longitudinalExponential ε hε (-h) (1/2)).graph := by
  have he := positive_graph ε a (-h) hε ha (neg_ne_zero.mpr hh)
    (by simpa only [abs_neg] using hb) (-p)
  have hs : input ε a (-h) hε ha (neg_ne_zero.mpr hh) (-p) = input ε a h hε ha hh p :=
    congrArg (inverseL ε hε) (boostedState_sign ε a h hε ha hh p)
  exact (congrArg (fun f : Hilbert => (f,negativeOutput ε a h hε ha hh hb p) ∈
    (longitudinalExponential ε hε (-h) (1/2)).graph) hs).mp he

theorem negative_exponential_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (input ε a h hε ha hh p,negativeOutput ε a h hε ha hh hb p) ∈
      (longitudinalExponential ε hε h (-(1/2))).graph :=
  (exponential_sign_graph ε hε h (1/2) _ _).mp (negative_graph ε a h hε ha hh hb p)

theorem negative_output_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) :
    ‖negativeOutput ε a h hε ha hh hb p‖^2 ≤ exponentialMass ε a (-p)/clockMass ε a :=
  boostedExponential_bound ε a (-h) hε ha (neg_ne_zero.mpr hh)
    (by simpa only [abs_neg] using hb) (by simpa only [abs_neg] using h1) (-p)

theorem negative_output_energy_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖negativeOutput ε a (h n) hε ha (hh n) (hb n) p‖^2) atTop
      (𝓝 (∫ s, Real.exp (-p.1/clock ε s)/clock ε s ∂clockLaw ε a)) := by
  have he := KFCausalClockFloorBoostedEnergyIdentification.exponential_energy_clockLaw
    ε a hε ha (-p) (fun n => -h n) (fun n => neg_ne_zero.mpr (hh n))
    (fun n => by simpa only [abs_neg] using hb n)
    (fun n => by simpa only [abs_neg] using h1 n) (by simpa only [neg_zero] using hz.neg)
  exact he

#print axioms positive_graph
#print axioms negative_graph
#print axioms negative_exponential_graph
#print axioms negative_output_bound
#print axioms negative_output_energy_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialNegativeExponential
