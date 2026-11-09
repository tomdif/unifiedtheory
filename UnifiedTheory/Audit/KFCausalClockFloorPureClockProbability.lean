/- The actual pure-clock momentum Born law, its transport characteristic,
and exact charge invariance. Graph outputs control both tails; no bound
along the Hamiltonian evolution is postulated or proved here. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockChargeGraph
import UnifiedTheory.Audit.KFCausalCanonicalClockTails

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockProbability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum momentum_graph_conjugacy)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport (transport transport_apply)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (translation)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCharge (inverse_coordinates_charge)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε)
local notation "U" => coordinates ε hε

def law (h : ℝ) (f : Hilbert) : Measure ℝ :=
  KFCausalCanonicalClockProbability.law h ((U).symm f)

def tail (h R : ℝ) (f : Hilbert) : ℝ :=
  KFCausalCanonicalClockTails.tail h R ((U).symm f)

theorem law_total (h : ℝ) (f : Hilbert) : law ε hε h f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [law,KFCausalCanonicalClockProbability.law_total,LinearIsometryEquiv.norm_map]

instance law_finite (h : ℝ) (f : Hilbert) : IsFiniteMeasure (law ε hε h f) :=
  KFCausalCanonicalClockProbability.law_finite h ((U).symm f)

theorem law_probability (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) : IsProbabilityMeasure (law ε hε h f) where
  measure_univ := by rw [law_total,hf,one_pow,ENNReal.ofReal_one]

theorem law_characteristic (h v : ℝ) (f : Hilbert) :
    charFun (law ε hε h f) v = inner ℂ f (transport ε hε (h*v) f) := by
  rw [law,KFCausalCanonicalClockProbability.law_characteristic]
  have he := (U).inner_map_map ((U).symm f) (translation (h*v) ((U).symm f))
  simpa only [LinearIsometryEquiv.apply_symm_apply,transport_apply] using he.symm

theorem law_charge (h : ℝ) (hne : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    law ε hε h (action h hne θ f) = law ε hε h f := by
  rw [law,inverse_coordinates_charge,KFCausalCanonicalClockProbability.law_charge]
  rfl

theorem averaged_law (h : ℝ) (hne : h ≠ 0) (f : Hilbert) (A : Set ℝ) :
    (∫⁻ θ, law ε hε h (action h hne (2*Real.pi*θ) f) A ∂angleMeasure) = law ε hε h f A := by
  simp only [law_charge,lintegral_const,measure_univ,mul_one]

theorem tail_nonnegative (h R : ℝ) (f : Hilbert) : 0 ≤ tail ε hε h R f :=
  KFCausalCanonicalClockTails.tail_nonnegative h R ((U).symm f)

theorem law_tail (h R : ℝ) (f : Hilbert) :
    law ε hε h f {p | R^2 ≤ p^2} = ENNReal.ofReal (tail ε hε h R f) :=
  KFCausalCanonicalClockTails.law_tail h R ((U).symm f)

theorem tail_charge (h : ℝ) (hne : h ≠ 0) (R θ : ℝ) (f : Hilbert) :
    tail ε hε h R (action h hne θ f) = tail ε hε h R f := by
  rw [tail,inverse_coordinates_charge,KFCausalCanonicalClockTails.tail_charge]
  rfl

theorem averaged_tail (h : ℝ) (hne : h ≠ 0) (R : ℝ) (f : Hilbert) :
    (∫ θ, tail ε hε h R (action h hne (2*Real.pi*θ) f) ∂angleMeasure) = tail ε hε h R f := by
  simp only [tail_charge,integral_const,probReal_univ,one_smul]

theorem inverse_graph (h : ℝ) (hne : h ≠ 0) (f g : Hilbert)
    (hg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    ((U).symm f,(U).symm g) ∈ (clockMomentum h).graph := by
  apply (momentum_graph_conjugacy ε hε h hne _ _).mpr
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hg

theorem graph_tail_bound (h : ℝ) (hne : h ≠ 0) (R : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    R^2*tail ε hε h R f ≤ ‖g‖^2 := by
  simpa only [LinearIsometryEquiv.norm_map] using KFCausalCanonicalClockTails.graph_tail_bound
    h hne R ((U).symm f) ((U).symm g) (inverse_graph ε hε h hne f g hg)

theorem law_outside_bound (h : ℝ) (hne : h ≠ 0) (R : ℝ) (hR : 0 < R) (f g : Hilbert)
    (hg : (f,g) ∈ (pureMomentum ε hε h).graph) :
    law ε hε h f (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal (‖g‖^2/R^2) := by
  simpa only [LinearIsometryEquiv.norm_map] using KFCausalCanonicalClockTails.law_outside_bound
    h hne R hR ((U).symm f) ((U).symm g) (inverse_graph ε hε h hne f g hg)

#print axioms law_total
#print axioms law_finite
#print axioms law_probability
#print axioms law_characteristic
#print axioms law_charge
#print axioms averaged_law
#print axioms tail_nonnegative
#print axioms law_tail
#print axioms tail_charge
#print axioms averaged_tail
#print axioms inverse_graph
#print axioms graph_tail_bound
#print axioms law_outside_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockProbability
