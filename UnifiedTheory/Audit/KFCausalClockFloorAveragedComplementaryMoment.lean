/- The actual averaged form controls all four complementary transverse
coordinates and the neutral momentum coordinate, in the complementary
representation. Finiteness follows from the closed kinetic outputs. -/
import UnifiedTheory.Audit.KFCausalClockFloorComplementaryTonelli
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment
noncomputable section
open MeasureTheory
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalClockFloorSymmetricOrbitGraph (symmetricEnergyIndex form_symmetric_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol (complementaryWeight complementaryWeight_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorComplementaryTonelli
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def complementaryMoment (ε h : ℝ) (i : Fin 2) (f : Hilbert) : ℝ :=
  ∫ x, complementaryWeight ε h i x*‖(dualPhysical f) x‖^2

theorem complementaryMoment_nonnegative (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    0 ≤ complementaryMoment ε h i f :=
  integral_nonneg (fun x => mul_nonneg (complementaryWeight_nonnegative ε hε h i x) (sq_nonneg _))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t
local notation "L" => sectionMap ε hε h hb hh m g κ t

theorem averaged_complementaryMass_le (i : Fin 2) (u : V) :
    ENNReal.ofReal (1/2)*complementaryMass ε h i (J u) ≤ ENNReal.ofReal (‖A u‖^2) := by
  have hi : Integrable (fun θ => ‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2) angleMeasure := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A u))).mp (Lp.memLp (A u))
    apply hi.congr
    filter_upwards [(KFCausalClosedGraphForm.energyOutput B).coeFn_compLp (L u)] with θ hθ
    change ‖(KFCausalClosedGraphForm.energyOutput B).compLp (L u) θ‖^2 = _
    exact congrArg (fun v => ‖v‖^2) hθ
  have hR := (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm.trans
      (congrArg ENNReal.ofReal (energy_integral ε hε h hb hh m g κ t u).symm)
  have hL := (congrArg (fun r => ENNReal.ofReal (1/2)*r)
    (rotatedMass_angle ε hε h hh i (J u)).symm).trans
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  apply hL.trans_le
  apply LE.le.trans_eq _ hR
  apply lintegral_mono_ae
  filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
  let y := KFCausalClosedGraphForm.energyOutput B (L u θ) (symmetricEnergyIndex i)
  have hg := form_symmetric_graph ε hε h hb m g κ t i (L u θ)
  have hsource := congrArg (fun f : Hilbert =>
    ((Real.sqrt (1/2) : ℂ) • f,y) ∈ (clockMomentum ε h (symmetricDirection i)).graph) hθ
  have he := rotatedMass_half_graph ε hε h hh (2*Real.pi*θ) i (J u) y (hsource.mp hg)
  exact he.trans_le (ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (KFCausalClosedGraphForm.energyOutput B (L u θ)) (symmetricEnergyIndex i)) 2))

theorem averaged_complementaryMass_finite (i : Fin 2) (u : V) : complementaryMass ε h i (J u) ≠ ⊤ := by
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (averaged_complementaryMass_le ε hε h hb hh m g κ t i u)
  intro hm
  apply ht
  rw [hm,ENNReal.mul_top]
  norm_num

theorem averaged_complementaryDensity_integrable (i : Fin 2) (u : V) :
    Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical (J u)) x‖^2) :=
  (complementaryDensity_integrable_iff ε hε h i (J u)).mpr
    (averaged_complementaryMass_finite ε hε h hb hh m g κ t i u)

theorem averaged_complementaryMoment_bound (i : Fin 2) (u : V) :
    complementaryMoment ε h i (J u) ≤ 2*‖A u‖^2 := by
  have he := averaged_complementaryMass_le ε hε h hb hh m g κ t i u
  have hi := averaged_complementaryDensity_integrable ε hε h hb hh m g κ t i u
  let f : Hilbert := J u
  let E : ℝ := ‖A u‖^2
  have hE : 0 ≤ E := sq_nonneg _
  change ENNReal.ofReal (1/2)*complementaryMass ε h i f ≤ ENNReal.ofReal E at he
  change complementaryMoment ε h i f ≤ 2*E
  have hc : complementaryMass ε h i f = ENNReal.ofReal (complementaryMoment ε h i f) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (complementaryWeight_nonnegative ε hε h i x) (sq_nonneg _)))).symm
  rw [hc,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)] at he
  have hr := (ENNReal.ofReal_le_ofReal_iff hE).mp he
  linarith

omit hb in
theorem form_complementaryMoment_bound (hs : |h| ≤ 2*Real.pi*ε/3) (i : Fin 2)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ t) :
    Integrable (fun x => complementaryWeight ε h i x*
      ‖(dualPhysical (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u)) x‖^2) ∧
    complementaryMoment ε h i (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u) ≤
      2*‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t u‖^2 := by
  let v := Classical.choose (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  have hv := Classical.choose_spec (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  change KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hs m g κ t v = u at hv
  have hi := averaged_complementaryDensity_integrable ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t i v
  have he := averaged_complementaryMoment_bound ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t i v
  have hJ := congrArg (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t) hv
  have hA := congrArg (fun z => ‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t z‖^2) hv
  refine ⟨(congrArg (fun f : Hilbert => Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2)) hJ).mp hi,?_⟩
  exact (congrArg (complementaryMoment ε h i) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun r : ℝ => 2*r) hA))

#print axioms complementaryMoment_nonnegative
#print axioms averaged_complementaryMass_le
#print axioms averaged_complementaryMass_finite
#print axioms averaged_complementaryDensity_integrable
#print axioms averaged_complementaryMoment_bound
#print axioms form_complementaryMoment_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment
