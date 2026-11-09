/- Charge-averaged quantum energy forces finite inverse-clock weighted
second moments of two physical momenta and two paired positions. The
integrability assertion follows from the actual closed graph, via Tonelli. -/
import UnifiedTheory.Audit.KFCausalClockFloorChargedMomentTonelli
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment
noncomputable section
open MeasureTheory
open scoped ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action)
open UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph (antiIndex form_anti_graph)
open UnifiedTheory.Audit.KFCausalClockFloorRotatedAntiSymbol (chargedWeight chargedWeight_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorChargedMomentTonelli
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def chargedMoment (ε h : ℝ) (i : Fin 2) (f : Hilbert) : ℝ :=
  ∫ x, chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2

theorem chargedMoment_nonnegative (ε : ℝ) (hε : 0 < ε) (h : ℝ) (i : Fin 2) (f : Hilbert) :
    0 ≤ chargedMoment ε h i f :=
  integral_nonneg (fun x => mul_nonneg (chargedWeight_nonnegative ε hε h i x) (sq_nonneg _))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t
local notation "L" => sectionMap ε hε h hb hh m g κ t

theorem averaged_chargedMass_le (i : Fin 2) (u : V) :
    ENNReal.ofReal ((Real.exp t*Real.sqrt (1/2))^2)*chargedMass ε h i (J u) ≤
      ENNReal.ofReal (‖A u‖^2) := by
  have hi : Integrable (fun θ => ‖KFCausalClosedGraphForm.energyOutput B (L u θ)‖^2) angleMeasure := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A u))).mp (Lp.memLp (A u))
    apply hi.congr
    filter_upwards [(KFCausalClosedGraphForm.energyOutput B).coeFn_compLp (L u)] with θ hθ
    change ‖(KFCausalClosedGraphForm.energyOutput B).compLp (L u) θ‖^2 = _
    exact congrArg (fun v => ‖v‖^2) hθ
  have hR := (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm.trans
      (congrArg ENNReal.ofReal (energy_integral ε hε h hb hh m g κ t u).symm)
  have hL := (congrArg (fun r => ENNReal.ofReal ((Real.exp t*Real.sqrt (1/2))^2)*r)
    (kineticMass_angle ε hε h hh i (J u)).symm).trans
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  apply hL.trans_le
  apply LE.le.trans_eq _ hR
  apply lintegral_mono_ae
  filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
  have hg := form_anti_graph ε hε h hb m g κ t i (L u θ)
  have he := (kineticMass_smul ε h i (Real.exp t*Real.sqrt (1/2)) _).symm.trans
    (kineticMass_graph ε hε h hh i _ _ hg)
  have hk := congrArg (fun f : Hilbert => ENNReal.ofReal ((Real.exp t*Real.sqrt (1/2))^2)*
    kineticMass ε h i f) hθ
  exact (hk.symm.trans he).trans_le (ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (KFCausalClosedGraphForm.energyOutput B (L u θ)) (antiIndex i)) 2))

theorem averaged_chargedMass_finite (i : Fin 2) (u : V) : chargedMass ε h i (J u) ≠ ⊤ := by
  have hc : ENNReal.ofReal ((Real.exp t*Real.sqrt (1/2))^2) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    positivity
  have ht := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (averaged_chargedMass_le ε hε h hb hh m g κ t i u)
  intro hm
  apply ht
  rw [hm,ENNReal.mul_top]
  exact hc

theorem averaged_chargedDensity_integrable (i : Fin 2) (u : V) :
    Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates (J u)) x‖^2) :=
  (chargedDensity_integrable_iff ε hε h i (J u)).mpr
    (averaged_chargedMass_finite ε hε h hb hh m g κ t i u)

theorem averaged_chargedMoment_bound (i : Fin 2) (u : V) :
    chargedMoment ε h i (J u) ≤ 2*Real.exp (-2*t)*‖A u‖^2 := by
  have he := averaged_chargedMass_le ε hε h hb hh m g κ t i u
  have hi := averaged_chargedDensity_integrable ε hε h hb hh m g κ t i u
  let f : Hilbert := J u
  let E : ℝ := ‖A u‖^2
  have hE : 0 ≤ E := sq_nonneg _
  change ENNReal.ofReal ((Real.exp t*Real.sqrt (1/2))^2)*chargedMass ε h i f ≤ ENNReal.ofReal E at he
  change chargedMoment ε h i f ≤ 2*Real.exp (-2*t)*E
  have hc : chargedMass ε h i f = ENNReal.ofReal (chargedMoment ε h i f) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (chargedWeight_nonnegative ε hε h i x) (sq_nonneg _)))).symm
  rw [hc,← ENNReal.ofReal_mul (sq_nonneg _)] at he
  have hr := (ENNReal.ofReal_le_ofReal_iff hE).mp he
  have hw : (Real.exp t*Real.sqrt (1/2))^2 = Real.exp (2*t)/2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2),
      show 2*t=t+t by ring,Real.exp_add]
    ring
  rw [hw] at hr
  have hp := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.exp (-2*t) by positivity)
  have hex : Real.exp (-2*t)*Real.exp (2*t) = 1 := by
    rw [← Real.exp_add,show -2*t+2*t=0 by ring,Real.exp_zero]
  calc
    chargedMoment ε h i f = 2*Real.exp (-2*t)*(Real.exp (2*t)/2*chargedMoment ε h i f) := by
      calc
        _ = (Real.exp (-2*t)*Real.exp (2*t))*chargedMoment ε h i f := by rw [hex,one_mul]
        _ = _ := by ring
    _ ≤ _ := by simpa only [mul_assoc] using hp

omit hb in
theorem form_chargedMoment_bound (hs : |h| ≤ 2*Real.pi*ε/3) (i : Fin 2)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ t) :
    Integrable (fun x => chargedWeight ε h i x*
      ‖(chargeCoordinates (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u)) x‖^2) ∧
    chargedMoment ε h i (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t u) ≤
      2*Real.exp (-2*t)*‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t u‖^2 := by
  let v := Classical.choose (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  have hv := Classical.choose_spec (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ t u)
  change KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hs m g κ t v = u at hv
  have hi := averaged_chargedDensity_integrable ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t i v
  have he := averaged_chargedMoment_bound ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ t i v
  have hJ := congrArg (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ t) hv
  have hA := congrArg (fun z => ‖KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hs m g κ t z‖^2) hv
  refine ⟨(congrArg (fun f : Hilbert => Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2)) hJ).mp hi,?_⟩
  exact (congrArg (chargedMoment ε h i) hJ).symm.trans_le
    (he.trans_eq (congrArg (fun r : ℝ => 2*Real.exp (-2*t)*r) hA))

#print axioms chargedMoment_nonnegative
#print axioms averaged_chargedMass_le
#print axioms averaged_chargedMass_finite
#print axioms averaged_chargedDensity_integrable
#print axioms averaged_chargedMoment_bound
#print axioms form_chargedMoment_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment
