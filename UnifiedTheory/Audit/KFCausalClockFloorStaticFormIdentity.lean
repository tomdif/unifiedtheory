/- Exact ambient static energy in the actual complementary Fourier chart.
Every vector in the completed averaged form has the three finite moments
below, and its static output norm is exactly their half-sum. The neutral
momentum and its charge-average cross terms are retained by the proved
rotated symbol identity. No maximal static-operator or common-core
identification is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticFormIdentity
noncomputable section
open MeasureTheory
open scoped ENNReal
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorChargeClockHalf (clockHalf_graph_action)
open KFCausalClockFloorDualClock (dualClock_integral dualClock_integrable)
open KFCausalClockFloorAveragedClockBound (averaged_clock_graph)
open KFCausalClockFloorAveragedComplementaryMoment
open KFCausalClockFloorComplementaryTonelli
open KFCausalClockFloorSymmetricOrbitGraph (symmetricEnergyIndex form_symmetric_graph)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalComplementaryChargeSymbol (complementaryWeight complementaryWeight_nonnegative)
open KFCausalClockFloorAveragedEnergy
open KFCausalAveragedOutputRescaling (staticOutputLp)
open KFCausalPhysicalEnergyTransport (staticOutput)
open KFCausalFiniteOutputRescaling (selected_apply)
open KFCausalPhysicalCircleAction (action)
open KFCausalUnitIntervalOrbit (angleMeasure)

def clockMoment (ε : ℝ) (f : Hilbert) : ℝ :=
  ∫ x, clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2

private theorem clm_square_integrable {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (v : Lp X 2 angleMeasure) :
    Integrable (fun θ => ‖T (v θ)‖^2) angleMeasure := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (T.compLp v))).mp
    (Lp.memLp (T.compLp v))
  apply hi.congr
  filter_upwards [T.coeFn_compLp v] with θ hθ
  exact congrArg (fun y : Y => ‖y‖^2) hθ

private theorem clock_integrable_of_graph_exists (ε : ℝ) (hε : 0 < ε) (f : Hilbert)
    (hf : ∃ y : Hilbert, (f,y) ∈ (clockHalf ε).graph) :
    Integrable (fun x => clock ε (x (.inr 0))*‖(dualPhysical f) x‖^2) :=
  hf.elim (fun y hy => dualClock_integrable ε hε f y hy)

private theorem clock_orbit_integral (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f y : Hilbert) (z : ℝ → Hilbert) (hy : (f,y) ∈ (clockHalf ε).graph)
    (hz : ∀ᵐ θ ∂angleMeasure,
      (((Real.sqrt (1/2):ℝ):ℂ) • action h hh (2*Real.pi*θ) f,z θ) ∈ (clockHalf ε).graph) :
    (∫ θ, ‖z θ‖^2 ∂angleMeasure) = (1/2)*clockMoment ε f := by
  have he : (fun θ => ‖z θ‖^2) =ᵐ[angleMeasure] fun _ => (1/2)*‖y‖^2 := by
    filter_upwards [hz] with θ hθ
    have hs := (clockHalf ε).graph.smul_mem ((Real.sqrt (1/2):ℝ):ℂ)
      (clockHalf_graph_action ε hε h hh (2*Real.pi*θ) f y hy)
    have ho := (clockHalf ε).mem_graph_snd_inj' hθ hs rfl
    change z θ = ((Real.sqrt (1/2):ℝ):ℂ) • action h hh (2*Real.pi*θ) y at ho
    rw [ho,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2),(action h hh (2*Real.pi*θ)).norm_map]
  rw [integral_congr_ae he]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  exact congrArg (fun z : ℝ => (1/2)*z) (dualClock_integral ε hε f y hy).symm

private theorem half_integral_of_mass (z : ℝ → Hilbert) (M : ℝ) (hM : 0 ≤ M)
    (iz : Integrable (fun θ => ‖z θ‖^2) angleMeasure) (F : ℝ → ℝ≥0∞)
    (hF : (∫⁻ θ, F θ ∂angleMeasure) = ENNReal.ofReal M)
    (he : (fun θ => ENNReal.ofReal (1/2)*F θ) =ᵐ[angleMeasure]
      fun θ => ENNReal.ofReal (‖z θ‖^2)) :
    (∫ θ, ‖z θ‖^2 ∂angleMeasure) = (1/2)*M := by
  have hl := (lintegral_const_mul' (ENNReal.ofReal (1/2)) F ENNReal.ofReal_ne_top).trans
    (congrArg (fun r : ℝ≥0∞ => ENNReal.ofReal (1/2)*r) hF)
  have hr := (ofReal_integral_eq_lintegral_ofReal iz
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
  have hs := hl.symm.trans ((lintegral_congr_ae he).trans hr)
  dsimp only at hs
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)] at hs
  exact ((ENNReal.ofReal_eq_ofReal_iff
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hM)
    (integral_nonneg (fun _ => sq_nonneg _))).mp hs).symm

private theorem static_norm_square (y : PiLp 2 (fun _ : Fin 8 => Hilbert)) :
    ‖staticOutput y‖^2 = ‖y 0‖^2+‖y 1‖^2+‖y 2‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [staticOutput,selected_apply,Fin.sum_univ_succ,add_assoc]

private theorem static_compLp_energy {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] PiLp 2 (fun _ : Fin 8 => Hilbert)) (v : Lp X 2 angleMeasure) :
    ‖staticOutputLp (T.compLp v)‖^2 =
      (∫ θ, ‖T (v θ) 0‖^2 ∂angleMeasure)+
      (∫ θ, ‖T (v θ) 1‖^2 ∂angleMeasure)+
      (∫ θ, ‖T (v θ) 2‖^2 ∂angleMeasure) := by
  have hi (i : Fin 8) : Integrable (fun θ => ‖T (v θ) i‖^2) angleMeasure :=
    clm_square_integrable ((PiLp.proj 2 (fun _ : Fin 8 => Hilbert) i).comp T) v
  rw [KFCausalAveragedEnergyGraph.l2_norm_square]
  have he : (fun θ => ‖staticOutputLp (T.compLp v) θ‖^2) =ᵐ[angleMeasure]
      fun θ => ‖T (v θ) 0‖^2+‖T (v θ) 1‖^2+‖T (v θ) 2‖^2 := by
    filter_upwards [staticOutput.coeFn_compLp (T.compLp v),T.coeFn_compLp v] with θ hs ht
    change ‖staticOutput.compLp (T.compLp v) θ‖^2 = _
    rw [hs,ht]
    exact static_norm_square (T (v θ))
  rw [integral_congr_ae he]
  calc
    _ = (∫ θ, ‖T (v θ) 0‖^2+‖T (v θ) 1‖^2 ∂angleMeasure)+
        (∫ θ, ‖T (v θ) 2‖^2 ∂angleMeasure) := by
      simpa only [Pi.add_apply] using integral_add ((hi 0).add (hi 1)) (hi 2)
    _ = _ := congrArg (fun r : ℝ => r+(∫ θ, ‖T (v θ) 2‖^2 ∂angleMeasure))
      (integral_add (hi 0) (hi 1))

private theorem half_sum {a b c x y z : ℝ}
    (ha : a=(1/2)*x) (hb : b=(1/2)*y) (hc : c=(1/2)*z) :
    a+b+c=(x+y+z)/2 := by rw [ha,hb,hc]; ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ Real.pi*ε) (hh : h ≠ 0)
  (m g κ t : ℝ)
local notation "B" => KFCausalClockFloorFormHamiltonian.formData ε hε h hb m g κ t
local notation "V" => AveragedSpace ε hε h hb hh m g κ t
local notation "J" => embedding ε hε h hb hh m g κ t
local notation "A" => energyOutput ε hε h hb hh m g κ t
local notation "L" => sectionMap ε hε h hb hh m g κ t
local notation "E" => KFCausalClosedGraphForm.energyOutput B

private theorem component_integrable (u : V) (i : Fin 8) :
    Integrable (fun θ => ‖E (L u θ) i‖^2) angleMeasure :=
  clm_square_integrable ((PiLp.proj 2 (fun _ : Fin 8 => Hilbert) i).comp E) (L u)

private theorem base_clock_graph (v : KFCausalClosedGraphForm.FormSpace B) :
    (((Real.sqrt (1/2):ℝ):ℂ) • KFCausalClosedGraphForm.embedding B v,E v 0) ∈
      (clockHalf ε).graph := by
  let f : Hilbert := KFCausalClosedGraphForm.embedding B v
  let y := E v
  have hc := KFCausalClockFloorJointEnergy.closedEnergy_component_graph ε hε h
    KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField
    m g κ t hb f y v.property 0
  change (((Real.sqrt (1/2):ℝ):ℂ) • f,y 0) ∈ (clockHalf ε).closure.graph at hc
  have hclosed := (clockHalf_selfAdjoint ε).isClosed
  have he : (clockHalf ε).closure.graph = (clockHalf ε).graph :=
    hclosed.isClosable.graph_closure_eq_closure_graph.symm.trans
      hclosed.submodule_topologicalClosure_eq
  exact he ▸ hc

theorem averaged_clockMoment_integrable (u : V) :
    Integrable (fun x => clock ε (x (.inr 0))*‖(dualPhysical (J u)) x‖^2) :=
  clock_integrable_of_graph_exists ε hε (J u)
    (averaged_clock_graph ε hε h hb hh m g κ t u)

theorem averaged_clock_component (u : V) :
    (∫ θ, ‖E (L u θ) 0‖^2 ∂angleMeasure) = (1/2)*clockMoment ε (J u) := by
  let y : Hilbert := Classical.choose (averaged_clock_graph ε hε h hb hh m g κ t u)
  have hy : (J u,y) ∈ (clockHalf ε).graph :=
    Classical.choose_spec (averaged_clock_graph ε hε h hb hh m g κ t u)
  apply clock_orbit_integral ε hε h hh (J u) y (fun θ => E (L u θ) 0) hy
  filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
  have hc := base_clock_graph ε hε h hb m g κ t (L u θ)
  exact (congrArg (fun f : Hilbert =>
    (((Real.sqrt (1/2):ℝ):ℂ) • f,E (L u θ) 0) ∈ (clockHalf ε).graph) hθ).mp hc

theorem averaged_symmetric_component (u : V) (i : Fin 2) :
    (∫ θ, ‖E (L u θ) (symmetricEnergyIndex i)‖^2 ∂angleMeasure) =
      (1/2)*complementaryMoment ε h i (J u) := by
  let f : Hilbert := J u
  let z : ℝ → Hilbert := fun θ => E (L u θ) (symmetricEnergyIndex i)
  have iz : Integrable (fun θ => ‖z θ‖^2) angleMeasure :=
    component_integrable ε hε h hb hh m g κ t u (symmetricEnergyIndex i)
  have hf := averaged_complementaryDensity_integrable ε hε h hb hh m g κ t i u
  have hm : complementaryMass ε h i f = ENNReal.ofReal (complementaryMoment ε h i f) :=
    (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (complementaryWeight_nonnegative ε hε h i x) (sq_nonneg _)))).symm
  apply half_integral_of_mass z (complementaryMoment ε h i f)
    (complementaryMoment_nonnegative ε hε h i f) iz
    (fun θ => rotatedMass ε h hh (2*Real.pi*θ) i f)
    ((rotatedMass_angle ε hε h hh i f).trans hm)
  filter_upwards [orbit_lift_ae ε hε h hb hh m g κ t u] with θ hθ
  have hg := form_symmetric_graph ε hε h hb m g κ t i (L u θ)
  have hs := congrArg (fun v : Hilbert =>
    (((Real.sqrt (1/2):ℝ):ℂ) • v,z θ) ∈
      (clockMomentum ε h (symmetricDirection i)).graph) hθ
  exact rotatedMass_half_graph ε hε h hh (2*Real.pi*θ) i f (z θ) (hs.mp hg)

theorem averaged_static_energy (u : V) :
    ‖staticOutputLp (A u)‖^2 =
      (clockMoment ε (J u)+complementaryMoment ε h 0 (J u)+complementaryMoment ε h 1 (J u))/2 :=
  (static_compLp_energy E (L u)).trans
    (half_sum (averaged_clock_component ε hε h hb hh m g κ t u)
      (averaged_symmetric_component ε hε h hb hh m g κ t u 0)
      (averaged_symmetric_component ε hε h hb hh m g κ t u 1))

omit hb t in
theorem reference_static_energy (hs : |h| ≤ 2*Real.pi*ε/3)
    (u : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hs m g κ 0) :
    ‖KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hs m g κ u‖^2 =
      (clockMoment ε (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0 u)+
        complementaryMoment ε h 0 (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0 u)+
        complementaryMoment ε h 1 (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0 u))/2 := by
  let v := Classical.choose
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ 0 u)
  have hv := Classical.choose_spec
    (KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hs m g κ 0 u)
  have he := averaged_static_energy ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hs) hh m g κ 0 v
  have hJ := congrArg
    (KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hs m g κ 0) hv
  have hA := congrArg
    (fun z => ‖KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hs m g κ z‖^2) hv
  exact hA.symm.trans (he.trans (congrArg (fun f : Hilbert =>
    (clockMoment ε f+complementaryMoment ε h 0 f+complementaryMoment ε h 1 f)/2) hJ))

#print axioms averaged_clockMoment_integrable
#print axioms averaged_clock_component
#print axioms averaged_symmetric_component
#print axioms averaged_static_energy
#print axioms reference_static_energy
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticFormIdentity
