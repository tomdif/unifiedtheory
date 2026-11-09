/- Exact charged kinetic moments on the ACTUAL growing-output closure.
The two retained factor graphs and nonnegative charge averaging derive
moment finiteness; no separate maximal-factor domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorAveragedChargedMoment

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialFormIdentity
noncomputable section
open MeasureTheory
open scoped ENNReal
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorOrbitVacuumGraph (physicalOrbit physicalOrbit_coe)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinateLp)
open KFCausalClockFloorGrowingOutputClosure
open KFCausalClockFloorOrbitFactorGraphs (factorOperator growingWeight)
open KFCausalClockFloorAntisymmetricGraph
open KFCausalClockFloorChargedMomentTonelli
open KFCausalClockFloorAveragedChargedMoment (chargedMoment chargedMoment_nonnegative)
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight chargedWeight_nonnegative)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalPhysicalCircleAction (action chargeCoordinates)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedEnergyGraph (l2_norm_square)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)

theorem kinetic_graph (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (operator ε hε h hh hb m g κ).graph) (i : Fin 2) :
    ∀ᵐ θ ∂angleMeasure,
      (((Real.sqrt (1/2):ℝ):ℂ) • action h hh (2*Real.pi*θ) f,
        coordinateLp (antiIndex i) y θ) ∈ (clockMomentum ε h (antiDirection i)).graph := by
  have hz : (f,y) ∈ (initialGraph ε hε h hh hb m g κ).topologicalClosure := by
    rwa [← operator_graph]
  have hc := closure_component ε hε h hh hb m g κ (f,y) hz (antiIndex i)
  have hi : ¬ (antiIndex i).val < 3 := by fin_cases i <;> decide
  have hw : growingWeight m g κ (antiIndex i)=((Real.sqrt (1/2):ℝ):ℂ) := by
    rw [growingWeight,if_neg hi,antiIndex_weight,Real.exp_zero,one_mul]
  rw [hw,factorOperator,KFCausalLpClosedOperator.operator_graph] at hc
  have ht := clockMomentum_closed ε hε h (antiDirection i)
  have he := ht.isClosable.graph_closure_eq_closure_graph.symm.trans
    ht.submodule_topologicalClosure_eq
  filter_upwards [hc,physicalOrbit_coe h hh (((Real.sqrt (1/2):ℝ):ℂ) • f)] with θ hθ hθ'
  change (physicalOrbit h hh (((Real.sqrt (1/2):ℝ):ℂ) • f) θ,
    coordinateLp (antiIndex i) y θ) ∈
      (KFCausalClockFloorCommonDomain.energyFactor ε hε h
        KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField
          (antiIndex i)).closure.graph at hθ
  rw [antiIndex_factor,he,hθ',map_smul] at hθ
  exact hθ

theorem kinetic_mass (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (operator ε hε h hh hb m g κ).graph) (i : Fin 2) :
    ENNReal.ofReal (1/2)*chargedMass ε h i f =
      ENNReal.ofReal (‖coordinateLp (antiIndex i) y‖^2) := by
  let z := coordinateLp (antiIndex i) y
  have hp := kinetic_graph ε hε h hh hb m g κ f y hy i
  have he : (fun θ => ENNReal.ofReal (1/2)*
      kineticMass ε h i (action h hh (2*Real.pi*θ) f)) =ᵐ[angleMeasure]
        fun θ => ENNReal.ofReal (‖z θ‖^2) := by
    filter_upwards [hp] with θ hθ
    have hg := kineticMass_graph ε hε h hh i _ (z θ) hθ
    rw [kineticMass_smul,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)] at hg
    exact hg
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable z)).mp (Lp.memLp z)
  calc
    _ = ENNReal.ofReal (1/2)*(∫⁻ θ,
        kineticMass ε h i (action h hh (2*Real.pi*θ) f) ∂angleMeasure) :=
      congrArg (fun q : ℝ≥0∞ => ENNReal.ofReal (1/2)*q)
        (kineticMass_angle ε hε h hh i f).symm
    _ = ∫⁻ θ, ENNReal.ofReal (1/2)*
        kineticMass ε h i (action h hh (2*Real.pi*θ) f) ∂angleMeasure :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ θ, ENNReal.ofReal (‖z θ‖^2) ∂angleMeasure := lintegral_congr_ae he
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),← l2_norm_square]

theorem charged_integrable (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (operator ε hε h hh hb m g κ).graph) (i : Fin 2) :
    Integrable (fun x => chargedWeight ε h i x*‖(chargeCoordinates f) x‖^2) := by
  apply (chargedDensity_integrable_iff ε hε h i f).mpr
  have ht : ENNReal.ofReal (1/2)*chargedMass ε h i f ≠ ⊤ := by
    rw [kinetic_mass ε hε h hh hb m g κ f y hy i]
    exact ENNReal.ofReal_ne_top
  intro hm
  simp [hm] at ht

theorem kinetic_energy (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (operator ε hε h hh hb m g κ).graph) (i : Fin 2) :
    (1/2)*chargedMoment ε h i f = ‖coordinateLp (antiIndex i) y‖^2 := by
  have hi := charged_integrable ε hε h hh hb m g κ f y hy i
  have hm : chargedMass ε h i f=ENNReal.ofReal (chargedMoment ε h i f) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
      (fun x => mul_nonneg (chargedWeight_nonnegative ε hε h i x) (sq_nonneg _)))).symm
  have he := kinetic_mass ε hε h hh hb m g κ f y hy i
  rw [hm,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)] at he
  exact (ENNReal.ofReal_eq_ofReal_iff
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (chargedMoment_nonnegative ε hε h i f))
    (sq_nonneg _)).mp he

#print axioms kinetic_graph
#print axioms kinetic_mass
#print axioms charged_integrable
#print axioms kinetic_energy
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialFormIdentity
