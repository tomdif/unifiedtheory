/- Actual matter and full energy-form response bounds with no initial
shear derivative. The sharper bound keeps the positive final weighted
norm; the simpler bound uses only the initial transported norm and the
terminal derivative moment. Energy control of these costs remains open. -/
import UnifiedTheory.Audit.KFCausalNormMatterAverage
import UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNormMatterResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage (matterIndex factor_matter)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockSecantMultiplier (operator)
open UnifiedTheory.Audit.KFCausalMatterScalarAbsorption (coefficient)
open UnifiedTheory.Audit.KFCausalMatterAbsorptionWeight (moment)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalNormMatterAverage (cost weightedCost)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "S" => coherentSpan ε a h hε ha hh
local notation "W" => root ε hε h hb hh
local notation "M" => operator ε h hε hb hh

def sharpLower (f : S) (g : Fin 8 → ℝ → Hilbert) (d : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  (2/ε^2)*((∫ θ, ‖M (g (matterIndex i) θ)‖^2 ∂angleMeasure)-
    weightedCost ε a h hε ha hh hb pointField i f)-
      coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure)

def normLower (f : S) (d : Fin 2 → ℝ → Hilbert) (i : Fin 2) : ℝ :=
  -(1/(2*ε))*cost ε a h hε ha hh hb pointField i f-
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure)

theorem actual_average_lower (f : S) (b : Hilbert)
    (hB : ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph)
    (g k : Fin 8 → ℝ → Hilbert)
    (hOut : ∀ θ i,
      (action h hh (2*Real.pi*θ) (f:Hilbert),g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph ∧
      (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
    (hc : ∀ i, Continuous (g i) ∧ Continuous (k i)) :
    ∃ d : Fin 2 → ℝ → Hilbert,
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, sharpLower ε a h hε ha hh hb f g d i ≤ rate h g k (matterIndex i) ∧
        normLower ε a h hε ha hh hb f d i ≤ rate h g k (matterIndex i)) := by
  obtain ⟨q,j,d,hq,hj,hd,hrep,hk,hMI,hr,habs,hlower⟩ :=
    KFCausalActualMatterAbsorbedLower.actual_average_lower ε hε h hb hh a ha f f.property b hB g k hOut hc
  have hg (θ : ℝ) : (action h hh (2*Real.pi*θ) (f:Hilbert),g 7 θ) ∈
      (orderedExponential ε hε h).graph := (hOut θ 7).1
  have hF (θ : ℝ) (i : Fin 2) : (g 7 θ,g (matterIndex i) θ) ∈ (fieldPower pointField i).graph := by
    have hM := (hOut θ (matterIndex i)).1
    rw [factor_matter] at hM
    obtain ⟨g',ht,hF'⟩ := (composition_graph _ _ _ _).mp hM
    have eg : g' = g 7 θ := (orderedExponential ε hε h).mem_graph_snd_inj' ht (hg θ) rfl
    exact eg ▸ hF'
  refine ⟨d,hd,hrep,hMI,?_⟩
  intro i
  have hiS := (KFCausalNormMatterAverage.actual_average_secant ε a h hε ha hh hb pointField i f
    (g 7) (g (matterIndex i)) (fun θ => j i θ+(-Complex.I*(h:ℂ)) • d i θ)
    hg (fun θ => hF θ i) (fun θ => hk θ i)).2
  have hiN := KFCausalNormMatterAverage.actual_average_norm_lower ε a h hε ha hh hb pointField i f
    (g 7) (g (matterIndex i)) (fun θ => j i θ+(-Complex.I*(h:ℂ)) • d i θ)
    hg (fun θ => hF θ i) (fun θ => hk θ i)
  let Q := ∫ θ, (inner ℂ (W (g (matterIndex i) θ))
    (W (j i θ+(-Complex.I*(h:ℂ)) • d i θ))).re ∂angleMeasure
  have hs : (2/ε^2)*((∫ θ, ‖M (g (matterIndex i) θ)‖^2 ∂angleMeasure)-
      weightedCost ε a h hε ha hh hb pointField i f) ≤ (4/ε^2)*Q := by
    convert mul_le_mul_of_nonneg_left hiS (by positivity : 0 ≤ 4/ε^2) using 1
    ring
  have hn : -(1/(2*ε))*cost ε a h hε ha hh hb pointField i f ≤ (4/ε^2)*Q := by
    convert mul_le_mul_of_nonneg_left hiN (by positivity : 0 ≤ 4/ε^2) using 1
    field_simp
    ring
  have hl := hlower i
  change (∫ θ, (4/ε^2)*(inner ℂ (W (g (matterIndex i) θ))
      (W (j i θ+(-Complex.I*(h:ℂ)) • d i θ))).re ∂angleMeasure)-
    coefficient ε h*(∫ θ, moment ε hε (d i θ) ∂angleMeasure) ≤ rate h g k (matterIndex i) at hl
  rw [integral_const_mul] at hl
  exact ⟨(sub_le_sub_right hs _).trans hl,(sub_le_sub_right hn _).trans hl⟩

variable (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

theorem exists_full_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum) (f : S) :
    ∃ (b : Hilbert) (u v : Full) (g k : Fin 8 → ℝ → Hilbert) (d : Fin 2 → ℝ → Hilbert),
      ((f:Hilbert),b) ∈ (pureMomentum ε hε h).graph ∧ embed u = (f:Hilbert) ∧ embed v = b ∧
      (∀ θ i, (action h hh (2*Real.pi*θ) (f:Hilbert),g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (∀ i, Continuous (d i)) ∧
      (∀ θ i, d i θ =ᵐ[volume] fun x => powerSlope pointField i x*g 7 θ x) ∧
      (∀ i, Integrable (fun θ => moment ε hε (d i θ)) angleMeasure) ∧
      (∀ i, sharpLower ε a h hε ha hh hb f g d i ≤ rate h g k (matterIndex i) ∧
        normLower ε a h hε ha hh hb f d i ≤ rate h g k (matterIndex i)) ∧
      (-2/h)*(inner ℂ (out u) (out v)).im =
        KFCausalCoherentFullResponseReduction.fullRate mass2 quartic vacuum t h g k ∧
      Real.exp (2*t)*(mass2/2*sharpLower ε a h hε ha hh hb f g d 0+
        quartic/4*sharpLower ε a h hε ha hh hb f g d 1)-‖(f:Hilbert)‖^2/2 ≤
        (-2/h)*(inner ℂ (out u) (out v)).im ∧
      Real.exp (2*t)*(mass2/2*normLower ε a h hε ha hh hb f d 0+
        quartic/4*normLower ε a h hε ha hh hb f d 1)-‖(f:Hilbert)‖^2/2 ≤
        (-2/h)*(inner ℂ (out u) (out v)).im := by
  exact (KFCausalCoherentFullResponseReduction.exists_actual_reduction ε h hε hh hb
    mass2 quartic vacuum t hm hq hvac a ha f f.property).elim fun b hx =>
    hx.elim fun u hx => hx.elim fun v hx => hx.elim fun g hx => hx.elim fun k hx =>
      (actual_average_lower ε a h hε ha hh hb f b hx.1 g k hx.2.2.2.1 hx.2.2.2.2.1).elim fun d hy => by
        have hLift (L : Fin 2 → ℝ) (hL : ∀ i, L i ≤ rate h g k (matterIndex i)) :
            Real.exp (2*t)*(mass2/2*L 0+quartic/4*L 1)-‖(f:Hilbert)‖^2/2 ≤
              (-2/h)*(inner ℂ (out u) (out v)).im := by
          have h5 : L 0 ≤ rate h g k 5 := hL 0
          have h6 : L 1 ≤ rate h g k 6 := hL 1
          have hm' := mul_le_mul_of_nonneg_left h5 (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2))
          have hq' := mul_le_mul_of_nonneg_left h6 (div_nonneg hq (by norm_num : (0:ℝ) ≤ 4))
          have hs := mul_le_mul_of_nonneg_left (add_le_add hm' hq') (Real.exp_pos (2*t)).le
          exact (sub_le_sub_right hs (‖(f:Hilbert)‖^2/2)).trans hx.2.2.2.2.2.2
        exact ⟨b,u,v,g,k,d,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hy.1,hy.2.1,hy.2.2.1,
          hy.2.2.2,hx.2.2.2.2.2.1,
          hLift _ (fun i => (hy.2.2.2 i).1),hLift _ (fun i => (hy.2.2.2 i).2)⟩

#print axioms actual_average_lower
#print axioms exists_full_bound
end
end UnifiedTheory.Audit.KFCausalNormMatterResponse
