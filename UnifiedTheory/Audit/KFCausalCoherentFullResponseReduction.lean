/- The full signed energy-form response is reduced to its two actual
ordered matter rates, a bounded clock loss and nonnegative kinetic/vacuum
terms. All outputs and form lifts exist on the coherent span. This is a
fixed-time form identity, not an Ehrenfest identity along evolution. -/
import UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate physical_decomposition)
open UnifiedTheory.Audit.KFCausalCoherentFactorResponseBounds
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

def fullRate (mass2 quartic vacuum t h : ℝ) (g k : Fin 8 → ℝ → Hilbert) : ℝ :=
  (rate h g k 0+rate h g k 1+rate h g k 2)/2+
    Real.exp (2*t)*((rate h g k 3+rate h g k 4)/2+
      mass2/2*rate h g k 5+quartic/4*rate h g k 6+vacuum*rate h g k 7)

def matterResidual (mass2 quartic t h : ℝ) (g k : Fin 8 → ℝ → Hilbert) : ℝ :=
  Real.exp (2*t)*(mass2/2*rate h g k 5+quartic/4*rate h g k 6)

theorem lower_bound (mass2 quartic vacuum t h : ℝ) (f : Hilbert) (g k : Fin 8 → ℝ → Hilbert)
    (hv : 0 ≤ vacuum) (hClock : -‖f‖^2 ≤ rate h g k 0)
    (hKin : ∀ i : Fin 4, 0 ≤ rate h g k (kineticIndex i)) (hVac : 0 ≤ rate h g k 7) :
    matterResidual mass2 quartic t h g k-‖f‖^2/2 ≤ fullRate mass2 quartic vacuum t h g k := by
  have h1 : 0 ≤ rate h g k 1 := hKin 0
  have h2 : 0 ≤ rate h g k 2 := hKin 1
  have h3 : 0 ≤ rate h g k 3 := hKin 2
  have h4 : 0 ≤ rate h g k 4 := hKin 3
  have hp := mul_nonneg (Real.exp_pos (2*t)).le
    (add_nonneg (div_nonneg (add_nonneg h3 h4) (by norm_num : (0:ℝ) ≤ 2)) (mul_nonneg hv hVac))
  have he : fullRate mass2 quartic vacuum t h g k-matterResidual mass2 quartic t h g k =
      (rate h g k 0+rate h g k 1+rate h g k 2)/2+
        Real.exp (2*t)*((rate h g k 3+rate h g k 4)/2+vacuum*rate h g k 7) := by
    unfold fullRate matterResidual
    ring
  linarith

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

theorem actual_response (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (b : Hilbert) (hB : (f,b) ∈ (pureMomentum ε hε h).graph)
    (u v : Full) (hu : embed u = f) (hv : embed v = b) :
    ∃ g k : Fin 8 → ℝ → Hilbert,
      (∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (-‖f‖^2 ≤ rate h g k 0 ∧ rate h g k 0 ≤ 0) ∧
      (∀ i : Fin 4, 0 ≤ rate h g k (kineticIndex i)) ∧
      0 ≤ rate h g k 7 ∧
      (-2/h)*(inner ℂ (out u) (out v)).im = fullRate mass2 quartic vacuum t h g k ∧
      matterResidual mass2 quartic t h g k-‖f‖^2/2 ≤ (-2/h)*(inner ℂ (out u) (out v)).im := by
  exact (KFCausalCoherentFullMomentumPairing.actual_pairing ε h hε hh hb mass2 quartic vacuum t
    a ha f hf b hB u v hu hv).elim fun g hx => hx.elim fun k hx => by
      have hc := clock_bounds ε h hε hh f b g k hB hx.1 a ha hf (hx.2.1 0).1 (hx.2.1 0).2
      have hkin (i : Fin 4) : 0 ≤ rate h g k (kineticIndex i) :=
        (kinetic_bounds ε h hε hh f b g k hB hx.1 i (hx.2.1 _).1 (hx.2.1 _).2).1
      have hvac' := vacuum_nonneg ε h hε hh hb f b g k hB hx.1 a ha hf
      have he : (-2/h)*(inner ℂ (out u) (out v)).im = fullRate mass2 quartic vacuum t h g k :=
        hx.2.2.2.2.2.trans (physical_decomposition mass2 quartic vacuum t h hm hq hvac g k
          (fun i => (hx.2.1 i).1) (fun i => (hx.2.1 i).2))
      exact ⟨g,k,hx.1,hx.2.1,hc,hkin,hvac',he,
        (lower_bound mass2 quartic vacuum t h f g k hvac hc.1 hkin hvac').trans_eq he.symm⟩

theorem exists_actual_reduction (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (u v : Full) (g k : Fin 8 → ℝ → Hilbert),
      (f,b) ∈ (pureMomentum ε hε h).graph ∧ embed u = f ∧ embed v = b ∧
      (∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (-2/h)*(inner ℂ (out u) (out v)).im = fullRate mass2 quartic vacuum t h g k ∧
      matterResidual mass2 quartic t h g k-‖f‖^2/2 ≤ (-2/h)*(inner ℂ (out u) (out v)).im := by
  exact (KFCausalCoherentMomentumEnergyLift.coherent_momentum_lifts ε h hε hh hb mass2 quartic vacuum t
    a ha f hf).elim fun b hx => hx.elim fun u hx => hx.elim fun v hx =>
      (actual_response ε h hε hh hb mass2 quartic vacuum t hm hq hvac a ha f hf b hx.1 u v hx.2.1 hx.2.2).elim
        fun g hy => hy.elim fun k hy =>
          ⟨b,u,v,g,k,hx.1,hx.2.1,hx.2.2,hy.1,hy.2.1,hy.2.2.2.2.2.1,hy.2.2.2.2.2.2⟩

#print axioms lower_bound
#print axioms actual_response
#print axioms exists_actual_reduction
end
end UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction
