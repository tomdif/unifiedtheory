/- The full actual energy-form response is bounded below by its signed
field-weighted shear contribution and the known clock loss. All matter
compositions and scalar integrals are derived on the coherent span.
The remaining shear estimate is not assumed to follow from energy. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFullMatterShearReduction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalCoherentMatterResponseAverage
open UnifiedTheory.Audit.KFCausalCoherentFullResponseReduction (matterResidual)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (rate)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic t : ℝ)

def matterLongitudinal (g : Fin 8 → ℝ → Hilbert) : ℝ := Real.exp (2*t)*
  (mass2/2*longitudinalMean ε h hε hb g 0+quartic/4*longitudinalMean ε h hε hb g 1)

def matterShear (g : Fin 8 → ℝ → Hilbert) (j : Fin 2 → ℝ → Hilbert) : ℝ := Real.exp (2*t)*
  (mass2/2*shearMean ε h hε hb g j 0+quartic/4*shearMean ε h hε hb g j 1)

variable (hh : h ≠ 0) (vacuum : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

theorem exists_full_matter_bound (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hvac : 0 ≤ vacuum)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (b : Hilbert) (u v : Full) (g k : Fin 8 → ℝ → Hilbert)
      (q : ℝ → Hilbert) (j : Fin 2 → ℝ → Hilbert),
      (f,b) ∈ (pureMomentum ε hε h).graph ∧ embed u = f ∧ embed v = b ∧
      (∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (F i).graph ∧
        (action h hh (2*Real.pi*θ) b,k i θ) ∈ (F i).graph) ∧
      (∀ i, Continuous (g i) ∧ Continuous (k i)) ∧
      (∀ θ, (g 7 θ,q θ) ∈ (shearMomentum h).graph) ∧
      (∀ θ i, (q θ,j i θ) ∈ (fieldPower pointField i).graph) ∧
      (∀ i, Continuous (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) ∧
        Integrable (fun θ => shearRate ε h hε hb (g (matterIndex i) θ) (j i θ)) angleMeasure) ∧
      matterResidual mass2 quartic t h g k =
        matterLongitudinal ε h hε hb mass2 quartic t g-matterShear ε h hε hb mass2 quartic t g j ∧
      0 ≤ matterLongitudinal ε h hε hb mass2 quartic t g ∧
      -matterShear ε h hε hb mass2 quartic t g j-‖f‖^2/2 ≤ (-2/h)*(inner ℂ (out u) (out v)).im := by
  exact (KFCausalCoherentMomentumEnergyLift.coherent_momentum_lifts ε h hε hh hb mass2 quartic vacuum t
    a ha f hf).elim fun b hz => hz.elim fun u hz => hz.elim fun v hz =>
      (KFCausalCoherentFullResponseReduction.actual_response ε h hε hh hb mass2 quartic vacuum t
        hm hq hvac a ha f hf b hz.1 u v hz.2.1 hz.2.2).elim fun g hx => hx.elim fun k hx =>
          (actual_split ε h hε hb hh a ha f hf b hz.1 g k hx.1 hx.2.1).elim fun q hy => hy.elim fun j hy => by
            have h5 : rate h g k 5 = longitudinalMean ε h hε hb g 0-shearMean ε h hε hb g j 0 :=
              hy.2.2.2.2.2.1 0
            have h6 : rate h g k 6 = longitudinalMean ε h hε hb g 1-shearMean ε h hε hb g j 1 :=
              hy.2.2.2.2.2.1 1
            have hM : matterResidual mass2 quartic t h g k =
                matterLongitudinal ε h hε hb mass2 quartic t g-matterShear ε h hε hb mass2 quartic t g j := by
              unfold matterResidual matterLongitudinal matterShear
              rw [h5,h6]
              ring
            have hL : 0 ≤ matterLongitudinal ε h hε hb mass2 quartic t g :=
              mul_nonneg (Real.exp_pos _).le (add_nonneg
                (mul_nonneg (div_nonneg hm (by norm_num)) (hy.2.2.2.2.2.2 0))
                (mul_nonneg (div_nonneg hq (by norm_num)) (hy.2.2.2.2.2.2 1)))
            have hLower : -matterShear ε h hε hb mass2 quartic t g j-‖f‖^2/2 ≤
                matterResidual mass2 quartic t h g k-‖f‖^2/2 := by linarith
            exact ⟨b,u,v,g,k,q,j,hz.1,hz.2.1,hz.2.2,hx.1,hx.2.1,hy.1,hy.2.1,
              fun i => ⟨hy.2.2.1 i,hy.2.2.2.1 i⟩,hM,hL,hLower.trans hx.2.2.2.2.2.2⟩

#print axioms exists_full_matter_bound
end
end UnifiedTheory.Audit.KFCausalFullMatterShearReduction
