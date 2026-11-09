/- A physical charge-zero vector with all eight natural factor outputs
has an actual averaged energy-form lift. Its full energy and response
pairings retain exactly the physical factor weights. -/
import UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift
import UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift (lift lift_pairing)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (weighted_inner_im)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField

variable (f : Hilbert) (hf : f ∈ zeroSector h hh) (g : Fin 8 → Hilbert)
  (hg : ∀ i, (f,g i) ∈ (energyFactor ε hε h modelDirections pointField i).graph)

include hf hg in
theorem fixed_orbit_graph (θ : ℝ) (i : Fin 8) :
    (action h hh (2*Real.pi*θ) f,g i) ∈ (F i).graph := by
  have hfix : ∀ θ, action h hh θ f = f := hf
  rw [hfix]
  exact hg i

def fixedLift : Full :=
  lift ε h hε hh hb mass2 quartic vacuum t f (fun i _ => g i)
    (fun _ => continuous_const) (fixed_orbit_graph ε h hε hh f hf g hg)

theorem fixedLift_embedding :
    embed (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg) = f := rfl

include hf hg in
theorem fixedLift_energy_domain :
    f ∈ (energyOperator ε hε h hp hh mass2 quartic vacuum t).domain :=
  (energy_domain ε hε h hp hh mass2 quartic vacuum t f).mpr
    ⟨fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg,rfl⟩

theorem fixedLift_pairing (b : Hilbert) (hb₀ : b ∈ zeroSector h hh)
    (k : Fin 8 → Hilbert) (hk : ∀ i, (b,k i) ∈ (F i).graph) :
    inner ℂ (out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg))
      (out (fixedLift ε h hε hh hb mass2 quartic vacuum t b hb₀ k hk)) =
        ∑ i : Fin 8, inner ℂ (energyWeight mass2 quartic vacuum t i • g i)
          (energyWeight mass2 quartic vacuum t i • k i) := by
  simpa only [integral_const,probReal_univ,one_smul] using
    lift_pairing ε h hε hh hb mass2 quartic vacuum t f b
      (fun i _ => g i) (fun i _ => k i) (fun _ => continuous_const) (fun _ => continuous_const)
      (fixed_orbit_graph ε h hε hh f hf g hg) (fixed_orbit_graph ε h hε hh b hb₀ k hk)

theorem fixedLift_energy :
    ‖out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg)‖^2 =
      ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*‖g i‖^2 := by
  have he := congrArg Complex.re
    (fixedLift_pairing ε h hε hh hb mass2 quartic vacuum t f hf g hg f hf g hg)
  have hl : (inner ℂ (out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg))
      (out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg))).re =
      ‖out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg)‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hr (x : Hilbert) : (inner ℂ x x).re = ‖x‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Complex.re_sum,hl,hr,norm_smul,mul_pow] using he

theorem fixedLift_response (b : Hilbert) (hb₀ : b ∈ zeroSector h hh)
    (k : Fin 8 → Hilbert) (hk : ∀ i, (b,k i) ∈ (F i).graph) :
    (-2/h)*(inner ℂ (out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg))
      (out (fixedLift ε h hε hh hb mass2 quartic vacuum t b hb₀ k hk))).im =
        ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*((-2/h)*(inner ℂ (g i) (k i)).im) := by
  rw [fixedLift_pairing ε h hε hh hb mass2 quartic vacuum t f hf g hg b hb₀ k hk]
  simp only [Complex.im_sum,Finset.mul_sum,weighted_inner_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms fixed_orbit_graph
#print axioms fixedLift_embedding
#print axioms fixedLift_energy_domain
#print axioms fixedLift_pairing
#print axioms fixedLift_energy
#print axioms fixedLift_response
end
end UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
