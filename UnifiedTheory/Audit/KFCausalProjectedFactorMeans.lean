/- Coordinates of the actual projected eight-factor energy output.
Bochner means commute with bounded coordinate projections. This derives
all weighted factor means from the existing form lifts and gives their
full energy and signed-response decompositions. -/
import UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedFactorMeans
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalCoherentMomentumEnergyLift
  (weightedOutput weightedOutput_continuous lift lift_output_coe)
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean (mean mean_integral const_norm)
open UnifiedTheory.Audit.KFCausalZeroChargeStructuredResponse (output project projected_output projected_pairing)
open UnifiedTheory.Audit.KFCausalFullMomentumRateDecomposition (weighted_inner_im)

theorem weighted_integral (mass2 quartic vacuum t : ℝ) (g : Fin 8 → ℝ → Hilbert)
    (hc : ∀ i, Continuous (g i)) :
    (∫ θ, weightedOutput mass2 quartic vacuum t g θ ∂angleMeasure) =
      WithLp.toLp 2 (fun i : Fin 8 => energyWeight mass2 quartic vacuum t i • ∫ θ, g i θ ∂angleMeasure) := by
  have hi := (continuous_angle_memLp _ (weightedOutput_continuous mass2 quartic vacuum t g hc)).integrable
    (by norm_num)
  apply PiLp.ext
  intro i
  let L : Output (Fin 8) Hilbert →L[ℂ] Hilbert := PiLp.proj 2 (fun _ : Fin 8 => Hilbert) i
  change L (∫ θ, weightedOutput mass2 quartic vacuum t g θ ∂angleMeasure) = _
  rw [← L.integral_comp_comm hi]
  change (∫ θ, energyWeight mass2 quartic vacuum t i • g i θ ∂angleMeasure) = _
  exact integral_smul _ _

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "out" => output ε h hε hh hb mass2 quartic vacuum t
local notation "P" => project ε h hε hh hb mass2 quartic vacuum t

variable (f b : Hilbert) (g k : Fin 8 → ℝ → Hilbert)
  (hc : ∀ i, Continuous (g i)) (hd : ∀ i, Continuous (k i))
  (hg : ∀ θ i, (action h hh (2*Real.pi*θ) f,g i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
  (hk : ∀ θ i, (action h hh (2*Real.pi*θ) b,k i θ) ∈ (energyFactor ε hε h modelDirections pointField i).graph)
local notation "u" => lift ε h hε hh hb mass2 quartic vacuum t f g hc hg
local notation "v" => lift ε h hε hh hb mass2 quartic vacuum t b k hd hk

include hg in
theorem lift_mean_output : mean angleMeasure (out u) =
    WithLp.toLp 2 (fun i : Fin 8 => energyWeight mass2 quartic vacuum t i • ∫ θ, g i θ ∂angleMeasure) := by
  exact (mean_integral angleMeasure (out u)).trans
    ((integral_congr_ae (lift_output_coe ε h hε hh hb mass2 quartic vacuum t f g hc hg)).trans
      (weighted_integral mass2 quartic vacuum t g hc))

include hg hk in
theorem projected_lift_pairing : inner ℂ (out (P u)) (out (P v)) =
    ∑ i : Fin 8, inner ℂ
      (energyWeight mass2 quartic vacuum t i • ∫ θ, g i θ ∂angleMeasure)
      (energyWeight mass2 quartic vacuum t i • ∫ θ, k i θ ∂angleMeasure) := by
  exact (projected_pairing ε h hε hh hb mass2 quartic vacuum t u v).trans
    ((congrArg₂ (inner ℂ)
      (lift_mean_output ε h hε hh hb mass2 quartic vacuum t f g hc hg)
      (lift_mean_output ε h hε hh hb mass2 quartic vacuum t b k hd hk)).trans (PiLp.inner_apply _ _))

include hg in
theorem projected_lift_energy : ‖out (P u)‖^2 =
    ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*‖∫ θ, g i θ ∂angleMeasure‖^2 := by
  have he := (projected_output ε h hε hh hb mass2 quartic vacuum t u).trans
    (congrArg (Lp.const 2 angleMeasure)
      (lift_mean_output ε h hε hh hb mass2 quartic vacuum t f g hc hg))
  refine (congrArg (fun z => ‖z‖^2) he).trans ?_
  refine (congrArg (fun r : ℝ => r^2) (const_norm angleMeasure _)).trans ?_
  exact (PiLp.norm_sq_eq_of_L2 _ _).trans (by simp only [norm_smul,mul_pow])

include hg hk in
theorem projected_lift_response : (-2/h)*(inner ℂ (out (P u)) (out (P v))).im =
    ∑ i : Fin 8, ‖energyWeight mass2 quartic vacuum t i‖^2*
      ((-2/h)*(inner ℂ (∫ θ, g i θ ∂angleMeasure) (∫ θ, k i θ ∂angleMeasure)).im) := by
  refine (congrArg (fun z : ℂ => (-2/h)*z.im)
    (projected_lift_pairing ε h hε hh hb mass2 quartic vacuum t f b g k hc hd hg hk)).trans ?_
  simp only [Complex.im_sum,Finset.mul_sum,weighted_inner_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms weighted_integral
#print axioms lift_mean_output
#print axioms projected_lift_pairing
#print axioms projected_lift_energy
#print axioms projected_lift_response
end
end UnifiedTheory.Audit.KFCausalProjectedFactorMeans
