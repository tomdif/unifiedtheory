/- Charge cancellation at the averaged initial endpoint, followed by the
actual endpoint comparison. This controls a weighted projected shear
pairing; identification with the full Hamiltonian response is separate. -/
import UnifiedTheory.Audit.KFCausalStructuredShearMean
import UnifiedTheory.Audit.KFCausalStructuredShearRegularity
import UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation
import UnifiedTheory.Audit.KFCausalPeriodicFourTermAverage

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedStructuredShearSign
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation
  (input shear initial_charge input_graph seed amplitudeCoefficient)
open UnifiedTheory.Audit.KFCausalStructuredShearMean
  (meanInputAt meanShearAt angle_continuous mean_endpoint_comparison)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroProjection action_zeroProjection)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation (pairing_reverse physical_outputs_cancel)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem mean_initial_projection : meanInputAt ε h hε hh hb S 0 =
    zeroProjection h hh (input ε h hε hh hb S 0 0) := by
  rw [← KFCausalProjectedKineticResponse.action_integral h hh]
  unfold meanInputAt
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    change input ε h hε hh hb S (2*Real.pi*θ) 0 = action h hh (2*Real.pi*θ) (input ε h hε hh hb S 0 0)
    rw [initial_charge,zero_add])

theorem mean_initial_fixed (φ : ℝ) : action h hh φ (meanInputAt ε h hε hh hb S 0) =
    meanInputAt ε h hε hh hb S 0 := by
  rw [mean_initial_projection,action_zeroProjection]

theorem shear_period (θ t : ℝ) : shear ε h hε hh hb S (θ+2*Real.pi) t =
    shear ε h hε hh hb S θ t := by
  simp only [shear,KFCausalImaginaryShearSuperposition.sumShear,seed,amplitudeCoefficient,
    KFCausalChargeModulationFlow.parameter_period]

theorem initial_weighted_zero (W : Hilbert →L[ℂ] Hilbert)
    (hW : ∀ θ f, W (action h hh θ f) = action h hh θ (W f)) :
    (inner ℂ (W (meanInputAt ε h hε hh hb S 0)) (W (meanShearAt ε h hε hh hb S 0))).re = 0 := by
  let F := meanInputAt ε h hε hh hb S 0
  let J : ℝ → Hilbert := fun θ => shear ε h hε hh hb S (2*Real.pi*θ) 0
  let L : Hilbert →L[ℝ] ℝ := Complex.reCLM.comp (((innerSL ℂ (W F)).comp W).restrictScalars ℝ)
  let f : ℝ → ℝ := fun θ => L (J θ)
  have hF (φ : ℝ) : action h hh φ F = F := mean_initial_fixed ε h hε hh hb S φ
  have hL (φ : ℝ) (g : Hilbert) : L (action h hh (-φ) g) = L g := by
    change (inner ℂ (W F) (W (action h hh (-φ) g))).re = (inner ℂ (W F) (W g)).re
    rw [← pairing_reverse h hh W hW,hF]
  have hJ : Continuous J := (angle_continuous ε h hε hh hb S ⟨0,by constructor <;> norm_num⟩).2.comp
    (continuous_const.mul continuous_id)
  have hc : Continuous f := L.continuous.comp hJ
  have hp : Function.Periodic f 1 := by
    intro θ
    dsimp [f,J]
    rw [show 2*Real.pi*(θ+1) = 2*Real.pi*θ+2*Real.pi by ring,shear_period]
  have hn (θ : ℝ) : f θ+f (θ+1/4)+f (θ+1/2)+f (θ+(-1/4)) = 0 := by
    obtain ⟨φ,hφ,hs⟩ := KFCausalStructuredShearRegularity.initial_structured_smooth ε h hε hh hb S (2*Real.pi*θ)
    have hg (d : ℝ) : (action h hh d (input ε h hε hh hb S (2*Real.pi*θ) 0),
        shear ε h hε hh hb S (2*Real.pi*θ+d) 0) ∈
        (KFCausalTransverseShearMomentum.shearMomentum h).graph := by
      rw [initial_charge]
      exact input_graph ε h hε hh hb S _ ⟨0,by constructor <;> norm_num⟩
    have he := physical_outputs_cancel h hh (input ε h hε hh hb S (2*Real.pi*θ) 0)
      _ _ _ _ φ hφ (hs.differentiable (by norm_num)) (hg 0) (hg (Real.pi/2)) (hg Real.pi) (hg (-Real.pi/2))
    have hel := congrArg L he
    simp only [map_add,map_zero,hL] at hel
    change L (shear ε h hε hh hb S (2*Real.pi*θ+0) 0)+
      L (shear ε h hε hh hb S (2*Real.pi*θ+Real.pi/2) 0)+
      L (shear ε h hε hh hb S (2*Real.pi*θ+Real.pi) 0)+
      L (shear ε h hε hh hb S (2*Real.pi*θ+-Real.pi/2) 0) = 0 at hel
    simpa only [f,J,add_zero,
      show 2*Real.pi*(θ+1/4) = 2*Real.pi*θ+Real.pi/2 by ring,
      show 2*Real.pi*(θ+1/2) = 2*Real.pi*θ+Real.pi by ring,
      show 2*Real.pi*(θ+(-1/4)) = 2*Real.pi*θ+-Real.pi/2 by ring] using hel
  have hpos := KFCausalPeriodicFourTermAverage.nonnegative f hc hp (1/4) (1/2) (-1/4)
    (fun θ => (hn θ).ge)
  have hneg := KFCausalPeriodicFourTermAverage.nonnegative (fun θ => -f θ) hc.neg
    (by intro θ; dsimp; rw [hp θ]) (1/4) (1/2) (-1/4) (fun θ => by have := hn θ; linarith)
  rw [integral_neg] at hneg
  have hz : (∫ θ, f θ ∂angleMeasure) = 0 := by linarith
  have hi : Integrable J angleMeasure := (continuous_angle_memLp _ hJ).integrable (by norm_num)
  rw [show (∫ θ, f θ ∂angleMeasure) = L (∫ θ, J θ ∂angleMeasure) from L.integral_comp_comm hi] at hz
  exact hz

theorem projected_weighted_nonnegative (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)
    (hC : ∀ θ f, W (action h hh θ f) = action h hh θ (W f)) :
    0 ≤ (inner ℂ (W (meanInputAt ε h hε hh hb S 1)) (W (meanShearAt ε h hε hh hb S 1))).re := by
  have he := mean_endpoint_comparison ε h hε hh hb S W w hW
  rw [initial_weighted_zero ε h hε hh hb S W hC] at he
  exact he

theorem projected_root_nonnegative :
    0 ≤ (inner ℂ
      (KFCausalClockFloorShearWeight.root ε hε h hb hh (meanInputAt ε h hε hh hb S 1))
      (KFCausalClockFloorShearWeight.root ε hε h hb hh (meanShearAt ε h hε hh hb S 1))).re :=
  projected_weighted_nonnegative ε h hε hh hb S _ (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh)
    (KFCausalWeightedQuarterShearCancellation.root_charge h hh ε hε hb)

#print axioms mean_initial_projection
#print axioms mean_initial_fixed
#print axioms shear_period
#print axioms initial_weighted_zero
#print axioms projected_weighted_nonnegative
#print axioms projected_root_nonnegative
end
end UnifiedTheory.Audit.KFCausalProjectedStructuredShearSign
