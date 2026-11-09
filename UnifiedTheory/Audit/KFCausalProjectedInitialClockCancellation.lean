/- Quarter-turn cancellation for arbitrary charge-invariant continuous
real functionals, including mixed initial pairings with complex clock
coefficients. No weighted energy comparison is assumed. -/
import UnifiedTheory.Audit.KFCausalProjectedStructuredShearSign
import UnifiedTheory.Audit.KFCausalInitialNormVacuumComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedInitialClockCancellation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (input shear initial_charge input_graph)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt meanShearAt angle_continuous)
open UnifiedTheory.Audit.KFCausalProjectedStructuredShearSign (mean_initial_fixed shear_period)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalWeightedQuarterShearCancellation (physical_outputs_cancel)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem initial_functional_zero (L : Hilbert →L[ℝ] ℝ)
    (hL : ∀ φ g, L (action h hh (-φ) g) = L g) :
    L (meanShearAt ε h hε hh hb S 0) = 0 := by
  let J : ℝ → Hilbert := fun θ => shear ε h hε hh hb S (2*Real.pi*θ) 0
  let f : ℝ → ℝ := fun θ => L (J θ)
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

theorem initial_cross_zero (A B : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ θ f, A (action h hh θ f) = action h hh θ (A f))
    (hB : ∀ θ f, B (action h hh θ f) = action h hh θ (B f)) :
    (inner ℂ (A (meanInputAt ε h hε hh hb S 0)) (B (meanShearAt ε h hε hh hb S 0))).re = 0 := by
  let F := meanInputAt ε h hε hh hb S 0
  let L : Hilbert →L[ℝ] ℝ := Complex.reCLM.comp (((innerSL ℂ (A F)).comp B).restrictScalars ℝ)
  apply initial_functional_zero ε h hε hh hb S L
  intro φ g
  change (inner ℂ (A F) (B (action h hh (-φ) g))).re = (inner ℂ (A F) (B g)).re
  rw [hB]
  have hf : action h hh (-φ) (A F) = A F := by
    rw [← hA,mean_initial_fixed]
  have he := (action h hh (-φ)).inner_map_map (A F) (B g)
  rw [hf] at he
  exact congrArg Complex.re he

theorem initial_clock_tangent_zero (W : Hilbert →L[ℂ] Hilbert)
    (hW : ∀ θ f, W (action h hh θ f) = action h hh θ (W f)) :
    (inner ℂ (W (meanInputAt ε h hε hh hb S 0))
      (coefficientOperator ε h hε hb hh (W (meanShearAt ε h hε hh hb S 0)))).re = 0 := by
  apply initial_cross_zero ε h hε hh hb S W ((coefficientOperator ε h hε hb hh).comp W) hW
  intro θ f
  change coefficientOperator ε h hε hb hh (W (action h hh θ f)) = _
  rw [hW,KFCausalInitialNormVacuumComparison.coefficient_charge]
  rfl

#print axioms initial_functional_zero
#print axioms initial_cross_zero
#print axioms initial_clock_tangent_zero
end
end UnifiedTheory.Audit.KFCausalProjectedInitialClockCancellation
