/- Continuity and norm bounds for chart phases on the actual output
space, sufficient for taking the zero-frequency limit of the dynamics. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem modulation_zero (ε : ℝ) (f : Hilbert) : modulation ε 0 f = f := by
  apply Lp.ext
  filter_upwards [modulation_coe ε 0 f] with x hx
  simpa only [phase,zero_mul,Real.fourierChar_apply,mul_zero,Complex.ofReal_zero,
    Complex.exp_zero,one_mul] using hx

theorem modulation_continuous (ε : ℝ) (f : Hilbert) : Continuous (fun r => modulation ε r f) := by
  let F := fun r x => phase ε r x*f x
  have hf (r : ℝ) : MemLp (F r) 2 volume := (Lp.memLp (modulation ε r f)).ae_eq (modulation_coe ε r f)
  have he : (fun r => (hf r).toLp (F r)) = fun r => modulation ε r f := by
    funext r
    exact Lp.ext ((hf r).coeFn_toLp.trans (modulation_coe ε r f).symm)
  rw [← he]
  apply KFCausalDominatedL2Continuity.continuous_toLp F hf f (Lp.memLp f)
  · intro r
    exact Eventually.of_forall (fun x => by simp only [F,norm_mul,phase_norm,one_mul,le_refl])
  · filter_upwards [] with x
    unfold F phase
    simp only [Real.fourierChar_apply]
    fun_prop

theorem phaseOutput_zero (ε : ℝ) (x : Output (Fin 8) Hilbert) : phaseOutput ε 0 x = x := by
  apply PiLp.ext
  intro i
  rw [phaseOutput_apply,modulation_zero]

theorem phaseOutput_continuous (ε : ℝ) (x : Output (Fin 8) Hilbert) :
    Continuous (fun r => phaseOutput ε r x) := by
  change Continuous (fun r => WithLp.toLp 2 (fun i => phaseOutput ε r x i))
  simp only [phaseOutput_apply]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => modulation_continuous ε (x i)))

theorem phaseOutput_norm (ε r : ℝ) (x : Output (Fin 8) Hilbert) : ‖phaseOutput ε r x‖ = ‖x‖ := by
  have he : ‖phaseOutput ε r x‖^2 = ‖x‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2,phaseOutput_apply,LinearIsometryEquiv.norm_map]
  nlinarith [norm_nonneg (phaseOutput ε r x),norm_nonneg x]

theorem phaseOutputLp_zero (ε : ℝ) (x : EnergyOutputSpace) : phaseOutputLp ε 0 x = x := by
  apply Lp.ext
  filter_upwards [(phaseOutput ε 0).coeFn_compLp x] with θ hθ
  exact hθ.trans (phaseOutput_zero ε (x θ))

theorem phaseOutputLp_norm (ε r : ℝ) (x : EnergyOutputSpace) : ‖phaseOutputLp ε r x‖ = ‖x‖ := by
  have he : (fun θ => ‖phaseOutputLp ε r x θ‖) =ᵐ[angleMeasure] fun θ => ‖x θ‖ := by
    filter_upwards [(phaseOutput ε r).coeFn_compLp x] with θ hθ
    exact (congrArg norm hθ).trans (phaseOutput_norm ε r (x θ))
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ hx => hx.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ hx => hx.ge)))

theorem lp_pairing_bound (ε r : ℝ) (x : EnergyOutputSpace) :
    ‖inner ℂ x (phaseOutputLp ε r x)‖ ≤ ‖x‖^2 := by
  simpa only [phaseOutputLp_norm,pow_two] using norm_inner_le_norm (𝕜 := ℂ) x (phaseOutputLp ε r x)

theorem lp_pairing_continuous (ε : ℝ) (x : EnergyOutputSpace) :
    Continuous (fun r => inner ℂ x (phaseOutputLp ε r x)) := by
  have he (r : ℝ) : inner ℂ x (phaseOutputLp ε r x) =
      ∫ θ, inner ℂ (x θ) (phaseOutput ε r (x θ)) ∂angleMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(phaseOutput ε r).coeFn_compLp x] with θ hθ
    exact congrArg (inner ℂ (x θ)) hθ
  simp only [he]
  apply continuous_of_dominated (bound := fun θ => ‖x θ‖^2)
  · intro r
    exact (Lp.aestronglyMeasurable x).inner
      ((phaseOutput ε r).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable x))
  · intro r
    exact Eventually.of_forall (fun θ => by
      simpa only [phaseOutput_norm,pow_two] using
        norm_inner_le_norm (𝕜 := ℂ) (x θ) (phaseOutput ε r (x θ)))
  · exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)
  · exact Eventually.of_forall (fun θ => continuous_const.inner (𝕜 := ℂ) (phaseOutput_continuous ε (x θ)))

#print axioms modulation_zero
#print axioms modulation_continuous
#print axioms phaseOutput_zero
#print axioms phaseOutput_continuous
#print axioms phaseOutput_norm
#print axioms phaseOutputLp_zero
#print axioms phaseOutputLp_norm
#print axioms lp_pairing_bound
#print axioms lp_pairing_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity
