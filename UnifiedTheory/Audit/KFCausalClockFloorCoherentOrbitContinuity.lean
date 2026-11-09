/- Continuous physical L2 lifts along the charge-circle parameter orbit.
The actual clock-half output is continuous, using a uniform Gaussian
majorant rather than pointwise domain membership alone. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
import UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters
import UnifiedTheory.Audit.KFCausalDominatedL2Continuity
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates (displacement spectatorParameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCoherentParameters
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (sourceProfile_eq)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (physicalGaussian_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf clockHalf_graph halfWeight)

theorem physicalProfile_bound (C : ℂ) (p α β B : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hC : ‖C‖ ≤ 1) (hb : sourceSize b ≤ B)
    (x : Configuration) :
    ‖physicalProfile C p α β b g x‖ ≤
      Real.exp (B*positionConstant α β/2)*‖g x.1*physicalGaussian (α/2) (β/2) x.2‖ := by
  have hc : Real.exp (sourceConstant α β b/2) ≤ Real.exp (B*positionConstant α β/2) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (positionConstant_positive α β hα hβ).le) (by norm_num)
  have hp := (sourcedPacket_bound α β hα hβ hw b x.2).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  rw [physicalProfile,clockMultiplier,norm_mul,norm_mul,norm_mul,clockPhase_real_norm,mul_one]
  calc
    _ ≤ ‖g x.1‖*‖sourcedPacket α β b x.2‖ := by
      simpa only [one_mul,mul_assoc] using
        mul_le_mul_of_nonneg_right hC (mul_nonneg (norm_nonneg (g x.1)) (norm_nonneg (sourcedPacket α β b x.2)))
    _ ≤ ‖g x.1‖*(Real.exp (B*positionConstant α β/2)*‖physicalGaussian (α/2) (β/2) x.2‖) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := by rw [norm_mul]; ring

theorem physicalProfile_curve_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ =>
      (physicalProfile_memLp (C θ) (p θ) α β hα hβ hw (b θ) g hg).toLp
        (physicalProfile (C θ) (p θ) α β (b θ) g)) := by
  let G : Configuration → ℂ := fun x => (Real.exp (B*positionConstant α β/2):ℂ)*
    (g x.1*physicalGaussian (α/2) (β/2) x.2)
  have hG : MemLp G 2 volume :=
    (configuration_product_memLp _ _ hg (physicalGaussian_memLp _ _ (by positivity) (by positivity))).const_mul _
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _ G hG
  · intro θ
    filter_upwards [] with x
    simpa only [G,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      physicalProfile_bound (C θ) (p θ) α β B hα hβ hw (b θ) g (hC θ) (hb θ) x
  · filter_upwards [] with x
    unfold physicalProfile clockMultiplier sourcedPacket linearSource clockPhase
    fun_prop

theorem amplitudeConstant_continuous (hbar : ℝ) : Continuous (amplitudeConstant hbar) := by
  unfold amplitudeConstant constant displacement
  simp only [split_fst,KFCausalNormalizedChargeFlow.dilate]
  fun_prop

theorem clockFrequency_continuous : Continuous clockFrequency := by
  unfold clockFrequency frequency spectatorParameter
  simp only [split_snd]
  fun_prop

theorem sourceCoefficients_continuous (hbar : ℝ) : Continuous (sourceCoefficients hbar) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [sourceCoefficients,coefficients,displacement,spectatorParameter,
    split_fst,split_snd,KFCausalNormalizedChargeFlow.dilate] <;> fun_prop

def profileState (hbar : ℝ) (hh : hbar ≠ 0) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (k : Joint 2 4) : Hilbert :=
  (physicalProfile_memLp (amplitudeConstant hbar k) (clockFrequency k) (groundWidth hbar) (neutralWidth hbar)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
    (sourceCoefficients hbar k) g hg).toLp
      (physicalProfile (amplitudeConstant hbar k) (clockFrequency k) (groundWidth hbar) (neutralWidth hbar)
        (sourceCoefficients hbar k) g)

theorem profileState_orbit_continuous (hbar : ℝ) (hh : hbar ≠ 0) (g : ℝ → ℂ)
    (hg : MemLp g 2 volume) (k : Joint 2 4) :
    Continuous (fun θ => profileState hbar hh g hg (parameter θ k)) := by
  have hp : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  exact physicalProfile_curve_continuous _ _ (4*Real.pi^2*‖k‖^2)
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
    _ _ _ g hg ((amplitudeConstant_continuous hbar).comp hp) (clockFrequency_continuous.comp hp)
    ((sourceCoefficients_continuous hbar).comp hp) (fun θ => amplitudeConstant_bound hbar hh _)
    (fun θ => by rw [sourceCoefficients_parameter hbar hh]; exact sourceCoefficients_bound hbar hh k)

def clockOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) (k : Joint 2 4) : Hilbert :=
  profileState hbar hh (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha) k

theorem clockOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,clockOutput ε a hbar hε ha hh k) ∈
      (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [state_configuration_coe ε a hbar hε ha hh k,
    (physicalProfile_memLp (amplitudeConstant hbar k) (clockFrequency k) (groundWidth hbar) (neutralWidth hbar)
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
      (sourceCoefficients hbar k) (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)).coeFn_toLp]
    with x hx hy
  refine hy.trans ?_
  rw [hx,sourceProfile_eq]
  simp only [physicalProfile,clockMultiplier,halfClockFunction,halfWeight,
    amplitudeConstant,clockFrequency,sourceCoefficients]
  ring

theorem clockOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : Continuous (fun θ => clockOutput ε a hbar hε ha hh (parameter θ k)) :=
  profileState_orbit_continuous hbar hh _ _ k

theorem continuous_angle_memLp {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f) :
    MemLp f 2 KFCausalUnitIntervalOrbit.angleMeasure := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  exact ae_restrict_of_forall_mem measurableSet_Ioc (fun θ hθ => hC θ ⟨hθ.1.le,hθ.2⟩)

theorem clockOutput_orbit_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    MemLp (fun θ => clockOutput ε a hbar hε ha hh (parameter (2*Real.pi*θ) k)) 2
      KFCausalUnitIntervalOrbit.angleMeasure :=
  continuous_angle_memLp _ ((clockOutput_orbit_continuous ε a hbar hε ha hh k).comp
    (continuous_const.mul continuous_id))

theorem clockOutput_action_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (θ : ℝ) (k : Joint 2 4) :
    (KFCausalPhysicalCircleAction.action hbar hh θ (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k),
      clockOutput ε a hbar hε ha hh (parameter θ k)) ∈ (clockHalf ε).graph := by
  rw [KFCausalClockFloorCoherentStates.action_state]
  exact clockOutput_graph ε a hbar hε ha hh _

theorem clockOutput_energy_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    Integrable (fun θ => ‖clockOutput ε a hbar hε ha hh (parameter (2*Real.pi*θ) k)‖^2)
      KFCausalUnitIntervalOrbit.angleMeasure :=
  (memLp_two_iff_integrable_sq_norm (clockOutput_orbit_memLp ε a hbar hε ha hh k).aestronglyMeasurable).mp
    (clockOutput_orbit_memLp ε a hbar hε ha hh k)

#print axioms physicalProfile_bound
#print axioms physicalProfile_curve_continuous
#print axioms amplitudeConstant_continuous
#print axioms clockFrequency_continuous
#print axioms sourceCoefficients_continuous
#print axioms profileState_orbit_continuous
#print axioms clockOutput_graph
#print axioms clockOutput_orbit_continuous
#print axioms continuous_angle_memLp
#print axioms clockOutput_orbit_memLp
#print axioms clockOutput_action_graph
#print axioms clockOutput_energy_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
