/- The actual charge-averaged ordered exponential controls the unweighted
initial interpolation norm, uniformly over finite complex superpositions.
The result does not assert the analogous field-weighted comparison. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearNormConvexity
import UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator
import UnifiedTheory.Audit.KFCausalCoherentVacuumShearSign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalInitialNormVacuumComparison
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_period)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action action_reverse)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoherentBridge (coherentSeed)
open UnifiedTheory.Audit.KFCausalImaginaryShearQuarterComparison (initial initialOutput initial_rotate initial_graph)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity (mixedSum mixedSum_smooth initial_coordinates)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient coefficient_bound coefficient_smooth)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "Cclock" => coefficientOperator ε h hε hb hh

omit a ha in
theorem coefficient_charge (θ : ℝ) (f : Hilbert) :
    Cclock (action h hh θ f) = action h hh θ (Cclock f) :=
  KFCausalBoundedClockCharge.multiplier_charge (coefficient ε h)
    (coefficient_smooth ε h hε hb).continuous.measurable (1/(2*ε)) (by positivity)
    (fun s => coefficient_bound ε h s hε hh hb) h hh θ f

variable {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
local notation "I₀" => initial ε a h hε ha hh hb k z
local notation "J₀" => initialOutput ε a h hε ha hh hb k z

def initialTangent (θ : ℝ) : ℝ := (inner ℂ (I₀ θ) (Cclock (J₀ θ))).re
def finalNorm (θ : ℝ) : ℝ := ‖∑ i, z i • shiftedOutput ε a h hε ha hh hb (parameter θ (k i))‖^2

theorem initial_norm (θ : ℝ) : ‖I₀ θ‖ = ‖I₀ 0‖ := by
  have he := initial_rotate ε a h hε ha hh hb k z 0 θ
  rw [zero_add] at he
  exact (congrArg norm he).symm.trans ((action h hh θ).norm_map _)

theorem initial_tangents_cancel (θ : ℝ) :
    initialTangent ε a h hε ha hh hb k z θ+
      initialTangent ε a h hε ha hh hb k z (θ+Real.pi/2)+
      initialTangent ε a h hε ha hh hb k z (θ+Real.pi)+
      initialTangent ε a h hε ha hh hb k z (θ+(-Real.pi/2)) = 0 := by
  have hg (φ : ℝ) : (action h hh φ (I₀ θ),J₀ (θ+φ)) ∈ (shearMomentum h).graph := by
    rw [initial_rotate]
    exact initial_graph ε a h hε ha hh hb k z (θ+φ)
  have hc := KFCausalWeightedQuarterShearCancellation.physical_outputs_cancel h hh (I₀ θ)
    (J₀ (θ+0)) (J₀ (θ+Real.pi/2)) (J₀ (θ+Real.pi)) (J₀ (θ+(-Real.pi/2)))
    (mixedSum ε a h (fun i => parameter θ (k i)) z)
    (initial_coordinates ε a h hε ha hh hb (fun i => parameter θ (k i)) z)
    ((mixedSum_smooth ε a h hε hb (fun i => parameter θ (k i)) z).differentiable (by norm_num))
    (hg 0) (hg (Real.pi/2)) (hg Real.pi) (hg (-Real.pi/2))
  have hr (φ : ℝ) : initialTangent ε a h hε ha hh hb k z (θ+φ) =
      (inner ℂ (I₀ θ) (Cclock (action h hh (-φ) (J₀ (θ+φ))))).re := by
    unfold initialTangent
    rw [← initial_rotate ε a h hε ha hh hb k z θ φ]
    have he := ((action h hh (-φ)).inner_map_map
      (action h hh φ (I₀ θ)) (Cclock (J₀ (θ+φ)))).symm
    rw [action_reverse,← coefficient_charge ε h hε hh hb] at he
    exact congrArg Complex.re he
  have h0 := hr 0
  rw [add_zero] at h0
  rw [h0,hr (Real.pi/2),hr Real.pi,hr (-Real.pi/2)]
  simp only [← Complex.add_re,← inner_add_right,← map_add]
  simpa only [add_zero,map_zero,inner_zero_right,Complex.zero_re] using
    congrArg (fun v : Hilbert => (inner ℂ (I₀ θ) (Cclock v)).re) hc

theorem endpoint_tangent (θ : ℝ) :
    ‖I₀ 0‖^2+2*initialTangent ε a h hε ha hh hb k z θ ≤
      finalNorm ε a h hε ha hh hb k z θ := by
  let seeds := fun i => coherentSeed a h ha hh (parameter θ (k i))
  let cs := fun i => z i*amplitudeConstant h (parameter θ (k i))
  have hm := KFCausalImaginaryShearNormConvexity.tangent_monotone Cclock (coefficient ε h)
    (coefficientOperator_coe ε h hε hb hh) h hh
    (KFCausalImaginaryShearSuperposition.sumInput ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.sumShear ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.sumSecond ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.input_continuous ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.shear_continuous ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.input_derivative ε h hε hb seeds cs hh)
    (KFCausalImaginaryShearSuperposition.shear_derivative ε h hε hb seeds cs hh)
    (KFCausalImaginaryShearSuperposition.input_graph ε h hε hb seeds cs hh)
    (KFCausalImaginaryShearSuperposition.shear_graph ε h hε hb seeds cs hh)
  have he := KFCausalImaginaryShearNormConvexity.initial_tangent_lower Cclock _ _
    (KFCausalImaginaryShearSuperposition.input_continuous ε h hε hb seeds cs)
    (KFCausalImaginaryShearSuperposition.input_derivative ε h hε hb seeds cs hh) hm
  change ‖I₀ θ‖^2+2*initialTangent ε a h hε ha hh hb k z θ ≤
    ‖KFCausalImaginaryShearCoherentBridge.input ε a h hε ha hh hb
      (fun i => parameter θ (k i)) z 1‖^2 at he
  rw [initial_norm,KFCausalImaginaryShearCoherentBridge.input_one] at he
  exact he

theorem final_four_lower (θ : ℝ) : 4*‖I₀ 0‖^2 ≤
    finalNorm ε a h hε ha hh hb k z θ+finalNorm ε a h hε ha hh hb k z (θ+Real.pi/2)+
      finalNorm ε a h hε ha hh hb k z (θ+Real.pi)+finalNorm ε a h hε ha hh hb k z (θ+(-Real.pi/2)) := by
  have h0 := endpoint_tangent ε a h hε ha hh hb k z θ
  have h1 := endpoint_tangent ε a h hε ha hh hb k z (θ+Real.pi/2)
  have h2 := endpoint_tangent ε a h hε ha hh hb k z (θ+Real.pi)
  have h3 := endpoint_tangent ε a h hε ha hh hb k z (θ+(-Real.pi/2))
  linarith [initial_tangents_cancel ε a h hε ha hh hb k z θ]

theorem finite_average_lower : ‖I₀ 0‖^2 ≤
    ∫ θ, finalNorm ε a h hε ha hh hb k z (2*Real.pi*θ) ∂angleMeasure := by
  have hc : Continuous (fun θ => finalNorm ε a h hε ha hh hb k z (2*Real.pi*θ)) :=
    (KFCausalCoherentVacuumShearSign.input_continuous ε a h hε ha hh hb k z).norm.pow 2
  have hn := KFCausalPeriodicFourTermAverage.nonnegative
    (fun θ => finalNorm ε a h hε ha hh hb k z (2*Real.pi*θ)-‖I₀ 0‖^2)
    (hc.sub continuous_const) (by
      intro θ
      simp only [mul_add,mul_one,finalNorm,parameter_period]) (1/4) (1/2) (-1/4) (by
        intro θ
        have he := final_four_lower ε a h hε ha hh hb k z (2*Real.pi*θ)
        dsimp only
        rw [show 2*Real.pi*(θ+1/4) = 2*Real.pi*θ+Real.pi/2 by ring,
          show 2*Real.pi*(θ+1/2) = 2*Real.pi*θ+Real.pi by ring,
          show 2*Real.pi*(θ+(-1/4)) = 2*Real.pi*θ+(-Real.pi/2) by ring]
        linarith)
  rw [integral_sub ((continuous_angle_memLp _ hc).integrable (by norm_num)) (integrable_const _)] at hn
  simpa only [integral_const,probReal_univ,one_smul,sub_nonneg] using hn

theorem actual_average_lower (f : coherentSpan ε a h hε ha hh) (g : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (f:Hilbert),g θ) ∈ (orderedExponential ε hε h).graph) :
    Continuous g ∧ Integrable (fun θ => ‖g θ‖^2) angleMeasure ∧
      ‖KFCausalCoherentMatterPathOperator.input ε a h hε ha hh hb 0 f‖^2 ≤
        ∫ θ, ‖g θ‖^2 ∂angleMeasure := by
  obtain ⟨n,k,z,hf⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f f.property
  have eg : g = KFCausalCoherentVacuumShearSign.orbitInput ε a h hε ha hh hb k z := by
    funext θ
    exact (orderedExponential ε hε h).mem_graph_snd_inj' (hg θ)
      (KFCausalCoherentVacuumShearSign.ordered_graph ε a h hε ha hh hb k z θ)
      (congrArg (action h hh (2*Real.pi*θ)) hf)
  have hc : Continuous g := eg.symm ▸ KFCausalCoherentVacuumShearSign.input_continuous ε a h hε ha hh hb k z
  refine ⟨hc,(continuous_angle_memLp _ (hc.norm.pow 2)).integrable (by norm_num),?_⟩
  rw [KFCausalCoherentMatterPathOperator.input_of_representation ε a h hε ha hh hb f k z hf,eg]
  have he := finite_average_lower ε a h hε ha hh hb k z
  simpa only [initial,UnifiedTheory.Audit.KFCausalChargeModulationFlow.parameter_zero] using he

#print axioms coefficient_charge
#print axioms initial_norm
#print axioms initial_tangents_cancel
#print axioms endpoint_tangent
#print axioms final_four_lower
#print axioms finite_average_lower
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalInitialNormVacuumComparison
