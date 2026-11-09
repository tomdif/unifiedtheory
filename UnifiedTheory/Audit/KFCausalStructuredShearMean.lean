/- The endpoint comparison for actual charge-projected structured states.
All source-orbit continuity and Bochner integrability are derived. -/
import UnifiedTheory.Audit.KFCausalStructuredShearInterpolation
import UnifiedTheory.Audit.KFCausalBoundedShearSourceContinuity
import UnifiedTheory.Audit.KFCausalShearEndpointMean
import UnifiedTheory.Audit.KFCausalProjectedKineticResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredShearMean
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (input shear seed amplitudeCoefficient)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (clockFrequency source)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
  (source_curve_continuous amplitude_curve_continuous source_orbit_bound clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (sumInput sumShear)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalShearEndpointMean (Endpoints endpoint gap)

private theorem actual_source_continuous (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (b : ℝ → Fin 5 → ℂ) (hc : Continuous b) (B : ℝ)
    (hB : ∀ θ, KFCausalClockFloorCoherentBounds.sourceSize (b θ) ≤ B) (t : Interval) :
    Continuous (fun θ => KFCausalActualImaginaryShearCurve.input ε a p h α β hε ha hα hβ hw hb (b θ) t) ∧
      Continuous (fun θ => KFCausalActualImaginaryShearCurve.shear ε a p h α β hε ha hα hβ hw hb (b θ) t) := by
  let A := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p (-h/2)
  let D := KFCausalImaginaryShearCoefficient.displacement ε h
  have hy := KFCausalImaginaryShearCoefficient.half_shift_bound ε h hb
  have hA := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p (-h/2) hε hy
  have hAm := KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha hy
  have hD := KFCausalImaginaryShearCoefficient.displacement_smooth ε h hε hb
  have hDb := KFCausalImaginaryShearPathDomain.displacement_strip_bound ε h hε hb
  exact ⟨KFCausalBoundedShearSourceContinuity.input_continuous A D hA hAm hD hDb α β hα hβ hw b hc B hB t,
    (KFCausalBoundedShearSourceContinuity.first_continuous A D hA hAm hD hDb α β hα hβ hw b hc B hB t).const_smul _⟩

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem angle_continuous (t : Interval) :
    Continuous (fun θ => input ε h hε hh hb S θ t) ∧
      Continuous (fun θ => shear ε h hε hh hb S θ t) := by
  have hp (i : Fin S.size) := source_orbit_bound h (S.packet i).centre (S.packet i).frequency
  have hc (i : Fin S.size) :
      Continuous (fun θ => (S.coefficient i)*amplitudeCoefficient ε h hε hh (S.packet i) θ) :=
    continuous_const.mul (continuous_const.mul
      (amplitude_curve_continuous h (S.packet i).centre (S.packet i).frequency))
  have hs (i : Fin S.size) := fun B hB => actual_source_continuous ε (S.packet i).width
    (clockFrequency h (S.packet i).frequency) h _ _ hε (S.packet i).width_pos
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hb
    (fun θ => source h (parameter θ (S.packet i).centre) (parameter θ (S.packet i).frequency))
    (source_curve_continuous h (S.packet i).centre (S.packet i).frequency) B hB t
  constructor
  · unfold input sumInput
    apply continuous_finset_sum
    intro i _
    obtain ⟨B,hB⟩ := hp i
    simp only [seed,clockFrequency_parameter]
    exact (hc i).smul (hs i B hB).1
  · unfold shear sumShear
    apply continuous_finset_sum
    intro i _
    obtain ⟨B,hB⟩ := hp i
    simp only [seed,clockFrequency_parameter]
    exact (hc i).smul (hs i B hB).2

def endpointValues (θ : ℝ) : Endpoints :=
  ((input ε h hε hh hb S θ 0,shear ε h hε hh hb S θ 0),
   (input ε h hε hh hb S θ 1,shear ε h hε hh hb S θ 1))

theorem endpoint_sum (θ : ℝ) : endpointValues ε h hε hh hb S θ =
    ∑ i, (S.coefficient i*amplitudeCoefficient ε h hε hh (S.packet i) θ) •
      endpoint ε h hε hb (seed h hh (S.packet i) θ) := by
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp only [endpointValues,endpoint,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
      input,shear,sumInput,sumShear]

theorem endpoint_continuous : Continuous (endpointValues ε h hε hh hb S) :=
  ((angle_continuous ε h hε hh hb S ⟨0,by constructor <;> norm_num⟩).1.prodMk
    (angle_continuous ε h hε hh hb S ⟨0,by constructor <;> norm_num⟩).2).prodMk
  ((angle_continuous ε h hε hh hb S ⟨1,by constructor <;> norm_num⟩).1.prodMk
    (angle_continuous ε h hε hh hb S ⟨1,by constructor <;> norm_num⟩).2)

def meanInputAt (t : ℝ) : Hilbert := ∫ θ, input ε h hε hh hb S (2*Real.pi*θ) t ∂angleMeasure
def meanShearAt (t : ℝ) : Hilbert := ∫ θ, shear ε h hε hh hb S (2*Real.pi*θ) t ∂angleMeasure

theorem mean_graph (t : Interval) : (meanInputAt ε h hε hh hb S t,meanShearAt ε h hε hh hb S t) ∈
    (KFCausalTransverseShearMomentum.shearMomentum h).graph :=
  KFCausalProjectedKineticResponse.integral_closed_graph _
    (KFCausalTransverseShearMomentum.shear_selfAdjoint h hh).isClosed _ _
    ((angle_continuous ε h hε hh hb S t).1.comp (continuous_const.mul continuous_id))
    ((angle_continuous ε h hε hh hb S t).2.comp (continuous_const.mul continuous_id))
    (fun θ => KFCausalStructuredShearInterpolation.input_graph ε h hε hh hb S (2*Real.pi*θ) t)

theorem mean_input_one : meanInputAt ε h hε hh hb S 1 =
    KFCausalStructuredProjectedHamiltonian.meanInput ε h hε hh hb S 7 := by
  unfold meanInputAt
  simp only [KFCausalStructuredShearInterpolation.input_one]
  rfl

theorem mean_endpoint_comparison (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    (inner ℂ (W (meanInputAt ε h hε hh hb S 0)) (W (meanShearAt ε h hε hh hb S 0))).re ≤
      (inner ℂ (W (meanInputAt ε h hε hh hb S 1)) (W (meanShearAt ε h hε hh hb S 1))).re := by
  have hi (t : Interval) : Integrable (fun θ => input ε h hε hh hb S (2*Real.pi*θ) t) angleMeasure := (continuous_angle_memLp _
    ((angle_continuous ε h hε hh hb S t).1.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hj (t : Interval) : Integrable (fun θ => shear ε h hε hh hb S (2*Real.pi*θ) t) angleMeasure := (continuous_angle_memLp _
    ((angle_continuous ε h hε hh hb S t).2.comp (continuous_const.mul continuous_id))).integrable (by norm_num)
  have hc : Continuous (fun θ => endpointValues ε h hε hh hb S (2*Real.pi*θ)) :=
    (endpoint_continuous ε h hε hh hb S).comp (continuous_const.mul continuous_id)
  have hm : ∀ θ, endpointValues ε h hε hh hb S (2*Real.pi*θ) ∈
      Submodule.span ℂ (Set.range (endpoint ε h hε hb)) := by
    intro θ
    rw [endpoint_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self _)))
  have he := KFCausalShearEndpointMean.mean_gap ε h hε hb hh W w hW _
    ((continuous_angle_memLp _ hc).integrable (by norm_num)) hm
  let zero : Interval := ⟨0,by constructor <;> norm_num⟩
  let one : Interval := ⟨1,by constructor <;> norm_num⟩
  have hmval : (∫ θ, endpointValues ε h hε hh hb S (2*Real.pi*θ) ∂angleMeasure) =
      ((meanInputAt ε h hε hh hb S 0,meanShearAt ε h hε hh hb S 0),
       (meanInputAt ε h hε hh hb S 1,meanShearAt ε h hε hh hb S 1)) := by
    unfold endpointValues
    rw [integral_pair ((hi zero).prodMk (hj zero)) ((hi one).prodMk (hj one)),
      integral_pair (hi zero) (hj zero),integral_pair (hi one) (hj one)]
    rfl
  rw [hmval] at he
  exact sub_nonneg.mp he

#print axioms angle_continuous
#print axioms endpoint_sum
#print axioms endpoint_continuous
#print axioms mean_graph
#print axioms mean_input_one
#print axioms mean_endpoint_comparison
end
end UnifiedTheory.Audit.KFCausalStructuredShearMean
