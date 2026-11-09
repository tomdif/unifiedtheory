/- The actual structured initial mean is fixed by physical reflection.
Source and amplitude identities are derived for a half-turn of the
original displaced packet orbit, including complex superpositions. -/
import UnifiedTheory.Audit.KFCausalInitialParityReflection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredInitialParity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint split_fst split_snd)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_compose parameter_period)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (dilate)
open UnifiedTheory.Audit.KFCausalInitialParityReflection (operator operator_coe sourceReflection reflection)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (seed amplitudeCoefficient input)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt angle_continuous)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

private theorem u_pi (h : ℝ) (q : Joint 2 4) : uParameter h (parameter Real.pi q) = -uParameter h q := by
  ext i
  fin_cases i <;> simp [uParameter,parameter,KFCausalPairedRotation.rotate,dilate,split_fst]

private theorem v_pi (h : ℝ) (q : Joint 2 4) : vParameter h (parameter Real.pi q) = -vParameter h q := by
  ext i
  fin_cases i <;> simp [vParameter,parameter,KFCausalPairedRotation.rotate,dilate,split_fst]

private theorem r_pi (h : ℝ) (q : Joint 2 4) (i : Fin 4) :
    rParameter h (parameter Real.pi q) i =
      if i=1 ∨ i=2 then -rParameter h q i else rParameter h q i := by
  fin_cases i <;> simp [rParameter,parameter,KFCausalPairedRotation.rotate,dilate,split_snd]

private theorem w_pi (h : ℝ) (q : Joint 2 4) (i : Fin 4) :
    wParameter h (parameter Real.pi q) i =
      if i=1 ∨ i=2 then -wParameter h q i else wParameter h q i := by
  fin_cases i <;> simp [wParameter,parameter,KFCausalPairedRotation.rotate,dilate,split_snd]

theorem source_pi (h : ℝ) (q k : Joint 2 4) :
    source h (parameter Real.pi q) (parameter Real.pi k) = sourceReflection (source h q k) := by
  funext i
  fin_cases i <;> simp [source,coefficients,u_pi,v_pi,r_pi,w_pi,sourceReflection] <;> ring

theorem amplitude_pi (h : ℝ) (q k : Joint 2 4) :
    amplitude h (parameter Real.pi q) (parameter Real.pi k) = amplitude h q k := by
  simp [amplitude,constant,u_pi,v_pi,w_pi,KFCausalFourierTranslation.phase,
    PiLp.inner_apply,Fin.sum_univ_succ]

private theorem periodic_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hp : Function.Periodic f 1) (d : ℝ) :
    (∫ θ, f (θ+d) ∂angleMeasure) = ∫ θ, f θ ∂angleMeasure := by
  change (∫ θ in Set.Ioc 0 1, f (θ+d)) = ∫ θ in Set.Ioc 0 1, f θ
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_comm 1 d] using hp.intervalIntegral_add_eq d 0

private theorem actual_input_coe (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (b : Fin 5 → ℂ) (t : KFCausalImaginaryShearPathDomain.Interval) :
    KFCausalActualImaginaryShearCurve.input ε a p h α β hε ha hα hβ hw hb b t =ᵐ[volume]
      KFCausalImaginaryShearInterpolation.actualPath ε a α β p h b t := by
  rw [KFCausalActualImaginaryShearCurve.input_eq_state ε a p h α β hε ha hα hβ hw hb b t]
  exact KFCausalImaginaryShearPathDomain.actualState_coe α β hα hβ hw b ε a p h hε ha hb t

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem orbit_reflection (θ : ℝ) : operator (input ε h hε hh hb S θ 0) =
    input ε h hε hh hb S (θ+Real.pi) 0 := by
  unfold input KFCausalImaginaryShearSuperposition.sumInput
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  have ha : amplitudeCoefficient ε h hε hh (S.packet k) (θ+Real.pi) =
      amplitudeCoefficient ε h hε hh (S.packet k) θ := by
    unfold amplitudeCoefficient
    rw [← parameter_compose,← parameter_compose,amplitude_pi]
  dsimp only
  rw [ha]
  congr 1
  apply Lp.ext
  let s := seed h hh (S.packet k) θ
  let t := seed h hh (S.packet k) (θ+Real.pi)
  have hs : t.b = sourceReflection s.b := by
    dsimp [s,t,seed]
    rw [← parameter_compose,← parameter_compose,source_pi]
  have hp : t.p = s.p := by
    dsimp [s,t,seed]
    rw [KFCausalClockFloorDisplacedParameterBounds.clockFrequency_parameter,
      KFCausalClockFloorDisplacedParameterBounds.clockFrequency_parameter]
  filter_upwards [operator_coe
      (KFCausalActualImaginaryShearCurve.input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 0),
    KFCausalInitialParityReflection.reflection_preserving.quasiMeasurePreserving.ae
      (actual_input_coe ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b
        ⟨0,by constructor <;> norm_num⟩),
    actual_input_coe ε t.a t.p h t.α t.β hε t.ha t.hα t.hβ t.hw hb t.b
      ⟨0,by constructor <;> norm_num⟩] with x hR hS hT
  change operator (KFCausalActualImaginaryShearCurve.input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 0) x = _ at hR
  change KFCausalActualImaginaryShearCurve.input ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b 0 (reflection x) = _ at hS
  change KFCausalActualImaginaryShearCurve.input ε t.a t.p h t.α t.β hε t.ha t.hα t.hβ t.hw hb t.b 0 x = _ at hT
  rw [hR,hS,hT]
  unfold KFCausalImaginaryShearInterpolation.actualPath
  rw [hp,hs]
  exact KFCausalInitialParityReflection.initial_profile _ _ _ _ _ x

theorem mean_initial_reflection : operator (meanInputAt ε h hε hh hb S 0) = meanInputAt ε h hε hh hb S 0 := by
  let f : ℝ → Hilbert := fun θ => input ε h hε hh hb S (2*Real.pi*θ) 0
  have hc : Continuous f := (angle_continuous ε h hε hh hb S ⟨0,by constructor <;> norm_num⟩).1.comp
    (continuous_const.mul continuous_id)
  have hi := (continuous_angle_memLp f hc).integrable (by norm_num)
  have hp : Function.Periodic f 1 := by
    intro θ
    dsimp [f]
    simp only [mul_add,mul_one,input,KFCausalImaginaryShearSuperposition.sumInput,
      seed,amplitudeCoefficient,parameter_period]
  change operator (∫ θ, f θ ∂angleMeasure) = ∫ θ, f θ ∂angleMeasure
  change operator.toContinuousLinearEquiv.toContinuousLinearMap (∫ θ, f θ ∂angleMeasure) = _
  rw [← operator.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi]
  calc
    _ = ∫ θ, f (θ+1/2) ∂angleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun θ => by
        change operator (input ε h hε hh hb S (2*Real.pi*θ) 0) = _
        rw [orbit_reflection]
        change input ε h hε hh hb S (2*Real.pi*θ+Real.pi) 0 =
          input ε h hε hh hb S (2*Real.pi*(θ+1/2)) 0
        congr 1
        ring)
    _ = _ := periodic_mean f hp (1/2)

theorem mean_initial_coe : (fun x => meanInputAt ε h hε hh hb S 0 (reflection x)) =ᵐ[volume]
    meanInputAt ε h hε hh hb S 0 := by
  have he := operator_coe (meanInputAt ε h hε hh hb S 0)
  rw [mean_initial_reflection] at he
  exact he.symm

#print axioms source_pi
#print axioms amplitude_pi
#print axioms orbit_reflection
#print axioms mean_initial_reflection
#print axioms mean_initial_coe
end
end UnifiedTheory.Audit.KFCausalStructuredInitialParity
