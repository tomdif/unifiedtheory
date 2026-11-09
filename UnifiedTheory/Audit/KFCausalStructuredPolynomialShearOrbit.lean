/- Physical field powers and their shear commutators on every structured
path. Joint angle/path continuity is derived for the actual displaced
orbits, including independent widths and all complex amplitudes. -/
import UnifiedTheory.Audit.KFCausalBoundedPolynomialShearContinuity
import UnifiedTheory.Audit.KFCausalStructuredShearMean
import UnifiedTheory.Audit.KFCausalFieldShearInterpolationEstimate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (seed amplitudeCoefficient input shear)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (clockFrequency source)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
  (source_curve_continuous amplitude_curve_continuous source_orbit_bound clockFrequency_parameter)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs (state firstState)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)

private theorem actual_joint_continuous (P : Weight) (ε a p h α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (b : ℝ → Fin 5 → ℂ) (hc : Continuous b) (B : ℝ)
    (hB : ∀ θ, KFCausalClockFloorCoherentBounds.sourceSize (b θ) ≤ B) :
    Continuous (fun v : ℝ × Interval =>
      KFCausalActualPolynomialShearCurve.input P ε a p h α β hε ha hα hβ hw hb (b v.1) v.2) ∧
    Continuous (fun v : ℝ × Interval =>
      KFCausalActualPolynomialShearCurve.weightedFirst P ε a p h α β hε ha hα hβ hw hb (b v.1) v.2) := by
  let A := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p (-h/2)
  let D := KFCausalImaginaryShearCoefficient.displacement ε h
  have hy := KFCausalImaginaryShearCoefficient.half_shift_bound ε h hb
  have hA := KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε a p (-h/2) hε hy
  have hAm := KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha hy
  have hD := KFCausalImaginaryShearCoefficient.displacement_smooth ε h hε hb
  have hDb := KFCausalImaginaryShearPathDomain.displacement_strip_bound ε h hε hb
  exact ⟨KFCausalBoundedPolynomialShearContinuity.input_continuous P A D hA hAm hD hDb α β hα hβ hw b hc B hB,
    (KFCausalBoundedPolynomialShearContinuity.first_continuous P A D hA hAm hD hDb α β hα hβ hw b hc B hB).const_smul _⟩

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

def weightedInput (P : Weight) (θ t : ℝ) : Hilbert :=
  ∑ k, (S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) θ) •
    state ε h hε hb (seed h hh (S.packet k) θ) P t

def weightedFirst (P : Weight) (θ t : ℝ) : Hilbert :=
  ∑ k, (S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) θ) •
    firstState ε h hε hb (seed h hh (S.packet k) θ) P t

theorem weighted_continuous (P : Weight) :
    Continuous (fun v : ℝ × Interval => weightedInput ε h hε hh hb S P v.1 v.2) ∧
    Continuous (fun v : ℝ × Interval => weightedFirst ε h hε hh hb S P v.1 v.2) := by
  have hc (k : Fin S.size) : Continuous (fun v : ℝ × Interval =>
      S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) v.1) :=
    continuous_const.mul (continuous_const.mul
      ((amplitude_curve_continuous h (S.packet k).centre (S.packet k).frequency).comp continuous_fst))
  have hs (k : Fin S.size) := fun B hB => actual_joint_continuous P ε (S.packet k).width
    (clockFrequency h (S.packet k).frequency) h _ _ hε (S.packet k).width_pos
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hb
    (fun θ => source h (parameter θ (S.packet k).centre) (parameter θ (S.packet k).frequency))
    (source_curve_continuous h (S.packet k).centre (S.packet k).frequency) B hB
  constructor
  · unfold weightedInput state
    apply continuous_finset_sum
    intro k _
    obtain ⟨B,hB⟩ := source_orbit_bound h (S.packet k).centre (S.packet k).frequency
    simp only [seed,clockFrequency_parameter]
    exact (hc k).smul (hs k B hB).1
  · unfold weightedFirst firstState
    apply continuous_finset_sum
    intro k _
    obtain ⟨B,hB⟩ := source_orbit_bound h (S.packet k).centre (S.packet k).frequency
    simp only [seed,clockFrequency_parameter]
    exact (hc k).smul (hs k B hB).2

theorem angle_continuous (P : Weight) (t : Interval) :
    Continuous (fun θ => weightedInput ε h hε hh hb S P θ t) ∧
    Continuous (fun θ => weightedFirst ε h hε hh hb S P θ t) := by
  have hc : Continuous (fun θ : ℝ => (θ,t)) := continuous_id.prodMk continuous_const
  have hi := (weighted_continuous ε h hε hh hb S P).1.comp hc
  have hj := (weighted_continuous ε h hε hh hb S P).2.comp hc
  constructor
  · simpa only [Function.comp_def] using hi
  · simpa only [Function.comp_def] using hj

theorem real_multiplier_graph (P : Weight)
    (r : KFCausalCoupledLongitudinalFlow.Configuration → ℝ) (hr : Measurable r)
    (hP : ∀ x, P.value x = (r x:ℂ)) (θ : ℝ) (t : Interval) :
    (input ε h hε hh hb S θ t,weightedInput ε h hε hh hb S P θ t) ∈
      (KFCausalUnitaryRealMultiplier.realPullback (LinearIsometryEquiv.refl ℂ Hilbert) r hr).graph := by
  let T := KFCausalUnitaryRealMultiplier.realPullback (LinearIsometryEquiv.refl ℂ Hilbert) r hr
  have hg (k : Fin S.size) :
      (KFCausalActualImaginaryShearCurve.input ε (seed h hh (S.packet k) θ).a (seed h hh (S.packet k) θ).p
        h (seed h hh (S.packet k) θ).α (seed h hh (S.packet k) θ).β hε
        (seed h hh (S.packet k) θ).ha (seed h hh (S.packet k) θ).hα (seed h hh (S.packet k) θ).hβ
        (seed h hh (S.packet k) θ).hw hb (seed h hh (S.packet k) θ).b t,
        state ε h hε hb (seed h hh (S.packet k) θ) P t) ∈ T.graph := by
    apply (KFCausalUnitaryRealMultiplier.realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert) r hr _ _).mpr
    filter_upwards [KFCausalFieldShearPathGraphs.base_coe ε h hε hb (seed h hh (S.packet k) θ) t,
      KFCausalActualPolynomialShearCurve.input_coe P ε (seed h hh (S.packet k) θ).a (seed h hh (S.packet k) θ).p
        h (seed h hh (S.packet k) θ).α (seed h hh (S.packet k) θ).β hε
        (seed h hh (S.packet k) θ).ha (seed h hh (S.packet k) θ).hα (seed h hh (S.packet k) θ).hβ
        (seed h hh (S.packet k) θ).hw hb (seed h hh (S.packet k) θ).b t] with x hx hy
    change state ε h hε hb (seed h hh (S.packet k) θ) P t x = _ at hy
    change state ε h hε hb (seed h hh (S.packet k) θ) P t x = _
    simp only [LinearIsometryEquiv.coe_refl,id_eq]
    rw [hy,hx,hP]
  have hs := T.graph.sum_mem
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin S.size))) =>
      T.graph.smul_mem (S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) θ) (hg k))
  simpa only [input,KFCausalImaginaryShearSuperposition.sumInput,weightedInput,Prod.smul_mk,← prod_mk_sum] using hs

theorem field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (θ : ℝ) (t : Interval) :
    (input ε h hε hh hb S θ t,weightedInput ε h hε hh hb S (fieldWeight l i) θ t) ∈
      (fieldPower l i).graph :=
  KFCausalFieldShearInterpolationEstimate.field_graph_sum ε h hε hb l i _ _ t

theorem first_field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (θ : ℝ) (t : Interval) :
    (shear ε h hε hh hb S θ t,weightedFirst ε h hε hh hb S (fieldWeight l i) θ t) ∈
      (fieldPower l i).graph := by
  have hs := (fieldPower l i).graph.sum_mem
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin S.size))) =>
      (fieldPower l i).graph.smul_mem (S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) θ)
        (KFCausalFieldShearPathGraphs.first_field_graph ε h hε hb (seed h hh (S.packet k) θ) l i t))
  simpa only [shear,KFCausalImaginaryShearSuperposition.sumShear,weightedFirst,
    Prod.smul_mk,← prod_mk_sum] using hs

theorem corrected_shear_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (θ : ℝ) (t : Interval) :
    (weightedInput ε h hε hh hb S (fieldWeight l i) θ t,
      weightedFirst ε h hε hh hb S (fieldWeight l i) θ t+
        (-Complex.I*(h:ℂ)) • weightedInput ε h hε hh hb S (slopeWeight l i) θ t) ∈
      (KFCausalTransverseShearMomentum.shearMomentum h).graph := by
  have hs := KFCausalFieldShearInterpolationEstimate.shear_graph_sum ε h hε hb l i
    (fun k => seed h hh (S.packet k) θ)
    (fun k => S.coefficient k*amplitudeCoefficient ε h hε hh (S.packet k) θ) hh t
  rw [KFCausalFieldShearInterpolationEstimate.shear_identity] at hs
  exact hs

#print axioms weighted_continuous
#print axioms angle_continuous
#print axioms real_multiplier_graph
#print axioms field_graph
#print axioms first_field_graph
#print axioms corrected_shear_graph
end
end UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit
