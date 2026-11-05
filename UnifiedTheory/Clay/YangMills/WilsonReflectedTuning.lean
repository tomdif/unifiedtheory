/- Actual finite Wilson centered reflected forms are continuous in the Wilson
coefficient. Intermediate-value tuning exposes its endpoint bracket; no
physical ultraviolet bracket, renormalization prescription, or limit is supplied. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import UnifiedTheory.Clay.YangMills.ReflectedDefectBound
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonReflectedTuning
noncomputable section
open MeasureTheory Filter ContinuumControl RegulatedGauge PeriodicLattice4
open PeriodicTimeReflection ReflectedWilsonRenormalization WilsonSmearedObservable
open scoped Topology

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem action_joint_continuous (χ : G → ℂ) (hcχ : Continuous χ) (offset : ℝ) :
    Continuous (fun z : ℝ × RegulatedGauge.Configuration (Vertex N) G =>
      orientedWilsonAction (Vertex N) G χ (base N) (loops N) z.1 offset z.2) := by
  have h := continuous_fst.mul
    ((continuous_orientedWilsonAction (Vertex N) G χ hcχ (base N) (loops N) 1 offset).comp
      continuous_snd)
  simpa only [Pi.mul_apply, Function.comp_def, orientedWilsonAction, wilsonAction, one_mul] using h

theorem wilsonLaw_eq_compactGibbs (χ : G → ℂ) (hcχ : Continuous χ) (beta offset : ℝ) :
    wilsonLaw N G χ beta offset = CompactGibbsContinuity.law
      (referenceMeasure G (Vertex N))
      (orientedWilsonAction (Vertex N) G χ (base N) (loops N) beta offset) :=
  GibbsCoordinateTransport.gibbs_eq_weightedLaw (Vertex N) G _
    (continuous_orientedWilsonAction (Vertex N) G χ hcχ (base N) (loops N) beta offset)

/-- The observable may itself depend jointly on the action coefficient and links. -/
theorem wilson_expectation_continuous (χ : G → ℂ) (hcχ : Continuous χ) (offset : ℝ)
    (F : ℝ → RegulatedGauge.Configuration (Vertex N) G → ℂ)
    (hF : Continuous F.uncurry) :
    Continuous (fun beta => ∫ U, F beta U ∂wilsonLaw N G χ beta offset) := by
  simpa only [wilsonLaw_eq_compactGibbs G N χ hcχ] using
    CompactGibbsContinuity.expectation_continuous (referenceMeasure G (Vertex N))
      (fun beta U => orientedWilsonAction (Vertex N) G χ (base N) (loops N) beta offset U)
      (action_joint_continuous G N χ hcχ offset) F hF

theorem mean_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (offset : ℝ)
    (f : CorrelationTest 1) :
    Continuous (fun beta => ∫ U, observable G N a plane χ 1 f U
      ∂wilsonLaw N G actionCharacter beta offset) :=
  wilson_expectation_continuous G N actionCharacter haction offset _
    ((observable_continuous G N a plane χ hcχ 1 f).comp continuous_snd)

theorem centered_joint_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (actionCharacter : G → ℂ)
    (haction : Continuous actionCharacter) (offset : ℝ) (f : CorrelationTest 1) :
    Continuous (fun z : ℝ × RegulatedGauge.Configuration (Vertex N) G =>
      centered G N a plane χ actionCharacter z.1 offset f z.2) :=
  ((observable_continuous G N a plane χ hcχ 1 f).comp continuous_snd).sub
    ((mean_continuous G N a plane χ hcχ actionCharacter haction offset f).comp continuous_fst)

/-- Finite-cutoff continuity includes both beta-dependent subtracted means.
It needs no assumed reflection invariance or positivity. -/
theorem reflectedForm_continuous (a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (actionCharacter : G → ℂ)
    (haction : Continuous actionCharacter) (offset : ℝ) (f g : CorrelationTest 1) :
    Continuous (fun beta => reflectedForm G N a plane χ actionCharacter beta offset f g) := by
  apply wilson_expectation_continuous G N actionCharacter haction offset
  exact ((centered_joint_continuous G N a plane χ hcχ actionCharacter haction offset f).comp
    (continuous_fst.prodMk ((ReflectedDefectBound.continuous_reflection G N).comp
      continuous_snd))).star.mul
    (centered_joint_continuous G N a plane χ hcχ actionCharacter haction offset g)

/-- `scale` is prescribed independently; this definition does not choose it by
forcing a desired variance. It may encode a separately justified normalization. -/
def dimensionlessCoupling (L a : ℝ) (plane : Plane) (χ actionCharacter : G → ℂ)
    (offset : ℝ) (f : CorrelationTest 1) (scale : ℝ → ℂ) (beta : ℝ) : ℝ :=
  L^8 * ‖scale beta‖^2 *
    (reflectedForm G N a plane χ actionCharacter beta offset f f).re

theorem dimensionlessCoupling_continuous (L a : ℝ) (plane : Plane)
    (χ : G → ℂ) (hcχ : Continuous χ) (actionCharacter : G → ℂ)
    (haction : Continuous actionCharacter) (offset : ℝ) (f : CorrelationTest 1)
    (scale : ℝ → ℂ) (hscale : Continuous scale) :
    Continuous (dimensionlessCoupling G N L a plane χ actionCharacter offset f scale) :=
  (continuous_const.mul (hscale.norm.pow 2)).mul
    (Complex.continuous_re.comp
      (reflectedForm_continuous G N a plane χ hcχ actionCharacter haction offset f f))

/-- The endpoint bracket is an explicit input; neither monotonicity nor the
physical existence of a bracket is claimed. -/
theorem exists_tuned_coefficient (L a : ℝ) (plane : Plane) (χ : G → ℂ)
    (hcχ : Continuous χ) (actionCharacter : G → ℂ) (haction : Continuous actionCharacter)
    (offset : ℝ) (f : CorrelationTest 1) (scale : ℝ → ℂ) (hscale : Continuous scale)
    (lo hi target : ℝ) (horder : lo ≤ hi)
    (hbracket : target ∈ Set.uIcc
      (dimensionlessCoupling G N L a plane χ actionCharacter offset f scale lo)
      (dimensionlessCoupling G N L a plane χ actionCharacter offset f scale hi)) :
    ∃ beta ∈ Set.Icc lo hi,
      dimensionlessCoupling G N L a plane χ actionCharacter offset f scale beta = target := by
  have h := intermediate_value_uIcc
    (dimensionlessCoupling_continuous G N L a plane χ hcχ actionCharacter haction
      offset f scale hscale).continuousOn hbracket
  simpa only [Set.uIcc_of_le horder, Set.mem_image] using h

/-- Selecting coefficients between supplied brackets preserves divergence of
the lower endpoint. The bracket is retained for every regulator. -/
theorem bracket_trajectory (u : ℕ → ℝ → ℝ) (hc : ∀ k, Continuous (u k))
    (lo hi : ℕ → ℝ) (target : ℝ) (horder : ∀ k, lo k ≤ hi k)
    (hbracket : ∀ k, target ∈ Set.uIcc (u k (lo k)) (u k (hi k)))
    (hlo : Tendsto lo atTop atTop) :
    ∃ beta : ℕ → ℝ, (∀ k, beta k ∈ Set.Icc (lo k) (hi k)) ∧
      (∀ k, u k (beta k) = target) ∧ Tendsto beta atTop atTop := by
  have hex (k : ℕ) : ∃ b ∈ Set.Icc (lo k) (hi k), u k b = target := by
    have h := intermediate_value_uIcc (hc k).continuousOn (hbracket k)
    simpa only [Set.uIcc_of_le (horder k), Set.mem_image] using h
  choose beta hb he using hex
  exact ⟨beta, hb, he, tendsto_atTop_mono (fun k => (hb k).1) hlo⟩

/-- Actual Wilson realization of the bracket-selection theorem, for varying
periods, mesh sizes, fixed tests and independently prescribed scales. -/
theorem wilson_bracket_trajectory (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (L a : ℕ → ℝ) (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (actionCharacter : G → ℂ) (haction : Continuous actionCharacter) (offset : ℝ)
    (f : CorrelationTest 1) (scale : ℕ → ℝ → ℂ) (hscale : ∀ k, Continuous (scale k))
    (lo hi : ℕ → ℝ) (target : ℝ) (horder : ∀ k, lo k ≤ hi k)
    (hbracket : ∀ k, target ∈ Set.uIcc
      (dimensionlessCoupling G (period k) (L k) (a k) plane χ actionCharacter offset f (scale k) (lo k))
      (dimensionlessCoupling G (period k) (L k) (a k) plane χ actionCharacter offset f (scale k) (hi k)))
    (hlo : Tendsto lo atTop atTop) :
    ∃ beta : ℕ → ℝ, (∀ k, beta k ∈ Set.Icc (lo k) (hi k)) ∧
      (∀ k, dimensionlessCoupling G (period k) (L k) (a k) plane χ actionCharacter
        offset f (scale k) (beta k) = target) ∧ Tendsto beta atTop atTop :=
  bracket_trajectory _ (fun k => dimensionlessCoupling_continuous G (period k) (L k) (a k)
    plane χ hcχ actionCharacter haction offset f (scale k) (hscale k))
    lo hi target horder hbracket hlo

end
end UnifiedTheory.Clay.YangMills.WilsonReflectedTuning
