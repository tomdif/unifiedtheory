/- Direct Haar coercivity can be proved on actual central slices of finite
Wilson cylinders and passed to the true ground law. The same constant
survives the fixed-cutoff temporal limit. A depth-uniform coercivity estimate
is an explicit remaining hypothesis, not supplied by this limit argument. -/
import UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum
import UnifiedTheory.Clay.YangMills.WilsonPhysicalHaarFrame
import UnifiedTheory.Clay.YangMills.WilsonDirectHaarBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderCoercivityLimit
noncomputable section
open MeasureTheory Filter WilsonTimeSlab WilsonSlabOperator WilsonInteriorVacuum
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHaarLinkResponse
open WilsonSymmetricLinkChange WilsonCylinderGluing WilsonFiniteCylinder
open scoped Topology

variable (n : ℕ) [NeZero n]

/-- Expectation on the actual central slice of a cylinder with j slices on each side. -/
def centralMean (β : ℝ) (j : ℕ) (F : C(Slice n, ℝ)) : ℝ :=
  correlation n β j 0 F 1

theorem centralMean_tendsto (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    Tendsto (fun j => centralMean n β j F) atTop
      (nhds (∫ u, F u ∂groundLaw n β hβ)) := by
  have h := correlation_tendsto n β hβ F 1 0
  rw [vacuumCorrelation_one_right] at h
  have he : groundMean n β hβ F = ∫ u, F u ∂groundLaw n β hβ :=
    (GroundStateDirichlet.stationary_integral (measure n)
      (WilsonGroundLocalComparison.ground n β hβ)
      (WilsonGroundLocalComparison.ground n β hβ).continuous F).symm
  rwa [he] at h

def centralVariance (β : ℝ) (j : ℕ) (F : C(Slice n, ℝ)) : ℝ :=
  centralMean n β j (F^2)-(centralMean n β j F)^2

/-- This is the variance under the original finite-cylinder probability law. -/
theorem centralVariance_eq (β : ℝ) (j : ℕ) (F : C(Slice n, ℝ)) :
    centralVariance n β j F = ProbabilityTheory.variance
      (fun z : Slices n Q (j+0+j) × TemporalLinks n Q (j+0+j) =>
        F (z.1 (mark (j+0) j)))
      (WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 (j+0+j)) := by
  letI : BorelSpace (Slices n Q (j+0+j) × TemporalLinks n Q (j+0+j)) :=
    WilsonFiniteCylinder.cylinderBorel (n := n) (G := Q) (j+0+j)
  let μ := WilsonFiniteCylinder.law (n := n) WilsonSingleLinkStaples.character β 2 (j+0+j)
  letI : IsProbabilityMeasure μ := WilsonFiniteCylinder.law_probability
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous β 2 _
  let f : C(Slices n Q (j+0+j) × TemporalLinks n Q (j+0+j), ℝ) :=
    ⟨fun z => F (z.1 (mark (j+0) j)), by fun_prop⟩
  have h := CompactLikelihoodVariance.variance_formula μ f f.continuous
  simpa only [centralVariance, centralMean, correlation, ContinuousMap.pow_apply,
    ContinuousMap.one_apply, mul_one, f, ContinuousMap.coe_mk, μ] using h.symm

theorem centralVariance_tendsto (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    Tendsto (fun j => centralVariance n β j F) atTop (nhds (variance n β hβ F)) := by
  have h := (centralMean_tendsto n β hβ (F^2)).sub
    ((centralMean_tendsto n β hβ F).pow 2)
  simpa only [centralVariance, variance_formula, ContinuousMap.pow_apply] using h

/-- The very same full-Haar energy observable used by the collective upper bound. -/
def haarObservable (F : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  ⟨fun u => ∑ e, ∫ q, (F (shift n e q u)-F u)^2 ∂RegulatedGauge.compactHaar Q,
    continuous_finset_sum _ (fun e _ => WilsonPhysicalHaarFrame.local_energy_continuous n e F)⟩

def centralEnergy (β : ℝ) (j : ℕ) (F : C(Slice n, ℝ)) : ℝ :=
  centralMean n β j (haarObservable n F)

theorem centralEnergy_tendsto (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    Tendsto (fun j => centralEnergy n β j F) atTop (nhds (totalEnergy n β hβ F)) := by
  have h := centralMean_tendsto n β hβ (haarObservable n F)
  rw [WilsonPhysicalHaarFrame.energy_integral]
  exact h

/-- A common finite-cylinder constant passes unchanged; no uniform convergence rate is assumed. -/
theorem coercivity_of_cylinders (β : ℝ) (hβ : 0 ≤ β) (A : ℝ)
    (hcoerce : ∀ j (F : C(Slice n, ℝ)), (∀ h U, F (gaugeSlice h U) = F U) →
      centralVariance n β j F ≤ A * centralEnergy n β j F)
    (F : C(Slice n, ℝ)) (hF : ∀ h U, F (gaugeSlice h U) = F U) :
    variance n β hβ F ≤ A*totalEnergy n β hβ F :=
  le_of_tendsto_of_tendsto (centralVariance_tendsto n β hβ F)
    ((centralEnergy_tendsto n β hβ F).const_mul A)
    (Eventually.of_forall (fun j => hcoerce j F hF))

/-- The lower estimate obtained this way matches the actual physical Haar family.
Both finite-cylinder coercivity and the collective upper estimate remain hypotheses. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hcoerce : ∀ j (F : C(Slice n, ℝ)), (∀ h U, F (gaugeSlice h U) = F U) →
      centralVariance n β j F ≤ A * centralEnergy n β j F)
    (hform : ∀ u (a : (SpatialVertex n × Fin 3) → C(Q, ℝ)),
      WilsonPhysicalHaarFrame.form n β hβ u a ≤
        κ * CompactHaarFrame.size (RegulatedGauge.compactHaar Q) a)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (A*κ/((k : ℝ)+A*κ))*variance n β hβ f :=
  WilsonDirectHaarBudget.slab_contraction n β hβ A κ hA hκ
    (coercivity_of_cylinders n β hβ A hcoerce)
    (fun F hF => WilsonPhysicalHaarFrame.energy_le_loss n β hβ κ hκ hform F hF)
    f hinv k hk

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderCoercivityLimit
