/- Averaging the complete link-rotation assignment converts the finite-family
bound to the matching full-Haar energy with no channel-count factor. This
binds both remaining estimates to actual finite Wilson cylinders. Their
depth- and spatially uniform numerical bounds are still not proved. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryMixedLimit
import UnifiedTheory.Clay.YangMills.WilsonCylinderCoercivityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryHaarContraction
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPhysicalVariance
open WilsonVarianceResponse WilsonHaarLinkResponse WilsonBoundaryMixedLimit
open WilsonCylinderCoercivityLimit CompactDensityEntropy

variable (n : ℕ) [NeZero n]

/-- Product Haar on complete rotation assignments has the required one-link marginals. -/
theorem energy_average (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ rotations : Slice n, WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1) f
      ∂measure n) = totalEnergy n β hβ f := by
  simp only [WilsonCollectiveGram.energy, one_pow, one_mul, id_eq, totalEnergy]
  have hi (e : SpatialVertex n × Fin 3) :
      Integrable (fun rotations : Slice n => responseEnergy n β hβ e (rotations e) f)
        (measure n) := continuous_integrable (measure n) _
      ((responseEnergy_continuous n β hβ e f).comp (continuous_apply e))
  rw [integral_finset_sum _ (fun e _ => hi e)]
  apply Finset.sum_congr rfl
  intro e _
  have hp := measurePreserving_eval
    (fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q) e
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable
    (responseEnergy_continuous n β hβ e f).aestronglyMeasurable]
  rfl

/-- The upper estimate controls all Haar rotations, with no factor for the number of links. -/
theorem totalEnergy_le_loss (β : ℝ) (hβ : 0 ≤ β) (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hcap : ∀ q : Q, coefficient β q ≤ D)
    (hboundary : ∀ j (rotations : Slice n) u e, boundaryFar n β j rotations u e ≤ R)
    (f : C(Slice n, ℝ)) :
    totalEnergy n β hβ (step n β hβ f) ≤ (16*D+R)*loss n β hβ f := by
  rw [← energy_average]
  have hc : Continuous (fun rotations : Slice n =>
      WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1) (step n β hβ f)) := by
    simp only [WilsonCollectiveGram.energy, one_pow, one_mul, id_eq]
    exact continuous_finset_sum _ (fun e _ =>
      (responseEnergy_continuous n β hβ e (step n β hβ f)).comp (continuous_apply e))
  have h := integral_mono (continuous_integrable (measure n) _ hc) (integrable_const _)
    (fun rotations => energy_le_loss_of_boundary n β hβ rotations D R hD hR
      (fun e => hcap (rotations e)) (fun j u e => hboundary j rotations u e) f)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- Both hypotheses use literal finite cylinders. The conclusion concerns the
original physical transfer and the same Haar energy on both sides. -/
theorem slab_contraction (β : ℝ) (hβ : 0 ≤ β) (A D R : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hcap : ∀ q : Q, coefficient β q ≤ D)
    (hboundary : ∀ j (rotations : Slice n) u e, boundaryFar n β j rotations u e ≤ R)
    (hcoerce : ∀ j (F : C(Slice n, ℝ)), (∀ h U, F (gaugeSlice h U) = F U) →
      centralVariance n β j F ≤ A * centralEnergy n β j F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (A*(16*D+R)/((k : ℝ)+A*(16*D+R)))*variance n β hβ f :=
  WilsonDirectHaarBudget.slab_contraction n β hβ A (16*D+R) hA (by positivity)
    (coercivity_of_cylinders n β hβ A hcoerce)
    (fun F _ => totalEnergy_le_loss n β hβ D R hD hR hcap hboundary F)
    f hinv k hk

/-- The local cap is proved for every rotation. Its exponential coupling cost
is explicit and is not a continuum-uniform estimate. -/
theorem slab_contraction_explicit_cap (β : ℝ) (hβ : 0 ≤ β) (A R : ℝ)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hboundary : ∀ j (rotations : Slice n) u e, boundaryFar n β j rotations u e ≤ R)
    (hcoerce : ∀ j (F : C(Slice n, ℝ)), (∀ h U, F (gaugeSlice h U) = F U) →
      centralVariance n β j F ≤ A * centralEnergy n β j F)
    (f : C(Slice n, ℝ)) (hinv : ∀ h U, f (gaugeSlice h U) = f U)
    (k : ℕ) (hk : 0 < k) :
    variance n β hβ (WilsonDissipationIteration.flow n β hβ f k) ≤
      (A*(16*(Real.exp (8*β)-1)^2+R)/
        ((k : ℝ)+A*(16*(Real.exp (8*β)-1)^2+R)))*variance n β hβ f :=
  slab_contraction n β hβ A ((Real.exp (8*β)-1)^2) R hA (sq_nonneg _) hR
    (coefficient_cap β hβ) hboundary hcoerce f hinv k hk

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryHaarContraction
