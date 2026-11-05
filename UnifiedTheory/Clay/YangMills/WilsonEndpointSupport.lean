/- The endpoint-support obstruction is bound to the actual Wilson pair source
and original-transfer variance loss. No unweighted rarity estimate removes it. -/
import UnifiedTheory.Clay.YangMills.CompactEndpointSupport
import UnifiedTheory.Clay.YangMills.WilsonGaugeSourceTail
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonEndpointSupport
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge WilsonTemporalInfluence
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonVariancePair WilsonGroundVarianceBudget
open CompactDensityEntropy
open WilsonGaugeSourceTail (source source_continuous source_nonneg pairProfile)

variable (n : ℕ) [NeZero n]

def density (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) : C(Slice n, ℝ) :=
  ⟨rawTransition n β hβ u, WilsonStationaryEntropy.row_continuous n β hβ u⟩

theorem source_pair (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u v : Slice n) :
    source n β hβ f (u,v) = ∫ w, CompactEndpointSupport.pair (density n β hβ u) f (v,w)
      ∂WilsonSlabOperator.measure n := by
  unfold source pairProfile CompactEndpointSupport.pair density
  simp only [ContinuousMap.coe_mk, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  ring

def rowMass (E : Set (Slice n)) (β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  (∫ v, E.indicator (fun v => source n β hβ f (u,v)) v ∂WilsonSlabOperator.measure n)/2

theorem rowMass_pair (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) :
    rowMass n E β hβ f u =
      CompactEndpointSupport.restricted (WilsonSlabOperator.measure n) E
        (density n β hβ u) f/2 := by
  rw [CompactEndpointSupport.restricted_iterated _ E hE]
  simp only [rowMass, source_pair]

theorem rowMass_integrable (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Integrable (rowMass n E β hβ f) (groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  exact (((continuous_integrable ((groundLaw n β hβ).prod (WilsonSlabOperator.measure n)) _
    (source_continuous n β hβ f)).indicator
      (hE.preimage measurable_snd)).integral_prod_left).div_const 2

theorem row_lower (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (hf : ∀ v, v ∉ E → f v = 0)
    (u : Slice n) : rowVariance n β hβ f u/2 ≤ rowMass n E β hβ f u := by
  have h := CompactEndpointSupport.pair_le_twice_restricted
    (WilsonSlabOperator.measure n) E hE (density n β hβ u) f
    (fun v => (rawTransition_pos n β hβ u v).le) hf
  have hv : CompactVariancePair.pairMoment (WilsonSlabOperator.measure n)
      (density n β hβ u) f/2 = rowVariance n β hβ f u := rowVariance_pair n β hβ u f
  rw [rowMass_pair n E hE]
  linarith

def meanMass (E : Set (Slice n)) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, rowMass n E β hβ f u ∂groundLaw n β hβ

/-- The restriction is on one actual endpoint; it already retains half of
the source mass for any observable supported in that endpoint region. -/
theorem loss_half_le (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (hf : ∀ v, v ∉ E → f v = 0) :
    loss n β hβ f/2 ≤ meanMass n E β hβ f := by
  letI := groundLaw_probability n β hβ
  have h := integral_mono
    ((continuous_integrable (groundLaw n β hβ) _ (rowVariance_continuous n β hβ f)).div_const 2)
    (rowMass_integrable n E hE β hβ f) (row_lower n E hE β hβ f hf)
  rw [integral_div, mean_rowVariance_eq_loss] at h
  exact h

theorem rowVariance_positive (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (x y : Slice n) (hne : f x ≠ f y) (u : Slice n) : 0 < rowVariance n β hβ f u := by
  letI : Measure.IsOpenPosMeasure (WilsonSlabOperator.measure n) := by
    unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar RegulatedGauge.compactHaar
    infer_instance
  have h := CompactEndpointSupport.pair_positive (WilsonSlabOperator.measure n)
    (density n β hβ u) f (rawTransition_pos n β hβ u) x y hne
  have hv : CompactVariancePair.pairMoment (WilsonSlabOperator.measure n)
      (density n β hβ u) f/2 = rowVariance n β hβ f u := rowVariance_pair n β hβ u f
  linarith

theorem loss_positive (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (x y : Slice n) (hne : f x ≠ f y) : 0 < loss n β hβ f := by
  letI := groundLaw_probability n β hβ
  letI := ground_openPos n β hβ
  rw [← mean_rowVariance_eq_loss]
  exact integral_pos_of_integrable_nonneg_nonzero (rowVariance_continuous n β hβ f)
    (continuous_integrable (groundLaw n β hβ) _ (rowVariance_continuous n β hβ f))
    (rowVariance_nonneg n β hβ f) (rowVariance_positive n β hβ f x y hne x).ne'

theorem no_small_bound (E : Set (Slice n)) (hE : MeasurableSet E)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (hf : ∀ v, v ∉ E → f v = 0)
    (x y : Slice n) (hne : f x ≠ f y) (ε : ℝ) (hε : ε < 1 / 2) :
    ¬meanMass n E β hβ f ≤ ε*loss n β hβ f := by
  have h := loss_half_le n E hE β hβ f hf
  have hp := loss_positive n β hβ f x y hne
  intro hu
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonEndpointSupport
