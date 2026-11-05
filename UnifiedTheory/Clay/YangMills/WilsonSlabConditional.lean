/- Exact normalized single-link comparison for the actual time-slab kernel.
Only the local oscillation enters; neither the spatial volume nor a global
partition lower bound appears. This is not a continuum source estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabConditional
noncomputable section
open MeasureTheory LocalGibbsComparison WilsonTimeSlab

section Normalization
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Pairwise weight comparison survives normalization with exactly the same
factor, rather than the square of that factor. -/
theorem normalized_expectation_lower (w : X → ℝ) (hw : Continuous w)
    (hpos : ∀ x, 0 < w x) (D : ℝ)
    (hratio : ∀ x y, w x ≤ Real.exp D * w y)
    (Q : X → ℝ) (hQ : Continuous Q) (hQpos : ∀ x, 0 ≤ Q x) :
    Real.exp (-D) * (∫ x, Q x ∂μ) ≤ ∫ x, Q x ∂weightedLaw μ w := by
  have hiw : Integrable w μ := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiQ : Integrable Q μ := hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiwQ : Integrable (fun x => w x * Q x) μ :=
    (hw.mul hQ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : 0 < ∫ x, w x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hiw]
    have hs : Function.support w = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hpos x).ne'
    simp [hs]
  have hpoint (y : X) : (∫ x, w x ∂μ) ≤ Real.exp D * w y := by
    calc
      _ ≤ ∫ _, Real.exp D * w y ∂μ :=
        integral_mono hiw (integrable_const _) (fun x => hratio x y)
      _ = _ := by simp
  have hi : (∫ x, w x ∂μ) * (∫ y, Q y ∂μ) ≤
      Real.exp D * (∫ y, w y * Q y ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul]
    exact integral_mono (hiQ.const_mul _) (hiwQ.const_mul _) (fun y => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint y) (hQpos y))
  rw [weighted_integral μ w hw.measurable (fun x => (hpos x).le) hz Q]
  apply (le_div_iff₀ hz).mpr
  calc
    (Real.exp (-D) * (∫ x, Q x ∂μ)) * (∫ x, w x ∂μ) =
        Real.exp (-D) * ((∫ x, w x ∂μ) * (∫ x, Q x ∂μ)) := by ring
    _ ≤ Real.exp (-D) * (Real.exp D * (∫ y, w y * Q y ∂μ)) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
end Normalization

variable (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def rowWeight (χ : G → ℂ) (β c : ℝ) (u v : SpatialLinks n G)
    (e : SpatialVertex n × Fin 3) (g : G) : ℝ :=
  kernel χ β c (Function.update u e g) v

theorem rowWeight_continuous (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (u v : SpatialLinks n G) (e : SpatialVertex n × Fin 3) :
    Continuous (rowWeight n G χ β c u v e) := by
  have hu : Continuous (fun g : G => Function.update u e g) := by
    apply continuous_pi
    intro i
    by_cases hi : i = e
    · subst i
      simpa only [Function.update_self] using (continuous_id : Continuous (fun g : G => g))
    · simpa only [Function.update_of_ne hi] using (continuous_const : Continuous (fun _ : G => u i))
  have hk : Continuous (fun uv : SpatialLinks n G × SpatialLinks n G =>
      kernel χ β c uv.1 uv.2) := kernel_continuous χ hcχ β c
  change Continuous (fun g : G => kernel χ β c (Function.update u e g) v)
  have hpair : Continuous (fun g : G => (Function.update u e g, v)) :=
    hu.prodMk continuous_const
  have hcomp := hk.comp hpair
  convert hcomp using 1

def rowLaw (χ : G → ℂ) (β c : ℝ) (u v : SpatialLinks n G)
    (e : SpatialVertex n × Fin 3) : Measure G :=
  weightedLaw (RegulatedGauge.compactHaar G) (rowWeight n G χ β c u v e)

theorem rowLaw_probability (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (u v : SpatialLinks n G) (e : SpatialVertex n × Fin 3) :
    IsProbabilityMeasure (rowLaw n G χ β c u v e) := by
  have hw := rowWeight_continuous n G χ hcχ β c u v e
  have hp (g : G) : 0 < rowWeight n G χ β c u v e g := kernel_positive χ hcχ β c _ v
  have hi : Integrable (rowWeight n G χ β c u v e) (RegulatedGauge.compactHaar G) :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply weightedLaw_probability _ _ hw.measurable hi (fun g => (hp g).le)
  rw [integral_pos_iff_support_of_nonneg (fun g => (hp g).le) hi]
  have hs : Function.support (rowWeight n G χ β c u v e) = Set.univ := by
    ext g
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp g).ne'
  simp [hs]

/-- The actual normalized one-link row of the full slab kernel dominates
Haar expectation by a factor independent of every lattice volume. -/
theorem row_expectation_lower (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (u v : SpatialLinks n G) (e : SpatialVertex n × Fin 3)
    (Q : G → ℝ) (hQ : Continuous Q) (hQpos : ∀ g, 0 ≤ Q g) :
    Real.exp (-(6 * |β| * B)) * (∫ g, Q g ∂RegulatedGauge.compactHaar G) ≤
      ∫ g, Q g ∂rowLaw n G χ β c u v e := by
  apply normalized_expectation_lower _ _ (rowWeight_continuous n G χ hcχ β c u v e)
    (fun g => kernel_positive χ hcχ β c _ v) _ _ Q hQ hQpos
  intro g h
  apply WilsonSlabLocalComparison.kernel_comparison n G χ hcχ B hB hχ β c e.1 e.2
  intro i hi
  simp only [Function.update_of_ne hi]

end
end UnifiedTheory.Clay.YangMills.WilsonSlabConditional
