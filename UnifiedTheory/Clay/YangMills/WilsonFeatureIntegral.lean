/- Integrated Wilson feature expansion. Every Taylor coefficient is an
explicit sum of squared feature moments. This concerns the transfer kernel;
it does not identify a full periodic lattice conditional response. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonFeatureIntegral
noncomputable section
open MeasureTheory WilsonCrossingKernel
open scoped Topology

variable {X D : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Fintype D]
  (μ : Measure X) [IsProbabilityMeasure μ]

def moment (φ : X → D → ℝ) (f : X → ℝ) (m : ℕ) (p : Fin m → D) : ℝ :=
  ∫ x, f x * ∏ t, φ x (p t) ∂μ

def coefficient (φ : X → D → ℝ) (f : X → ℝ) (m : ℕ) : ℝ :=
  ∑ p : Fin m → D, (moment μ φ f m p)^2

def pairing (φ : X → D → ℝ) (β : ℝ) (f : X → ℝ) : ℝ :=
  ∫ z : X × X, f z.1 * Real.exp (β * featureKernel φ z.1 z.2) * f z.2 ∂μ.prod μ

theorem coefficient_nonneg (φ : X → D → ℝ) (f : X → ℝ) (m : ℕ) :
    0 ≤ coefficient μ φ f m := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem power_pairing (φ : X → D → ℝ) (hφ : ∀ d, Continuous (fun x => φ x d))
    (f : X → ℝ) (hf : Continuous f) (m : ℕ) :
    (∫ z : X × X, f z.1 * (featureKernel φ z.1 z.2)^m * f z.2 ∂μ.prod μ) =
      coefficient μ φ f m := by
  simp_rw [feature_power, featureKernel, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _
    have he : (fun z : X × X => f z.1 *
        ((∏ t, φ z.1 (p t)) * ∏ t, φ z.2 (p t)) * f z.2) =
        (fun z : X × X => (f z.1 * ∏ t, φ z.1 (p t)) *
          (f z.2 * ∏ t, φ z.2 (p t))) := by funext z; ring
    rw [he, integral_prod_mul (fun x => f x * ∏ t, φ x (p t))
      (fun x => f x * ∏ t, φ x (p t))]
    exact (pow_two _).symm
  · intro p _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact ((hf.comp continuous_fst).mul
      ((continuous_finset_prod _ (fun t _ => (hφ (p t)).comp continuous_fst)).mul
        (continuous_finset_prod _ (fun t _ => (hφ (p t)).comp continuous_snd)))).mul
          (hf.comp continuous_snd)

theorem expansion (φ : X → D → ℝ) (hφ : ∀ d, Continuous (fun x => φ x d))
    (f : X → ℝ) (hf : Continuous f) (β : ℝ) :
    HasSum (fun m => β^m / (m.factorial : ℝ) * coefficient μ φ f m)
      (pairing μ φ β f) := by
  have hK : Continuous (fun z : X × X => featureKernel φ z.1 z.2) :=
    continuous_finset_sum _ (fun d _ =>
      ((hφ d).comp continuous_fst).mul ((hφ d).comp continuous_snd))
  obtain ⟨L,hL⟩ := (isCompact_range hf).isBounded.exists_norm_le
  obtain ⟨M,hM⟩ := (isCompact_range hK).isBounded.exists_norm_le
  let b : ℕ → ℝ := fun m => |L|^2 * (|β| * |M|)^m / (m.factorial : ℝ)
  have hb : Summable b := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (|β| * |M|)).summable.mul_left (|L|^2)
    simpa only [b, mul_div_assoc] using h
  have hc (m : ℕ) : Continuous (fun z : X × X =>
      f z.1 * ((β * featureKernel φ z.1 z.2)^m / (m.factorial : ℝ)) * f z.2) :=
    ((hf.comp continuous_fst).mul
      ((continuous_const.mul hK).pow m |>.div_const _)).mul (hf.comp continuous_snd)
  have hs := hasSum_integral_of_dominated_convergence
    (μ := μ.prod μ) (fun m (_ : X × X) => b m) (fun m => (hc m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall (fun z => by
      have hf1 : ‖f z.1‖ ≤ |L| := (hL _ ⟨z.1,rfl⟩).trans (le_abs_self _)
      have hf2 : ‖f z.2‖ ≤ |L| := (hL _ ⟨z.2,rfl⟩).trans (le_abs_self _)
      have hk : ‖featureKernel φ z.1 z.2‖ ≤ |M| :=
        (hM _ ⟨z,rfl⟩).trans (le_abs_self _)
      simp only [norm_mul, norm_div, norm_pow, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ (m.factorial : ℝ) from Nat.cast_nonneg _)]
      calc
        |f z.1| * ((|β| * |featureKernel φ z.1 z.2|)^m / (m.factorial : ℝ)) * |f z.2| ≤
            |L| * ((|β| * |M|)^m / (m.factorial : ℝ)) * |L| :=
          mul_le_mul (mul_le_mul hf1
            (div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hk (abs_nonneg _)) m)
              (Nat.cast_nonneg _)) (by positivity) (abs_nonneg _)) hf2
            (abs_nonneg _) (by positivity)
        _ = b m := by dsimp [b]; ring))
    (Filter.Eventually.of_forall (fun _ => hb)) (integrable_const _)
    (Filter.Eventually.of_forall (fun z => by
      have h := NormedSpace.expSeries_div_hasSum_exp (β * featureKernel φ z.1 z.2)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact (h.mul_left (f z.1)).mul_right (f z.2)))
  convert hs using 1
  funext m
  have he : (fun z : X × X => f z.1 *
      ((β * featureKernel φ z.1 z.2)^m / (m.factorial : ℝ)) * f z.2) =
      (fun z : X × X => (β^m / (m.factorial : ℝ)) *
        (f z.1 * (featureKernel φ z.1 z.2)^m * f z.2)) := by
    funext z
    rw [mul_pow]
    ring
  rw [he, integral_const_mul, power_pairing μ φ hφ f hf m]

theorem coefficient_lower (φ : X → D → ℝ) (hφ : ∀ d, Continuous (fun x => φ x d))
    (f : X → ℝ) (hf : Continuous f) (β : ℝ) (hβ : 0 ≤ β) (m : ℕ) :
    β^m / (m.factorial : ℝ) * coefficient μ φ f m ≤ pairing μ φ β f := by
  have hs := expansion μ φ hφ f hf β
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum m (fun k _ =>
    mul_nonneg (div_nonneg (pow_nonneg hβ _) (Nat.cast_nonneg _))
      (coefficient_nonneg μ φ f k))

end
end UnifiedTheory.Clay.YangMills.WilsonFeatureIntegral
