/- L2 convergence of real continuous boundary amplitudes passes to fixed
continuous insertions and normalized finite-time transfer pairings. -/
import UnifiedTheory.Clay.YangMills.SquaredDensityConvergence
import UnifiedTheory.Clay.YangMills.VacuumPowerConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuousBoundaryMoments
noncomputable section
open MeasureTheory Filter WilsonPositiveGroundState SquaredDensityConvergence
open TransferEnergySurvival
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def embed (f : C(X, ℝ)) : Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ (complexify f)

theorem embed_sub (f g : C(X, ℝ)) : embed μ (f - g) = embed μ f - embed μ g := by
  have he : complexify (f - g) = complexify f - complexify g := by
    ext x
    simp [complexify]
  simp only [embed, he, map_sub]

theorem embed_smul (c : ℝ) (f : C(X, ℝ)) : embed μ (c • f) = (c : ℂ) • embed μ f := by
  simp only [embed, complexify_smul, map_smul]

/-- Bounded continuous insertions preserve genuine L2 convergence. -/
theorem product_tendsto (u : ℕ → C(X, ℝ)) (v F : C(X, ℝ))
    (hu : Tendsto (fun j => embed μ (u j)) atTop (nhds (embed μ v))) :
    Tendsto (fun j => embed μ (F * u j)) atTop (nhds (embed μ (F * v))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (j : ℕ) : ‖embed μ (F * u j) - embed μ (F * v)‖ ≤
      ‖F‖ * ‖embed μ (u j) - embed μ v‖ := by
    rw [← embed_sub, ← mul_sub, ← embed_sub]
    simpa only [amplitudeNorm_complex, embed] using amplitudeNorm_mul_le μ F (u j - v)
  have hh := (tendsto_iff_norm_sub_tendsto_zero.mp hu).const_mul ‖F‖
  exact squeeze_zero (fun _ => norm_nonneg _) hb (by simpa using hh)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem iterate_continuous (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (k : ℕ) :
    Continuous (iterate A k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih => exact A.continuous.comp ih

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem iterate_smul (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (k : ℕ)
    (c : ℂ) (v : Lp ℂ 2 μ) : iterate A k (c • v) = c • iterate A k v := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ, ih, map_smul]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem iterate_fixed (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (v : Lp ℂ 2 μ)
    (hf : A v = v) (k : ℕ) : iterate A k v = v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, ih, hf]

/-- The common positive boundary overlap cancels from the limiting normalized
two-insertion pairing. The power k remains physical transfer time throughout. -/
theorem normalized_pairing_tendsto (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (ψ : C(X, ℝ)) (hn : ‖embed μ ψ‖ = 1) (hf : A (embed μ ψ) = embed μ ψ)
    (u : ℕ → C(X, ℝ)) (c : ℝ) (hc : 0 < c)
    (hu : Tendsto (fun j => embed μ (u j)) atTop (nhds ((c : ℂ) • embed μ ψ)))
    (F G : C(X, ℝ)) (k : ℕ) :
    Tendsto (fun j =>
      (inner ℂ (embed μ (F * u j)) (iterate A k (embed μ (G * u j)))).re /
        (inner ℂ (embed μ (u j)) (iterate A k (embed μ (u j)))).re) atTop
      (nhds ((inner ℂ (embed μ (F * ψ)) (iterate A k (embed μ (G * ψ)))).re)) := by
  have hu' : Tendsto (fun j => embed μ (u j)) atTop (nhds (embed μ (c • ψ))) := by
    simpa only [embed_smul] using hu
  have hF := product_tendsto μ u (c • ψ) F hu'
  have hG := product_tendsto μ u (c • ψ) G hu'
  have he (H : C(X, ℝ)) : embed μ (H * (c • ψ)) = (c : ℂ) • embed μ (H * ψ) := by
    rw [mul_smul_comm, embed_smul]
  simp only [he] at hF hG
  have hnum := Complex.continuous_re.tendsto _ |>.comp
    (hF.inner (𝕜 := ℂ) ((iterate_continuous μ A k).tendsto _ |>.comp hG))
  have hden := Complex.continuous_re.tendsto _ |>.comp
    (hu.inner (𝕜 := ℂ) ((iterate_continuous μ A k).tendsto _ |>.comp hu))
  have hnum' : Tendsto (fun j =>
      (inner ℂ (embed μ (F * u j)) (iterate A k (embed μ (G * u j)))).re) atTop
      (nhds (c^2 * (inner ℂ (embed μ (F * ψ))
        (iterate A k (embed μ (G * ψ)))).re)) := by
    rw [iterate_smul, inner_smul_left, inner_smul_right] at hnum
    simpa [Complex.mul_re, pow_two, mul_assoc, Function.comp_def] using hnum
  have hden' : Tendsto (fun j =>
      (inner ℂ (embed μ (u j)) (iterate A k (embed μ (u j)))).re) atTop
      (nhds (c^2)) := by
    rw [iterate_smul, iterate_fixed μ A _ hf, inner_smul_left, inner_smul_right,
      inner_self_eq_one_of_norm_eq_one hn] at hden
    simpa [Complex.mul_re, pow_two, Function.comp_def] using hden
  have h := hnum'.div hden' (ne_of_gt (sq_pos_of_pos hc))
  simpa only [mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos hc))] using h

end
end UnifiedTheory.Clay.YangMills.ContinuousBoundaryMoments
