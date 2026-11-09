/-
Connection of the positive-time Fourier limit to the actual gridHeat evolution.
The initial data here are reconstructed from the resolved Fourier coefficients.
Identification of these coefficients with cell averages is not assumed proved.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat
open UnifiedTheory.LayerA.AbelianCurvatureHeatDynamics
open UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
open UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
open Filter
open scoped Topology

def gridPosition (n : ℕ) (p : Grid n) : ℝ × ℝ :=
  ((p.1.val : ℝ) / n, (p.2.val : ℝ) / n)

theorem planeWave_integer_grid (n : ℕ) [NeZero n] (k p : ℤ × ℤ) :
    planeWave k ((p.1 : ℝ) / n, (p.2 : ℝ) / n) =
      gridCharacter n k ((p.1 : ZMod n), (p.2 : ZMod n)) := by
  change _ = ZMod.stdAddChar ((k.1 : ZMod n) * (p.1 : ZMod n) +
    (k.2 : ZMod n) * (p.2 : ZMod n))
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, ZMod.stdAddChar_coe]
  unfold planeWave
  push_cast
  congr 1
  ring

theorem planeWave_gridPosition (n : ℕ) [NeZero n] (k : ℤ × ℤ) (p : Grid n) :
    planeWave k (gridPosition n p) = gridCharacter n k p := by
  simpa [gridPosition] using planeWave_integer_grid n k (p.1.val, p.2.val)

def gridFrequencies (n : ℕ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (frequencyWindow (1 / (n : ℝ)))

theorem mem_gridFrequencies (n : ℕ) [NeZero n] (k : ℤ × ℤ) :
    k ∈ gridFrequencies n ↔ frequencyWindow (1 / (n : ℝ)) k := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hb (j : ℤ) (hj : -(1/2 : ℝ) ≤ (1 / (n : ℝ)) * j ∧
      (1 / (n : ℝ)) * j < 1/2) : -(n : ℤ) ≤ j ∧ j ≤ n := by
    have h1 := mul_le_mul_of_nonneg_left hj.1 hn.le
    have h2 := mul_le_mul_of_nonneg_left hj.2.le hn.le
    have he : (n : ℝ) * (1 / (n : ℝ) * j) = j := by field_simp
    rw [he] at h1 h2
    constructor
    · exact_mod_cast (show -(n : ℝ) ≤ (j : ℝ) by linarith)
    · exact_mod_cast (show (j : ℝ) ≤ (n : ℝ) by linarith)
  simp only [gridFrequencies, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨⟨hb k.1 h.1, hb k.2 h.2⟩, h⟩⟩

def reconstructedData (n : ℕ) [NeZero n] (c : ℤ × ℤ → ℂ) (p : Grid n) : ℝ :=
  ∑ k ∈ gridFrequencies n, (c k * gridCharacter n k p).re

theorem gridHeat_finite_modes (n : ℕ) [NeZero n] (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ → ℂ) (t : ℝ) (p : Grid n) :
    gridHeat n t (fun q => ∑ k ∈ S, (c k * gridCharacter n k q).re) p =
      ∑ k ∈ S, Real.exp (-discreteEigenvalue (1 / (n : ℝ)) k * t) *
        (c k * gridCharacter n k p).re := by
  have hf : (fun q => ∑ k ∈ S, (c k * gridCharacter n k q).re) =
      ∑ k ∈ S, (fun q => (c k * gridCharacter n k q).re) := by
    funext q; simp only [Finset.sum_apply]
  change heat (1, 0) (0, 1) _ _ p = _
  rw [← evolution_eq_heat, hf, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [evolution_eq_heat]
  exact gridHeat_mode n k (c k) t p

theorem discreteSeries_gridPosition (n : ℕ) [NeZero n] (c : ℤ × ℤ → ℂ)
    (t : ℝ) (p : Grid n) :
    (discreteSeries c (1 / (n : ℝ)) t (gridPosition n p)).re =
      gridHeat n t (reconstructedData n c) p := by
  classical
  have hz (k : ℤ × ℤ) (hk : k ∉ gridFrequencies n) :
      c k * (discreteMultiplier (1 / (n : ℝ)) t k : ℂ) * planeWave k (gridPosition n p) = 0 := by
    have hk' := (mem_gridFrequencies n k).not.mp hk
    simp only [discreteMultiplier, if_neg hk', Complex.ofReal_zero, mul_zero, zero_mul]
  unfold discreteSeries
  rw [tsum_eq_sum hz, Complex.re_sum]
  rw [show reconstructedData n c = (fun q => ∑ k ∈ gridFrequencies n,
      (c k * gridCharacter n k q).re) by rfl, gridHeat_finite_modes]
  apply Finset.sum_congr rfl
  intro k hk
  rw [planeWave_gridPosition]
  have hk' := (mem_gridFrequencies n k).mp hk
  simp only [discreteMultiplier, if_pos hk', Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im, zero_add]
  ring

/-- Uniform convergence over all nodes of the actual heat evolution, for a family
of bounded Fourier coefficients that converges at each fixed frequency. -/
theorem gridHeat_reconstruction_limit (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (M t : ℝ) (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M) (ht : 0 < t)
    (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p : Grid (n + 1),
      |gridHeat (n + 1) t (reconstructedData (n + 1) (c n)) p -
        (continuumSeries d t (gridPosition (n + 1) p)).re| < ε := by
  intro ε hε
  have hu := (Metric.tendstoUniformly_iff.mp
    (series_reciprocal_tendstoUniformly c d M t hc hd ht hcoeff)) ε hε
  filter_upwards [hu] with n hn p
  have hz := hn (gridPosition (n + 1) p)
  rw [dist_eq_norm, norm_sub_rev] at hz
  have hs := Complex.abs_re_le_norm (discreteSeries (c n) (1 / ((n : ℝ) + 1)) t
    (gridPosition (n + 1) p) - continuumSeries d t (gridPosition (n + 1) p))
  rw [Complex.sub_re] at hs
  have he : 1 / ((n : ℝ) + 1) = 1 / ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [he, discreteSeries_gridPosition] at hs
  rw [he] at hz
  exact hs.trans_lt hz

theorem gridHeat_stability (n : ℕ) [NeZero n] (f g : Grid n → ℝ) (t ε : ℝ)
    (ht : 0 ≤ t) (he : ∀ p, |f p - g p| ≤ ε) (p : Grid n) :
    |gridHeat n t f p - gridHeat n t g p| ≤ ε := by
  apply heat_initial_data_stability (1, 0) (0, 1) _ (by positivity)
    f g ‖f‖ ‖g‖ ε _ _ he p
  · intro q; simpa only [Real.norm_eq_abs] using norm_le_pi_norm f q
  · intro q; simpa only [Real.norm_eq_abs] using norm_le_pi_norm g q

/-- Vanishing initialization error does not change the actual grid-heat limit. -/
theorem gridHeat_perturbed_reconstruction_limit
    (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (g : (n : ℕ) → Grid (n + 1) → ℝ) (η : ℕ → ℝ) (M t : ℝ)
    (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M) (ht : 0 < t)
    (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k)))
    (hη : Tendsto η atTop (𝓝 0))
    (hg : ∀ n p, |g n p - reconstructedData (n + 1) (c n) p| ≤ η n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p : Grid (n + 1),
      |gridHeat (n + 1) t (g n) p -
        (continuumSeries d t (gridPosition (n + 1) p)).re| < ε := by
  intro ε hε
  have hhalf : 0 < ε/2 := half_pos hε
  filter_upwards [gridHeat_reconstruction_limit c d M t hc hd ht hcoeff (ε/2) hhalf,
    hη.eventually (gt_mem_nhds hhalf)] with n hn hηn p
  have hs := gridHeat_stability (n + 1) (g n) (reconstructedData (n + 1) (c n))
    t (η n) ht.le (hg n) p
  have hb := abs_sub_le (gridHeat (n + 1) t (g n) p)
    (gridHeat (n + 1) t (reconstructedData (n + 1) (c n)) p)
    (continuumSeries d t (gridPosition (n + 1) p)).re
  linarith [hn p]

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatGridLimit
