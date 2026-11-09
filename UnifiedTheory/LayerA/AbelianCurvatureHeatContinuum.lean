/-
Positive-time Fourier estimates for the classical two-dimensional heat limit.
These estimates concern scalar diffusion, not a quantum Yang--Mills measure.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeatFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeat
open Filter
open scoped Topology

theorem gaussian_moment_nat (a : ℝ) (ha : 0 < a) (q : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^q * Real.exp (-a * (n : ℝ)^2)) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul q ha).of_nonneg_of_le
  · intro n; positivity
  · intro n
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ)^2 := by
      exact_mod_cast (show n ≤ n^2 by simpa [pow_two] using Nat.le_mul_self n)
    nlinarith

theorem gaussian_moment_int (a : ℝ) (ha : 0 < a) (q : ℕ) :
    Summable (fun n : ℤ => |(n : ℝ)|^q * Real.exp (-a * (n : ℝ)^2)) := by
  apply Summable.of_nat_of_neg
  · simpa using gaussian_moment_nat a ha q
  · simpa using gaussian_moment_nat a ha q

def radiusSq (k : ℤ × ℤ) : ℝ := (k.1 : ℝ)^2 + (k.2 : ℝ)^2
def radiusOne (k : ℤ × ℤ) : ℝ := |(k.1 : ℝ)| + |(k.2 : ℝ)|

/-- All polynomially weighted two-dimensional Gaussian tails are summable. -/
theorem gaussian_moment (a : ℝ) (ha : 0 < a) (q : ℕ) :
    Summable (fun k : ℤ × ℤ => radiusOne k ^ q * Real.exp (-a * radiusSq k)) := by
  have h : Summable (fun k : ℤ × ℤ => ∑ j ∈ Finset.range (q + 1),
      ((|(k.1 : ℝ)| ^ j * Real.exp (-a * (k.1 : ℝ)^2)) *
        (|(k.2 : ℝ)| ^ (q-j) * Real.exp (-a * (k.2 : ℝ)^2))) * (q.choose j : ℝ)) := by
    apply summable_sum
    intro j _
    exact ((gaussian_moment_int a ha j).mul_of_nonneg (gaussian_moment_int a ha (q-j))
      (fun _ => by positivity) (fun _ => by positivity)).mul_right _
  convert h using 1
  funext k
  simp only [radiusOne, radiusSq, mul_add, Real.exp_add, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun k : ℤ × ℤ => Real.exp (-a * radiusSq k)) := by
  simpa using gaussian_moment a ha 0

theorem spectralSymbol_eq_sinc (h k : ℝ) (hh : h ≠ 0) :
    spectralSymbol h k = 4 * Real.pi^2 * k^2 * Real.sinc (Real.pi * h * k)^2 := by
  by_cases hk : k = 0
  · simp [hk, spectralSymbol]
  rw [Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero Real.pi_ne_zero hh) hk)]
  unfold spectralSymbol
  field_simp

/-- The discrete generator has the continuum eigenvalue at every fixed frequency. -/
theorem spectralSymbol_tendsto (k : ℝ) :
    Tendsto (fun h : ℝ => spectralSymbol h k) (𝓝[≠] 0) (𝓝 (4 * Real.pi^2 * k^2)) := by
  have hc : Tendsto (fun h : ℝ => Real.sinc (Real.pi * h * k)) (𝓝 0) (𝓝 1) := by
    simpa using Real.continuous_sinc.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul tendsto_id).mul_const k :
        Tendsto (fun h : ℝ => Real.pi * h * k) (𝓝 0) (𝓝 (Real.pi * 0 * k)))
  have ht := (hc.mono_left (show (𝓝[≠] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)).pow 2
  have hm := ht.const_mul (4 * Real.pi^2 * k^2)
  simp only [one_pow, mul_one] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (spectralSymbol_eq_sinc h k hh).symm

def continuumEigenvalue (k : ℤ × ℤ) : ℝ := 4 * Real.pi^2 * radiusSq k

def discreteEigenvalue (h : ℝ) (k : ℤ × ℤ) : ℝ :=
  spectralSymbol h k.1 + spectralSymbol h k.2

def frequencyWindow (h : ℝ) (k : ℤ × ℤ) : Prop :=
  (-(1 / 2) ≤ h * (k.1 : ℝ) ∧ h * (k.1 : ℝ) < 1 / 2) ∧
    (-(1 / 2) ≤ h * (k.2 : ℝ) ∧ h * (k.2 : ℝ) < 1 / 2)

/-- Zero extension outside the resolved frequency window. -/
def discreteMultiplier (h t : ℝ) (k : ℤ × ℤ) : ℝ := by
  classical
  exact if frequencyWindow h k then Real.exp (-discreteEigenvalue h k * t) else 0

def continuumMultiplier (t : ℝ) (k : ℤ × ℤ) : ℝ :=
  Real.exp (-continuumEigenvalue k * t)

theorem discreteEigenvalue_tendsto (k : ℤ × ℤ) :
    Tendsto (fun h => discreteEigenvalue h k) (𝓝[≠] 0) (𝓝 (continuumEigenvalue k)) := by
  have he : continuumEigenvalue k = 4 * Real.pi^2 * (k.1 : ℝ)^2 +
      4 * Real.pi^2 * (k.2 : ℝ)^2 := by unfold continuumEigenvalue radiusSq; ring
  rw [he]
  exact (spectralSymbol_tendsto (k.1 : ℝ)).add (spectralSymbol_tendsto (k.2 : ℝ))

theorem frequencyWindow_eventually (k : ℤ × ℤ) :
    ∀ᶠ h in 𝓝 (0 : ℝ), frequencyWindow h k := by
  have hx := ((tendsto_id.mul_const (k.1 : ℝ)).abs).eventually
    (gt_mem_nhds (show (|0 * (k.1 : ℝ)| : ℝ) < 1 / 2 by norm_num))
  have hy := ((tendsto_id.mul_const (k.2 : ℝ)).abs).eventually
    (gt_mem_nhds (show (|0 * (k.2 : ℝ)| : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hx, hy] with h hx hy
  exact ⟨⟨(abs_lt.mp hx).1.le, (abs_lt.mp hx).2⟩,
    ⟨(abs_lt.mp hy).1.le, (abs_lt.mp hy).2⟩⟩

theorem discreteMultiplier_tendsto (t : ℝ) (k : ℤ × ℤ) :
    Tendsto (fun h => discreteMultiplier h t k) (𝓝[≠] 0) (𝓝 (continuumMultiplier t k)) := by
  have ht := ((discreteEigenvalue_tendsto k).neg.mul_const t).rexp
  apply ht.congr'
  filter_upwards [(frequencyWindow_eventually k).filter_mono nhdsWithin_le_nhds] with h hh
  simp only [discreteMultiplier, if_pos hh]

theorem discreteMultiplier_bound (h t : ℝ) (hh : 0 < h) (ht : 0 ≤ t) (k : ℤ × ℤ) :
    |discreteMultiplier h t k| ≤ Real.exp (-(16 * t) * radiusSq k) := by
  unfold discreteMultiplier
  split_ifs with hk
  · rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hx := spectralSymbol_lower h (k.1 : ℝ) hh (abs_le.mpr ⟨hk.1.1, hk.1.2.le⟩)
    have hy := spectralSymbol_lower h (k.2 : ℝ) hh (abs_le.mpr ⟨hk.2.1, hk.2.2.le⟩)
    dsimp [discreteEigenvalue, radiusSq]
    nlinarith [mul_le_mul_of_nonneg_right (add_le_add hx hy) ht]
  · simp only [abs_zero]
    exact (Real.exp_pos _).le

theorem continuumMultiplier_bound (t : ℝ) (ht : 0 ≤ t) (k : ℤ × ℤ) :
    |continuumMultiplier t k| ≤ Real.exp (-(16 * t) * radiusSq k) := by
  rw [continuumMultiplier, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hp : 16 ≤ 4 * Real.pi^2 := by nlinarith [Real.two_le_pi]
  have hr : 0 ≤ radiusSq k := by unfold radiusSq; positivity
  dsimp [continuumEigenvalue]
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hr) ht]

/-- Positive-time smoothing majorant, with arbitrary derivative order. -/
theorem continuum_weighted_summable (c : ℤ × ℤ → ℂ) (M t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (ht : 0 < t) (q : ℕ) :
    Summable (fun k => radiusOne k^q * ‖c k * (continuumMultiplier t k : ℂ)‖) := by
  apply ((gaussian_moment (16 * t) (by positivity) q).mul_right M).of_nonneg_of_le
  · intro k; unfold radiusOne; positivity
  · intro k
    have hb := continuumMultiplier_bound t ht.le k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ radiusOne k^q * (M * Real.exp (-(16*t) * radiusSq k)) := by
        apply mul_le_mul_of_nonneg_left _ (by unfold radiusOne; positivity)
        exact mul_le_mul (hc k) hb (abs_nonneg _) (le_trans (norm_nonneg (c k)) (hc k))
      _ = _ := by ring

def planeWave (k : ℤ × ℤ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * ((k.1 : ℝ) * z.1 + (k.2 : ℝ) * z.2)))

theorem planeWave_norm (k : ℤ × ℤ) (z : ℝ × ℝ) : ‖planeWave k z‖ = 1 := by
  simp [planeWave, Complex.norm_exp]

def continuumSeries (c : ℤ × ℤ → ℂ) (t : ℝ) (z : ℝ × ℝ) : ℂ :=
  ∑' k, c k * (continuumMultiplier t k : ℂ) * planeWave k z

def discreteSeries (c : ℤ × ℤ → ℂ) (h t : ℝ) (z : ℝ × ℝ) : ℂ :=
  ∑' k, c k * (discreteMultiplier h t k : ℂ) * planeWave k z

theorem continuumSeries_summable (c : ℤ × ℤ → ℂ) (M t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (ht : 0 < t) (z : ℝ × ℝ) :
    Summable (fun k => c k * (continuumMultiplier t k : ℂ) * planeWave k z) := by
  have hs : Summable (fun k => ‖c k * (continuumMultiplier t k : ℂ)‖) := by
    simpa using continuum_weighted_summable c M t hc ht 0
  apply hs.of_norm_bounded
  intro k
  rw [norm_mul, planeWave_norm, mul_one]

theorem discreteSeries_summable (c : ℤ × ℤ → ℂ) (M h t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (hh : 0 < h) (ht : 0 < t) (z : ℝ × ℝ) :
    Summable (fun k => c k * (discreteMultiplier h t k : ℂ) * planeWave k z) := by
  apply ((gaussian_summable (16*t) (by positivity)).mul_left M).of_norm_bounded
  intro k
  rw [norm_mul, planeWave_norm, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (hc k) (discreteMultiplier_bound h t hh ht.le k)
    (abs_nonneg _) ((norm_nonneg (c k)).trans (hc k))

def coefficientError (c d : ℤ × ℤ → ℂ) (h t : ℝ) (k : ℤ × ℤ) : ℝ :=
  ‖c k * (discreteMultiplier h t k : ℂ) - d k * (continuumMultiplier t k : ℂ)‖

theorem coefficientError_bound (c d : ℤ × ℤ → ℂ) (M h t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (hh : 0 < h) (ht : 0 ≤ t) (k : ℤ × ℤ) :
    coefficientError c d h t k ≤ 2*M * Real.exp (-(16*t) * radiusSq k) := by
  have hM : 0 ≤ M := (norm_nonneg (c k)).trans (hc k)
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hx := mul_le_mul (hc k) (discreteMultiplier_bound h t hh ht k) (abs_nonneg _) hM
  have hy := mul_le_mul (hd k) (continuumMultiplier_bound t ht k) (abs_nonneg _) hM
  nlinarith

theorem coefficientError_summable (c d : ℤ × ℤ → ℂ) (M h t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M) (hh : 0 < h) (ht : 0 < t) :
    Summable (coefficientError c d h t) := by
  apply ((gaussian_summable (16*t) (by positivity)).mul_left (2*M)).of_nonneg_of_le
  · intro k; exact norm_nonneg _
  · exact coefficientError_bound c d M h t hc hd hh ht.le

/-- A single scalar error bound holds at every spatial point. -/
theorem series_error_bound (c d : ℤ × ℤ → ℂ) (M h t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (hh : 0 < h) (ht : 0 < t) (z : ℝ × ℝ) :
    ‖discreteSeries c h t z - continuumSeries d t z‖ ≤ ∑' k, coefficientError c d h t k := by
  rw [discreteSeries, continuumSeries,
    ← (discreteSeries_summable c M h t hc hh ht z).tsum_sub
      (continuumSeries_summable d M t hd ht z)]
  apply tsum_of_norm_bounded (coefficientError_summable c d M h t hc hd hh ht).hasSum
  intro k
  rw [← sub_mul, norm_mul, planeWave_norm, mul_one]
  rfl

/-- Bounded coefficients with modewise consistency suffice for the full positive-time series.
The hypotheses concern the coefficients; their derivation from cell averages is separate. -/
theorem coefficientError_tsum_tendsto (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (M t : ℝ) (h : ℕ → ℝ) (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (hh : ∀ n, 0 < h n) (ht : 0 < t)
    (hlim : Tendsto h atTop (𝓝[≠] 0))
    (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k))) :
    Tendsto (fun n => ∑' k, coefficientError (c n) d (h n) t k) atTop (𝓝 0) := by
  have hm (k) := (discreteMultiplier_tendsto t k).comp hlim
  have he (k) : Tendsto (fun n => coefficientError (c n) d (h n) t k) atTop (𝓝 0) := by
    have hx := ((hcoeff k).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp (hm k))).sub
      (tendsto_const_nhds (x := d k * (continuumMultiplier t k : ℂ)))
    simpa [coefficientError] using hx.norm
  have hs := tendsto_tsum_of_dominated_convergence
    ((gaussian_summable (16*t) (by positivity)).mul_left (2*M)) he
    (Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ coefficientError (c n) d (h n) t k from norm_nonneg _)]
      exact coefficientError_bound (c n) d M (h n) t (hc n) hd (hh n) ht.le k)
  simpa using hs

theorem series_tendstoUniformly (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (M t : ℝ) (h : ℕ → ℝ) (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (hh : ∀ n, 0 < h n) (ht : 0 < t)
    (hlim : Tendsto h atTop (𝓝[≠] 0))
    (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k))) :
    TendstoUniformly (fun n => discreteSeries (c n) (h n) t) (continuumSeries d t) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have he := (coefficientError_tsum_tendsto c d M t h hc hd hh ht hlim hcoeff).eventually
    (gt_mem_nhds hε)
  filter_upwards [he] with n hn z
  rw [dist_eq_norm, norm_sub_rev]
  exact (series_error_bound (c n) d M (h n) t (hc n) hd (hh n) ht z).trans_lt hn

/-- Reciprocal integer mesh sizes satisfy the convergence hypothesis. -/
theorem reciprocal_mesh_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall (fun n => by
      simp only [one_div, Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
      positivity)

theorem series_reciprocal_tendstoUniformly (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (M t : ℝ) (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (ht : 0 < t) (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k))) :
    TendstoUniformly (fun n => discreteSeries (c n) (1 / ((n : ℝ) + 1)) t)
      (continuumSeries d t) atTop :=
  series_tendstoUniformly c d M t _ hc hd (fun _ => by positivity) ht
    reciprocal_mesh_tendsto hcoeff

theorem continuumSeries_continuous (c : ℤ × ℤ → ℂ) (M t : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (ht : 0 < t) : Continuous (continuumSeries c t) := by
  apply continuous_tsum (u := fun k => M * Real.exp (-(16*t) * radiusSq k))
  · intro k
    unfold planeWave
    fun_prop
  · exact (gaussian_summable (16*t) (by positivity)).mul_left M
  · intro k z
    rw [norm_mul, planeWave_norm, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hc k) (continuumMultiplier_bound t ht.le k) (abs_nonneg _)
      ((norm_nonneg (c k)).trans (hc k))

/-- The error tends to zero even after any fixed polynomial frequency weight.
This controls derivative multipliers; differentiating the series is a separate step. -/
theorem weighted_coefficientError_tsum_tendsto (c : ℕ → ℤ × ℤ → ℂ) (d : ℤ × ℤ → ℂ)
    (M t : ℝ) (h : ℕ → ℝ) (hc : ∀ n k, ‖c n k‖ ≤ M) (hd : ∀ k, ‖d k‖ ≤ M)
    (hh : ∀ n, 0 < h n) (ht : 0 < t)
    (hlim : Tendsto h atTop (𝓝[≠] 0))
    (hcoeff : ∀ k, Tendsto (fun n => c n k) atTop (𝓝 (d k))) (q : ℕ) :
    Tendsto (fun n => ∑' k, radiusOne k^q * coefficientError (c n) d (h n) t k)
      atTop (𝓝 0) := by
  have he (k) : Tendsto (fun n => radiusOne k^q * coefficientError (c n) d (h n) t k)
      atTop (𝓝 0) := by
    have hm := (discreteMultiplier_tendsto t k).comp hlim
    have hx := ((hcoeff k).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hm)).sub
      (tendsto_const_nhds (x := d k * (continuumMultiplier t k : ℂ)))
    simpa [coefficientError] using hx.norm.const_mul (radiusOne k^q)
  have hs := tendsto_tsum_of_dominated_convergence
    ((gaussian_moment (16*t) (by positivity) q).mul_right (2*M)) he
    (Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ radiusOne k^q *
        coefficientError (c n) d (h n) t k by unfold radiusOne coefficientError; positivity)]
      have hb := mul_le_mul_of_nonneg_left
        (coefficientError_bound (c n) d M (h n) t (hc n) hd (hh n) ht.le k)
        (show 0 ≤ radiusOne k^q by unfold radiusOne; positivity)
      nlinarith [hb])
  simpa using hs

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
