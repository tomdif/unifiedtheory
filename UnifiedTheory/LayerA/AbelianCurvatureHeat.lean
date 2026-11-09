/-
The actual Poisson-series heat evolution of real (lifted U(1)) curvature.
This file proves convergence of its defining series, its maximum principle,
positivity, constant preservation, and stability with respect to initial data.
The Fourier smoothing/continuum argument is written in
ABELIAN_CURVATURE_HEAT_LIMIT.md and is not claimed to be fully formalized.
-/
import UnifiedTheory.LayerA.GaugeTransportStability
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeat
noncomputable section
open scoped BigOperators Topology

section Walk
variable {V : Type*} [AddCommGroup V]

/-- The nearest-neighbor Markov average; the directions will be the grid axes. -/
def step (ex ey : V) (f : V → ℝ) (p : V) : ℝ :=
  (f (p + ex) + f (p - ex) + f (p + ey) + f (p - ey)) / 4

def walk (ex ey : V) (f : V → ℝ) : ℕ → V → ℝ
  | 0 => f
  | k + 1 => step ex ey (walk ex ey f k)

theorem step_bound (ex ey : V) (f : V → ℝ) (M : ℝ)
    (hf : ∀ p, |f p| ≤ M) (p : V) : |step ex ey f p| ≤ M := by
  have h1 := abs_le.mp (hf (p + ex))
  have h2 := abs_le.mp (hf (p - ex))
  have h3 := abs_le.mp (hf (p + ey))
  have h4 := abs_le.mp (hf (p - ey))
  dsimp [step]
  apply abs_le.mpr
  constructor <;> linarith

theorem walk_bound (ex ey : V) (f : V → ℝ) (M : ℝ)
    (hf : ∀ p, |f p| ≤ M) (k : ℕ) (p : V) : |walk ex ey f k p| ≤ M := by
  induction k generalizing p with
  | zero => exact hf p
  | succ k ih => exact step_bound ex ey _ M ih p

theorem step_nonneg (ex ey : V) (f : V → ℝ) (hf : ∀ p, 0 ≤ f p) (p : V) :
    0 ≤ step ex ey f p := by
  dsimp [step]
  exact div_nonneg (add_nonneg (add_nonneg (add_nonneg (hf _) (hf _)) (hf _)) (hf _)) (by norm_num)

theorem walk_nonneg (ex ey : V) (f : V → ℝ) (hf : ∀ p, 0 ≤ f p) (k : ℕ) (p : V) :
    0 ≤ walk ex ey f k p := by
  induction k generalizing p with
  | zero => exact hf p
  | succ k ih => exact step_nonneg ex ey _ ih p

theorem walk_constant (ex ey : V) (c : ℝ) (k : ℕ) (p : V) :
    walk ex ey (fun _ => c) k p = c := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp only [walk, step, ih]; ring

theorem walk_sub (ex ey : V) (f g : V → ℝ) (k : ℕ) (p : V) :
    walk ex ey (fun q => f q - g q) k p = walk ex ey f k p - walk ex ey g k p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp only [walk, step, ih]; ring

theorem walk_translation (ex ey a : V) (f : V → ℝ) (k : ℕ) (p : V) :
    walk ex ey (fun q => f (q + a)) k p = walk ex ey f k (p + a) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      simp only [walk, step, ih]
      congr 2 <;> congr 1 <;> abel_nf

end Walk

def poissonWeight (s : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-s) * (s ^ k / (k.factorial : ℝ))

theorem poissonWeight_nonneg (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    0 ≤ poissonWeight s k := by
  dsimp [poissonWeight]
  positivity

/-- Normalization is proved from the exponential series, not an assumption. -/
theorem poissonWeight_hasSum (s : ℝ) : HasSum (poissonWeight s) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp s).mul_left (Real.exp (-s))
  have he : NormedSpace.exp s = Real.exp s := congr_fun Real.exp_eq_exp_ℝ.symm s
  simpa only [poissonWeight, he, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using h

section Heat
variable {V : Type*} [AddCommGroup V]

/-- Continuous-time heat is a Poisson mixture of actual nearest-neighbor walks. -/
def heat (ex ey : V) (s : ℝ) (f : V → ℝ) (p : V) : ℝ :=
  ∑' k : ℕ, poissonWeight s k * walk ex ey f k p

theorem heat_series_summable (ex ey : V) (s : ℝ) (hs : 0 ≤ s)
    (f : V → ℝ) (M : ℝ) (hf : ∀ p, |f p| ≤ M) (p : V) :
    Summable (fun k => poissonWeight s k * walk ex ey f k p) := by
  apply ((poissonWeight_hasSum s).mul_right M).summable.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonWeight_nonneg s hs k)]
  exact mul_le_mul_of_nonneg_left (walk_bound ex ey f M hf k p) (poissonWeight_nonneg s hs k)

/-- Maximum principle for the actual infinite-series evolution. -/
theorem heat_bound (ex ey : V) (s : ℝ) (hs : 0 ≤ s)
    (f : V → ℝ) (M : ℝ) (hf : ∀ p, |f p| ≤ M) (p : V) :
    |heat ex ey s f p| ≤ M := by
  have h := tsum_of_norm_bounded (f := fun k => poissonWeight s k * walk ex ey f k p)
    ((poissonWeight_hasSum s).mul_right M) (fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonWeight_nonneg s hs k)]
    exact mul_le_mul_of_nonneg_left (walk_bound ex ey f M hf k p)
      (poissonWeight_nonneg s hs k))
  simpa only [heat, Real.norm_eq_abs, one_mul] using h

theorem heat_nonneg (ex ey : V) (s : ℝ) (hs : 0 ≤ s)
    (f : V → ℝ) (hf : ∀ p, 0 ≤ f p) (p : V) : 0 ≤ heat ex ey s f p := by
  exact tsum_nonneg fun k => mul_nonneg (poissonWeight_nonneg s hs k)
    (walk_nonneg ex ey f hf k p)

theorem heat_constant (ex ey : V) (s c : ℝ) (p : V) :
    heat ex ey s (fun _ => c) p = c := by
  simp only [heat, walk_constant]
  simpa only [one_mul] using ((poissonWeight_hasSum s).mul_right c).tsum_eq

theorem heat_zero (ex ey : V) (f : V → ℝ) (p : V) : heat ex ey 0 f p = f p := by
  unfold heat
  rw [tsum_eq_single 0]
  · simp [poissonWeight, walk]
  · intro k hk
    simp [poissonWeight, zero_pow hk]

theorem heat_sub (ex ey : V) (s : ℝ) (hs : 0 ≤ s)
    (f g : V → ℝ) (M N : ℝ) (hf : ∀ p, |f p| ≤ M) (hg : ∀ p, |g p| ≤ N) (p : V) :
    heat ex ey s (fun q => f q - g q) p = heat ex ey s f p - heat ex ey s g p := by
  simp only [heat, walk_sub, mul_sub]
  exact Summable.tsum_sub (heat_series_summable ex ey s hs f M hf p)
    (heat_series_summable ex ey s hs g N hg p)

/-- Stability is obtained from the dynamics, with no time-growing constant. -/
theorem heat_initial_data_stability (ex ey : V) (s : ℝ) (hs : 0 ≤ s)
    (f g : V → ℝ) (M N ε : ℝ) (hf : ∀ p, |f p| ≤ M) (hg : ∀ p, |g p| ≤ N)
    (he : ∀ p, |f p - g p| ≤ ε) (p : V) :
    |heat ex ey s f p - heat ex ey s g p| ≤ ε := by
  rw [← heat_sub ex ey s hs f g M N hf hg p]
  exact heat_bound ex ey s hs _ ε he p

theorem heat_translation (ex ey a : V) (s : ℝ) (f : V → ℝ) (p : V) :
    heat ex ey s (fun q => f (q + a)) p = heat ex ey s f (p + a) := by
  simp only [heat, walk_translation]

end Heat

abbrev Grid (n : ℕ) := ZMod n × ZMod n

def gridHeat (n : ℕ) (t : ℝ) (f : Grid n → ℝ) : Grid n → ℝ :=
  heat (1, 0) (0, 1) (4 * (n : ℝ)^2 * t) f

def generator (n : ℕ) (f : Grid n → ℝ) (p : Grid n) : ℝ :=
  (n : ℝ)^2 * (f (p + (1, 0)) + f (p - (1, 0)) +
    f (p + (0, 1)) + f (p - (0, 1)) - 4 * f p)

theorem generator_uniformization (n : ℕ) (f : Grid n → ℝ) (p : Grid n) :
    generator n f p = 4 * (n : ℝ)^2 * (step (1, 0) (0, 1) f p - f p) := by
  dsimp [generator, step]
  ring

theorem gridHeat_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Grid n → ℝ) (M : ℝ) (hf : ∀ p, |f p| ≤ M) (p : Grid n) :
    |gridHeat n t f p| ≤ M :=
  heat_bound (1, 0) (0, 1) _ (by positivity) f M hf p

theorem gridHeat_zero (n : ℕ) (f : Grid n → ℝ) (p : Grid n) :
    gridHeat n 0 f p = f p := by
  simp only [gridHeat, mul_zero, heat_zero]

/-- One coordinate of the actual discrete Fourier eigenvalue. -/
def spectralSymbol (h k : ℝ) : ℝ := 4 * Real.sin (Real.pi * h * k)^2 / h^2

theorem spectralSymbol_lower (h k : ℝ) (hh : 0 < h) (hk : |h * k| ≤ 1 / 2) :
    16 * k^2 ≤ spectralSymbol h k := by
  have ht : |Real.pi * h * k| ≤ Real.pi / 2 := by
    rw [mul_assoc, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hk Real.pi_pos.le]
  have hs := Real.mul_abs_le_abs_sin ht
  have ha : |Real.pi * h * k| = Real.pi * h * |k| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]
  rw [ha] at hs
  have hc : 2 / Real.pi * (Real.pi * h * |k|) = 2 * h * |k| := by
    field_simp
  rw [hc] at hs
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * h * |k|)
    (abs_nonneg (Real.sin (Real.pi * h * k)))).mpr hs
  simp only [mul_pow, sq_abs] at hsq
  unfold spectralSymbol
  apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
  nlinarith

theorem spectralSymbol_upper (h k : ℝ) (hh : 0 < h) :
    spectralSymbol h k ≤ 4 * Real.pi^2 * k^2 := by
  have hs : |Real.sin (Real.pi * h * k)| ≤ |Real.pi * h * k| := Real.abs_sin_le_abs
  have hsq := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hs
  simp only [sq_abs, mul_pow] at hsq
  unfold spectralSymbol
  apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
  nlinarith

/-- The U(1) bridge from real curvature/phase estimates to observable errors. -/
theorem phase_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y)‖ ≤ |x-y| := by
  have hid : Complex.exp (Complex.I * x) - Complex.exp (Complex.I * y) =
      (Complex.exp (Complex.I * (x-y : ℝ)) - 1) * Complex.exp (Complex.I * y) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul]
  have hn : ‖Complex.exp (Complex.I * y)‖ = 1 := by simp [Complex.norm_exp]
  rw [hn, mul_one]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y)

end
end UnifiedTheory.LayerA.AbelianCurvatureHeat
