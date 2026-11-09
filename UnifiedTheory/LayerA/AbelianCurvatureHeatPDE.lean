/-
Termwise differentiation and the heat equation for the existing continuum
Fourier series. Polynomial coefficient bounds are discharged from the original
bounded coefficients and the explicit derivative symbols.
-/
import UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.AbelianCurvatureHeatPDE
noncomputable section
open UnifiedTheory.LayerA.AbelianCurvatureHeatContinuum
open Filter Set
open scoped Topology

def xSymbol (k : ℤ × ℤ) : ℂ := Complex.I * (2 * Real.pi * (k.1 : ℝ))
def ySymbol (k : ℤ × ℤ) : ℂ := Complex.I * (2 * Real.pi * (k.2 : ℝ))
def xCoeff (c : ℤ × ℤ → ℂ) (k : ℤ × ℤ) : ℂ := xSymbol k * c k
def yCoeff (c : ℤ × ℤ → ℂ) (k : ℤ × ℤ) : ℂ := ySymbol k * c k
def timeCoeff (c : ℤ × ℤ → ℂ) (k : ℤ × ℤ) : ℂ := -(continuumEigenvalue k : ℂ) * c k

theorem radiusSq_nonneg (k : ℤ × ℤ) : 0 ≤ radiusSq k := by
  unfold radiusSq; positivity

theorem radiusOne_nonneg (k : ℤ × ℤ) : 0 ≤ radiusOne k := by
  unfold radiusOne; positivity

theorem radiusSq_le_radiusOne_sq (k : ℤ × ℤ) : radiusSq k ≤ radiusOne k ^ 2 := by
  unfold radiusSq radiusOne
  nlinarith [sq_abs (k.1 : ℝ), sq_abs (k.2 : ℝ),
    mul_nonneg (abs_nonneg (k.1 : ℝ)) (abs_nonneg (k.2 : ℝ))]

theorem xSymbol_norm_le (k : ℤ × ℤ) : ‖xSymbol k‖ ≤ (2 * Real.pi) * radiusOne k := by
  simp only [xSymbol, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, abs_of_pos Real.pi_pos]
  norm_num only [Complex.norm_ofNat]
  unfold radiusOne
  nlinarith [Real.pi_pos, abs_nonneg (k.2 : ℝ)]

theorem ySymbol_norm_le (k : ℤ × ℤ) : ‖ySymbol k‖ ≤ (2 * Real.pi) * radiusOne k := by
  simp only [ySymbol, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    one_mul, abs_of_pos Real.pi_pos]
  norm_num only [Complex.norm_ofNat]
  unfold radiusOne
  nlinarith [Real.pi_pos, abs_nonneg (k.1 : ℝ)]

theorem symbolCoeff_bound (c σ : ℤ × ℤ → ℂ) (M B : ℝ) (q r : ℕ)
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q)
    (hσ : ∀ k, ‖σ k‖ ≤ B * radiusOne k ^ r) (k : ℤ × ℤ) :
    ‖σ k * c k‖ ≤ (B*M) * radiusOne k^(q + r) := by
  rw [norm_mul]
  calc
    _ ≤ (B * radiusOne k ^ r) * (M * radiusOne k ^ q) :=
      mul_le_mul (hσ k) (hc k) (norm_nonneg _)
        (mul_nonneg hB (pow_nonneg (radiusOne_nonneg k) r))
    _ = _ := by rw [pow_add]; ring

theorem xCoeff_bound (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (k : ℤ × ℤ) :
    ‖xCoeff c k‖ ≤ (2 * Real.pi * M) * radiusOne k^(q + 1) := by
  exact symbolCoeff_bound c xSymbol M (2 * Real.pi) q 1 hM (by positivity) hc
    (by simpa using xSymbol_norm_le) k

theorem yCoeff_bound (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (k : ℤ × ℤ) :
    ‖yCoeff c k‖ ≤ (2 * Real.pi * M) * radiusOne k^(q + 1) := by
  exact symbolCoeff_bound c ySymbol M (2 * Real.pi) q 1 hM (by positivity) hc
    (by simpa using ySymbol_norm_le) k

theorem timeCoeff_bound (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (k : ℤ × ℤ) :
    ‖timeCoeff c k‖ ≤ (4 * Real.pi^2 * M) * radiusOne k^(q + 2) := by
  apply symbolCoeff_bound c (fun k => -(continuumEigenvalue k : ℂ)) M
    (4 * Real.pi^2) q 2 hM (by positivity) hc _ k
  intro j
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ continuumEigenvalue j by
      unfold continuumEigenvalue; exact mul_nonneg (by positivity) (radiusSq_nonneg j))]
  exact mul_le_mul_of_nonneg_left (radiusSq_le_radiusOne_sq j) (by positivity)

theorem mode_bound (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t₀ t : ℝ) (ht₀ : 0 ≤ t₀)
    (ht : t₀ ≤ t) (k : ℤ × ℤ) (z : ℝ × ℝ) :
    ‖c k * (continuumMultiplier t k : ℂ) * planeWave k z‖ ≤
      M * (radiusOne k ^ q * Real.exp (-(16 * t₀) * radiusSq k)) := by
  rw [norm_mul, planeWave_norm, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb : |continuumMultiplier t k| ≤ Real.exp (-(16 * t₀) * radiusSq k) := by
    apply (continuumMultiplier_bound t (ht₀.trans ht) k).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right ht (radiusSq_nonneg k)]
  have hp := mul_le_mul (hc k) hb (abs_nonneg _)
    (mul_nonneg hM (pow_nonneg (radiusOne_nonneg k) q))
  nlinarith [hp]

theorem polynomial_series_summable (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ)
    (hM : 0 ≤ M) (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q)
    (t : ℝ) (ht : 0 < t) (z : ℝ × ℝ) :
    Summable (fun k => c k * (continuumMultiplier t k : ℂ) * planeWave k z) := by
  exact ((gaussian_moment (16 * t) (by positivity) q).mul_left M).of_norm_bounded
    (fun k => mode_bound c M q hM hc t t ht.le le_rfl k z)

theorem planeWave_dx (k : ℤ × ℤ) (x y : ℝ) :
    HasDerivAt (fun u => planeWave k (u, y)) (xSymbol k * planeWave k (x, y)) x := by
  have hr := (((hasDerivAt_id x).const_mul (k.1 : ℝ)).add_const
    ((k.2 : ℝ) * y)).const_mul (2 * Real.pi)
  have he := (hr.ofReal_comp.const_mul Complex.I).cexp
  convert he using 1 <;> simp [planeWave, xSymbol, mul_comm, mul_left_comm, mul_assoc]

theorem planeWave_dy (k : ℤ × ℤ) (x y : ℝ) :
    HasDerivAt (fun u => planeWave k (x, u)) (ySymbol k * planeWave k (x, y)) y := by
  have hr := (((hasDerivAt_id y).const_mul (k.2 : ℝ)).const_add
    ((k.1 : ℝ) * x)).const_mul (2 * Real.pi)
  have he := (hr.ofReal_comp.const_mul Complex.I).cexp
  convert he using 1 <;> simp [planeWave, ySymbol, mul_comm, mul_left_comm, mul_assoc]

theorem mode_dt (c : ℤ × ℤ → ℂ) (k : ℤ × ℤ) (t : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun s => c k * (continuumMultiplier s k : ℂ) * planeWave k z)
      (timeCoeff c k * (continuumMultiplier t k : ℂ) * planeWave k z) t := by
  have he := (((hasDerivAt_id t).const_mul (-continuumEigenvalue k)).exp.ofReal_comp.const_mul
    (c k)).mul_const (planeWave k z)
  convert he using 1 <;>
    simp [continuumMultiplier, timeCoeff, mul_comm, mul_left_comm, mul_assoc]

theorem series_dx (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u => continuumSeries c t (u, y))
      (continuumSeries (xCoeff c) t (x, y)) x := by
  unfold continuumSeries
  apply hasDerivAt_tsum
    (g := fun k u => c k * (continuumMultiplier t k : ℂ) * planeWave k (u, y))
    (g' := fun k u => xCoeff c k * (continuumMultiplier t k : ℂ) * planeWave k (u, y))
    (y₀ := x)
    ((gaussian_moment (16 * t) (by positivity) (q + 1)).mul_left (2 * Real.pi * M))
  · intro k u
    convert (planeWave_dx k u y).const_mul (c k * (continuumMultiplier t k : ℂ)) using 1
    unfold xCoeff
    ring
  · intro k u
    exact mode_bound (xCoeff c) (2 * Real.pi * M) (q + 1) (by positivity)
      (xCoeff_bound c M q hM hc) t t ht.le le_rfl k (u, y)
  · exact polynomial_series_summable c M q hM hc t ht (x, y)

theorem series_dy (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u => continuumSeries c t (x, u))
      (continuumSeries (yCoeff c) t (x, y)) y := by
  unfold continuumSeries
  apply hasDerivAt_tsum
    (g := fun k u => c k * (continuumMultiplier t k : ℂ) * planeWave k (x, u))
    (g' := fun k u => yCoeff c k * (continuumMultiplier t k : ℂ) * planeWave k (x, u))
    (y₀ := y)
    ((gaussian_moment (16 * t) (by positivity) (q + 1)).mul_left (2 * Real.pi * M))
  · intro k u
    convert (planeWave_dy k x u).const_mul (c k * (continuumMultiplier t k : ℂ)) using 1
    unfold yCoeff
    ring
  · intro k u
    exact mode_bound (yCoeff c) (2 * Real.pi * M) (q + 1) (by positivity)
      (yCoeff_bound c M q hM hc) t t ht.le le_rfl k (x, u)
  · exact polynomial_series_summable c M q hM hc t ht (x, y)

theorem series_dt (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (z : ℝ × ℝ) :
    HasDerivAt (fun s => continuumSeries c s z) (continuumSeries (timeCoeff c) t z) t := by
  unfold continuumSeries
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun k s => c k * (continuumMultiplier s k : ℂ) * planeWave k z)
    (g' := fun k s => timeCoeff c k * (continuumMultiplier s k : ℂ) * planeWave k z)
    (y₀ := t)
    ((gaussian_moment (16 * (t / 2)) (by positivity) (q + 2)).mul_left (4 * Real.pi^2 * M))
    (t := Ioi (t / 2)) isOpen_Ioi isPreconnected_Ioi
  · intro k s _
    exact mode_dt c k s z
  · intro k s hs
    exact mode_bound (timeCoeff c) (4 * Real.pi^2 * M) (q + 2) (by positivity)
      (timeCoeff_bound c M q hM hc) (t / 2) s (by positivity) hs.le k z
  · exact (show t / 2 < t by linarith)
  · exact polynomial_series_summable c M q hM hc t ht z
  · exact (show t / 2 < t by linarith)

theorem timeCoeff_eq_laplacian (c : ℤ × ℤ → ℂ) :
    timeCoeff c = fun k => xCoeff (xCoeff c) k + yCoeff (yCoeff c) k := by
  funext k
  unfold timeCoeff xCoeff yCoeff xSymbol ySymbol continuumEigenvalue radiusSq
  push_cast
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

theorem series_laplacian (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (z : ℝ × ℝ) :
    continuumSeries (timeCoeff c) t z =
      continuumSeries (xCoeff (xCoeff c)) t z + continuumSeries (yCoeff (yCoeff c)) t z := by
  have hx := xCoeff_bound (xCoeff c) (2 * Real.pi * M) (q + 1) (by positivity)
    (xCoeff_bound c M q hM hc)
  have hy := yCoeff_bound (yCoeff c) (2 * Real.pi * M) (q + 1) (by positivity)
    (yCoeff_bound c M q hM hc)
  rw [timeCoeff_eq_laplacian]
  simp only [continuumSeries, add_mul]
  exact (polynomial_series_summable _ _ _ (by positivity) hx t ht z).tsum_add
    (polynomial_series_summable _ _ _ (by positivity) hy t ht z)

/-- The actual positive-time Fourier series solves the two-dimensional heat PDE. -/
theorem continuum_heat_equation (c : ℤ × ℤ → ℂ) (M : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    deriv (fun s => continuumSeries c s (x, y)) t =
      deriv (fun u => deriv (fun v => continuumSeries c t (v, y)) u) x +
      deriv (fun u => deriv (fun v => continuumSeries c t (x, v)) u) y := by
  have hM : 0 ≤ M := (norm_nonneg (c (0, 0))).trans (hc (0, 0))
  have hc₀ : ∀ k, ‖c k‖ ≤ M * radiusOne k^0 := by simpa using hc
  have hdx : (fun u => deriv (fun v => continuumSeries c t (v, y)) u) =
      (fun u => continuumSeries (xCoeff c) t (u, y)) :=
    funext fun u => (series_dx c M 0 hM hc₀ t ht u y).deriv
  have hdy : (fun u => deriv (fun v => continuumSeries c t (x, v)) u) =
      (fun u => continuumSeries (yCoeff c) t (x, u)) :=
    funext fun u => (series_dy c M 0 hM hc₀ t ht x u).deriv
  rw [hdx, hdy, (series_dt c M 0 hM hc₀ t ht (x, y)).deriv,
    (series_dx (xCoeff c) (2 * Real.pi * M) 1 (by positivity)
      (xCoeff_bound c M 0 hM hc₀) t ht x y).deriv,
    (series_dy (yCoeff c) (2 * Real.pi * M) 1 (by positivity)
      (yCoeff_bound c M 0 hM hc₀) t ht x y).deriv]
  exact series_laplacian c M 0 hM hc₀ t ht (x, y)

def realHeat (c : ℤ × ℤ → ℂ) (t : ℝ) (z : ℝ × ℝ) : ℝ :=
  (continuumSeries c t z).re

theorem real_series_dx (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u => realHeat c t (u, y)) (realHeat (xCoeff c) t (x, y)) x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (series_dx c M q hM hc t ht x y)

theorem real_series_dy (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun u => realHeat c t (x, u)) (realHeat (yCoeff c) t (x, y)) y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (series_dy c M q hM hc t ht x y)

theorem real_series_dt (c : ℤ × ℤ → ℂ) (M : ℝ) (q : ℕ) (hM : 0 ≤ M)
    (hc : ∀ k, ‖c k‖ ≤ M * radiusOne k ^ q) (t : ℝ) (ht : 0 < t) (z : ℝ × ℝ) :
    HasDerivAt (fun s => realHeat c s z) (realHeat (timeCoeff c) t z) t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (series_dt c M q hM hc t ht z)

theorem real_heat_equation (c : ℤ × ℤ → ℂ) (M : ℝ)
    (hc : ∀ k, ‖c k‖ ≤ M) (t : ℝ) (ht : 0 < t) (x y : ℝ) :
    deriv (fun s => realHeat c s (x, y)) t =
      deriv (fun u => deriv (fun v => realHeat c t (v, y)) u) x +
      deriv (fun u => deriv (fun v => realHeat c t (x, v)) u) y := by
  have hM : 0 ≤ M := (norm_nonneg (c (0, 0))).trans (hc (0, 0))
  have hc₀ : ∀ k, ‖c k‖ ≤ M * radiusOne k^0 := by simpa using hc
  have hdx : (fun u => deriv (fun v => realHeat c t (v, y)) u) =
      (fun u => realHeat (xCoeff c) t (u, y)) :=
    funext fun u => (real_series_dx c M 0 hM hc₀ t ht u y).deriv
  have hdy : (fun u => deriv (fun v => realHeat c t (x, v)) u) =
      (fun u => realHeat (yCoeff c) t (x, u)) :=
    funext fun u => (real_series_dy c M 0 hM hc₀ t ht x u).deriv
  rw [hdx, hdy, (real_series_dt c M 0 hM hc₀ t ht (x, y)).deriv,
    (real_series_dx (xCoeff c) (2 * Real.pi * M) 1 (by positivity)
      (xCoeff_bound c M 0 hM hc₀) t ht x y).deriv,
    (real_series_dy (yCoeff c) (2 * Real.pi * M) 1 (by positivity)
      (yCoeff_bound c M 0 hM hc₀) t ht x y).deriv]
  exact congrArg Complex.re (series_laplacian c M 0 hM hc₀ t ht (x, y))

end
end UnifiedTheory.LayerA.AbelianCurvatureHeatPDE
