/- Quantitative stability of the twisted flat classification, with constants that do not
depend on the cutoff. Discrete Stokes with errors bounds the failure of the winding
relations by the sum of plaquette defects on a sheet. Cauchy-Schwarz and averaging over
parallel sheets then give a bound by the square root of the total twisted action.
This is classical geometry of the action. It is not a measure estimate. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-- The chord distance between unit quaternions. -/
def d (g h : Q) : ℝ := ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖

theorem d_nonneg (g h : Q) : 0 ≤ d g h := norm_nonneg _

theorem norm_coe (g : Q) : ‖(g : ℍ[ℝ])‖ = 1 := by
  have h : ‖(g : ℍ[ℝ])‖ * ‖(g : ℍ[ℝ])‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    exact unit_normSq g
  nlinarith [norm_nonneg (g : ℍ[ℝ]), sq_nonneg (‖(g : ℍ[ℝ])‖ - 1)]

theorem d_mul_left (k g h : Q) : d (k * g) (k * h) = d g h := by
  unfold d
  change ‖(k : ℍ[ℝ]) * g - (k : ℍ[ℝ]) * h‖ = _
  rw [← mul_sub, norm_mul, norm_coe, one_mul]

theorem d_mul_right (k g h : Q) : d (g * k) (h * k) = d g h := by
  unfold d
  change ‖(g : ℍ[ℝ]) * k - (h : ℍ[ℝ]) * k‖ = _
  rw [← sub_mul, norm_mul, norm_coe, mul_one]

theorem d_triangle (f g h : Q) : d f h ≤ d f g + d g h := by
  unfold d
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

variable {N : ℕ}

/-- Cell condition from a plaquette defect. -/
theorem cell_of_defect (A B C D w : Q) (δ : ℝ) (h : d (A * B * C⁻¹ * D⁻¹) w ≤ δ) :
    d (A * B) (w * (D * C)) ≤ δ := by
  have e := d_mul_right (D * C) (A * B * C⁻¹ * D⁻¹) w
  have hs : A * B * C⁻¹ * D⁻¹ * (D * C) = A * B := by group
  rw [hs] at e
  rwa [e]

variable (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (ε : Vertex N → ℕ) (δ : Vertex N → ℝ)
  (hcell : ∀ y, d (L y μ * L (step N y μ) ν) (ω ^ ε y * (L y ν * L (step N y ν) μ)) ≤ δ y)

include hcell

/-- Stokes with errors along a strip. -/
theorem strip_error (x : Vertex N) (a : ℕ) :
    d (run L μ x a * L (walk μ x a) ν)
        (ω ^ (∑ i ∈ Finset.range a, ε (walk μ x i)) * (L x ν * run L μ (step N x ν) a)) ≤
      ∑ i ∈ Finset.range a, δ (walk μ x i) := by
  have hpow (k : ℕ) (g : Q) : Commute (ω ^ k) g := (ω_commute g).pow_left k
  induction a with
  | zero =>
    simp [run, walk_zero, d]
  | succ a ih =>
    have hw : walk μ (step N x ν) a = step N (walk μ x a) ν := by
      simp only [walk, step]
      abel
    rw [walk_succ μ x a, Finset.sum_range_succ, Finset.sum_range_succ, pow_add]
    simp only [run]
    rw [hw]
    set y := walk μ x a with hy
    set R := run L μ x a
    set F := run L μ (step N x ν) a
    set T := ω ^ (∑ i ∈ Finset.range a, ε (walk μ x i))
    set t := ω ^ ε y
    have e1 : R * L y μ * L (step N y μ) ν = R * (L y μ * L (step N y μ) ν) := mul_assoc _ _ _
    have s1 : d (R * (L y μ * L (step N y μ) ν)) (R * (t * (L y ν * L (step N y ν) μ))) ≤ δ y := by
      rw [d_mul_left]
      exact hcell y
    have e2 : R * (t * (L y ν * L (step N y ν) μ)) =
        t * ((R * L y ν) * L (step N y ν) μ) := by
      rw [← mul_assoc R t, ← (hpow _ _).eq]
      simp only [mul_assoc]
      rfl
    have s2 : d (t * ((R * L y ν) * L (step N y ν) μ))
        (t * ((T * (L x ν * F)) * L (step N y ν) μ)) ≤
        ∑ i ∈ Finset.range a, δ (walk μ x i) := by
      rw [d_mul_left, d_mul_right]
      exact ih
    have e3 : t * ((T * (L x ν * F)) * L (step N y ν) μ) =
        T * t * (L x ν * (F * L (step N y ν) μ)) := by
      simp only [mul_assoc]
      rw [← mul_assoc, (hpow _ _).eq, mul_assoc]
    rw [e1]
    rw [e2] at s1
    rw [e3] at s2
    linarith [d_triangle (R * (L y μ * L (step N y μ) ν))
      (t * ((R * L y ν) * L (step N y ν) μ)) (T * t * (L x ν * (F * L (step N y ν) μ)))]

/-- Stokes with errors on a rectangle. -/
theorem rectangle_error (x : Vertex N) (a b : ℕ) :
    d (run L μ x a * run L ν (walk μ x a) b)
        (ω ^ (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, ε (walk μ (walk ν x j) i)) *
          (run L ν x b * run L μ (walk ν x b) a)) ≤
      ∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, δ (walk μ (walk ν x j) i) := by
  have hpow (k : ℕ) (g : Q) : Commute (ω ^ k) g := (ω_commute g).pow_left k
  induction b with
  | zero => simp [run, walk_zero, d]
  | succ b ih =>
    have hs := strip_error L μ ν ε δ hcell (walk ν x b) a
    rw [Finset.sum_range_succ, Finset.sum_range_succ, pow_add, walk_succ ν x b]
    simp only [run]
    rw [walk_comm μ ν x a b]
    set R := run L μ x a
    set V := run L ν (walk μ x a) b
    set V₀ := run L ν x b
    set H := run L μ (walk ν x b) a
    set z := walk μ (walk ν x b) a
    set T := ω ^ (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, ε (walk μ (walk ν x j) i))
    set S := ω ^ (∑ i ∈ Finset.range a, ε (walk μ (walk ν x b) i))
    set x' := walk ν x b
    have s1 : d (R * (V * L z ν)) (T * (V₀ * (H * L z ν))) ≤
        ∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, δ (walk μ (walk ν x j) i) := by
      have e1 : R * (V * L z ν) = (R * V) * L z ν := (mul_assoc _ _ _).symm
      have e2 : T * (V₀ * (H * L z ν)) = (T * (V₀ * H)) * L z ν := by simp only [mul_assoc]
      rw [e1, e2, d_mul_right]
      exact ih
    have s2 : d (T * (V₀ * (H * L z ν))) (T * (V₀ * (S * (L x' ν * run L μ (step N x' ν) a)))) ≤
        ∑ i ∈ Finset.range a, δ (walk μ x' i) := by
      rw [d_mul_left, d_mul_left]
      exact hs
    have e3 : T * (V₀ * (S * (L x' ν * run L μ (step N x' ν) a))) =
        T * S * (V₀ * L x' ν * run L μ (step N x' ν) a) := by
      rw [← mul_assoc V₀ S, ← (hpow _ _).eq]
      simp only [mul_assoc]
      rfl
    rw [e3] at s2
    linarith [d_triangle (R * (V * L z ν)) (T * (V₀ * (H * L z ν)))
      (T * S * (V₀ * L x' ν * run L μ (step N x' ν) a))]

/-- Winding relation with errors. -/
theorem winding_error (x : Vertex N) :
    d (run L μ x N * run L ν x N)
        (ω ^ (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ε (walk μ (walk ν x j) i)) *
          (run L ν x N * run L μ x N)) ≤
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, δ (walk μ (walk ν x j) i) := by
  have h := rectangle_error L μ ν ε δ hcell x N N
  rwa [walk_card, walk_card] at h

omit hcell

/-! ### A quantitative form of `central_of_anticommuting` -/

theorem cs4 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ) :
    (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) ^ 2 ≤
      (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by
  nlinarith [sq_nonneg (x0 * y1 - x1 * y0), sq_nonneg (x0 * y2 - x2 * y0),
    sq_nonneg (x0 * y3 - x3 * y0), sq_nonneg (x1 * y2 - x2 * y1),
    sq_nonneg (x1 * y3 - x3 * y1), sq_nonneg (x2 * y3 - x3 * y2)]

/-- The real-variable core: near anticommutation and near commutation force a small
imaginary part. All constants are explicit and free of any lattice size. -/
theorem real_core (a0 a1 a2 a3 b0 b1 b2 b3 v1 v2 v3 q0 ε : ℝ)
    (na : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1) (nb : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 = 1)
    (nq : q0 ^ 2 + v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 1) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (he : (2 * (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3)) ^ 2 + (2 * (a0 * b1 + b0 * a1)) ^ 2 +
      (2 * (a0 * b2 + b0 * a2)) ^ 2 + (2 * (a0 * b3 + b0 * a3)) ^ 2 ≤ ε ^ 2)
    (hf : (2 * (v2 * a3 - v3 * a2)) ^ 2 + (2 * (v3 * a1 - v1 * a3)) ^ 2 +
      (2 * (v1 * a2 - v2 * a1)) ^ 2 ≤ ε ^ 2)
    (hg : (2 * (v2 * b3 - v3 * b2)) ^ 2 + (2 * (v3 * b1 - v1 * b3)) ^ 2 +
      (2 * (v1 * b2 - v2 * b1)) ^ 2 ≤ ε ^ 2) :
    v1 ^ 2 + v2 ^ 2 + v3 ^ 2 ≤ 29 / 9 * ε ^ 2 := by
  set E0 := 2 * (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3) with hE0
  set E1 := 2 * (a0 * b1 + b0 * a1) with hE1
  set E2 := 2 * (a0 * b2 + b0 * a2) with hE2
  set E3 := 2 * (a0 * b3 + b0 * a3) with hE3
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  -- real parts are small
  have hb0 : (2 * b0) ^ 2 ≤ ε ^ 2 := by
    have hid : 2 * b0 = a0 * E0 + a1 * E1 + a2 * E2 + a3 * E3 := by
      rw [hE0, hE1, hE2, hE3]
      linear_combination (-2 * b0) * na
    rw [hid]
    have := cs4 a0 a1 a2 a3 E0 E1 E2 E3
    rw [na, one_mul] at this
    linarith
  have ha0 : (2 * a0) ^ 2 ≤ ε ^ 2 := by
    have hid : 2 * a0 = b0 * E0 + b1 * E1 + b2 * E2 + b3 * E3 := by
      rw [hE0, hE1, hE2, hE3]
      linear_combination (-2 * a0) * nb
    rw [hid]
    have := cs4 b0 b1 b2 b3 E0 E1 E2 E3
    rw [nb, one_mul] at this
    linarith
  have hb0' : 4 * b0 ^ 2 ≤ ε ^ 2 := by linarith only [hb0, mul_pow 2 b0 2, (by norm_num : (2 : ℝ) ^ 2 = 4)]
  have ha0' : 4 * a0 ^ 2 ≤ ε ^ 2 := by linarith only [ha0, mul_pow 2 a0 2, (by norm_num : (2 : ℝ) ^ 2 = 4)]
  have hBv : 3 / 4 ≤ b1 ^ 2 + b2 ^ 2 + b3 ^ 2 := by linarith only [nb, hb0', hε2]
  have hAv : 3 / 4 ≤ a1 ^ 2 + a2 ^ 2 + a3 ^ 2 := by linarith only [na, ha0', hε2]
  have hAle : a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ≤ 1 := by linarith only [na, sq_nonneg a0]
  have hVle : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 ≤ 1 := by linarith only [nq, sq_nonneg q0]
  -- the inner product `s = a · b` is small
  set s := a1 * b1 + a2 * b2 + a3 * b3 with hs
  have hab : (a0 * b0) ^ 2 ≤ ε ^ 4 / 16 := by
    have : (2 * a0) ^ 2 * (2 * b0) ^ 2 ≤ ε ^ 2 * ε ^ 2 :=
      mul_le_mul ha0 hb0 (sq_nonneg _) (sq_nonneg _)
    have e : (2 * a0) ^ 2 * (2 * b0) ^ 2 = 16 * (a0 * b0) ^ 2 := by ring
    have e' : ε ^ 2 * ε ^ 2 = ε ^ 4 := by ring
    linarith only [this, e, e']
  have hE0sq : E0 ^ 2 ≤ ε ^ 2 := by
    linarith only [he, sq_nonneg E1, sq_nonneg E2, sq_nonneg E3]
  have hs2 : s ^ 2 ≤ 9 / 16 * ε ^ 2 := by
    have hse : s = a0 * b0 - E0 / 2 := by
      rw [hE0, hs]
      ring
    have hp : (a0 * b0) ^ 2 ≤ ε ^ 2 / 16 := by
      have : ε ^ 2 * ε ^ 2 ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hε2 (sq_nonneg ε)
      have e' : ε ^ 2 * ε ^ 2 = ε ^ 4 := by ring
      linarith only [this, e', hab]
    rw [hse]
    -- `(x - y)² ≤ 3 x² + (3/2) y²`
    have hq : (a0 * b0 - E0 / 2) ^ 2 ≤ 3 * (a0 * b0) ^ 2 + 3 / 2 * (E0 / 2) ^ 2 := by
      nlinarith only [sq_nonneg (2 * (a0 * b0) + E0 / 2)]
    have he2 : (E0 / 2) ^ 2 = E0 ^ 2 / 4 := by ring
    linarith only [hq, hp, hE0sq, he2]
  -- `w = v · a` is small, using `(v × b) × a = b (v · a) - v (a · b)`
  set w := v1 * a1 + v2 * a2 + v3 * a3 with hw
  set m1 := v2 * b3 - v3 * b2 with hm1
  set m2 := v3 * b1 - v1 * b3 with hm2
  set m3 := v1 * b2 - v2 * b1 with hm3
  have hmsq : m1 ^ 2 + m2 ^ 2 + m3 ^ 2 ≤ ε ^ 2 / 4 := by
    have e : (2 * m1) ^ 2 + (2 * m2) ^ 2 + (2 * m3) ^ 2 = 4 * (m1 ^ 2 + m2 ^ 2 + m3 ^ 2) := by ring
    linarith only [hg, e]
  set c1 := m2 * a3 - m3 * a2 with hc1
  set c2 := m3 * a1 - m1 * a3 with hc2
  set c3 := m1 * a2 - m2 * a1 with hc3
  have hcsq : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ ε ^ 2 / 4 := by
    have hL : c1 ^ 2 + c2 ^ 2 + c3 ^ 2 ≤ (m1 ^ 2 + m2 ^ 2 + m3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) := by
      have e : (m1 ^ 2 + m2 ^ 2 + m3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) =
          c1 ^ 2 + c2 ^ 2 + c3 ^ 2 + (m1 * a1 + m2 * a2 + m3 * a3) ^ 2 := by
        rw [hc1, hc2, hc3]
        ring
      rw [e]
      linarith only [sq_nonneg (m1 * a1 + m2 * a2 + m3 * a3)]
    have : (m1 ^ 2 + m2 ^ 2 + m3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) ≤ (ε ^ 2 / 4) * 1 :=
      mul_le_mul hmsq hAle (by positivity) (by positivity)
    linarith
  have ek1 : b1 * w = c1 + v1 * s := by
    rw [hc1, hm2, hm3, hw, hs]
    ring
  have ek2 : b2 * w = c2 + v2 * s := by
    rw [hc2, hm3, hm1, hw, hs]
    ring
  have ek3 : b3 * w = c3 + v3 * s := by
    rw [hc3, hm1, hm2, hw, hs]
    ring
  have hws : (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * w ^ 2 ≤
      2 * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2) + 2 * ((v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * s ^ 2) := by
    have : (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * w ^ 2 = (b1 * w) ^ 2 + (b2 * w) ^ 2 + (b3 * w) ^ 2 := by ring
    rw [this, ek1, ek2, ek3]
    have e : 2 * (c1 ^ 2 + c2 ^ 2 + c3 ^ 2) + 2 * ((v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * s ^ 2) -
        ((c1 + v1 * s) ^ 2 + (c2 + v2 * s) ^ 2 + (c3 + v3 * s) ^ 2) =
        (c1 - v1 * s) ^ 2 + (c2 - v2 * s) ^ 2 + (c3 - v3 * s) ^ 2 := by ring
    linarith only [e, sq_nonneg (c1 - v1 * s), sq_nonneg (c2 - v2 * s), sq_nonneg (c3 - v3 * s)]
  have hvs : (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * s ^ 2 ≤ 1 * (9 / 16 * ε ^ 2) :=
    mul_le_mul hVle hs2 (sq_nonneg _) (by norm_num)
  have hw2 : w ^ 2 ≤ 13 / 6 * ε ^ 2 := by
    have h3 : (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * w ^ 2 ≤ 13 / 8 * ε ^ 2 := by linarith
    have h4 : 3 / 4 * w ^ 2 ≤ (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) * w ^ 2 :=
      mul_le_mul_of_nonneg_right hBv (sq_nonneg _)
    linarith
  -- Lagrange
  have hlag : (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) =
      (v2 * a3 - v3 * a2) ^ 2 + (v3 * a1 - v1 * a3) ^ 2 + (v1 * a2 - v2 * a1) ^ 2 + w ^ 2 := by
    rw [hw]
    ring
  have hf' : (v2 * a3 - v3 * a2) ^ 2 + (v3 * a1 - v1 * a3) ^ 2 + (v1 * a2 - v2 * a1) ^ 2 ≤
      ε ^ 2 / 4 := by
    have e : (2 * (v2 * a3 - v3 * a2)) ^ 2 + (2 * (v3 * a1 - v1 * a3)) ^ 2 +
        (2 * (v1 * a2 - v2 * a1)) ^ 2 = 4 * ((v2 * a3 - v3 * a2) ^ 2 + (v3 * a1 - v1 * a3) ^ 2 +
        (v1 * a2 - v2 * a1) ^ 2) := by ring
    linarith only [hf, e]
  have hfin : 3 / 4 * (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) ≤
      (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hAv (by positivity : 0 ≤ v1 ^ 2 + v2 ^ 2 + v3 ^ 2)
    linarith only [this]
  rw [hlag] at hfin
  linarith

theorem one_sub_le (r V : ℝ) (h : r ^ 2 = 1 - V) (hV : 0 ≤ V) (hr : 0 ≤ r) : 1 - r ≤ V := by
  nlinarith [sq_nonneg (r - 1)]

/-- Near anticommutation and near commutation force `q` near `±1`, with absolute constant. -/
theorem near_central (a b q : Q) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hab : d (a * b) (ω * (b * a)) ≤ ε) (hqa : d (q * a) (a * q) ≤ ε)
    (hqb : d (q * b) (b * q) ≤ ε) : d q 1 ≤ 8 / 3 * ε ∨ d q ω ≤ 8 / 3 * ε := by
  have sqd (g h : Q) (δ : ℝ) (hg : d g h ≤ δ) : ‖(g : ℍ[ℝ]) - (h : ℍ[ℝ])‖ ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  have toCoord (x : ℍ[ℝ]) : ‖x‖ ^ 2 = x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  have e1 := sqd _ _ _ hab
  have e2 := sqd _ _ _ hqa
  have e3 := sqd _ _ _ hqb
  rw [toCoord] at e1 e2 e3
  have na := unit_normSq a
  have nb := unit_normSq b
  have nq := unit_normSq q
  have hcoe1 : ((a * b : Q) : ℍ[ℝ]) - ((ω * (b * a) : Q) : ℍ[ℝ]) =
      (a : ℍ[ℝ]) * b + (b : ℍ[ℝ]) * a := by
    change (a : ℍ[ℝ]) * b - (-1) * ((b : ℍ[ℝ]) * a) = _
    simp
  have hcoe2 : ((q * a : Q) : ℍ[ℝ]) - ((a * q : Q) : ℍ[ℝ]) = (q : ℍ[ℝ]) * a - (a : ℍ[ℝ]) * q := rfl
  have hcoe3 : ((q * b : Q) : ℍ[ℝ]) - ((b * q : Q) : ℍ[ℝ]) = (q : ℍ[ℝ]) * b - (b : ℍ[ℝ]) * q := rfl
  rw [hcoe1] at e1
  rw [hcoe2] at e2
  rw [hcoe3] at e3
  simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] at e1 e2 e3
  generalize (a : ℍ[ℝ]) = A at *
  generalize (b : ℍ[ℝ]) = B at *
  have hv := real_core A.re A.imI A.imJ A.imK B.re B.imI B.imJ B.imK
    (q : ℍ[ℝ]).imI (q : ℍ[ℝ]).imJ (q : ℍ[ℝ]).imK (q : ℍ[ℝ]).re ε na nb
    (by linarith only [nq]) h0 h1 (by linarith only [e1]) (by linarith only [e2])
    (by linarith only [e3])
  set V := (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 with hV
  have hq0 : (q : ℍ[ℝ]).re ^ 2 = 1 - V := by rw [hV]; linarith only [nq]
  have hbound : 2 * V ≤ (8 / 3 * ε) ^ 2 := by
    have e : (8 / 3 * ε) ^ 2 = 64 / 9 * ε ^ 2 := by ring
    linarith only [hv, e, sq_nonneg ε]
  have hV0 : 0 ≤ V := by positivity
  have hd1 : d q 1 ^ 2 = 2 - 2 * (q : ℍ[ℝ]).re := by
    unfold d
    rw [toCoord]
    change ((q : ℍ[ℝ]) - 1).re ^ 2 + ((q : ℍ[ℝ]) - 1).imI ^ 2 + ((q : ℍ[ℝ]) - 1).imJ ^ 2 +
      ((q : ℍ[ℝ]) - 1).imK ^ 2 = _
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    linear_combination nq
  have hdω : d q ω ^ 2 = 2 + 2 * (q : ℍ[ℝ]).re := by
    unfold d
    rw [toCoord, ω_coe]
    simp only [sub_neg_eq_add, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one]
    linear_combination nq
  have hK : 0 ≤ 8 / 3 * ε := by positivity
  by_cases hs : 0 ≤ (q : ℍ[ℝ]).re
  · left
    have hle : 1 - (q : ℍ[ℝ]).re ≤ V := one_sub_le _ V hq0 hV0 hs
    exact abs_le_of_sq_le_sq' (by rw [hd1]; linarith only [hle, hbound]) hK |>.2
  · right
    push_neg at hs
    have hle : 1 + (q : ℍ[ℝ]).re ≤ V := by
      have := one_sub_le (-(q : ℍ[ℝ]).re) V (by rw [neg_sq]; exact hq0) hV0 (by linarith only [hs])
      linarith only [this]
    exact abs_le_of_sq_le_sq' (by rw [hdω]; linarith only [hle, hbound]) hK |>.2

/-! ### From the total twisted action to the winding relations -/

theorem d_comm (g h : Q) : d g h = d h g := by
  unfold d
  exact norm_sub_rev _ _

/-- The plaquette defect relative to the twist. -/
def defect (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (y : Vertex N) : ℝ :=
  d (L y μ * L (step N y μ) ν * (L (step N y ν) μ)⁻¹ * (L y ν)⁻¹) (ω ^ twistExp μ ν y)

theorem defect_nonneg (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (y : Vertex N) :
    0 ≤ defect L μ ν y := d_nonneg _ _

/-- The defect squared on one sheet through `x`. -/
def sheet (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) : ℝ :=
  ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, defect L μ ν (walk μ (walk ν x j) i) ^ 2

theorem sheet_nonneg (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) :
    0 ≤ sheet L μ ν x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Cauchy-Schwarz on a sheet. -/
theorem sum_defect_le (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, defect L μ ν (walk μ (walk ν x j) i)) ^ 2 ≤
      (N : ℝ) ^ 2 * sheet L μ ν x := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N ×ˢ Finset.range N)
    (f := fun p : ℕ × ℕ => defect L μ ν (walk μ (walk ν x p.1) p.2))
  rw [Finset.sum_product, Finset.sum_product, Finset.card_product, Finset.card_range] at h
  unfold sheet
  push_cast at h
  calc _ ≤ ((N : ℝ) * N) * _ := h
    _ = _ := by ring

variable [NeZero N]

theorem sum_translate (f : Vertex N → ℝ) (c : Vertex N) : ∑ x, f (x + c) = ∑ y, f y :=
  Equiv.sum_comp (Equiv.addRight c) f

/-- Averaging over parallel sheets. -/
theorem sum_sheet (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) :
    ∑ x, sheet L μ ν x = (N : ℝ) ^ 2 * ∑ y, defect L μ ν y ^ 2 := by
  unfold sheet
  rw [Finset.sum_comm]
  have hin (j : ℕ) : ∑ x, ∑ i ∈ Finset.range N, defect L μ ν (walk μ (walk ν x j) i) ^ 2 =
      (N : ℝ) * ∑ y, defect L μ ν y ^ 2 := by
    rw [Finset.sum_comm]
    have hk (i : ℕ) : ∑ x, defect L μ ν (walk μ (walk ν x j) i) ^ 2 = ∑ y, defect L μ ν y ^ 2 := by
      have hw (x : Vertex N) : walk μ (walk ν x j) i =
          x + (j • (Pi.single ν 1 : Vertex N) + i • (Pi.single μ 1 : Vertex N)) := by
        simp only [walk]
        abel
      simp only [hw]
      exact sum_translate (fun y => defect L μ ν y ^ 2) _
    simp only [hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem card_vertex : (Fintype.card (Vertex N) : ℝ) = (N : ℝ) ^ 4 := by
  simp [ZMod.card]

/-- Some base point has its five relevant sheets all small, with no factor of `N`. -/
theorem exists_good_base (L : Vertex N → Fin 4 → Q) (S : ℝ)
    (hS : ∑ y, (defect L 1 2 y ^ 2 + defect L 1 3 y ^ 2 + defect L 2 3 y ^ 2 +
      defect L 0 1 y ^ 2 + defect L 0 2 y ^ 2) ≤ S) :
    ∃ x, (N : ℝ) ^ 2 * (sheet L 1 2 x + sheet L 1 3 x + sheet L 2 3 x + sheet L 0 1 x +
      sheet L 0 2 x) ≤ S := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hsum : ∑ x, ((N : ℝ) ^ 2 * (sheet L 1 2 x + sheet L 1 3 x + sheet L 2 3 x + sheet L 0 1 x +
      sheet L 0 2 x)) ≤ ∑ _x : Vertex N, S := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, sum_sheet, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_vertex]
    simp only [Finset.sum_add_distrib] at hS
    have : (N : ℝ) ^ 4 * (∑ y, defect L 1 2 y ^ 2 + ∑ y, defect L 1 3 y ^ 2 +
        ∑ y, defect L 2 3 y ^ 2 + ∑ y, defect L 0 1 y ^ 2 + ∑ y, defect L 0 2 y ^ 2) ≤
        (N : ℝ) ^ 4 * S := mul_le_mul_of_nonneg_left hS (by positivity)
    nlinarith only [this]
  obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨x, hx⟩

/-- A winding relation bounded by the square root of the action, with no `N`. -/
theorem winding_le_sqrt (L : Vertex N → Fin 4 → Q) (μ ν : Fin 4) (x : Vertex N) (S : ℝ)
    (hs : (N : ℝ) ^ 2 * sheet L μ ν x ≤ S) :
    d (run L μ x N * run L ν x N)
        (ω ^ (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, twistExp μ ν (walk μ (walk ν x j) i)) *
          (run L ν x N * run L μ x N)) ≤ Real.sqrt S := by
  refine (winding_error L μ ν (twistExp μ ν) (defect L μ ν) (fun y => ?_) x).trans ?_
  · exact cell_of_defect _ _ _ _ _ _ le_rfl
  · apply Real.le_sqrt_of_sq_le
    exact (sum_defect_le L μ ν x).trans hs

theorem exp_sum_zero (μ ν : Fin 4) (h : ¬ (μ = 1 ∧ ν = 2)) (x : Vertex N) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, twistExp μ ν (walk μ (walk ν x j) i)) = 0 := by
  have hz : ∀ y : Vertex N, twistExp μ ν y = 0 := by
    intro y
    unfold twistExp
    rw [if_neg]
    tauto
  simp [hz]

/-- **Scale-invariant stability.** For a link field with total defect at most `S ≤ 1`, some base
point has nearly anticommuting `W₁, W₂`, and `W₀, W₃` within `(8/3) √S` of `±1`. -/
theorem holonomy_stability (L : Vertex N → Fin 4 → Q) (S : ℝ) (hS1 : S ≤ 1)
    (hS : ∑ y, (defect L 1 2 y ^ 2 + defect L 1 3 y ^ 2 + defect L 2 3 y ^ 2 +
      defect L 0 1 y ^ 2 + defect L 0 2 y ^ 2) ≤ S) :
    ∃ x, d (wind L 1 x * wind L 2 x) (ω * (wind L 2 x * wind L 1 x)) ≤ Real.sqrt S ∧
      (d (wind L 3 x) 1 ≤ 8 / 3 * Real.sqrt S ∨ d (wind L 3 x) ω ≤ 8 / 3 * Real.sqrt S) ∧
      (d (wind L 0 x) 1 ≤ 8 / 3 * Real.sqrt S ∨ d (wind L 0 x) ω ≤ 8 / 3 * Real.sqrt S) := by
  obtain ⟨x, hx⟩ := exists_good_base L S hS
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have one (μ ν : Fin 4) (hle : sheet L μ ν x ≤ sheet L 1 2 x + sheet L 1 3 x + sheet L 2 3 x +
      sheet L 0 1 x + sheet L 0 2 x) : (N : ℝ) ^ 2 * sheet L μ ν x ≤ S :=
    (mul_le_mul_of_nonneg_left hle hN2).trans hx
  have n12 := sheet_nonneg L 1 2 x
  have n13 := sheet_nonneg L 1 3 x
  have n23 := sheet_nonneg L 2 3 x
  have n01 := sheet_nonneg L 0 1 x
  have n02 := sheet_nonneg L 0 2 x
  have h12 := winding_le_sqrt L 1 2 x S (one 1 2 (by linarith))
  have h13 := winding_le_sqrt L 1 3 x S (one 1 3 (by linarith))
  have h23 := winding_le_sqrt L 2 3 x S (one 2 3 (by linarith))
  have h01 := winding_le_sqrt L 0 1 x S (one 0 1 (by linarith))
  have h02 := winding_le_sqrt L 0 2 x S (one 0 2 (by linarith))
  rw [twist_total, pow_one] at h12
  rw [exp_sum_zero 1 3 (by decide), pow_zero, one_mul] at h13
  rw [exp_sum_zero 2 3 (by decide), pow_zero, one_mul] at h23
  rw [exp_sum_zero 0 1 (by decide), pow_zero, one_mul] at h01
  rw [exp_sum_zero 0 2 (by decide), pow_zero, one_mul] at h02
  have hε0 := Real.sqrt_nonneg S
  have hε1 : Real.sqrt S ≤ 1 := by
    have := Real.sqrt_le_sqrt hS1
    rwa [Real.sqrt_one] at this
  refine ⟨x, h12, ?_, ?_⟩
  · exact near_central _ _ _ _ hε0 hε1 h12 (by rw [d_comm]; exact h13) (by rw [d_comm]; exact h23)
  · exact near_central _ _ _ _ hε0 hε1 h12 h01 h02

/-! ### The actual twisted action -/

open TwistedReflection PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

/-- Each plaquette term of the actual twisted action is exactly the squared defect. -/
theorem term_eq_defect_sq (n : ℕ) [NeZero n] (U : Configuration (Vertex (2 * n)) Q)
    (x : Vertex (2 * n)) (μ ν : Fin 4) (h : μ < ν) :
    term n Q (spatialTwist n) character 2 U (x, ⟨(μ, ν), h⟩) =
      defect (linkValue (2 * n) Q U) μ ν x ^ 2 := by
  unfold term defect d
  rw [spatialTwist_eq, character_re]
  change 2 - _ * (2 * ((plaquetteProduct (2 * n) Q U x μ ν : Q) : ℍ[ℝ]).re) =
    ‖((plaquetteProduct (2 * n) Q U x μ ν : Q) : ℍ[ℝ]) - ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ])‖ ^ 2
  generalize plaquetteProduct (2 * n) Q U x μ ν = P
  have hn := unit_normSq P
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  rcases (by unfold twistExp; split_ifs <;> simp : twistExp μ ν x = 0 ∨ twistExp μ ν x = 1)
    with hc | hc
  · rw [hc]
    simp only [pow_zero, zero_ne_one, if_false]
    change _ = (((P : ℍ[ℝ]) - 1).re) ^ 2 + (((P : ℍ[ℝ]) - 1).imI) ^ 2 + (((P : ℍ[ℝ]) - 1).imJ) ^ 2 +
      (((P : ℍ[ℝ]) - 1).imK) ^ 2
    simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
      Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    linear_combination -hn
  · rw [hc]
    simp only [if_true, pow_one, ω_coe]
    simp only [sub_neg_eq_add, Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
      Quaternion.imK_one]
    linear_combination -hn

theorem five_planes_le_action (n : ℕ) [NeZero n] (U : Configuration (Vertex (2 * n)) Q) :
    ∑ y, (defect (linkValue (2 * n) Q U) 1 2 y ^ 2 + defect (linkValue (2 * n) Q U) 1 3 y ^ 2 +
      defect (linkValue (2 * n) Q U) 2 3 y ^ 2 + defect (linkValue (2 * n) Q U) 0 1 y ^ 2 +
      defect (linkValue (2 * n) Q U) 0 2 y ^ 2) ≤
      action n Q (spatialTwist n) character 1 2 U := by
  unfold action
  rw [one_mul, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun y _ => ?_
  have hmem (μ ν : Fin 4) (h : μ < ν) : (⟨(μ, ν), h⟩ : Plane) ∈ (Finset.univ : Finset Plane) :=
    Finset.mem_univ _
  let s : Finset Plane := {⟨(1, 2), by decide⟩, ⟨(1, 3), by decide⟩, ⟨(2, 3), by decide⟩,
    ⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩}
  have hs : ∑ d ∈ s, term n Q (spatialTwist n) character 2 U (y, d) ≤
      ∑ d, term n Q (spatialTwist n) character 2 U (y, d) :=
    Finset.sum_le_univ_sum_of_nonneg fun d => term_nonneg n U (y, d)
  refine le_trans (le_of_eq ?_) hs
  simp only [s]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [term_eq_defect_sq]
  ring

/-- **Stability of the actual twisted action.** A field with `S(U) ≤ 1` has, at some base point,
`W₁, W₂` nearly anticommuting and `W₀, W₃` within `(8/3) √S` of `±1`. No constant involves the
lattice size. -/
theorem action_stability (n : ℕ) [NeZero n] (U : Configuration (Vertex (2 * n)) Q)
    (hS : action n Q (spatialTwist n) character 1 2 U ≤ 1) :
    ∃ x, d (wind (linkValue (2 * n) Q U) 1 x * wind (linkValue (2 * n) Q U) 2 x)
          (ω * (wind (linkValue (2 * n) Q U) 2 x * wind (linkValue (2 * n) Q U) 1 x)) ≤
          Real.sqrt (action n Q (spatialTwist n) character 1 2 U) ∧
      (d (wind (linkValue (2 * n) Q U) 3 x) 1 ≤
          8 / 3 * Real.sqrt (action n Q (spatialTwist n) character 1 2 U) ∨
        d (wind (linkValue (2 * n) Q U) 3 x) ω ≤
          8 / 3 * Real.sqrt (action n Q (spatialTwist n) character 1 2 U)) ∧
      (d (wind (linkValue (2 * n) Q U) 0 x) 1 ≤
          8 / 3 * Real.sqrt (action n Q (spatialTwist n) character 1 2 U) ∨
        d (wind (linkValue (2 * n) Q U) 0 x) ω ≤
          8 / 3 * Real.sqrt (action n Q (spatialTwist n) character 1 2 U)) :=
  holonomy_stability _ _ hS (five_planes_le_action n U)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
