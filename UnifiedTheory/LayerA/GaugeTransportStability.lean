/-
Quantitative ingredients for reconstruction of a connection from square-grid
plaquettes. The companion GAUGE_DISCRETE_CONTINUUM.md contains the complete
analytic U(m) theorem and explicitly identifies its formalization boundary.

Here: exact rooted tree gauge, noncommutative strip reconstruction, contractive
product stability, a second-order product remainder, and stability/convergence
of the continuum axial primitive. No new axioms or admitted proofs.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.GaugeTransportStability
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

section GroupGeometry
variable {G : Type*} [Group G]

/-- Chronological product for links mapping the head frame to the tail frame. -/
def rightProduct (a : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => rightProduct a n * a n

/-- Product in the order required by the axial plaquette recursion. -/
def leftProduct (a : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => a n * leftProduct a n

def treeGauge (H V : ℕ → ℕ → G) (i j : ℕ) : G :=
  rightProduct (V 0) j * rightProduct (fun k => H k j) i

def gaugedH (H : ℕ → ℕ → G) (g : ℕ → ℕ → G) (i j : ℕ) : G :=
  g i j * H i j * (g (i + 1) j)⁻¹

def gaugedV (V : ℕ → ℕ → G) (g : ℕ → ℕ → G) (i j : ℕ) : G :=
  g i j * V i j * (g i (j + 1))⁻¹

def plaquette (H V : ℕ → ℕ → G) (i j : ℕ) : G :=
  H i j * V (i + 1) j * (H i (j + 1))⁻¹ * (V i j)⁻¹

theorem path_gauge (a g : ℕ → G) (n : ℕ) :
    rightProduct (fun k => g k * a k * (g (k + 1))⁻¹) n =
      g 0 * rightProduct a n * (g n)⁻¹ := by
  induction n with
  | zero => simp [rightProduct]
  | succ n ih =>
      rw [rightProduct, rightProduct, ih]
      group

@[simp] theorem treeGauge_root (H V : ℕ → ℕ → G) : treeGauge H V 0 0 = 1 := by
  simp [treeGauge, rightProduct]

theorem treeGauge_horizontal (H V : ℕ → ℕ → G) (i j : ℕ) :
    gaugedH H (treeGauge H V) i j = 1 := by
  simp only [gaugedH, treeGauge, rightProduct]
  group

theorem treeGauge_left_boundary (H V : ℕ → ℕ → G) (j : ℕ) :
    gaugedV V (treeGauge H V) 0 j = 1 := by
  simp only [gaugedV, treeGauge, rightProduct, mul_one]
  group

theorem plaquette_gauge (H V g : ℕ → ℕ → G) (i j : ℕ) :
    plaquette (gaugedH H g) (gaugedV V g) i j =
      g i j * plaquette H V i j * (g i j)⁻¹ := by
  simp only [plaquette, gaugedH, gaugedV]
  group

theorem axial_plaquette (V : ℕ → ℕ → G) (i j : ℕ) :
    plaquette (fun _ _ => 1) V i j = V (i + 1) j * (V i j)⁻¹ := by
  simp [plaquette]

/-- No commutativity is assumed. The order of the factors is essential. -/
theorem axial_reconstruction (V : ℕ → ℕ → G) (j : ℕ) (h0 : V 0 j = 1)
    (i : ℕ) :
    V i j = leftProduct (fun k => plaquette (fun _ _ => 1) V k j) i := by
  induction i with
  | zero => simpa [leftProduct] using h0
  | succ i ih =>
      rw [leftProduct, axial_plaquette, ← ih]
      group

end GroupGeometry

section ContractiveProducts
variable {R : Type*} [NormedRing R] [NormOneClass R]

def orderedProduct (a : ℕ → R) : ℕ → R
  | 0 => 1
  | n + 1 => a n * orderedProduct a n

theorem orderedProduct_norm_le_one (a : ℕ → R) (n : ℕ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1) : ‖orderedProduct a n‖ ≤ 1 := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
      calc
        ‖orderedProduct a (n + 1)‖ ≤ ‖a n‖ * ‖orderedProduct a n‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (ha n (by omega))
          (ih (fun k hk => ha k (by omega))) (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1

omit [NormOneClass R] in
theorem contractive_mul_difference (a b u v : R) (ha : ‖a‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖a * u - b * v‖ ≤ ‖u - v‖ + ‖a - b‖ := by
  calc
    ‖a * u - b * v‖ = ‖a * (u - v) + (a - b) * v‖ := by congr 1; noncomm_ring
    _ ≤ ‖a * (u - v)‖ + ‖(a - b) * v‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖u - v‖ + ‖a - b‖ * ‖v‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * ‖u - v‖ + ‖a - b‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    _ = ‖u - v‖ + ‖a - b‖ := by ring

/-- Dimension-free telescoping bound; applies to unitary operators in operator norm. -/
theorem orderedProduct_difference (a b : ℕ → R) (n : ℕ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1) (hb : ∀ k < n, ‖b k‖ ≤ 1) :
    ‖orderedProduct a n - orderedProduct b n‖ ≤
      ∑ k ∈ Finset.range n, ‖a k - b k‖ := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
      rw [orderedProduct, orderedProduct, Finset.sum_range_succ]
      exact (contractive_mul_difference _ _ _ _ (ha n (by omega))
        (orderedProduct_norm_le_one b n (fun k hk => hb k (by omega)))).trans
        (add_le_add (ih (fun k hk => ha k (by omega))
          (fun k hk => hb k (by omega))) le_rfl)

theorem orderedProduct_uniform_error (a b : ℕ → R) (n : ℕ) (δ : ℝ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1) (hb : ∀ k < n, ‖b k‖ ≤ 1)
    (he : ∀ k < n, ‖a k - b k‖ ≤ δ) :
    ‖orderedProduct a n - orderedProduct b n‖ ≤ (n : ℝ) * δ := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖a k - b k‖ := orderedProduct_difference a b n ha hb
    _ ≤ ∑ _k ∈ Finset.range n, δ := Finset.sum_le_sum fun k hk => he k (Finset.mem_range.mp hk)
    _ = (n : ℝ) * δ := by simp

omit [NormOneClass R] in
@[simp] theorem orderedProduct_one (n : ℕ) : orderedProduct (fun _ => (1 : R)) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct, ih]

theorem orderedProduct_distance_one (a : ℕ → R) (n : ℕ) (d : ℝ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1) (hd : ∀ k < n, ‖a k - 1‖ ≤ d) :
    ‖orderedProduct a n - 1‖ ≤ (n : ℝ) * d := by
  simpa using orderedProduct_uniform_error a (fun _ => 1) n d ha
    (fun _ _ => le_of_eq (norm_one : ‖(1 : R)‖ = 1)) hd

/-- Second-order remainder for a genuinely noncommutative product.
The hypotheses separate a first-order increment bound from its local remainder. -/
theorem orderedProduct_linearization (a t : ℕ → R) (n : ℕ) (d r : ℝ)
    (hd0 : 0 ≤ d)
    (ha : ∀ k < n, ‖a k‖ ≤ 1)
    (hd : ∀ k < n, ‖a k - 1‖ ≤ d)
    (hr : ∀ k < n, ‖a k - 1 - t k‖ ≤ r) :
    ‖orderedProduct a n - 1 - ∑ k ∈ Finset.range n, t k‖ ≤
      (n : ℝ) * r + (n : ℝ) * ((n : ℝ) - 1) / 2 * d ^ 2 := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih =>
      have hprev := ih (fun k hk => ha k (by omega))
        (fun k hk => hd k (by omega)) (fun k hk => hr k (by omega))
      have hone := orderedProduct_distance_one a n d
        (fun k hk => ha k (by omega)) (fun k hk => hd k (by omega))
      have hm : ‖(a n - 1) * (orderedProduct a n - 1)‖ ≤ d * ((n : ℝ) * d) :=
        (norm_mul_le _ _).trans
          (mul_le_mul (hd n (by omega)) hone (norm_nonneg _) hd0)
      have hid : orderedProduct a (n + 1) - 1 - ∑ k ∈ Finset.range (n + 1), t k =
          (orderedProduct a n - 1 - ∑ k ∈ Finset.range n, t k) +
          (a n - 1 - t n) + (a n - 1) * (orderedProduct a n - 1) := by
        rw [orderedProduct, Finset.sum_range_succ]
        noncomm_ring
      rw [hid]
      calc
        _ ≤ ‖orderedProduct a n - 1 - ∑ k ∈ Finset.range n, t k‖ +
            ‖a n - 1 - t n‖ + ‖(a n - 1) * (orderedProduct a n - 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ ((n : ℝ) * r + (n : ℝ) * ((n : ℝ) - 1) / 2 * d ^ 2) + r +
            d * ((n : ℝ) * d) := add_le_add (add_le_add hprev (hr n (by omega))) hm
        _ = ((n + 1 : ℕ) : ℝ) * r + ((n + 1 : ℕ) : ℝ) *
            (((n + 1 : ℕ) : ℝ) - 1) / 2 * d ^ 2 := by push_cast; ring

end ContractiveProducts

section UnitaryStrips
variable {R : Type*} [NormedRing R] [StarRing R] [CStarRing R] [Nontrivial R]

omit [CStarRing R] [Nontrivial R] in
theorem coe_leftProduct (a : ℕ → unitary R) (n : ℕ) :
    ((leftProduct a n : unitary R) : R) = orderedProduct (fun k => (a k : R)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (a n : R) * ((leftProduct a n : unitary R) : R) =
        (a n : R) * orderedProduct (fun k => (a k : R)) n
      rw [ih]

/-- Exact plaquette-to-link estimate in a C*-algebra's unitary group.
In particular this applies to finite-dimensional unitary operators. -/
theorem unitary_axial_strip_stability (V W : ℕ → ℕ → unitary R)
    (i j : ℕ) (δ : ℝ) (hV : V 0 j = 1) (hW : W 0 j = 1)
    (hp : ∀ k < i,
      ‖((plaquette (fun _ _ => 1) V k j : unitary R) : R) -
        ((plaquette (fun _ _ => 1) W k j : unitary R) : R)‖ ≤ δ) :
    ‖(V i j : R) - (W i j : R)‖ ≤ (i : ℝ) * δ := by
  rw [axial_reconstruction V j hV i, axial_reconstruction W j hW i,
    coe_leftProduct, coe_leftProduct]
  exact orderedProduct_uniform_error _ _ i δ
    (fun k _ => le_of_eq (CStarRing.norm_coe_unitary _))
    (fun k _ => le_of_eq (CStarRing.norm_coe_unitary _)) hp

omit [Nontrivial R] in
theorem unitary_inverse_distance (U V : unitary R) :
    ‖((U⁻¹ : unitary R) : R) - ((V⁻¹ : unitary R) : R)‖ = ‖(U : R) - (V : R)‖ := by
  change ‖star (U : R) - star (V : R)‖ = _
  rw [← star_sub, norm_star]

omit [Nontrivial R] in
/-- The chronological path product, including repeated factors, is stable. -/
theorem unitary_path_stability (a b : ℕ → unitary R) (n : ℕ) (δ : ℝ)
    (he : ∀ k < n, ‖(a k : R) - (b k : R)‖ ≤ δ) :
    ‖((rightProduct a n : unitary R) : R) - ((rightProduct b n : unitary R) : R)‖ ≤
      (n : ℝ) * δ := by
  induction n with
  | zero => simp [rightProduct]
  | succ n ih =>
      have hid : ((rightProduct a (n + 1) : unitary R) : R) -
          ((rightProduct b (n + 1) : unitary R) : R) =
          (((rightProduct a n : unitary R) : R) - ((rightProduct b n : unitary R) : R)) *
            (a n : R) + ((rightProduct b n : unitary R) : R) * ((a n : R) - (b n : R)) := by
        change ((rightProduct a n : unitary R) : R) * (a n : R) -
          ((rightProduct b n : unitary R) : R) * (b n : R) = _
        noncomm_ring
      rw [hid]
      calc
        _ ≤ ‖(((rightProduct a n : unitary R) : R) - ((rightProduct b n : unitary R) : R)) *
            (a n : R)‖ + ‖((rightProduct b n : unitary R) : R) * ((a n : R) - (b n : R))‖ :=
          norm_add_le _ _
        _ = ‖((rightProduct a n : unitary R) : R) - ((rightProduct b n : unitary R) : R)‖ +
            ‖(a n : R) - (b n : R)‖ := by
          rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
        _ ≤ (n : ℝ) * δ + δ := add_le_add (ih (fun k hk => he k (by omega))) (he n (by omega))
        _ = ((n + 1 : ℕ) : ℝ) * δ := by push_cast; ring

def orientedV (V : ℕ → ℕ → unitary R) (backward : Bool) (i j : ℕ) : unitary R :=
  if backward then (V i j)⁻¹ else V i j

/-- Global plaquette-to-path bound. Horizontal identity links are omitted.
No composability assumption is necessary: the estimate holds for every word,
and hence for each composable grid path and each closed loop. -/
theorem unitary_axial_word_stability (V W : ℕ → ℕ → unitary R)
    (cols rows : ℕ → ℕ) (backward : ℕ → Bool) (m n : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hc : ∀ k < m, cols k ≤ n)
    (hV : ∀ j, V 0 j = 1) (hW : ∀ j, W 0 j = 1)
    (hp : ∀ k < m, ∀ a < cols k,
      ‖((plaquette (fun _ _ => 1) V a (rows k) : unitary R) : R) -
        ((plaquette (fun _ _ => 1) W a (rows k) : unitary R) : R)‖ ≤ δ) :
    ‖((rightProduct (fun k => orientedV V (backward k) (cols k) (rows k)) m : unitary R) : R) -
      ((rightProduct (fun k => orientedV W (backward k) (cols k) (rows k)) m : unitary R) : R)‖ ≤
        (m : ℝ) * (n : ℝ) * δ := by
  have hb : ∀ k < m,
      ‖(orientedV V (backward k) (cols k) (rows k) : R) -
        (orientedV W (backward k) (cols k) (rows k) : R)‖ ≤ (n : ℝ) * δ := by
    intro k hk
    have hs := unitary_axial_strip_stability V W (cols k) (rows k) δ
      (hV (rows k)) (hW (rows k)) (hp k hk)
    have hn : (cols k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc k hk
    have hs' := hs.trans (mul_le_mul_of_nonneg_right hn hδ)
    cases backward k <;> simp only [orientedV, Bool.false_eq_true, ↓reduceIte]
    · exact hs'
    · simpa only [unitary_inverse_distance] using hs'
  simpa only [mul_assoc] using unitary_path_stability
    (fun k => orientedV V (backward k) (cols k) (rows k))
    (fun k => orientedV W (backward k) (cols k) (rows k)) m ((n : ℝ) * δ) hb

end UnitaryStrips

section AxialPrimitive
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def axialPrimitive (F : ℝ → ℝ → E) (x y : ℝ) : E := ∫ s in (0 : ℝ)..x, F s y

/-- Sup-norm contraction on the unit square, with its sharper factor x retained. -/
theorem axialPrimitive_error (F G : ℝ → ℝ → E) (x y ε : ℝ)
    (hx : 0 ≤ x)
    (hF : IntervalIntegrable (fun s => F s y) volume 0 x)
    (hG : IntervalIntegrable (fun s => G s y) volume 0 x)
    (he : ∀ s ∈ Set.Ioc 0 x, ‖F s y - G s y‖ ≤ ε) :
    ‖axialPrimitive F x y - axialPrimitive G x y‖ ≤ ε * x := by
  unfold axialPrimitive
  rw [← intervalIntegral.integral_sub hF hG]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => F s y - G s y) (a := 0) (b := x) (C := ε) (by
      simpa only [Set.uIoc_of_le hx] using he)
  simpa [abs_of_nonneg hx] using h

/-- Uniform error estimate permits points (x_n,y_n) to move with the mesh.
This is stronger than convergence at a fixed point, without using a supremum. -/
theorem axialPrimitive_moving_point_convergence
    (F : ℕ → ℝ → ℝ → E) (G : ℝ → ℝ → E) (x y ε : ℕ → ℝ)
    (hx : ∀ n, 0 ≤ x n ∧ x n ≤ 1) (hε : ∀ n, 0 ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hF : ∀ n, IntervalIntegrable (fun s => F n s (y n)) volume 0 (x n))
    (hG : ∀ n, IntervalIntegrable (fun s => G s (y n)) volume 0 (x n))
    (he : ∀ n s, s ∈ Set.Ioc 0 (x n) → ‖F n s (y n) - G s (y n)‖ ≤ ε n) :
    Tendsto (fun n => ‖axialPrimitive (F n) (x n) (y n) -
      axialPrimitive G (x n) (y n)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => norm_nonneg _) _ hεlim
  intro n
  exact (axialPrimitive_error (F n) G (x n) (y n) (ε n) (hx n).1 (hF n) (hG n)
    (he n)).trans (by nlinarith [hε n, (hx n).2])

end AxialPrimitive
end
end UnifiedTheory.LayerA.GaugeTransportStability
