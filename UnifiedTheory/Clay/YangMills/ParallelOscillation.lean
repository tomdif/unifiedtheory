/- Collective oscillation control for genuine parallel product updates.
The clock here counts auxiliary color updates, not physical transfer time. -/
import UnifiedTheory.Clay.YangMills.FiniteProductInfluence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ParallelOscillation
noncomputable section
open MeasureTheory FiniteProductInfluence

variable {I X : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Selected coordinates use their actual conditional marginals; all others are retained. -/
def updateMarginal (K : I → (I → X) → Measure X) (S : Finset I)
    (x : I → X) (i : I) : Measure X :=
  if i ∈ S then K i x else Measure.dirac (x i)

instance updateMarginal_probability (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (S : Finset I) (x : I → X) (i : I) :
    IsProbabilityMeasure (updateMarginal K S x i) := by
  unfold updateMarginal
  split <;> infer_instance

/-- The literal expectation under the simultaneous product update law. -/
def parallelAverage (K : I → (I → X) → Measure X) (S : Finset I)
    (F : C(I → X, ℝ)) (x : I → X) : ℝ :=
  ∫ y, F y ∂Measure.pi (updateMarginal K S x)

/-- Local influences are stated only for one-coordinate changes and actual one-site laws. -/
def LocalInfluence (K : I → (I → X) → Measure X) (C : I → I → ℝ) : Prop :=
  ∀ i j x y, (∀ l, l ≠ j → x l = y l) →
    ∀ (G : C(X, ℝ)) (d : ℝ), (∀ a b, |G a - G b| ≤ d) →
      |(∫ a, G a ∂K i x) - (∫ a, G a ∂K i y)| ≤ C i j * d

/-- Sensitivity remaining in one input coordinate after a selected parallel update. -/
def blockBound (C : I → I → ℝ) (S : Finset I) (d : I → ℝ) (j : I) : ℝ :=
  (if j ∈ S then 0 else d j) + ∑ i ∈ S, C i j * d i

/-- Product comparison derives the block oscillation estimate from one-site influences. -/
theorem parallel_oscillation (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (C : I → I → ℝ)
    (hK : LocalInfluence K C) (S : Finset I) (F : C(I → X, ℝ))
    (d : I → ℝ) (hF : OscBound F d) :
    OscBound (parallelAverage K S F) (blockBound C S d) := by
  intro j x y hxy
  let b : I → ℝ := fun i =>
    if i ∈ S then C i j * d i else if i = j then d j else 0
  have hloc (i : I) (G : C(X, ℝ)) (hG : ∀ a b, |G a - G b| ≤ d i) :
      |(∫ a, G a ∂updateMarginal K S x i) -
        (∫ a, G a ∂updateMarginal K S y i)| ≤ b i := by
    by_cases hi : i ∈ S
    · simp only [updateMarginal, hi, ↓reduceIte, b]
      exact hK i j x y hxy G (d i) hG
    · simp only [updateMarginal, hi, ↓reduceIte, b]
      rw [integral_dirac' G _ G.continuous.stronglyMeasurable,
        integral_dirac' G _ G.continuous.stronglyMeasurable]
      by_cases hij : i = j
      · subst i
        simp only [↓reduceIte]
        exact hG _ _
      · simp only [hij, ↓reduceIte, hxy i hij, sub_self, abs_zero, le_refl]
  have h := product_comparison (updateMarginal K S x) (updateMarginal K S y)
    F d b hF hloc
  have hb : ∑ i, b i = blockBound C S d j := by
    unfold b blockBound
    rw [Finset.sum_ite]
    have hout : (∑ i ∈ Finset.univ.filter (fun i => i ∉ S),
        if i = j then d j else 0) = if j ∈ S then 0 else d j := by simp
    rw [hout]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  simpa only [parallelAverage, hb, abs_sub_comm] using h

omit [DecidableEq I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Coordinate oscillations bound the difference of two complete configurations by telescoping. -/
theorem global_difference (F : (I → X) → ℝ) (d : I → ℝ) (hF : OscBound F d)
    (x y : I → X) : |F x - F y| ≤ ∑ i, d i := by
  classical
  let z (S : Finset I) (i : I) := if i ∈ S then x i else y i
  have hp (S : Finset I) : |F (z S) - F y| ≤ ∑ i ∈ S, d i := by
    induction S using Finset.induction_on with
    | empty =>
      have hz : z ∅ = y := by funext i; simp [z]
      simp only [hz, sub_self, abs_zero, Finset.sum_empty, le_refl]
    | @insert e S he ih =>
      have hs : |F (z (insert e S)) - F (z S)| ≤ d e := by
        apply hF e
        intro j hj
        simp [z, hj]
      calc
        _ ≤ |F (z (insert e S)) - F (z S)| + |F (z S) - F y| := abs_sub_le _ _ _
        _ ≤ d e + ∑ i ∈ S, d i := add_le_add hs ih
        _ = _ := by rw [Finset.sum_insert he]
  have hz : z Finset.univ = x := by funext i; simp [z]
  simpa only [hz] using hp Finset.univ

omit [Fintype I] [DecidableEq I] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
/-- Every continuous bounded observable supplies a finite coordinate-oscillation vector. -/
theorem uniform_oscillation (F : C(I → X, ℝ)) : OscBound F (fun _ => 2 * ‖F‖) := by
  intro i x y _
  calc
    |F x - F y| ≤ |F x| + |F y| := abs_sub _ _
    _ ≤ ‖F‖ + ‖F‖ := add_le_add (ContinuousMap.norm_coe_le_norm F x)
      (ContinuousMap.norm_coe_le_norm F y)
    _ = _ := by ring

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- A continuous test with bounded oscillation has an attained interval of that width. -/
theorem interval_of_oscillation [Nonempty X] (G : C(X, ℝ)) (d : ℝ)
    (hG : ∀ a b, |G a - G b| ≤ d) :
    ∃ c : ℝ, c ≤ c + d ∧ ∀ a, G a ∈ Set.Icc c (c + d) := by
  obtain ⟨x, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) G.continuous.continuousOn
  have hd : 0 ≤ d := by simpa only [sub_self, abs_zero] using hG x x
  refine ⟨G x, by linarith, fun a => ⟨hmin (Set.mem_univ a), ?_⟩⟩
  have h := (abs_le.mp (hG a x)).2
  linarith

section Colors
variable {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color]

/-- The actual average over uniformly selected geometric colors. -/
def colorAverage (K : I → (I → X) → Measure X) (color : I → Color)
    (F : C(I → X, ℝ)) (x : I → X) : ℝ :=
  (Fintype.card Color : ℝ)⁻¹ *
    ∑ c : Color, parallelAverage K (Finset.univ.filter (fun i => color i = c)) F x

/-- The resulting coordinate bound includes both retained and resampled coordinates. -/
def colorBound (C : I → I → ℝ) (d : I → ℝ) (j : I) : ℝ :=
  (1 - (Fintype.card Color : ℝ)⁻¹) * d j +
    (Fintype.card Color : ℝ)⁻¹ * ∑ i, C i j * d i

theorem sum_blockBound (color : I → Color) (C : I → I → ℝ) (d : I → ℝ) (j : I) :
    (Fintype.card Color : ℝ)⁻¹ *
      ∑ c : Color, blockBound C (Finset.univ.filter (fun i => color i = c)) d j =
      colorBound (Color := Color) C d j := by
  have hm : (Fintype.card Color : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [blockBound, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_add_distrib]
  have hret : (∑ c : Color, if color j = c then (0 : ℝ) else d j) =
      (Fintype.card Color : ℝ) * d j - d j := by
    have he (c : Color) : (if color j = c then (0 : ℝ) else d j) =
        d j - if color j = c then d j else 0 := by split <;> simp_all
    simp_rw [he, Finset.sum_sub_distrib]
    simp
  rw [hret]
  have hres : (∑ c : Color, ∑ i ∈ Finset.univ.filter (fun i => color i = c), C i j * d i) =
      ∑ i, C i j * d i := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [hres]
  unfold colorBound
  field_simp

/-- A uniform random color update satisfies the derived coordinate influence inequality. -/
theorem color_oscillation (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (F : C(I → X, ℝ)) (d : I → ℝ) (hF : OscBound F d) :
    OscBound (colorAverage K color F) (colorBound (Color := Color) C d) := by
  intro j x y hxy
  unfold colorAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color,
        |parallelAverage K (Finset.univ.filter (fun i => color i = c)) F x -
          parallelAverage K (Finset.univ.filter (fun i => color i = c)) F y| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color,
        blockBound C (Finset.univ.filter (fun i => color i = c)) d j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro c _
      exact parallel_oscillation K C hK _ F d hF j x y hxy
    _ = _ := sum_blockBound color C d j

omit [DecidableEq I] [DecidableEq Color] in
/-- Row sums, not column sums, control the total coordinate-oscillation budget. -/
theorem color_budget (C : I → I → ℝ) (d : I → ℝ) (α : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hrow : ∀ i, ∑ j, C i j ≤ α) :
    (∑ j, colorBound (Color := Color) C d j) ≤
      (1 - (1 - α) / Fintype.card Color) * ∑ i, d i := by
  simp only [colorBound, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum : (∑ j, ∑ i, C i j * d i) ≤ α * ∑ i, d i := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, (∑ j, C i j) * d i := by simp only [Finset.sum_mul]
      _ ≤ ∑ i, α * d i :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (hd i))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hm := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (Fintype.card Color : ℝ)⁻¹)
  calc
    _ ≤ (1 - (Fintype.card Color : ℝ)⁻¹) * ∑ j, d j +
        (Fintype.card Color : ℝ)⁻¹ * (α * ∑ i, d i) := add_le_add le_rfl hm
    _ = _ := by ring

/-- The auxiliary random-color contraction rate. -/
def colorRate (α : ℝ) : ℝ := 1 - (1 - α) / Fintype.card Color

omit [DecidableEq I] [DecidableEq Color] in
theorem colorBound_nonneg (C : I → I → ℝ) (d : I → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hd : ∀ i, 0 ≤ d i) (j : I) :
    0 ≤ colorBound (Color := Color) C d j := by
  have hm : (1 : ℝ) ≤ Fintype.card Color := by exact_mod_cast Fintype.card_pos
  have hi : (Fintype.card Color : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr hm
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi) (hd j))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => mul_nonneg (hC i j) (hd i))))

omit [DecidableEq Color] in
theorem colorRate_nonneg (α : ℝ) (hα : 0 ≤ α) : 0 ≤ colorRate (Color := Color) α := by
  have hm : (1 : ℝ) ≤ Fintype.card Color := by exact_mod_cast Fintype.card_pos
  have hi : (Fintype.card Color : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr hm
  unfold colorRate
  have he : 1 - (1 - α) / (Fintype.card Color : ℝ) =
      1 - (Fintype.card Color : ℝ)⁻¹ + α * (Fintype.card Color : ℝ)⁻¹ := by ring
  rw [he]
  exact add_nonneg (sub_nonneg.mpr hi) (mul_nonneg hα (by positivity))

omit [DecidableEq Color] in
theorem colorRate_lt_one (α : ℝ) (hα : α < 1) : colorRate (Color := Color) α < 1 := by
  have hm : 0 < (Fintype.card Color : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold colorRate
  exact sub_lt_self _ (div_pos (sub_pos.mpr hα) hm)

/-- The explicitly propagated coordinate bounds. -/
def budgetIterate (C : I → I → ℝ) : ℕ → (I → ℝ) → I → ℝ
  | 0, d => d
  | k + 1, d => colorBound (Color := Color) C (budgetIterate C k d)

omit [DecidableEq I] [DecidableEq Color] in
theorem budgetIterate_nonneg (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (k : ℕ) (j : I) :
    0 ≤ budgetIterate (Color := Color) C k d j := by
  induction k generalizing j with
  | zero => exact hd j
  | succ k ih => exact colorBound_nonneg C _ hC ih j

omit [DecidableEq I] [DecidableEq Color] in
/-- The total sensitivity loses a fixed fraction per color update, without a site-count factor. -/
theorem budgetIterate_sum (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (α : ℝ) (hα : 0 ≤ α)
    (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) :
    (∑ j, budgetIterate (Color := Color) C k d j) ≤
      colorRate (Color := Color) α ^ k * ∑ j, d j := by
  induction k with
  | zero => simp [budgetIterate]
  | succ k ih =>
    calc
      _ ≤ colorRate (Color := Color) α * ∑ j, budgetIterate (Color := Color) C k d j :=
        color_budget C _ α (budgetIterate_nonneg C hC d hd k) hrow
      _ ≤ colorRate (Color := Color) α *
          (colorRate (Color := Color) α ^ k * ∑ j, d j) :=
        mul_le_mul_of_nonneg_left ih (colorRate_nonneg α hα)
      _ = _ := by rw [pow_succ]; ring

/-- Iteration of the actual continuous observable update. -/
def updateIterate (P : C(I → X, ℝ) → C(I → X, ℝ)) : ℕ → C(I → X, ℝ) → C(I → X, ℝ)
  | 0, F => F
  | k + 1, F => P (updateIterate P k F)

/-- Local conditional influences and the product-update dictionary control every iterate. -/
theorem updateIterate_oscillation (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hP : ∀ F x, P F x = colorAverage K color F x)
    (F : C(I → X, ℝ)) (d : I → ℝ) (hF : OscBound F d) (k : ℕ) :
    OscBound (updateIterate P k F) (budgetIterate (Color := Color) C k d) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    intro j x y hxy
    change |P (updateIterate P k F) x - P (updateIterate P k F) y| ≤ _
    rw [hP, hP]
    exact color_oscillation K color C hK _ _ ih j x y hxy

/-- Geometric contraction of complete-configuration differences under actual color updates. -/
theorem updateIterate_difference (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (hC : ∀ i j, 0 ≤ C i j)
    (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hP : ∀ F x, P F x = colorAverage K color F x)
    (F : C(I → X, ℝ)) (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) (x y : I → X) :
    |updateIterate P k F x - updateIterate P k F y| ≤
      colorRate (Color := Color) α ^ k * ∑ i, d i :=
  (global_difference _ _ (updateIterate_oscillation K color C hK P hP F d hF k) x y).trans
    (budgetIterate_sum C hC d hd α hα hrow k)

omit [DecidableEq I] [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] in
/-- Stationarity of the observable update propagates through its exact iterates. -/
theorem updateIterate_mean (π : Measure (I → X))
    (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hstation : ∀ F, (∫ x, P F x ∂π) = ∫ x, F x ∂π)
    (F : C(I → X, ℝ)) (k : ℕ) :
    (∫ x, updateIterate P k F x ∂π) = ∫ x, F x ∂π := by
  induction k with
  | zero => rfl
  | succ k ih => rw [updateIterate, hstation, ih]

/-- Stationarity turns the derived oscillation decay into an actual uniform expectation bound. -/
theorem stationary_error (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (hC : ∀ i j, 0 ≤ C i j)
    (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hP : ∀ F x, P F x = colorAverage K color F x)
    (π : Measure (I → X)) [IsProbabilityMeasure π]
    (hstation : ∀ F, (∫ x, P F x ∂π) = ∫ x, F x ∂π)
    (F : C(I → X, ℝ)) (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) (x : I → X) :
    |updateIterate P k F x - ∫ y, F y ∂π| ≤
      colorRate (Color := Color) α ^ k * ∑ i, d i := by
  rw [← updateIterate_mean π P hstation F k]
  have hi : Integrable (fun y => updateIterate P k F y) π :=
    (updateIterate P k F).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : updateIterate P k F x - (∫ y, updateIterate P k F y ∂π) =
      ∫ y, updateIterate P k F x - updateIterate P k F y ∂π := by
    rw [integral_sub (integrable_const _) hi]
    simp
  rw [he]
  calc
    _ ≤ ∫ y, |updateIterate P k F x - updateIterate P k F y| ∂π :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _y, colorRate (Color := Color) α ^ k * ∑ i, d i ∂π :=
      integral_mono ((integrable_const _).sub hi).abs (integrable_const _)
        (updateIterate_difference K color C hK hC P hP F d hF hd α hα hrow k x)
    _ = _ := by simp

/-- Centered continuous correlations inherit the auxiliary update rate.
The test-dependent prefactor is finite; no uniform prefactor is postulated. -/
theorem stationary_correlation (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (hC : ∀ i j, 0 ≤ C i j)
    (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hP : ∀ F x, P F x = colorAverage K color F x)
    (π : Measure (I → X)) [IsProbabilityMeasure π]
    (hstation : ∀ F, (∫ x, P F x ∂π) = ∫ x, F x ∂π)
    (F : C(I → X, ℝ)) (hmean : (∫ x, F x ∂π) = 0)
    (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) :
    |∫ x, F x * updateIterate P k F x ∂π| ≤
      (‖F‖ * ∑ i, d i) * colorRate (Color := Color) α ^ k := by
  have hb (x : I → X) : |updateIterate P k F x| ≤
      colorRate (Color := Color) α ^ k * ∑ i, d i := by
    simpa only [hmean, sub_zero] using
      stationary_error K color C hK hC P hP π hstation F d hF hd α hα hrow k x
  have hi : Integrable (fun x => F x * updateIterate P k F x) π :=
    (F.continuous.mul (updateIterate P k F).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, |F x * updateIterate P k F x| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ _x, ‖F‖ * (colorRate (Color := Color) α ^ k * ∑ i, d i) ∂π := by
      apply integral_mono hi.abs (integrable_const _)
      intro x
      change |F x * updateIterate P k F x| ≤
        ‖F‖ * (colorRate (Color := Color) α ^ k * ∑ i, d i)
      rw [abs_mul]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm F x) (hb x)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- All centered continuous tests have a finite geometric moment bound,
suitable for a dense-test L² spectral argument. -/
theorem stationary_correlation_uniform (K : I → (I → X) → Measure X)
    [∀ i x, IsProbabilityMeasure (K i x)] (color : I → Color) (C : I → I → ℝ)
    (hK : LocalInfluence K C) (hC : ∀ i j, 0 ≤ C i j)
    (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hP : ∀ F x, P F x = colorAverage K color F x)
    (π : Measure (I → X)) [IsProbabilityMeasure π]
    (hstation : ∀ F, (∫ x, P F x ∂π) = ∫ x, F x ∂π)
    (F : C(I → X, ℝ)) (hmean : (∫ x, F x ∂π) = 0)
    (α : ℝ) (hα : 0 ≤ α) (hrow : ∀ i, ∑ j, C i j ≤ α) (k : ℕ) :
    |∫ x, F x * updateIterate P k F x ∂π| ≤
      (2 * Fintype.card I * ‖F‖ ^ 2) * colorRate (Color := Color) α ^ k := by
  have h := stationary_correlation K color C hK hC P hP π hstation F hmean
    (fun _ => 2 * ‖F‖) (uniform_oscillation F) (fun _ => by positivity) α hα hrow k
  have he : ‖F‖ * (∑ _i : I, 2 * ‖F‖) = 2 * Fintype.card I * ‖F‖ ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he] at h
  exact h

end Colors
end
end UnifiedTheory.Clay.YangMills.ParallelOscillation
