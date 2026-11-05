/- A reusable locality-to-clustering theorem for genuine reversible updates.
The norm contraction and support/cancellation premises are explicit and are
bound to actual cylinder conditionals in the Wilson application. -/
import UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction
import UnifiedTheory.Clay.YangMills.ParallelOscillation
import Mathlib.Logic.Function.DependsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ReversibleLocalClustering
noncomputable section
open MeasureTheory ParallelOscillation

variable {I X : Type*} [Fintype I] [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure (I → X)) [IsProbabilityMeasure μ]

def centered (F : C(I → X, ℝ)) : C(I → X, ℝ) :=
  F - ContinuousMap.const _ (∫ x, F x ∂μ)

theorem centered_mean (F : C(I → X, ℝ)) : (∫ x, centered μ F x ∂μ) = 0 := by
  simp only [centered, ContinuousMap.sub_apply, ContinuousMap.const_apply]
  rw [integral_sub (F.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] in
theorem centered_dependsOn (F : C(I → X, ℝ)) (A : Finset I)
    (hF : DependsOn (F : (I → X) → ℝ) (A : Set I)) :
    DependsOn (centered μ F : (I → X) → ℝ) (A : Set I) := by
  intro x y hxy
  change F x - (∫ z, F z ∂μ) = F y - (∫ z, F z ∂μ)
  rw [hF hxy]

theorem centered_norm_eq_sqrt_variance (F : C(I → X, ℝ)) :
    ‖ContinuousMap.toLp 2 μ ℝ (centered μ F)‖ =
      Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ) := by
  have he : ‖ContinuousMap.toLp 2 μ ℝ (centered μ F)‖ ^ 2 =
      ∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ := by
    simpa only [ContinuousUpdateGap.pairing, centered, ContinuousMap.sub_apply,
      ContinuousMap.const_apply, pow_two] using
      ContinuousUpdateGap.embedding_square μ (centered μ F)
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

theorem centered_norm_le (F : C(I → X, ℝ)) :
    ‖ContinuousMap.toLp 2 μ ℝ (centered μ F)‖ ≤ 2 * ‖F‖ := by
  have hm : |∫ x, F x ∂μ| ≤ ‖F‖ := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := fun x : I → X => F x)
        (Filter.Eventually.of_forall (fun x => ContinuousMap.norm_coe_le_norm F x))
  have hb (x : I → X) : |centered μ F x| ≤ 2 * ‖F‖ := by
    change |F x - ∫ y, F y ∂μ| ≤ _
    exact (abs_sub _ _).trans ((add_le_add (ContinuousMap.norm_coe_le_norm F x) hm).trans
      (by ring_nf; rfl))
  have hs : ‖ContinuousMap.toLp 2 μ ℝ (centered μ F)‖^2 ≤ (2 * ‖F‖)^2 := by
    rw [ContinuousUpdateGap.embedding_square]
    change (∫ x, centered μ F x * centered μ F x ∂μ) ≤ _
    have hi : Integrable (fun x => centered μ F x * centered μ F x) μ :=
      ((centered μ F).continuous.mul (centered μ F).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := integral_mono hi (integrable_const ((2 * ‖F‖)^2)) (fun x => by
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
      rw [sq_abs] at hh
      nlinarith)
    simpa using h
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 μ ℝ (centered μ F)), norm_nonneg F]

theorem centered_iterate_norm (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hstation : ∀ F, (∫ x, P F x ∂μ) = ∫ x, F x ∂μ)
    (q : ℝ) (hq : 0 ≤ q)
    (hcontract : ∀ F, (∫ x, F x ∂μ) = 0 →
      ‖ContinuousMap.toLp 2 μ ℝ (P F)‖ ≤ q * ‖ContinuousMap.toLp 2 μ ℝ F‖)
    (F : C(I → X, ℝ)) (hmean : (∫ x, F x ∂μ) = 0) (k : ℕ) :
    ‖ContinuousMap.toLp 2 μ ℝ (updateIterate P k F)‖ ≤
      q^k * ‖ContinuousMap.toLp 2 μ ℝ F‖ := by
  induction k with
  | zero => simp only [updateIterate, pow_zero, one_mul, le_refl]
  | succ k ih =>
    have hm : (∫ x, updateIterate P k F x ∂μ) = 0 := by
      rw [updateIterate_mean μ P hstation, hmean]
    calc
      _ ≤ q * ‖ContinuousMap.toLp 2 μ ℝ (updateIterate P k F)‖ := hcontract _ hm
      _ ≤ q * (q^k * ‖ContinuousMap.toLp 2 μ ℝ F‖) := mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [IsProbabilityMeasure μ] in
/-- No stochastic time is identified with distance: exact locality and
disjoint cross-energy give this deterministic pairing telescope. -/
theorem pairing_eq_iterate (P : C(I → X, ℝ) → C(I → X, ℝ))
    (N : Finset I → ℕ → Finset I)
    (hlocal : ∀ (F : C(I → X, ℝ)) (A : Finset I), DependsOn (F : (I → X) → ℝ) (A : Set I) → ∀ k,
      DependsOn (updateIterate P k F : (I → X) → ℝ) (N A k : Set I))
    (hcancel : ∀ (F G : C(I → X, ℝ)) (A B : Finset I), Disjoint A B →
      DependsOn (F : (I → X) → ℝ) (A : Set I) →
      DependsOn (G : (I → X) → ℝ) (B : Set I) →
      (∫ x, F x * G x ∂μ) = ∫ x, P F x * G x ∂μ)
    (F G : C(I → X, ℝ)) (A B : Finset I)
    (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (N A j) B) :
    (∫ x, F x * G x ∂μ) = ∫ x, updateIterate P d F x * G x ∂μ := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      _ = ∫ x, updateIterate P d F x * G x ∂μ :=
        ih (fun j hj => hsep j (Nat.lt_succ_of_lt hj))
      _ = _ := hcancel _ G (N A d) B (hsep d (Nat.lt_succ_self d)) (hlocal F A hF d) hG

/-- The hypotheses will be derived from the actual local Gibbs law, not
supplied as an unproved spatial covariance bound. -/
theorem covariance_norm_bound (P : C(I → X, ℝ) → C(I → X, ℝ))
    (hstation : ∀ F, (∫ x, P F x ∂μ) = ∫ x, F x ∂μ)
    (q : ℝ) (hq : 0 ≤ q)
    (hcontract : ∀ F, (∫ x, F x ∂μ) = 0 →
      ‖ContinuousMap.toLp 2 μ ℝ (P F)‖ ≤ q * ‖ContinuousMap.toLp 2 μ ℝ F‖)
    (N : Finset I → ℕ → Finset I)
    (hlocal : ∀ (F : C(I → X, ℝ)) (A : Finset I), DependsOn (F : (I → X) → ℝ) (A : Set I) → ∀ k,
      DependsOn (updateIterate P k F : (I → X) → ℝ) (N A k : Set I))
    (hcancel : ∀ (F G : C(I → X, ℝ)) (A B : Finset I), Disjoint A B →
      DependsOn (F : (I → X) → ℝ) (A : Set I) →
      DependsOn (G : (I → X) → ℝ) (B : Set I) →
      (∫ x, F x * G x ∂μ) = ∫ x, P F x * G x ∂μ)
    (F G : C(I → X, ℝ)) (A B : Finset I)
    (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I))
    (d : ℕ) (hsep : ∀ j, j < d → Disjoint (N A j) B) :
    |∫ x, centered μ F x * centered μ G x ∂μ| ≤
      q^d * ‖ContinuousMap.toLp 2 μ ℝ (centered μ F)‖ *
        ‖ContinuousMap.toLp 2 μ ℝ (centered μ G)‖ := by
  rw [pairing_eq_iterate μ P N hlocal hcancel _ _ A B
    (centered_dependsOn μ F A hF) (centered_dependsOn μ G B hG) d hsep]
  exact (ContinuousUpdateContraction.abs_pairing_le μ _ _).trans
    (mul_le_mul_of_nonneg_right
      (centered_iterate_norm μ P hstation q hq hcontract _ (centered_mean μ F) d)
      (norm_nonneg _))

end
end UnifiedTheory.Clay.YangMills.ReversibleLocalClustering
