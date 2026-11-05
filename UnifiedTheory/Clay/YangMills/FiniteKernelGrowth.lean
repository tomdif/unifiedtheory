/- Kernel-chain growth estimates with all boundary constants retained.
A complex eigenfunction is controlled by positive path integrals; a positive
comparison eigenfunction bounds those integrals from above. These are fixed
compact-space statements, not uniform Yang-Mills mass-gap estimates. -/
import UnifiedTheory.Clay.YangMills.FiniteKernelChain
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteKernelGrowth
noncomputable section
open MeasureTheory FiniteKernelChain Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

local instance pathBorel (L : ℕ) : BorelSpace (Path (X := X) L) := Pi.borelSpace

theorem endpoint_lower (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (B : C(X, ℝ)) (c : ℝ) (hc : 0 ≤ c) (hB : ∀ x, c ≤ B x) (L : ℕ) :
    c^2 * endpoint μ K L 1 1 ≤ endpoint μ K L B B := by
  unfold endpoint
  rw [← integral_const_mul]
  apply integral_mono
  · exact (continuous_const.mul (endpoint_continuous K L 1 1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (endpoint_continuous K L B B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro u
    have hp : 0 ≤ chain K L u := Finset.prod_nonneg (fun t _ => hK _ _)
    have hb := mul_le_mul (hB (u 0)) (hB (u (Fin.last L))) hc (hc.trans (hB (u 0)))
    have hh := mul_le_mul_of_nonneg_right hb hp
    simpa only [ContinuousMap.one_apply, one_mul, mul_one, pow_two, mul_assoc, mul_comm,
      mul_left_comm] using hh

theorem endpoint_upper (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (B ψ : C(X, ℝ)) (hB : ∀ x, 0 ≤ B x) (lam C : ℝ)
    (hψ : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (hcomp : ∀ x, B x ≤ C * ψ x) (L : ℕ) :
    endpoint μ K L B B ≤ (C * ∫ x, B x * ψ x ∂μ) * lam^L := by
  rw [endpoint_message]
  have hm (x : X) := message_mono μ K hK B (C • ψ) hcomp L x
  simp only [message_smul, ContinuousMap.smul_apply, smul_eq_mul, message_eigen μ K ψ lam hψ]
    at hm
  calc
    _ ≤ ∫ x, B x * (C * (lam^L * ψ x)) ∂μ := by
      apply integral_mono
      · exact (B.continuous.mul (message μ K B L).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (B.continuous.mul (continuous_const.mul
          (continuous_const.mul ψ.continuous))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      · intro x
        exact mul_le_mul_of_nonneg_left (hm x) (hB x)
    _ = _ := by
      have he (x : X) : B x * (C * (lam^L * ψ x)) = (C * lam^L) * (B x * ψ x) := by ring
      simp_rw [he]
      rw [integral_const_mul]
      ring

omit [SecondCountableTopology X] in
theorem eigen_message_bound (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (ψ : C(X, ℂ)) (lam M : ℝ) (hlam : 0 ≤ lam) (hM : ∀ x, ‖ψ x‖ ≤ M)
    (hψ : ∀ x, (∫ y, (K (x, y) : ℂ) * ψ y ∂μ) = (lam : ℂ) * ψ x)
    (L : ℕ) (x : X) : lam^L * ‖ψ x‖ ≤ M * message μ K 1 L x := by
  induction L generalizing x with
  | zero => simpa [message] using hM x
  | succ L ih =>
    calc
      _ = lam^L * ‖∫ y, (K (x, y) : ℂ) * ψ y ∂μ‖ := by
        rw [hψ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam, pow_succ]
        ring
      _ ≤ lam^L * ∫ y, ‖(K (x, y) : ℂ) * ψ y‖ ∂μ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (pow_nonneg hlam _)
      _ = ∫ y, K (x, y) * (lam^L * ‖ψ y‖) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK x y)]
        ring
      _ ≤ ∫ y, K (x, y) * (M * message μ K 1 L y) ∂μ := by
        apply integral_mono
        · exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (continuous_const.mul ψ.continuous.norm)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
        · exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
            (continuous_const.mul (message μ K 1 L).continuous)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
        · intro y
          exact mul_le_mul_of_nonneg_left (ih y) (hK x y)
      _ = _ := by
        simp_rw [mul_left_comm (K (x,_)) M]
        rw [integral_const_mul, message_succ]

theorem message_partition_bound (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (C : ℝ) (hC : ∀ x y, K (x, y) ≤ C) (L : ℕ) (x : X) :
    message μ K 1 (L + 1) x ≤ C * endpoint μ K L 1 1 := by
  rw [message_succ, endpoint_message, ← integral_const_mul]
  simp only [ContinuousMap.one_apply, one_mul]
  apply integral_mono
  · exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (message μ K 1 L).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul (message μ K 1 L).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro y
    exact mul_le_mul_of_nonneg_right (hC x y)
      (message_nonneg μ K hK 1 (fun _ => by simp) L y)

theorem eigen_partition_bound (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (B : C(X, ℝ)) (c : ℝ) (hc : 0 ≤ c) (hB : ∀ x, c ≤ B x)
    (ψ : C(X, ℂ)) (lam M C : ℝ) (hlam : 0 ≤ lam) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hM : ∀ x, ‖ψ x‖ ≤ M) (hC : ∀ x y, K (x, y) ≤ C)
    (hψ : ∀ x, (∫ y, (K (x, y) : ℂ) * ψ y ∂μ) = (lam : ℂ) * ψ x)
    (L : ℕ) (x : X) :
    c^2 * (lam^(L + 1) * ‖ψ x‖) ≤ (M * C) * endpoint μ K L B B := by
  have he := eigen_message_bound μ K hK ψ lam M hlam hM hψ (L + 1) x
  have hp := message_partition_bound μ K hK C hC L x
  have hb := endpoint_lower μ K hK B c hc hB L
  calc
    _ ≤ c^2 * (M * message μ K 1 (L + 1) x) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg c)
    _ ≤ c^2 * (M * (C * endpoint μ K L 1 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hM0) (sq_nonneg c)
    _ = (M * C) * (c^2 * endpoint μ K L 1 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (mul_nonneg hM0 hC0)

/-- Positive prefactors disappear in the exponential growth comparison. -/
theorem rate_le {a b c C : ℝ} (hb : 0 ≤ b) (hc : 0 < c)
    (h : ∀ L : ℕ, c * a^L ≤ C * b^L) : a ≤ b := by
  by_contra! hab
  have ha0 : 0 < a := lt_of_le_of_lt hb hab
  have hr : b / a < 1 := (div_lt_one ha0).mpr hab
  have hr0 : 0 ≤ b / a := div_nonneg hb ha0.le
  have hl := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).const_mul C
  have he (L : ℕ) : c ≤ C * (b / a)^L := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha0 L)).mpr (h L)
  have hzero : c ≤ 0 := ge_of_tendsto (by simpa using hl) (Filter.Eventually.of_forall he)
  linarith

end
end UnifiedTheory.Clay.YangMills.FiniteKernelGrowth
