/- A finite-chain insertion floor controls the actual compact positive
operator norm. Boundary prefactors are proved irrelevant to the growth rate;
no reflected or positive modified-ground profile is assumed. -/
import UnifiedTheory.Clay.YangMills.FiniteKernelGrowth
import UnifiedTheory.Clay.YangMills.PositiveKernelGroundState

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.KernelPartitionNorm
noncomputable section
open MeasureTheory FiniteKernelChain FiniteKernelGrowth CompactKernelOperator

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem positive_floor [Nonempty X] (B : C(X, ℝ)) (hB : ∀ x, 0 < B x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ B x := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty B.continuous.continuousOn
  exact ⟨B x,hB x,fun y => hx (Set.mem_univ y)⟩

theorem norm_comparison (K₀ K : C(X × X, ℝ))
    (hpos : (operator μ K₀).IsPositive)
    (hK₀ : ∀ x y, 0 ≤ K₀ (x, y)) (hK : ∀ x y, 0 ≤ K (x, y))
    (B₀ B ψ : C(X, ℝ)) (c : ℝ) (hc : 0 < c) (hB₀ : ∀ x, c ≤ B₀ x)
    (hB : ∀ x, 0 ≤ B x) (lam C : ℝ) (hlam : 0 ≤ lam)
    (hψ : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x)
    (hcomp : ∀ x, B x ≤ C * ψ x) (m : ℝ) (hm : 0 < m)
    (hfloor : ∀ L : ℕ, m^(L + 1) * endpoint μ K₀ L B₀ B₀ ≤ endpoint μ K L B B) :
    m * ‖operator μ K₀‖ ≤ lam := by
  by_cases hz : operator μ K₀ = 0
  · simpa only [hz, norm_zero, mul_zero] using hlam
  obtain ⟨hlam0,v,hvnorm,hve⟩ := PositiveKernelGroundState.positive_compact_top_eigenvector
    (operator μ K₀) hpos (operator_compact μ K₀) hz
  let lam0 := ‖operator μ K₀‖
  change 0 < lam0 at hlam0
  change operator μ K₀ v = lam0 • v at hve
  let φ : C(X, ℂ) := (lam0 : ℂ)⁻¹ • smoothing μ K₀ v
  have hembed : ContinuousMap.toLp 2 μ ℂ φ = v := by
    rw [show φ = (lam0 : ℂ)⁻¹ • smoothing μ K₀ v from rfl, map_smul]
    change (lam0 : ℂ)⁻¹ • operator μ K₀ v = v
    rw [hve, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change (((lam0 : ℂ)⁻¹) * (lam0 : ℂ)) • v = v
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam0.ne'), one_smul]
  have hφ (x : X) : (∫ y, (K₀ (x, y) : ℂ) * φ y ∂μ) = (lam0 : ℂ) * φ x := by
    rw [← smoothing_continuous_input, hembed]
    change smoothing μ K₀ v x = (lam0 : ℂ) * ((lam0 : ℂ)⁻¹ * smoothing μ K₀ v x)
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hlam0.ne'), one_mul]
  obtain ⟨x,hx⟩ : ∃ x : X, φ x ≠ 0 := by
    by_contra! hh
    have hzero : φ = 0 := ContinuousMap.ext hh
    have hvzero : v = 0 := by rw [← hembed, hzero, map_zero]
    rw [hvzero, norm_zero] at hvnorm
    norm_num at hvnorm
  have hbound (L : ℕ) := eigen_partition_bound μ K₀ hK₀ B₀ c hc.le hB₀ φ lam0
    ‖φ‖ ‖K₀‖ hlam0.le (norm_nonneg _) (norm_nonneg _)
    (fun y => ContinuousMap.norm_coe_le_norm φ y)
    (fun y z => (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm K₀ (y, z))) hφ L x
  have hupper (L : ℕ) := endpoint_upper μ K hK B ψ hB lam C hψ hcomp L
  apply rate_le hlam (c := c^2 * m * lam0 * ‖φ x‖)
    (C := (‖φ‖ * ‖K₀‖) * (C * ∫ y, B y * ψ y ∂μ))
    (by positivity [norm_pos_iff.mpr hx])
  intro L
  calc
    _ = m^(L + 1) * (c^2 * (lam0^(L + 1) * ‖φ x‖)) := by rw [mul_pow, pow_succ, pow_succ]; ring
    _ ≤ m^(L + 1) * ((‖φ‖ * ‖K₀‖) * endpoint μ K₀ L B₀ B₀) :=
      mul_le_mul_of_nonneg_left (hbound L) (pow_nonneg hm.le _)
    _ = (‖φ‖ * ‖K₀‖) * (m^(L + 1) * endpoint μ K₀ L B₀ B₀) := by ring
    _ ≤ (‖φ‖ * ‖K₀‖) * endpoint μ K L B B :=
      mul_le_mul_of_nonneg_left (hfloor L) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (hupper L)
        (mul_nonneg (norm_nonneg φ) (norm_nonneg K₀))
      simpa only [mul_assoc] using hh

end
end UnifiedTheory.Clay.YangMills.KernelPartitionNorm
