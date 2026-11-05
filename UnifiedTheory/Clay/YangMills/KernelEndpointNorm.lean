/- Bounds on actual finite-chain growth using operator norms. The upper
bound requires no modified ground-state eigenfunction. The lower bound is
proved from compact positivity and a strictly positive endpoint floor. -/
import UnifiedTheory.Clay.YangMills.KernelPartitionNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.KernelEndpointNorm
noncomputable section
open MeasureTheory FiniteKernelChain FiniteKernelGrowth CompactKernelOperator
open WilsonPositiveGroundState TransferEnergySurvival

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [SecondCountableTopology X] in
theorem message_embedding (K : C(X × X, ℝ)) (B : C(X, ℝ)) (L : ℕ) :
    ContinuousMap.toLp 2 μ ℂ (complexify (message μ K B L)) =
      iterate (operator μ K) L (ContinuousMap.toLp 2 μ ℂ (complexify B)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change ContinuousMap.toLp 2 μ ℂ (complexify (realSmoothing μ K (message μ K B L))) = _
    rw [complexify_realSmoothing]
    change operator μ K (ContinuousMap.toLp 2 μ ℂ (complexify (message μ K B L))) = _
    rw [ih, iterate_succ]

omit [SecondCountableTopology X] in
theorem message_norm (K : C(X × X, ℝ)) (B : C(X, ℝ)) (L : ℕ) :
    ‖ContinuousMap.toLp 2 μ ℂ (complexify (message μ K B L))‖ ≤
      ‖operator μ K‖^L * ‖ContinuousMap.toLp 2 μ ℂ (complexify B)‖ := by
  rw [message_embedding]
  induction L with
  | zero => simp [iterate]
  | succ L ih =>
    rw [iterate_succ]
    exact ((operator μ K).le_opNorm _).trans
      (by simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left ih (norm_nonneg (operator μ K)))

theorem endpoint_inner (K : C(X × X, ℝ)) (B : C(X, ℝ)) (L : ℕ) :
    (endpoint μ K L B B : ℂ) =
      inner ℂ (ContinuousMap.toLp 2 μ ℂ (complexify B))
        (ContinuousMap.toLp 2 μ ℂ (complexify (message μ K B L))) := by
  rw [endpoint_message, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [complexify, ContinuousMap.coe_mk, Complex.conj_ofReal,
    ← Complex.ofReal_mul, integral_complex_ofReal, mul_comm]

theorem endpoint_upper_norm (K : C(X × X, ℝ)) (B : C(X, ℝ)) (L : ℕ) :
    endpoint μ K L B B ≤
      ‖ContinuousMap.toLp 2 μ ℂ (complexify B)‖^2 * ‖operator μ K‖^L := by
  have hi := norm_inner_le_norm (𝕜 := ℂ)
    (ContinuousMap.toLp 2 μ ℂ (complexify B))
    (ContinuousMap.toLp 2 μ ℂ (complexify (message μ K B L)))
  rw [← endpoint_inner, Complex.norm_real, Real.norm_eq_abs] at hi
  have hm := mul_le_mul_of_nonneg_left (message_norm μ K B L)
    (norm_nonneg (ContinuousMap.toLp 2 μ ℂ (complexify B)))
  exact (le_abs_self _).trans (hi.trans (by convert hm using 1; ring))

theorem endpoint_lower_rate (K : C(X × X, ℝ))
    (hpos : (operator μ K).IsPositive) (hne : operator μ K ≠ 0)
    (hK : ∀ x y, 0 ≤ K (x, y)) (B : C(X, ℝ))
    (c : ℝ) (hc : 0 < c) (hB : ∀ x, c ≤ B x) :
    ∃ a A : ℝ, 0 < a ∧ 0 ≤ A ∧
      ∀ L : ℕ, a * ‖operator μ K‖^L ≤ A * endpoint μ K L B B := by
  obtain ⟨hlam,v,hvnorm,hve⟩ := PositiveKernelGroundState.positive_compact_top_eigenvector
    (operator μ K) hpos (operator_compact μ K) hne
  let lam := ‖operator μ K‖
  let φ : C(X, ℂ) := (lam : ℂ)⁻¹ • smoothing μ K v
  have hembed : ContinuousMap.toLp 2 μ ℂ φ = v := by
    rw [show φ = (lam : ℂ)⁻¹ • smoothing μ K v from rfl, map_smul]
    change (lam : ℂ)⁻¹ • operator μ K v = v
    rw [hve, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change (((lam : ℂ)⁻¹) * (lam : ℂ)) • v = v
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_smul]
  have hφ (x : X) : (∫ y, (K (x, y) : ℂ) * φ y ∂μ) = (lam : ℂ) * φ x := by
    rw [← smoothing_continuous_input, hembed]
    change smoothing μ K v x = (lam : ℂ) * ((lam : ℂ)⁻¹ * smoothing μ K v x)
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_mul]
  obtain ⟨x,hx⟩ : ∃ x : X, φ x ≠ 0 := by
    by_contra! hh
    have hz : φ = 0 := ContinuousMap.ext hh
    have hvz : v = 0 := by rw [← hembed, hz, map_zero]
    rw [hvz, norm_zero] at hvnorm
    norm_num at hvnorm
  refine ⟨c^2 * lam * ‖φ x‖, ‖φ‖ * ‖K‖, ?_, by positivity, ?_⟩
  · positivity [norm_pos_iff.mpr hx]
  · intro L
    have h := eigen_partition_bound μ K hK B c hc.le hB φ lam ‖φ‖ ‖K‖
      hlam.le (norm_nonneg _) (norm_nonneg _)
      (fun y => ContinuousMap.norm_coe_le_norm φ y)
      (fun y z => (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm K (y, z))) hφ L x
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- The square partition comparison passes to the actual compact operator
norms; all endpoint constants disappear in the exponential growth rate. -/
theorem norm_schwarz (K Kp Km : C(X × X, ℝ))
    (hpos : (operator μ K).IsPositive) (hK : ∀ x y, 0 ≤ K (x, y))
    (B Bp Bm : C(X, ℝ)) (c : ℝ) (hc : 0 < c) (hB : ∀ x, c ≤ B x)
    (hminus : ∀ L, 0 ≤ endpoint μ Km L Bm Bm)
    (hcs : ∀ L, (endpoint μ K L B B) ^ 2 ≤
      endpoint μ Kp L Bp Bp * endpoint μ Km L Bm Bm) :
    ‖operator μ K‖^2 ≤ ‖operator μ Kp‖ * ‖operator μ Km‖ := by
  by_cases hz : operator μ K = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  obtain ⟨a,A,ha,hA,hlower⟩ := endpoint_lower_rate μ K hpos hz hK B c hc hB
  apply rate_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (c := a^2)
    (C := A^2 * (‖ContinuousMap.toLp 2 μ ℂ (complexify Bp)‖^2 *
      ‖ContinuousMap.toLp 2 μ ℂ (complexify Bm)‖^2)) (sq_pos_of_pos ha)
  intro L
  have hl := pow_le_pow_left₀ (mul_nonneg ha.le (pow_nonneg (norm_nonneg _) _)) (hlower L) 2
  have hp := mul_le_mul (endpoint_upper_norm μ Kp Bp L) (endpoint_upper_norm μ Km Bm L)
    (hminus L) (by positivity)
  have hh := mul_le_mul_of_nonneg_left ((hcs L).trans hp) (sq_nonneg A)
  calc
    _ = (a * ‖operator μ K‖^L)^2 := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
    _ ≤ (A * endpoint μ K L B B)^2 := hl
    _ ≤ _ := by
      rw [mul_pow]
      convert hh using 1; ring

end
end UnifiedTheory.Clay.YangMills.KernelEndpointNorm
