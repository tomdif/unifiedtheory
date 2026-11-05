/- A positive continuous ground state constructed from the attained top eigenvalue
of the actual full Wilson operator. All normalization is at finite cutoff. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelGroundState
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- A real continuous function viewed in the complex Hilbert space. -/
def complexify (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/-- The pointwise modulus of a continuous complex function. -/
def modulus (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => ‖f x‖, f.continuous.norm⟩

theorem embedding_norm_sq (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  apply Complex.ofReal_injective
  have h := MeasureTheory.ContinuousMap.inner_toLp μ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [Complex.mul_conj, ← Complex.sq_norm] at h
  rw [integral_complex_ofReal] at h
  simpa only [Complex.ofReal_pow] using h

theorem real_embedding_norm_sq (f : C(X, ℝ)) :
    ‖ContinuousMap.toLp 2 μ ℂ (complexify f)‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [embedding_norm_sq]
  congr 1
  ext x
  simp [complexify, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem modulus_embedding_norm (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ (complexify (modulus f))‖ =
      ‖ContinuousMap.toLp 2 μ ℂ f‖ := by
  have h := real_embedding_norm_sq μ (modulus f)
  change _ = ∫ x, ‖f x‖ ^ 2 ∂μ at h
  rw [← embedding_norm_sq μ f] at h
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 μ ℂ (complexify (modulus f))),
    norm_nonneg (ContinuousMap.toLp 2 μ ℂ f)]

/-- The real representative obtained by integrating the actual real kernel. -/
def realSmoothing (K : C(X × X, ℝ)) (f : C(X, ℝ)) : C(X, ℝ) :=
  ⟨fun x => (CompactKernelOperator.smoothing μ K
    (ContinuousMap.toLp 2 μ ℂ (complexify f)) x).re,
    Complex.continuous_re.comp (CompactKernelOperator.smoothing μ K
      (ContinuousMap.toLp 2 μ ℂ (complexify f))).continuous⟩

theorem realSmoothing_integral (K : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    realSmoothing μ K f x = ∫ y, K (x, y) * f y ∂μ := by
  change (CompactKernelOperator.smoothing μ K
    (ContinuousMap.toLp 2 μ ℂ (complexify f)) x).re = _
  rw [CompactKernelOperator.smoothing_continuous_input]
  simp only [complexify, ContinuousMap.coe_mk, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]

theorem complexify_realSmoothing (K : C(X × X, ℝ)) (f : C(X, ℝ)) :
    complexify (realSmoothing μ K f) = CompactKernelOperator.smoothing μ K
      (ContinuousMap.toLp 2 μ ℂ (complexify f)) := by
  ext x
  change (realSmoothing μ K f x : ℂ) = _
  rw [realSmoothing_integral, CompactKernelOperator.smoothing_continuous_input]
  simp only [complexify, ContinuousMap.coe_mk, ← Complex.ofReal_mul,
    integral_complex_ofReal]


omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem complexify_smul (c : ℝ) (f : C(X, ℝ)) :
    complexify (c • f) = (c : ℂ) • complexify f := by
  ext x
  simp [complexify, Complex.ofReal_mul]

/-- Equality in the monotonicity of the L² norm forces equality of nonnegative functions. -/
theorem embedding_eq_of_le_of_norm_le (f g : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (hn : ‖ContinuousMap.toLp 2 μ ℂ (complexify g)‖ ≤
      ‖ContinuousMap.toLp 2 μ ℂ (complexify f)‖) :
    ContinuousMap.toLp 2 μ ℂ (complexify f) =
      ContinuousMap.toLp 2 μ ℂ (complexify g) := by
  have hfi : Integrable (fun x => (f x) ^ 2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable (fun x => (g x) ^ 2) μ :=
    (g.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsq (x : X) : (f x) ^ 2 ≤ (g x) ^ 2 := by
    nlinarith [hf x, hfg x]
  have hie : (∫ x, (f x) ^ 2 ∂μ) = ∫ x, (g x) ^ 2 ∂μ := by
    apply le_antisymm (integral_mono hfi hgi hsq)
    rw [← real_embedding_norm_sq, ← real_embedding_norm_sq]
    nlinarith [norm_nonneg (ContinuousMap.toLp 2 μ ℂ (complexify g))]
  have hae := (integral_eq_iff_of_ae_le hfi hgi (Eventually.of_forall hsq)).mp hie
  apply Lp.ext
  filter_upwards [(complexify f).coeFn_toLp (p := 2) (𝕜 := ℂ) μ,
    (complexify g).coeFn_toLp (p := 2) (𝕜 := ℂ) μ, hae] with x hxf hxg hxe
  rw [hxf, hxg]
  change (f x : ℂ) = (g x : ℂ)
  congr 1
  nlinarith [hf x, hfg x]


/-- A nonnegative continuous function with unit L² norm has positive mean. -/
theorem integral_pos_of_nonneg_of_embedding_norm_one (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) (hn : ‖ContinuousMap.toLp 2 μ ℂ (complexify f)‖ = 1) :
    0 < ∫ x, f x ∂μ := by
  have hi := f.continuous.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf
  by_contra! h
  have he := (integral_eq_zero_iff_of_nonneg hf hi).mp (le_antisymm h hnonneg)
  have hemb : ContinuousMap.toLp 2 μ ℂ (complexify f) = 0 := by
    apply Lp.ext
    filter_upwards [(complexify f).coeFn_toLp (p := 2) (𝕜 := ℂ) μ,
      he, (Lp.coeFn_zero ℂ 2 μ)] with x hx he hz
    rw [hx, hz]
    change (f x : ℂ) = 0
    simp only [Pi.zero_apply] at he
    simp [he]
  rw [hemb, norm_zero] at hn
  norm_num at hn

open WilsonSlabOperator WilsonTimeSlab

variable (n : ℕ) [NeZero n]

/-- The actual full Wilson transfer has an everywhere strictly positive real,
continuous, gauge-invariant unit ground state, constructed from its top eigenvalue. -/
theorem exists_positive_top_eigenfunction (β : ℝ) (hβ : 0 ≤ β) :
    ∃ η : C(Slice n, ℝ),
      (∀ u, 0 < η u) ∧
      (∫ u, (η u) ^ 2 ∂WilsonSlabOperator.measure n) = 1 ∧
      ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (complexify η)‖ = 1 ∧
      (∀ h : SliceGauge n WilsonSlabOperator.Q, ∀ u, η (gaugeSlice h u) = η u) ∧
      ∀ u, (∫ v, kernel WilsonSingleLinkStaples.character β 2 u v * η v
        ∂WilsonSlabOperator.measure n) = ‖transfer n β‖ * η u := by
  let μ := WilsonSlabOperator.measure n
  let K := kernelMap n β
  let lam := ‖transfer n β‖
  have hlam : 0 < lam := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  obtain ⟨ψ, hψnorm, _, hψeig⟩ :=
    PositiveKernelGroundState.exists_continuous_top_eigenfunction n β hβ
  let φ := modulus ψ
  let g := realSmoothing μ K φ
  have hφ (u : Slice n) : 0 ≤ φ u := by
    change 0 ≤ ‖ψ u‖
    exact norm_nonneg _
  have hφnorm : ‖ContinuousMap.toLp 2 μ ℂ (complexify φ)‖ = 1 :=
    (modulus_embedding_norm μ ψ).trans hψnorm
  have hK (u v : Slice n) : 0 ≤ K (u, v) :=
    (kernel_positive WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2 u v).le
  have horder (u : Slice n) : lam * φ u ≤ g u := by
    have ht := norm_integral_le_integral_norm
      (fun v => (kernel WilsonSingleLinkStaples.character β 2 u v : ℂ) * ψ v)
        (μ := μ)
    rw [hψeig u] at ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm] at ht
    rw [realSmoothing_integral]
    exact ht.trans_eq (integral_congr_ae (Eventually.of_forall (fun v => by
      change |K (u, v)| * ‖ψ v‖ = K (u, v) * φ v
      rw [abs_of_nonneg (hK u v)]
      rfl)))
  have hgnorm : ‖ContinuousMap.toLp 2 μ ℂ (complexify g)‖ ≤ lam := by
    rw [complexify_realSmoothing]
    change ‖transfer n β (ContinuousMap.toLp 2 μ ℂ (complexify φ))‖ ≤ lam
    exact ((transfer n β).le_opNorm _).trans_eq (by rw [hφnorm, mul_one])
  have hscaled : ‖ContinuousMap.toLp 2 μ ℂ (complexify (lam • φ))‖ = lam := by
    rw [complexify_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlam, hφnorm, mul_one]
  have hemb := embedding_eq_of_le_of_norm_le μ (lam • φ) g
    (fun u => mul_nonneg hlam.le (hφ u)) horder (hgnorm.trans_eq hscaled.symm)
  let η : C(Slice n, ℝ) := lam⁻¹ • g
  have hηemb : ContinuousMap.toLp 2 μ ℂ (complexify η) =
      ContinuousMap.toLp 2 μ ℂ (complexify φ) := by
    change ContinuousMap.toLp 2 μ ℂ (complexify (lam⁻¹ • g)) = _
    rw [complexify_smul, map_smul, ← hemb, complexify_smul, map_smul, smul_smul]
    simp only [Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'),
      one_smul]
  have hηnorm : ‖ContinuousMap.toLp 2 μ ℂ (complexify η)‖ = 1 := by
    rw [hηemb, hφnorm]
  have hmean : 0 < ∫ u, φ u ∂μ :=
    integral_pos_of_nonneg_of_embedding_norm_one μ φ hφ hφnorm
  have hgpos (u : Slice n) : 0 < g u := by
    let m := Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))
    have hmi : Integrable (fun v => m * φ v) μ :=
      (continuous_const.mul φ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgi : Integrable (fun v => K (u, v) * φ v) μ :=
      ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        φ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi := integral_mono hmi hgi (fun v => mul_le_mul_of_nonneg_right
      (WilsonSlabBounds.kernel_bounds n β hβ u v).1 (hφ v))
    rw [integral_const_mul, ← realSmoothing_integral] at hi
    exact (mul_pos (Real.exp_pos _) hmean).trans_le hi
  refine ⟨η, ?_, ?_, hηnorm, ?_, ?_⟩
  · intro u
    exact mul_pos (inv_pos.mpr hlam) (hgpos u)
  · rw [← real_embedding_norm_sq, hηnorm, one_pow]
  · intro h u
    change lam⁻¹ * (representative n β
      (ContinuousMap.toLp 2 μ ℂ (complexify φ)) (gaugeSlice h u)).re =
      lam⁻¹ * (representative n β (ContinuousMap.toLp 2 μ ℂ (complexify φ)) u).re
    rw [representative_gauge]
  · intro u
    change (∫ v, K (u, v) * η v ∂μ) = lam * η u
    rw [← realSmoothing_integral]
    have hsm : realSmoothing μ K η u = g u := by
      change (CompactKernelOperator.smoothing μ K
        (ContinuousMap.toLp 2 μ ℂ (complexify η)) u).re = _
      rw [hηemb]
      rfl
    rw [hsm]
    change g u = lam * (lam⁻¹ * g u)
    rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]


/-- Every nonnegative top eigenfunction obeys the explicit finite-volume profile comparison. -/
theorem top_eigenfunction_profile_comparison (β : ℝ) (hβ : 0 ≤ β)
    (η : C(Slice n, ℝ)) (hηnonneg : ∀ u, 0 ≤ η u)
    (hη : ∀ u, (∫ v, kernel WilsonSingleLinkStaples.character β 2 u v * η v
      ∂WilsonSlabOperator.measure n) = ‖transfer n β‖ * η u) (u v : Slice n) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) * η v ≤ η u := by
  let μ := WilsonSlabOperator.measure n
  let m := Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))
  have hm : 0 < m := Real.exp_pos _
  have hlam : 0 < ‖transfer n β‖ :=
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have hi : Integrable (fun w => η w) μ := η.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hki (z : Slice n) : Integrable
      (fun w => kernel WilsonSingleLinkStaples.character β 2 z w * η w) μ :=
    (((kernelMap n β).continuous.comp (continuous_const.prodMk continuous_id)).mul
      η.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hu := integral_mono (hi.const_mul m) (hki u) (fun w =>
    mul_le_mul_of_nonneg_right (WilsonSlabBounds.kernel_bounds n β hβ u w).1 (hηnonneg w))
  have hv := integral_mono (hki v) hi (fun w => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (WilsonSlabBounds.kernel_bounds n β hβ v w).2 (hηnonneg w))
  rw [integral_const_mul, hη u] at hu
  rw [hη v] at hv
  apply (mul_le_mul_iff_right₀ hlam).mp
  nlinarith [mul_le_mul_of_nonneg_left hv hm.le]

/-- Unit-normalized positive ground-state profiles have explicit pointwise upper and lower bounds.
These bounds depend exponentially on coupling times spatial volume. -/
theorem top_eigenfunction_profile_bounds (β : ℝ) (hβ : 0 ≤ β)
    (η : C(Slice n, ℝ)) (hηnonneg : ∀ u, 0 ≤ η u)
    (hηnorm : (∫ u, (η u) ^ 2 ∂WilsonSlabOperator.measure n) = 1)
    (hη : ∀ u, (∫ v, kernel WilsonSingleLinkStaples.character β 2 u v * η v
      ∂WilsonSlabOperator.measure n) = ‖transfer n β‖ * η u) (u : Slice n) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) ≤ η u ∧
      η u ≤ (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))))⁻¹ := by
  let μ := WilsonSlabOperator.measure n
  let m := Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))
  have hm : 0 < m := Real.exp_pos _
  have hi : Integrable (fun w => (η w) ^ 2) μ :=
    (η.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow := integral_mono (hi.const_mul (m ^ 2)) (integrable_const ((η u) ^ 2))
    (fun w => by
      have h := top_eigenfunction_profile_comparison n β hβ η hηnonneg hη u w
      change m * η w ≤ η u at h
      nlinarith [hηnonneg u, hηnonneg w, mul_nonneg hm.le (hηnonneg w)])
  rw [integral_const_mul, hηnorm] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at hlow
  have hupp := integral_mono (integrable_const ((m * η u) ^ 2)) hi (fun w => by
    have h := top_eigenfunction_profile_comparison n β hβ η hηnonneg hη w u
    change m * η u ≤ η w at h
    nlinarith [hηnonneg u, hηnonneg w, mul_nonneg hm.le (hηnonneg u)])
  rw [hηnorm] at hupp
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hupp
  constructor
  · change m ≤ η u
    nlinarith [hηnonneg u]
  · change η u ≤ m⁻¹
    rw [← one_div, le_div_iff₀ hm]
    nlinarith [mul_nonneg hm.le (hηnonneg u)]

end
end UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
