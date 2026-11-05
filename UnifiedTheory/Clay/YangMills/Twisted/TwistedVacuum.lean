/- The top eigenvector of the twisted transfer operator at finite cutoff is strictly
positive, unique and invariant under every center flip. The bound degenerates with the
cutoff, so this gives a well-posed neutral vacuum and no uniform gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer
import UnifiedTheory.Clay.YangMills.PositiveKernelRatio
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum
noncomputable section
open MeasureTheory Filter WilsonTimeSlab WilsonSlabOperator TwistedFlat TwistedTransfer
open WilsonPositiveGroundState (complexify modulus realSmoothing realSmoothing_integral
  complexify_realSmoothing complexify_smul embedding_eq_of_le_of_norm_le
  integral_pos_of_nonneg_of_embedding_norm_one modulus_embedding_norm)
open scoped InnerProductSpace

variable (n : ℕ) [NeZero n]

local notation "μ'" => WilsonSlabOperator.measure n

/-- Output representative of the twisted operator. -/
def representative (β : ℝ) (f : Hilbert n) : C(Slice n, ℂ) :=
  CompactKernelOperator.smoothing (μ') (twistedKernel n β) f

theorem eigenfunction_embedding (β lam : ℝ) (hlam : lam ≠ 0) (v : Hilbert n)
    (hv : TwistedTransfer.transfer n β v = lam • v) :
    ContinuousMap.toLp 2 (μ') ℂ ((lam : ℂ)⁻¹ • representative n β v) = v := by
  rw [map_smul]
  change (lam : ℂ)⁻¹ • TwistedTransfer.transfer n β v = v
  rw [hv, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  change (((lam : ℂ)⁻¹) * (lam : ℂ)) • v = v
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam), one_smul]

/-- A continuous representative of a nonzero eigenvector, solving the kernel equation. -/
theorem continuous_eigenfunction (β rho : ℝ) (hrho : rho ≠ 0) (v : Hilbert n)
    (heig : TwistedTransfer.transfer n β v = rho • v) :
    ∃ f : C(Slice n, ℂ), ContinuousMap.toLp 2 (μ') ℂ f = v ∧
      ∀ u, (∫ w, (twistedKernel n β (u, w) : ℂ) * f w ∂μ') = (rho : ℂ) * f u := by
  let f : C(Slice n, ℂ) := (rho : ℂ)⁻¹ • representative n β v
  have hf : ContinuousMap.toLp 2 (μ') ℂ f = v := eigenfunction_embedding n β rho hrho v heig
  refine ⟨f, hf, fun u => ?_⟩
  calc
    _ = representative n β (ContinuousMap.toLp 2 (μ') ℂ f) u :=
      (CompactKernelOperator.smoothing_continuous_input (μ') (twistedKernel n β) f u).symm
    _ = representative n β v u := by rw [hf]
    _ = (rho : ℂ) * f u := by
      dsimp only [f, ContinuousMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hrho), one_mul]

/-- Positive bounds on the twisted kernel, from compactness. -/
theorem kernel_bounds (β : ℝ) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u v, m ≤ twistedKernel n β (u, v) ∧
      twistedKernel n β (u, v) ≤ M := by
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Slice n × Slice n))
    (twistedKernel n β).continuous.continuousOn
  obtain ⟨q, -, hq⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := Slice n × Slice n))
    (twistedKernel n β).continuous.continuousOn
  exact ⟨_, _, twistedKernel_pos n β p, twistedKernel_pos n β q,
    fun u v => ⟨hp (Set.mem_univ (u, v)), hq (Set.mem_univ (u, v))⟩⟩

/-- A strictly positive continuous unit ground state. -/
theorem exists_positive_top (β : ℝ) (hβ : 0 ≤ β) :
    ∃ η : C(Slice n, ℝ), (∀ u, 0 < η u) ∧
      ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1 ∧
      ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖TwistedTransfer.transfer n β‖ * η u := by
  let K := twistedKernel n β
  let lam := ‖TwistedTransfer.transfer n β‖
  obtain ⟨hlam, v, hvnorm, hv⟩ := top_eigenvector n β hβ
  have hlam' : 0 < lam := hlam
  obtain ⟨ψ, hψ, hψeig⟩ := continuous_eigenfunction n β lam hlam.ne' v hv
  have hψnorm : ‖ContinuousMap.toLp 2 (μ') ℂ ψ‖ = 1 := by rw [hψ, hvnorm]
  let φ := modulus ψ
  let g := realSmoothing (μ') K φ
  have hφ (u : Slice n) : 0 ≤ φ u := by
    change 0 ≤ ‖ψ u‖
    exact norm_nonneg _
  have hφnorm : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify φ)‖ = 1 :=
    (modulus_embedding_norm (μ') ψ).trans hψnorm
  have hK (u v : Slice n) : 0 ≤ K (u, v) := (twistedKernel_pos n β (u, v)).le
  have horder (u : Slice n) : lam * φ u ≤ g u := by
    have ht := norm_integral_le_integral_norm
      (fun v => (twistedKernel n β (u, v) : ℂ) * ψ v) (μ := μ')
    rw [hψeig u] at ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
    rw [abs_of_pos hlam'] at ht
    rw [realSmoothing_integral]
    change lam * ‖ψ u‖ ≤ _
    exact ht.trans_eq (integral_congr_ae (Eventually.of_forall (fun v => by
      change |K (u, v)| * ‖ψ v‖ = K (u, v) * φ v
      rw [abs_of_nonneg (hK u v)]
      rfl)))
  have hgnorm : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify g)‖ ≤ lam := by
    rw [complexify_realSmoothing]
    change ‖TwistedTransfer.transfer n β (ContinuousMap.toLp 2 (μ') ℂ (complexify φ))‖ ≤ lam
    exact ((TwistedTransfer.transfer n β).le_opNorm _).trans_eq (by rw [hφnorm, mul_one])
  have hscaled : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify (lam • φ))‖ = lam := by
    rw [complexify_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlam', hφnorm, mul_one]
  have hemb := embedding_eq_of_le_of_norm_le (μ') (lam • φ) g
    (fun u => mul_nonneg hlam'.le (hφ u)) horder (hgnorm.trans_eq hscaled.symm)
  let η : C(Slice n, ℝ) := lam⁻¹ • g
  have hηemb : ContinuousMap.toLp 2 (μ') ℂ (complexify η) =
      ContinuousMap.toLp 2 (μ') ℂ (complexify φ) := by
    change ContinuousMap.toLp 2 (μ') ℂ (complexify (lam⁻¹ • g)) = _
    rw [complexify_smul, map_smul, ← hemb, complexify_smul, map_smul, smul_smul]
    simp only [Complex.ofReal_inv, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam'.ne'),
      one_smul]
  have hηnorm : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1 := by
    rw [hηemb, hφnorm]
  have hmean : 0 < ∫ u, φ u ∂μ' :=
    integral_pos_of_nonneg_of_embedding_norm_one (μ') φ hφ hφnorm
  obtain ⟨m, _, hm, _, hb⟩ := kernel_bounds n β
  have hgpos (u : Slice n) : 0 < g u := by
    have hmi : Integrable (fun v => m * φ v) μ' :=
      (continuous_const.mul φ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hgi : Integrable (fun v => K (u, v) * φ v) μ' :=
      ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        φ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi := integral_mono hmi hgi (fun v => mul_le_mul_of_nonneg_right (hb u v).1 (hφ v))
    rw [integral_const_mul, ← realSmoothing_integral] at hi
    exact (mul_pos hm hmean).trans_le hi
  refine ⟨η, fun u => mul_pos (inv_pos.mpr hlam') (hgpos u), hηnorm, fun u => ?_⟩
  change (∫ v, K (u, v) * η v ∂μ') = lam * η u
  rw [← realSmoothing_integral]
  have hsm : realSmoothing (μ') K η u = g u := by
    change (CompactKernelOperator.smoothing (μ') K
      (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) u).re = _
    rw [hηemb]
    rfl
  rw [hsm]
  change g u = lam * (lam⁻¹ * g u)
  rw [← mul_assoc, mul_inv_cancel₀ hlam'.ne', one_mul]

theorem flip_continuous (i : Fin 3) (c : ZMod n) : Continuous (TwistedTransfer.flip n i c) := by
  refine continuous_pi fun e => ?_
  unfold TwistedTransfer.flip
  by_cases h : e.2 = i ∧ e.1 i = c
  · simp only [if_pos h]
    exact continuous_const.mul (continuous_apply e)
  · simp only [if_neg h]
    exact continuous_apply e

/-- **The neutral vacuum at finite cutoff.** A unique unit top eigenvector exists up to
phase, and it is invariant under every center flip. -/
theorem neutral_vacuum (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧
      TwistedTransfer.transfer n β Ω = ‖TwistedTransfer.transfer n β‖ • Ω ∧ Neutral n Ω ∧
      ∀ v, TwistedTransfer.transfer n β v = ‖TwistedTransfer.transfer n β‖ • v →
        ∃ c : ℂ, v = c • Ω := by
  obtain ⟨η, hη, hnorm, heig⟩ := exists_positive_top n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  set lam := ‖TwistedTransfer.transfer n β‖ with hlamdef
  obtain ⟨m, M, hm, hM, hb⟩ := kernel_bounds n β
  have hprop (f : C(Slice n, ℂ))
      (hf : ∀ u, (∫ w, (twistedKernel n β (u, w) : ℂ) * f w ∂μ') = (lam : ℂ) * f u) :
      ∃ c : ℂ, ∀ u, f u = c * (η u : ℂ) :=
    PositiveKernelRatio.complex_top_proportional (μ') (twistedKernel n β) η hη lam m M hlam hm hM
      (fun u v => (hb u v).1) (fun u v => (hb u v).2) heig f hf
  let f := complexify η
  have hf (u : Slice n) : (∫ w, (twistedKernel n β (u, w) : ℂ) * f w ∂μ') = (lam : ℂ) * f u := by
    simp only [f, complexify, ContinuousMap.coe_mk, ← Complex.ofReal_mul, integral_complex_ofReal]
    exact congrArg (fun x : ℝ => (x : ℂ)) (heig u)
  have htop : TwistedTransfer.transfer n β (ContinuousMap.toLp 2 (μ') ℂ f) =
      lam • ContinuousMap.toLp 2 (μ') ℂ f := by
    have hs : CompactKernelOperator.smoothing (μ') (twistedKernel n β)
        (ContinuousMap.toLp 2 (μ') ℂ f) = (lam : ℂ) • f := by
      ext u
      rw [CompactKernelOperator.smoothing_continuous_input]
      exact hf u
    change ContinuousMap.toLp 2 (μ') ℂ (CompactKernelOperator.smoothing (μ') (twistedKernel n β)
      (ContinuousMap.toLp 2 (μ') ℂ f)) = _
    rw [hs, map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  refine ⟨ContinuousMap.toLp 2 (μ') ℂ f, hnorm, htop, ?_, ?_⟩
  · intro i c
    have hmp := flip_measurePreserving n i c
    have hmp' : MeasurePreserving (flipEquiv n i c) (μ') (μ') := hmp
    let fσ : C(Slice n, ℂ) := ⟨fun u => f (TwistedTransfer.flip n i c u), f.continuous.comp (flip_continuous n i c)⟩
    have hfσ (u : Slice n) :
        (∫ w, (twistedKernel n β (u, w) : ℂ) * fσ w ∂μ') = (lam : ℂ) * fσ u := by
      change _ = (lam : ℂ) * f (TwistedTransfer.flip n i c u)
      rw [← hf (TwistedTransfer.flip n i c u), ← hmp'.integral_comp'
        (fun w => (twistedKernel n β (TwistedTransfer.flip n i c u, w) : ℂ) * f w)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      change (twistedKernel n β (u, w) : ℂ) * f (TwistedTransfer.flip n i c w) =
        (twistedKernel n β (TwistedTransfer.flip n i c u, TwistedTransfer.flip n i c w) : ℂ) * f (TwistedTransfer.flip n i c w)
      rw [twistedKernel_flip]
    obtain ⟨z, hz⟩ := hprop fσ hfσ
    -- `z` is real positive, and the flip is an involution, so `z = 1`.
    let u₀ : Slice n := fun _ => 1
    have hval (u : Slice n) : (η (TwistedTransfer.flip n i c u) : ℂ) = z * (η u : ℂ) := hz u
    have hzr : z = ((η (TwistedTransfer.flip n i c u₀) / η u₀ : ℝ) : ℂ) := by
      have h0 := hval u₀
      have hne : (η u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hη u₀).ne'
      push_cast
      rw [h0]
      field_simp
    set r : ℝ := η (TwistedTransfer.flip n i c u₀) / η u₀ with hr
    have hrpos : 0 < r := div_pos (hη _) (hη _)
    have hreal (u : Slice n) : η (TwistedTransfer.flip n i c u) = r * η u := by
      have := hval u
      rw [hzr] at this
      exact_mod_cast this
    have hr1 : r = 1 := by
      have h1 := hreal u₀
      have h2 := hreal (TwistedTransfer.flip n i c u₀)
      rw [flip_flip, h1] at h2
      have hne := (hη u₀).ne'
      have : r * r = 1 := by
        have : η u₀ * (r * r - 1) = 0 := by linear_combination -h2
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hne
        · linarith
      nlinarith
    have hinv (u : Slice n) : f (TwistedTransfer.flip n i c u) = f u := by
      simp only [f, complexify, ContinuousMap.coe_mk]
      rw [hreal, hr1, one_mul]
    apply Lp.ext
    have h1 : (flipOp n i c (ContinuousMap.toLp 2 (μ') ℂ f) : Slice n → ℂ) =ᵐ[μ']
        ((ContinuousMap.toLp 2 (μ') ℂ f : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
      Lp.coeFn_compMeasurePreserving _ hmp
    have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') f
    have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
    refine h1.trans (h3.trans (Filter.EventuallyEq.trans ?_ h2.symm))
    exact Eventually.of_forall hinv
  · intro v hv
    obtain ⟨g, hg, hgeig⟩ := continuous_eigenfunction n β lam hlam.ne' v hv
    obtain ⟨c, hc⟩ := hprop g hgeig
    refine ⟨c, ?_⟩
    have hgf : g = c • f := by
      ext u
      exact hc u
    rw [← hg, hgf, map_smul]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum
