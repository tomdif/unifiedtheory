/- Compact self-adjoint operators attain every nonzero real spectral value
as an actual eigenvalue. The proof constructs normalized approximate vectors
and uses compactness; no eigenpair or norm-attainment premise is introduced. -/
import UnifiedTheory.Clay.YangMills.CompactKernelOperator
import UnifiedTheory.Clay.YangMills.WilsonSlabPositiveOperator
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveKernelGroundState
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded-below self-adjoint operator is invertible; orthogonality supplies dense range. -/
theorem selfAdjoint_isUnit_of_bound (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (C : ℝ≥0) (hC : ∀ x, ‖x‖ ≤ C * ‖R x‖) : IsUnit R := by
  have ha := R.antilipschitz_of_bound hC
  rw [ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, ⟨C, ha⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, hR.isSymmetric.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr ha.injective

/-- A real spectral point has normalized approximate eigenvectors. -/
theorem spectral_approximate_vector (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (lam : ℝ) (hlam : lam ∈ spectrum ℝ T) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : H, ‖v‖ = 1 ∧ ‖(algebraMap ℝ (H →L[ℂ] H) lam - T) v‖ < ε := by
  let R := algebraMap ℝ (H →L[ℂ] H) lam - T
  have hR : IsSelfAdjoint R := (IsSelfAdjoint.algebraMap _ (show IsSelfAdjoint lam by rfl)).sub hT
  by_contra! h
  have hb (x : H) : ‖x‖ ≤ ε⁻¹ * ‖R x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let v := (‖x‖⁻¹ : ℂ) • x
    have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn.ne']
    have hvR : ε ≤ ‖R v‖ := h v hv
    rw [map_smul, norm_smul] at hvR
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] at hvR
    rw [mul_comm (ε⁻¹), ← div_eq_mul_inv]
    apply (le_div_iff₀ hε).mpr
    have hh := mul_le_mul_of_nonneg_left hvR hn.le
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at hh
    exact hh
  have hu := selfAdjoint_isUnit_of_bound R hR ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ hb
  exact (spectrum.mem_iff.mp hlam) hu

/-- Compactness converts the approximate vectors into a genuine unit eigenvector. -/
theorem eigenvector_of_nonzero_spectral (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hcompact : IsCompactOperator T) (lam : ℝ) (hlam : lam ∈ spectrum ℝ T) (hlam₀ : lam ≠ 0) :
    ∃ v : H, ‖v‖ = 1 ∧ T v = lam • v := by
  let R := algebraMap ℝ (H →L[ℂ] H) lam - T
  have hvexists (n : ℕ) : ∃ v : H, ‖v‖ = 1 ∧ ‖R v‖ < 1 / ((n : ℝ) + 1) :=
    spectral_approximate_vector T hT lam hlam _ (by positivity)
  choose v hvnorm hvR using hvexists
  have hzero : Tendsto (fun n => R (v n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => (hvR n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : IsCompact (closure (T '' Metric.closedBall (0 : H) 1)) :=
    hcompact.isCompact_closure_image_closedBall 1
  obtain ⟨y, _, φ, hφ, hy⟩ := hc.tendsto_subseq (x := fun n => T (v n)) (fun n =>
    subset_closure ⟨v n, by simpa only [Metric.mem_closedBall, dist_zero_right, hvnorm] using
      (le_refl (1 : ℝ)), rfl⟩)
  have hr := hzero.comp hφ.tendsto_atTop
  have hlim : Tendsto (fun n => v (φ n)) atTop (𝓝 (lam⁻¹ • y)) := by
    have he (n : ℕ) : v (φ n) = lam⁻¹ • (T (v (φ n)) + R (v (φ n))) := by
      have hadd : T (v (φ n)) + R (v (φ n)) = lam • v (φ n) := by
        simp only [R, ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
        module
      rw [hadd, smul_smul, inv_mul_cancel₀ hlam₀, one_smul]
    have hl := (hy.add hr).const_smul lam⁻¹
    simp only [Function.comp_apply, add_zero] at hl
    exact hl.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))
  have hnorm : ‖lam⁻¹ • y‖ = 1 := by
    have hn := hlim.norm
    have hn' : Tendsto (fun n => ‖v (φ n)‖) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hvnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hn hn'
  have hRy : R (lam⁻¹ • y) = 0 :=
    tendsto_nhds_unique ((R.continuous.tendsto _).comp hlim) hr
  refine ⟨lam⁻¹ • y, hnorm, ?_⟩
  change (algebraMap ℝ (H →L[ℂ] H) lam - T) (lam⁻¹ • y) = 0 at hRy
  simp only [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at hRy
  exact (sub_eq_zero.mp hRy).symm

/-- A nonzero positive compact operator attains its positive norm as an eigenvalue. -/
theorem positive_compact_top_eigenvector (T : H →L[ℂ] H) (hpos : T.IsPositive)
    (hcompact : IsCompactOperator T) (hne : T ≠ 0) :
    0 < ‖T‖ ∧ ∃ v : H, ‖v‖ = 1 ∧ T v = ‖T‖ • v := by
  letI : Nontrivial (H →L[ℂ] H) := ⟨⟨T, 0, hne⟩⟩
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hne
  have hs : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hpos.isSymmetric
  exact ⟨hn, eigenvector_of_nonzero_spectral T hs hcompact ‖T‖
    (CStarAlgebra.norm_mem_spectrum_of_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mpr hpos)) hn.ne'⟩

open WilsonSlabOperator WilsonTimeSlab

variable (n : ℕ) [NeZero n]

/-- The actual full interacting Wilson operator has an attained positive top eigenvalue. -/
theorem transfer_top_eigenvector (β : ℝ) (hβ : 0 ≤ β) :
    0 < ‖transfer n β‖ ∧
      ∃ v : WilsonSlabOperator.Hilbert n, ‖v‖ = 1 ∧ transfer n β v = ‖transfer n β‖ • v :=
  positive_compact_top_eigenvector (transfer n β)
    (WilsonSlabPositiveOperator.transfer_positive n β hβ)
    (transfer_compact n β) (transfer_ne_zero n β)

/-- Every nonzero L² eigenvalue has a continuous representative obtained from the actual kernel. -/
theorem eigenfunction_embedding (β lam : ℝ) (hlam : lam ≠ 0)
    (v : WilsonSlabOperator.Hilbert n) (hv : transfer n β v = lam • v) :
    ContinuousMap.toLp 2 (measure n) ℂ
      ((lam : ℂ)⁻¹ • representative n β v) = v := by
  rw [map_smul]
  change (lam : ℂ)⁻¹ • transfer n β v = v
  rw [hv, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [smul_smul]
  change (((lam : ℂ)⁻¹) * (lam : ℂ)) • v = v
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam), one_smul]

/-- The finite-cutoff top eigenfunction is continuous and gauge invariant, and
satisfies the full kernel equation pointwise. No pointwise sign or simplicity claim is made. -/
theorem exists_continuous_top_eigenfunction (β : ℝ) (hβ : 0 ≤ β) :
    ∃ ψ : C(Slice n, ℂ),
      ‖ContinuousMap.toLp 2 (measure n) ℂ ψ‖ = 1 ∧
      (∀ h : SliceGauge n WilsonSlabOperator.Q, ∀ u, ψ (gaugeSlice h u) = ψ u) ∧
      ∀ u, (∫ w, (kernel WilsonSingleLinkStaples.character β 2 u w : ℂ) * ψ w ∂measure n) =
        (‖transfer n β‖ : ℂ) * ψ u := by
  obtain ⟨hlam, v, hvnorm, hv⟩ := transfer_top_eigenvector n β hβ
  let ψ : C(Slice n, ℂ) := (‖transfer n β‖ : ℂ)⁻¹ • representative n β v
  have he : ContinuousMap.toLp 2 (measure n) ℂ ψ = v :=
    eigenfunction_embedding n β ‖transfer n β‖ hlam.ne' v hv
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [he]
    exact hvnorm
  · intro h u
    simp only [ψ, ContinuousMap.smul_apply, representative_gauge]
  · intro u
    calc
      _ = representative n β (ContinuousMap.toLp 2 (measure n) ℂ ψ) u :=
        (CompactKernelOperator.smoothing_continuous_input (measure n) (kernelMap n β) ψ u).symm
      _ = representative n β v u := by rw [he]
      _ = (‖transfer n β‖ : ℂ) * ψ u := by
        dsimp only [ψ, ContinuousMap.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_mul]

end
end UnifiedTheory.Clay.YangMills.PositiveKernelGroundState
