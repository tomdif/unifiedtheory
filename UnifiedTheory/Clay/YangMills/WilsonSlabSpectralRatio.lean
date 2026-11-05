/- Spectral control for the actual full Wilson L² transfer operator.
Continuous-kernel estimates are applied to genuine L² eigenvectors using
their constructed continuous representatives. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelGroundState
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds
import UnifiedTheory.Clay.YangMills.TransferPhysicalRatio
import UnifiedTheory.Clay.YangMills.WilsonSlabContinuousRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabSpectralRatio
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab

variable (n : ℕ) [NeZero n]

/-- The pointwise continuous kernel equation is the actual L² eigenvector
equation after embedding, including zero eigenvalues. -/
theorem embedded_eigenfunction (beta rho : ℝ) (f : C(Slice n, ℂ))
    (heig : ∀ u, (∫ w, (kernelMap n beta (u, w) : ℂ) * f w ∂measure n) =
      (rho : ℂ) * f u) :
    transfer n beta (ContinuousMap.toLp 2 (measure n) ℂ f) =
      rho • ContinuousMap.toLp 2 (measure n) ℂ f := by
  have hf : CompactKernelOperator.smoothing (measure n) (kernelMap n beta)
      (ContinuousMap.toLp 2 (measure n) ℂ f) = (rho : ℂ) • f := by
    ext u
    rw [CompactKernelOperator.smoothing_continuous_input]
    exact heig u
  change ContinuousMap.toLp 2 (measure n) ℂ
    (CompactKernelOperator.smoothing (measure n) (kernelMap n beta)
      (ContinuousMap.toLp 2 (measure n) ℂ f)) = _
  rw [hf, map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- Every nonzero real eigenvalue of the full L² operator has an exact
continuous, gauge-invariant representative, with its embedding identified. -/
theorem continuous_eigenfunction (beta rho : ℝ) (hrho : rho ≠ 0)
    (v : WilsonSlabOperator.Hilbert n) (heig : transfer n beta v = rho • v) :
    ∃ f : C(Slice n, ℂ),
      ContinuousMap.toLp 2 (measure n) ℂ f = v ∧
      (∀ h : SliceGauge n Q, ∀ u, f (gaugeSlice h u) = f u) ∧
      ∀ u, (∫ w, (kernelMap n beta (u, w) : ℂ) * f w ∂measure n) =
        (rho : ℂ) * f u := by
  let f : C(Slice n, ℂ) := (rho : ℂ)⁻¹ • representative n beta v
  have hf : ContinuousMap.toLp 2 (measure n) ℂ f = v :=
    PositiveKernelGroundState.eigenfunction_embedding n beta rho hrho v heig
  refine ⟨f, hf, ?_, ?_⟩
  · intro h u
    simp only [f, ContinuousMap.smul_apply, representative_gauge]
  · intro u
    calc
      _ = representative n beta (ContinuousMap.toLp 2 (measure n) ℂ f) u :=
        (CompactKernelOperator.smoothing_continuous_input (measure n) (kernelMap n beta) f u).symm
      _ = representative n beta v u := by rw [hf]
      _ = (rho : ℂ) * f u := by
        dsimp only [f, ContinuousMap.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hrho), one_mul]

/-- A concrete ratio estimate for every nonzero full L² eigenvector outside
the top eigenvalue. No positive ground-state premise remains. -/
theorem eigenvalue_ratio (beta : ℝ) (hbeta : 0 ≤ beta) (rho : ℝ)
    (v : WilsonSlabOperator.Hilbert n) (hv : v ≠ 0)
    (heig : transfer n beta v = rho • v) (hrho : rho ≠ ‖transfer n beta‖) :
    |rho / ‖transfer n beta‖| ≤
      1 - Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) := by
  by_cases hz : rho = 0
  · rw [hz, zero_div, abs_zero]
    have h : Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    linarith
  · obtain ⟨f, hf, _, hfeig⟩ := continuous_eigenfunction n beta rho hz v heig
    have hf0 : f ≠ 0 := by
      intro h
      apply hv
      rw [← hf, h, map_zero]
    exact WilsonSlabContinuousRatio.continuous_eigenvalue_ratio n beta hbeta
      f rho hf0 hrho hfeig

/-- Compactness supplies actual eigenvectors for every nonzero spectral
point, so the ratio estimate controls the entire real spectrum off the top. -/
theorem spectral_ratio (beta : ℝ) (hbeta : 0 ≤ beta) (rho : ℝ)
    (hspec : rho ∈ spectrum ℝ (transfer n beta)) (hrho : rho ≠ ‖transfer n beta‖) :
    |rho / ‖transfer n beta‖| ≤
      1 - Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) := by
  by_cases hz : rho = 0
  · rw [hz, zero_div, abs_zero]
    have h : Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    linarith
  · obtain ⟨v, hv, heig⟩ := PositiveKernelGroundState.eigenvector_of_nonzero_spectral
      (transfer n beta) (transfer_selfAdjoint n beta) (transfer_compact n beta)
      rho hspec hz
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    exact eigenvalue_ratio n beta hbeta rho v hv0 heig hrho

/-- The resulting finite-cutoff spectral ratio is strictly below one. -/
theorem spectral_ratio_lt_one (beta : ℝ) (hbeta : 0 ≤ beta) (rho : ℝ)
    (hspec : rho ∈ spectrum ℝ (transfer n beta)) (hrho : rho ≠ ‖transfer n beta‖) :
    |rho / ‖transfer n beta‖| < 1 := by
  have h := spectral_ratio n beta hbeta rho hspec hrho
  have hp := Real.exp_pos (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))
  linarith

/-- A positive physical-energy lower bound at each fixed cutoff; its
coupling, volume and temporal-spacing dependence remains explicit. -/
theorem finite_energy_lower (beta : ℝ) (hbeta : 0 ≤ beta) (rho a : ℝ)
    (ha : 0 < a) (hrho0 : 0 < rho) (hspec : rho ∈ spectrum ℝ (transfer n beta))
    (hrho : rho ≠ ‖transfer n beta‖) :
    Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) / a ≤
      -Real.log (rho / ‖transfer n beta‖) / a := by
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1
  have h := spectral_ratio n beta hbeta rho hspec hrho
  rw [abs_of_pos (div_pos hrho0 hlam)] at h
  exact TransferPhysicalRatio.deficit_energy_lower a (rho / ‖transfer n beta‖)
    (Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))) ha
    (div_pos hrho0 hlam) h

/-- The exact logarithmic lower bound, before weakening it to the linear
minorization bound. This theorem excludes the zero eigenvalue from the logarithm. -/
theorem finite_log_energy_lower (beta : ℝ) (hbeta : 0 ≤ beta) (rho a : ℝ)
    (ha : 0 < a) (hrho0 : 0 < rho) (hspec : rho ∈ spectrum ℝ (transfer n beta))
    (hrho : rho ≠ ‖transfer n beta‖) :
    -Real.log (1 - Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))) / a ≤
      -Real.log (rho / ‖transfer n beta‖) / a := by
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1
  have h := spectral_ratio n beta hbeta rho hspec hrho
  rw [abs_of_pos (div_pos hrho0 hlam)] at h
  apply div_le_div_of_nonneg_right _ ha.le
  exact neg_le_neg (Real.log_le_log (div_pos hrho0 hlam) h)

/-- The top eigenspace of the full complex L² operator is one-dimensional,
with an actually constructed unit generator. -/
theorem simple_top_eigenspace (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ Omega : WilsonSlabOperator.Hilbert n,
      ‖Omega‖ = 1 ∧ transfer n beta Omega = ‖transfer n beta‖ • Omega ∧
      ∀ v, transfer n beta v = ‖transfer n beta‖ • v → ∃ c : ℂ, v = c • Omega := by
  obtain ⟨psi, hpsi, _, hnorm, _, heig⟩ :=
    WilsonPositiveGroundState.exists_positive_top_eigenfunction n beta hbeta
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1
  let f := WilsonPositiveGroundState.complexify psi
  have hf (u : Slice n) :
      (∫ w, (kernelMap n beta (u, w) : ℂ) * f w ∂measure n) =
        (‖transfer n beta‖ : ℂ) * f u := by
    simp only [f, WilsonPositiveGroundState.complexify, ContinuousMap.coe_mk,
      ← Complex.ofReal_mul, integral_complex_ofReal]
    exact congrArg (fun x : ℝ => (x : ℂ)) (heig u)
  refine ⟨ContinuousMap.toLp 2 (measure n) ℂ f, hnorm,
    embedded_eigenfunction n beta ‖transfer n beta‖ f hf, ?_⟩
  intro v hv
  obtain ⟨g, hg, _, hgeig⟩ := continuous_eigenfunction n beta ‖transfer n beta‖ hlam.ne' v hv
  obtain ⟨c, hc⟩ := PositiveKernelRatio.complex_top_proportional (measure n)
    (kernelMap n beta) psi hpsi ‖transfer n beta‖
    (Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))) 1
    hlam (Real.exp_pos _) (by norm_num)
    (fun u w => (WilsonSlabBounds.kernel_bounds n beta hbeta u w).1)
    (fun u w => (WilsonSlabBounds.kernel_bounds n beta hbeta u w).2) heig g hgeig
  have hgf : g = c • f := by ext u; exact hc u
  refine ⟨c, ?_⟩
  rw [← hg, hgf, map_smul]

/-- The excited-eigenvector estimate may be stated by vacuum orthogonality
alone: simplicity rules out a second top eigenvector. -/
theorem orthogonal_eigenvalue_ratio (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ Omega : WilsonSlabOperator.Hilbert n,
      ‖Omega‖ = 1 ∧ transfer n beta Omega = ‖transfer n beta‖ • Omega ∧
      ∀ (v : WilsonSlabOperator.Hilbert n) (rho : ℝ), v ≠ 0 →
        inner ℂ Omega v = 0 → transfer n beta v = rho • v →
        |rho / ‖transfer n beta‖| ≤
          1 - Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) := by
  obtain ⟨Omega, hnorm, htop, hsimple⟩ := simple_top_eigenspace n beta hbeta
  refine ⟨Omega, hnorm, htop, ?_⟩
  intro v rho hv horth heig
  apply eigenvalue_ratio n beta hbeta rho v hv heig
  intro heq
  rw [heq] at heig
  obtain ⟨c, hc⟩ := hsimple v heig
  rw [hc, inner_smul_right, inner_self_eq_one_of_norm_eq_one hnorm, mul_one] at horth
  apply hv
  rw [hc, horth, zero_smul]

end
end UnifiedTheory.Clay.YangMills.WilsonSlabSpectralRatio
