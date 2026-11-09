/- The actual Wilson spectral estimate controls every vector orthogonal to
its unique vacuum, and hence every connected matrix element at integer time
steps. The explicit volume-dependent rate is not a continuum mass gap. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabSpectralRatio
import UnifiedTheory.Clay.YangMills.CompactGroundContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabContraction
noncomputable section
open WilsonSlabOperator WilsonTimeSlab TransferEnergySurvival

variable (n : ℕ) [NeZero n]

/-- Normalization is by the actual attained top eigenvalue. -/
def normalized (beta : ℝ) : WilsonSlabOperator.Hilbert n →L[ℂ] WilsonSlabOperator.Hilbert n :=
  (‖transfer n beta‖⁻¹ : ℝ) • transfer n beta

def ratioCap (beta : ℝ) : ℝ :=
  1 - Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))

theorem ratioCap_nonneg (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ ratioCap n beta := by
  unfold ratioCap
  have h : Real.exp (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  linarith

theorem ratioCap_lt_one (beta : ℝ) : ratioCap n beta < 1 := by
  unfold ratioCap
  linarith [Real.exp_pos (-(24 * beta * (Fintype.card (SpatialVertex n) : ℝ)))]

theorem normalized_symmetric (beta : ℝ) (x y : WilsonSlabOperator.Hilbert n) :
    inner ℂ (normalized n beta x) y = inner ℂ x (normalized n beta y) := by
  simp only [normalized, ContinuousLinearMap.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, inner_smul_real_right]
  have hs := (transfer_selfAdjoint n beta).isSymmetric x y
  change inner ℂ (transfer n beta x) y = inner ℂ x (transfer n beta y) at hs
  exact congrArg (fun z : ℂ => (‖transfer n beta‖⁻¹ : ℝ) • z) hs

/-- The finite-cutoff estimate is a norm contraction on the whole
vacuum-orthogonal Hilbert space, not merely an eigenfunction assertion. -/
theorem full_orthogonal_contraction (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ Omega : WilsonSlabOperator.Hilbert n,
      ‖Omega‖ = 1 ∧ normalized n beta Omega = Omega ∧
      ∀ v, inner ℂ Omega v = 0 → ‖normalized n beta v‖ ≤ ratioCap n beta * ‖v‖ := by
  obtain ⟨Omega, hnorm, htop, hratio⟩ :=
    WilsonSlabSpectralRatio.orthogonal_eigenvalue_ratio n beta hbeta
  have hlam := (PositiveKernelGroundState.transfer_top_eigenvector n beta hbeta).1
  have hfix : normalized n beta Omega = Omega := by
    simp only [normalized, ContinuousLinearMap.smul_apply, htop, smul_smul,
      inv_mul_cancel₀ hlam.ne', one_smul]
  refine ⟨Omega, hnorm, hfix, ?_⟩
  intro v hv
  have h := CompactGroundContraction.norm_contraction (transfer n beta)
    (WilsonSlabPositiveOperator.transfer_positive n beta hbeta) (transfer_compact n beta)
    Omega ‖transfer n beta‖ (ratioCap n beta) hlam (ratioCap_nonneg n beta hbeta) htop
    (fun rho w _ hw horth heig => (le_abs_self _).trans (hratio w rho hw horth heig)) v hv
  calc
    ‖normalized n beta v‖ = ‖transfer n beta‖⁻¹ * ‖transfer n beta v‖ := by
      simp only [normalized, ContinuousLinearMap.smul_apply, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hlam]
    _ ≤ ‖transfer n beta‖⁻¹ * ((‖transfer n beta‖ * ratioCap n beta) * ‖v‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlam.le)
    _ = ratioCap n beta * ‖v‖ := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

/-- Explicit exponential-in-step decay of every orthogonal vector and
every connected matrix element, for the actual full interacting operator. -/
theorem all_step_decay (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ Omega : WilsonSlabOperator.Hilbert n,
      ‖Omega‖ = 1 ∧ normalized n beta Omega = Omega ∧
      ∀ v, inner ℂ Omega v = 0 → ∀ k : ℕ,
        ‖iterate (normalized n beta) k v‖ ≤ ratioCap n beta ^ k * ‖v‖ ∧
        ∀ u, ‖inner ℂ u (iterate (normalized n beta) k v)‖ ≤
          ratioCap n beta ^ k * ‖u‖ * ‖v‖ := by
  obtain ⟨Omega, hnorm, hfix, hc⟩ := full_orthogonal_contraction n beta hbeta
  refine ⟨Omega, hnorm, hfix, ?_⟩
  intro v hv k
  have hblock : ∀ w, inner ℂ Omega w = 0 →
      ‖iterate (normalized n beta) 1 w‖ ≤ ratioCap n beta * ‖w‖ := by
    simpa only [iterate_succ, iterate_zero] using hc
  constructor
  · simpa only [Nat.mul_one] using TransferPhysicalRatio.iterate_blocks_norm
      (normalized n beta) (normalized_symmetric n beta) Omega hfix (ratioCap n beta)
      (ratioCap_nonneg n beta hbeta) 1 hblock v hv k
  · intro u
    simpa only [Nat.mul_one] using TransferPhysicalRatio.block_pairing_bound
      (normalized n beta) (normalized_symmetric n beta) Omega hfix (ratioCap n beta)
      (ratioCap_nonneg n beta hbeta) 1 hblock u v hv k

end
end UnifiedTheory.Clay.YangMills.WilsonSlabContraction
