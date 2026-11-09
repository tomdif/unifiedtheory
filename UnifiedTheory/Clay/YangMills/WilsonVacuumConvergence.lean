/- Actual finite-cutoff Wilson convergence to the constructed positive vacuum.
The explicit ratio depends on the spatial lattice and coupling. -/
import UnifiedTheory.Clay.YangMills.VacuumPowerConvergence
import UnifiedTheory.Clay.YangMills.WilsonSlabContraction
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonVacuumConvergence
noncomputable section
open MeasureTheory Filter WilsonSlabOperator WilsonPositiveGroundState
open WilsonSlabContraction TransferEnergySurvival

variable (n : ℕ) [NeZero n]

/-- The actual chosen positive ground state embedded in the full Hilbert space. -/
def vacuum (β : ℝ) (hβ : 0 ≤ β) : WilsonSlabOperator.Hilbert n :=
  ContinuousMap.toLp 2 (measure n) ℂ (complexify (WilsonGroundLocalComparison.ground n β hβ))

/-- Free spatial boundary data, with unit Haar L² norm. -/
def boundary : WilsonSlabOperator.Hilbert n :=
  ContinuousMap.toLp 2 (measure n) ℂ (complexify (1 : C(Slice n, ℝ)))

def overlap (β : ℝ) (hβ : 0 ≤ β) : ℝ :=
  ∫ u, WilsonGroundLocalComparison.ground n β hβ u ∂measure n

theorem vacuum_norm (β : ℝ) (hβ : 0 ≤ β) : ‖vacuum n β hβ‖ = 1 :=
  (exists_positive_top_eigenfunction n β hβ).choose_spec.2.2.1

theorem vacuum_eigenvector (β : ℝ) (hβ : 0 ≤ β) :
    transfer n β (vacuum n β hβ) = ‖transfer n β‖ • vacuum n β hβ := by
  apply WilsonSlabSpectralRatio.embedded_eigenfunction
  intro u
  simp only [complexify, ContinuousMap.coe_mk, ← Complex.ofReal_mul,
    integral_complex_ofReal]
  exact congrArg (fun x : ℝ => (x : ℂ))
    (WilsonGroundLocalComparison.ground_equation n β hβ u)

theorem vacuum_fixed (β : ℝ) (hβ : 0 ≤ β) :
    normalized n β (vacuum n β hβ) = vacuum n β hβ := by
  change ‖transfer n β‖⁻¹ • transfer n β (vacuum n β hβ) = _
  rw [vacuum_eigenvector, smul_smul,
    inv_mul_cancel₀ (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1.ne',
    one_smul]

theorem vacuum_contraction (β : ℝ) (hβ : 0 ≤ β) (v : WilsonSlabOperator.Hilbert n)
    (hv : inner ℂ (vacuum n β hβ) v = 0) :
    ‖normalized n β v‖ ≤ ratioCap n β * ‖v‖ := by
  obtain ⟨Omega, hn, hf, hc⟩ := full_orthogonal_contraction n β hβ
  have hne : vacuum n β hβ ≠ 0 := by
    intro hz
    have h := vacuum_norm n β hβ
    rw [hz, norm_zero] at h
    norm_num at h
  exact VacuumPowerConvergence.rebase_contraction (normalized n β) Omega hn hf
    (ratioCap n β) (ratioCap_lt_one n β) hc (vacuum n β hβ) hne
    (vacuum_fixed n β hβ) v hv

theorem overlap_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < overlap n β hβ := by
  apply integral_pos_of_nonneg_of_embedding_norm_one
  · intro u
    exact (WilsonGroundLocalComparison.ground_pos n β hβ u).le
  · exact vacuum_norm n β hβ

theorem overlap_inner (β : ℝ) (hβ : 0 ≤ β) :
    inner ℂ (vacuum n β hβ) (boundary n) = (overlap n β hβ : ℂ) := by
  rw [vacuum, boundary, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [complexify, ContinuousMap.coe_mk, ContinuousMap.one_apply, Complex.ofReal_one,
    one_mul, Complex.conj_ofReal]
  exact integral_complex_ofReal

theorem boundary_norm : ‖boundary n‖ = 1 := by
  have h := real_embedding_norm_sq (measure n) (1 : C(Slice n, ℝ))
  change ‖boundary n‖ ^ 2 = _ at h
  simp only [ContinuousMap.one_apply, one_pow, integral_const, probReal_univ,
    smul_eq_mul, one_mul] at h
  nlinarith [norm_nonneg (boundary n)]

/-- Quantitative convergence for the actual free-boundary vector. -/
theorem boundary_power_error (β : ℝ) (hβ : 0 ≤ β) (k : ℕ) :
    ‖iterate (normalized n β) k (boundary n) -
      (overlap n β hβ : ℂ) • vacuum n β hβ‖ ≤
      ratioCap n β ^ k * ‖boundary n - (overlap n β hβ : ℂ) • vacuum n β hβ‖ := by
  simpa only [overlap_inner] using VacuumPowerConvergence.power_error (normalized n β)
    (normalized_symmetric n β) (vacuum n β hβ) (vacuum_norm n β hβ)
    (vacuum_fixed n β hβ) (ratioCap n β) (ratioCap_nonneg n β hβ)
    (vacuum_contraction n β hβ) (boundary n) k

/-- This is a fixed-cutoff vacuum limit, without a trace-class premise. -/
theorem boundary_power_tendsto (β : ℝ) (hβ : 0 ≤ β) :
    Tendsto (fun k => iterate (normalized n β) k (boundary n)) atTop
      (nhds ((overlap n β hβ : ℂ) • vacuum n β hβ)) := by
  simpa only [overlap_inner] using VacuumPowerConvergence.power_tendsto (normalized n β)
    (normalized_symmetric n β) (vacuum n β hβ) (vacuum_norm n β hβ)
    (vacuum_fixed n β hβ) (ratioCap n β) (ratioCap_nonneg n β hβ)
    (ratioCap_lt_one n β) (vacuum_contraction n β hβ) (boundary n)

end
end UnifiedTheory.Clay.YangMills.WilsonVacuumConvergence
