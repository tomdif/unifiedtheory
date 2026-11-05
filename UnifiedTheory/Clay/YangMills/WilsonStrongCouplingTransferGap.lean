/- An unconditional, spatial-volume-independent ratio bound for the ORIGINAL
SU2 Wilson transfer at strong coupling. Cylinder decay is derived from the
actual conditional laws; it is no longer a hypothesis of these theorems.
This is a regulated lattice result, not a nonzero continuum construction. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderClustering
import UnifiedTheory.Clay.YangMills.WilsonCylinderSpectralBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonStrongCouplingTransferGap
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonSlabContraction WilsonCylinderContraction
open TransferEnergySurvival

variable (n : ℕ) [NeZero n]

/-- The actual-model estimate discharges the spectral bridge's entire analytic premise. -/
theorem cylinderDecay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n) :
    WilsonCylinderSpectralBridge.CylinderDecay n β (rate β) := by
  intro F
  refine ⟨4 * ‖F‖^2, fun j k => ?_⟩
  simpa only [pow_two, mul_assoc] using
    WilsonCylinderClustering.interior_covariance_bound n β hβ heven F F j k

/-- The rate controls the original transfer on the full complex vacuum-orthogonal space. -/
theorem full_orthogonal_contraction (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (v : Hilbert n) (hv : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0) :
    ‖normalized n β v‖ ≤ rate β * ‖v‖ :=
  WilsonCylinderSpectralBridge.full_orthogonal_contraction n β hβ (rate β)
    (rate_nonneg β hβ) (cylinderDecay n β hβ heven) v hv

/-- Every original-transfer step has the same volume-independent contraction rate. -/
theorem all_step_decay (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n)
    (v : Hilbert n) (hv : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0) (k : ℕ) :
    ‖iterate (normalized n β) k v‖ ≤ rate β^k * ‖v‖ ∧
      ∀ u, ‖inner ℂ u (iterate (normalized n β) k v)‖ ≤ rate β^k * ‖u‖ * ‖v‖ :=
  WilsonCylinderSpectralBridge.all_step_decay n β hβ (rate β)
    (rate_nonneg β hβ) (cylinderDecay n β hβ heven) v hv k

/-- The excited-to-top ratio for the actual full spectrum has no volume factor. -/
theorem spectral_ratio (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n) (ρ : ℝ)
    (hspec : ρ ∈ spectrum ℝ (transfer n β)) (hρ : ρ ≠ ‖transfer n β‖) :
    |ρ / ‖transfer n β‖| ≤ 1 - (1 - 36 * β) / 8 :=
  WilsonCylinderSpectralBridge.spectral_ratio n β hβ (rate β)
    (rate_nonneg β hβ) (cylinderDecay n β hβ heven) ρ hspec hρ

/-- The ratio is strictly separated from one throughout the explicit strong-coupling range. -/
theorem spectral_ratio_lt_one (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36)
    (heven : 2 ∣ n) (ρ : ℝ) (hspec : ρ ∈ spectrum ℝ (transfer n β))
    (hρ : ρ ≠ ‖transfer n β‖) : |ρ / ‖transfer n β‖| < 1 :=
  (spectral_ratio n β hβ heven ρ hspec hρ).trans_lt (rate_lt_one β hsmall)

omit [NeZero n] in
theorem rate_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < rate β := by
  unfold rate
  linarith

/-- Dimensionless energy per original lattice-transfer step. No lattice spacing
or physical coupling trajectory is identified by this definition. -/
def energyFloor (β : ℝ) : ℝ := -Real.log (rate β)

omit [NeZero n] in
theorem energyFloor_pos (β : ℝ) (hβ : 0 ≤ β) (hsmall : β < 1 / 36) :
    0 < energyFloor β :=
  neg_pos.mpr (Real.log_neg (rate_pos β hβ) (rate_lt_one β hsmall))

/-- Every positive excited spectral value has the proved lattice energy floor. -/
theorem lattice_energy_lower (β : ℝ) (hβ : 0 ≤ β) (heven : 2 ∣ n) (ρ : ℝ)
    (hρpos : 0 < ρ) (hspec : ρ ∈ spectrum ℝ (transfer n β))
    (hρ : ρ ≠ ‖transfer n β‖) :
    energyFloor β ≤ -Real.log (ρ / ‖transfer n β‖) := by
  have hl := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have hr : 0 < ρ / ‖transfer n β‖ := div_pos hρpos hl
  have hb := spectral_ratio n β hβ heven ρ hspec hρ
  rw [abs_of_pos hr] at hb
  exact neg_le_neg (Real.log_le_log hr hb)

end
end UnifiedTheory.Clay.YangMills.WilsonStrongCouplingTransferGap
