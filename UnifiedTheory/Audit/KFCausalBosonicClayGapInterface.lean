/- Scoped adapter from the auxiliary Bose Hamiltonian to the Clay
spectral interface. The bounded-resolvent gap and finite excitation remain
explicit inputs; no Yang--Mills identity or full Clay conclusion is asserted. -/
import UnifiedTheory.Clay.YangMills.SpectralGap
import UnifiedTheory.Audit.KFCausalBosonicEnergyGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicClayGapInterface
noncomputable section
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalTensorSumEnergyFloor
open UnifiedTheory.Clay.YangMills.SpectralGap

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem auxiliary_vacuum_not_in_resolvent (D : Data H K) :
    ¬ InRealResolvent (fullHamiltonian D) 0 :=
  vacuum_not_in_resolvent (fullHamiltonian D) (vacuum D) (vacuum_norm D) (vacuum_stationary D)

theorem auxiliary_form_gap (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ) :
    VacuumFormGap (fullHamiltonian D) (vacuum D) δ :=
  KFCausalBosonicEnergyGap.orthogonal_energy_gap D δ hδ hD

theorem auxiliary_spectral_requirements_of_inputs (D : Data H K) (δ : ℝ)
    (hD : LowerBound D δ) (hgap : IntervalGap (fullHamiltonian D) δ)
    (hfinite : FiniteExcitation (fullHamiltonian D)) :
    SpectralRequirements (fullHamiltonian D) (vacuum D) δ where
  self_adjoint := full_selfAdjoint D
  vacuum_norm := vacuum_norm D
  vacuum_stationary := vacuum_stationary D
  positive_energy := full_positive D
  unique_zero_energy := fun x hx => ⟨KFCausalBosonicEnergyGap.vacuumCoefficient D x,
    KFCausalBosonicEnergyGap.zero_energy_kernel D δ hgap.1 hD x hx⟩
  spectral_gap := hgap
  finite_excitation := hfinite

end
end UnifiedTheory.Audit.KFCausalBosonicClayGapInterface
