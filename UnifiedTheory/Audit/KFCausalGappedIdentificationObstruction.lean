/- Even the newly proved particle energy gap does not select the proposed
quartic coupling. A concrete gapped member of the actual Hamiltonian family
coexists with Watson's identity and has a different coupling. -/
import UnifiedTheory.Audit.KFCausalInteractingParticleEnergyGap
import UnifiedTheory.Audit.KFCausalPhysicalIdentificationObstructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalGappedIdentificationObstruction
noncomputable section
open KFCausalTensorSumEnergyFloor KFCausalTensorParticleSectors

private theorem clock_positive : 0 < Real.pi / 6 := by positivity
private theorem clock_bound : |Real.pi / 6| ≤ Real.pi * 1 / 3 := by
  rw [abs_of_pos clock_positive]
  linarith [Real.pi_pos]

def family (g : ℝ) := KFCausalClockFloorAveragedHamiltonian.formData
  1 (by norm_num) (Real.pi / 6) clock_positive.ne'
  (KFCausalClockFloorRadialYosidaReference.wide_bound 1 (by norm_num)
    (Real.pi / 6) clock_bound) 1 g 1 0

theorem family_lower (g : ℝ) : LowerBound (family g) (1 / 2) :=
  KFCausalInteractingParticleEnergyGap.original_lower 1 (by norm_num)
    (Real.pi / 6) clock_positive clock_bound 1 g 1 (by norm_num) 0

def Gapped (g : ℝ) : Prop :=
  ∀ x : (fullHamiltonian (family g)).domain,
    inner ℂ (vacuum (family g)) (x : TensorFock (family g)) = 0 →
      (1 / 2) * ‖(x : TensorFock (family g))‖ ^ 2 ≤
        (inner ℂ (fullHamiltonian (family g) x) (x : TensorFock (family g))).re

theorem every_coupling_gapped (g : ℝ) : Gapped g :=
  KFCausalParticleEnergyGap.orthogonal_energy_gap (family g) (1 / 2) (by norm_num)
    (family_lower g)

theorem watson_gapped_countermodel :
    UnifiedTheory.QSeries.Watson.chiA =
      2 * UnifiedTheory.QSeries.Watson.F0w - UnifiedTheory.QSeries.Watson.P0w ∧
    ∃ g : ℝ, 0 < g ∧ g ≠ UnifiedTheory.LayerA.IdentificationChain.lambda_predicted ∧
      IsSelfAdjoint (fullHamiltonian (family g)) ∧ Gapped g := by
  refine ⟨UnifiedTheory.LayerA.WatsonSeriesBridge.chi0_R1, 1 / 2, by norm_num, ?_,
    full_selfAdjoint (family (1 / 2)), every_coupling_gapped (1 / 2)⟩
  exact ne_of_gt UnifiedTheory.LayerA.IdentificationChain.lambda_lt_half

end
end UnifiedTheory.Audit.KFCausalGappedIdentificationObstruction
