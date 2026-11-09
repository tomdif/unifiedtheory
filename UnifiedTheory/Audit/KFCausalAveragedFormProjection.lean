/- The one-period projection acts on the explicit averaged form domain.
Its energy bound follows from bounded form-space integration, not from an
assumed invariance of the unaveraged unbounded operator domain. -/
import UnifiedTheory.Audit.KFCausalAveragedFormSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFormProjection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (U : StrongUnitaryGroup H) (T : ℝ) (hT : 0 < T)
  (hperiod : ∀ f, U.action T f = f) (J : E →L[ℂ] H)

def project (u : FormSpace U T J) : FormSpace U T J :=
  ⟨WithLp.toLp 2 (average U (embedding U T J u) T,
    Lp.const 2 angleMeasure (meanLift U T J u)), by
      change J.compLp (Lp.const 2 angleMeasure (meanLift U T J u)) -
        orbit U T (average U (embedding U T J u) T) = 0
      rw [comp_const, embedding_meanLift U T J hT.ne',
        orbit_fixed U T _ (average_fixed U T hperiod _), sub_self]⟩

theorem project_embedding (u : FormSpace U T J) :
    embedding U T J (project U T hT hperiod J u) = average U (embedding U T J u) T := rfl

theorem project_section (u : FormSpace U T J) :
    sectionMap U T J (project U T hT hperiod J u) =
      Lp.const 2 angleMeasure (meanLift U T J u) := rfl

theorem project_fixed (u : FormSpace U T J) :
    embedding U T J (project U T hT hperiod J u) ∈ fixedSpace U :=
  average_fixed U T hperiod _

theorem project_idempotent (hJ : Function.Injective J) (u : FormSpace U T J) :
    project U T hT hperiod J (project U T hT hperiod J u) = project U T hT hperiod J u := by
  apply embedding_injective U T J hJ
  simp only [project_embedding, average_idempotent U T hT.ne' hperiod]

theorem project_of_fixed (hJ : Function.Injective J) (u : FormSpace U T J)
    (hu : embedding U T J u ∈ fixedSpace U) : project U T hT hperiod J u = u := by
  apply embedding_injective U T J hJ
  exact average_of_fixed U T hT.ne' _ hu

theorem project_norm_le (u : FormSpace U T J) : ‖project U T hT hperiod J u‖ ≤ ‖u‖ := by
  have hp := norm_identity U T J (project U T hT hperiod J u)
  rw [project_embedding, project_section, const_norm] at hp
  have hu := norm_identity U T J u
  have h1 := average_norm_le U T hT (embedding U T J u)
  have h2 := mean_norm_le angleMeasure (sectionMap U T J u)
  change ‖meanLift U T J u‖ ≤ ‖sectionMap U T J u‖ at h2
  have hs1 := sq_le_sq₀ (norm_nonneg (average U (embedding U T J u) T))
    (norm_nonneg (embedding U T J u)) |>.mpr h1
  have hs2 := sq_le_sq₀ (norm_nonneg (meanLift U T J u))
    (norm_nonneg (sectionMap U T J u)) |>.mpr h2
  nlinarith [norm_nonneg (project U T hT hperiod J u), norm_nonneg u]

def averagedOutput (A : E →L[ℂ] K) : FormSpace U T J →L[ℂ] Lp K 2 angleMeasure :=
  (A.compLpL 2 angleMeasure).comp (sectionMap U T J)

omit [CompleteSpace K] in
theorem project_output (A : E →L[ℂ] K) (u : FormSpace U T J) :
    averagedOutput U T J A (project U T hT hperiod J u) =
      Lp.const 2 angleMeasure (A (meanLift U T J u)) := by
  change A.compLp (sectionMap U T J (project U T hT hperiod J u)) = _
  rw [project_section, comp_const]

theorem project_energy_le (A : E →L[ℂ] K) (u : FormSpace U T J) :
    ‖averagedOutput U T J A (project U T hT hperiod J u)‖^2 ≤
      ‖averagedOutput U T J A u‖^2 := by
  rw [project_output, const_norm]
  have hm := mean_norm_le angleMeasure (A.compLp (sectionMap U T J u))
  rw [mean_comp] at hm
  change ‖A (meanLift U T J u)‖ ≤ ‖averagedOutput U T J A u‖ at hm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm

omit [CompleteSpace H] in
theorem projected_unaveraged_energy_le (A : E →L[ℂ] K) (u : FormSpace U T J) :
    ‖A (meanLift U T J u)‖^2 ≤ ‖averagedOutput U T J A u‖^2 := by
  have h := mean_norm_le angleMeasure (A.compLp (sectionMap U T J u))
  rw [mean_comp] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h

#print axioms project_embedding
#print axioms project_section
#print axioms project_fixed
#print axioms project_idempotent
#print axioms project_of_fixed
#print axioms project_norm_le
#print axioms project_output
#print axioms project_energy_le
#print axioms projected_unaveraged_energy_le

end
end UnifiedTheory.Audit.KFCausalAveragedFormProjection
