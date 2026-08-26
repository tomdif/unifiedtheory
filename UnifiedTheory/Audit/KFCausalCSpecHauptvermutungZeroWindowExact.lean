/-
  Audit/KFCausalCSpecHauptvermutungZeroWindowExact.lean

  ZERO-WINDOW CONSEQUENCES OF THE PHYSICAL HAUPTVERMUTUNG CERTIFICATE

  The certificate stores pointwise relative-error inequalities.  When its
  count, curvature, and chart-pair windows are exactly zero, those inequalities
  force the corresponding local equations exactly.  This is the forward
  semantic implication available from the present record.

  The converse is intentionally not claimed: the stored windows are arbitrary
  upper bounds and may contain slack.  A reverse equivalence requires canonical
  least upper bounds (or exact finite maxima) rather than the current fields.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHauptvermutungZeroWindowExact

noncomputable section

open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

universe u v w

variable {X : Type u} {Y : Type v} {chartIndex : Type w}
variable [AddCommGroup Y] [Module ℝ Y]
variable [Fintype chartIndex] [Nonempty chartIndex]

/-- Vanishing count window forces exact count-density-volume agreement at
every distinct pair in every chart. -/
theorem exact_count_density_volume_of_countWindow_eq_zero
    (C : PhysicalGrowthHauptvermutungCertificate X Y chartIndex)
    (hcountWindow : C.countWindow = 0) :
    ∀ i x x', x ≠ x' →
      C.count i x x' = C.density * C.volume i x x' := by
  intro i x x' hxx'
  have habs :
      |C.count i x x' / (C.density * C.volume i x x') - 1| = 0 := by
    apply le_antisymm
    · simpa [hcountWindow] using C.count_concentration i x x' hxx'
    · exact abs_nonneg _
  have hratio :
      C.count i x x' / (C.density * C.volume i x x') = 1 :=
    sub_eq_zero.mp (abs_eq_zero.mp habs)
  have hdenominator : C.density * C.volume i x x' ≠ 0 :=
    mul_ne_zero (ne_of_gt C.density_pos)
      (ne_of_gt (C.volume_pos i x x' hxx'))
  exact (div_eq_one_iff_eq hdenominator).mp hratio

/-- Vanishing curvature window forces the exact four-dimensional
volume/interval relation stored by the certificate. -/
theorem exact_curvature_volume_of_curvatureBias_eq_zero
    (C : PhysicalGrowthHauptvermutungCertificate X Y chartIndex)
    (hcurvatureBias : C.curvatureBias = 0) :
    ∀ i x x', x ≠ x' →
      C.volume i x x' =
        (Real.pi / 24) * (C.G x x') ^ 2 := by
  intro i x x' hxx'
  have habs :
      |C.volume i x x' / ((Real.pi / 24) * (C.G x x') ^ 2) - 1| = 0 := by
    apply le_antisymm
    · simpa [hcurvatureBias] using C.curvature_bias_bound i x x' hxx'
    · exact abs_nonneg _
  have hratio :
      C.volume i x x' / ((Real.pi / 24) * (C.G x x') ^ 2) = 1 :=
    sub_eq_zero.mp (abs_eq_zero.mp habs)
  have hpiDiv : Real.pi / 24 ≠ 0 :=
    div_ne_zero Real.pi_ne_zero (by norm_num)
  have hG : C.G x x' ≠ 0 := ne_of_gt (C.G_pos x x' hxx')
  have hdenominator : (Real.pi / 24) * (C.G x x') ^ 2 ≠ 0 :=
    mul_ne_zero hpiDiv (pow_ne_zero 2 hG)
  exact (div_eq_one_iff_eq hdenominator).mp hratio

/-- Vanishing pair-consistency window forces the exact chart-agreement
quadratic equation stored by the certificate. -/
theorem exact_chart_pair_equation_of_pairConsistency_eq_zero
    (C : PhysicalGrowthHauptvermutungCertificate X Y chartIndex)
    (hpairConsistency : C.pairConsistency = 0) :
    ∀ i j x x', x ≠ x' →
      C.B ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x'))
        ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x')) = 0 := by
  intro i j x x' hxx'
  have habs :
      |C.B ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x'))
        ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x'))| = 0 := by
    apply le_antisymm
    · simpa [hpairConsistency] using
        C.chart_pair_consistency i j x x' hxx'
    · exact abs_nonneg _
  exact abs_eq_zero.mp habs

/-- Bundled exact local-geometry consequences of simultaneous zero windows. -/
theorem exact_local_geometry_of_zero_windows
    (C : PhysicalGrowthHauptvermutungCertificate X Y chartIndex)
    (hcountWindow : C.countWindow = 0)
    (hcurvatureBias : C.curvatureBias = 0)
    (hpairConsistency : C.pairConsistency = 0) :
    (∀ i x x', x ≠ x' →
      C.count i x x' = C.density * C.volume i x x') ∧
    (∀ i x x', x ≠ x' →
      C.volume i x x' =
        (Real.pi / 24) * (C.G x x') ^ 2) ∧
    (∀ i j x x', x ≠ x' →
      C.B ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x'))
        ((C.chart i x - C.chart i x') -
          (C.chart j x - C.chart j x')) = 0) := by
  exact
    ⟨exact_count_density_volume_of_countWindow_eq_zero C hcountWindow,
      exact_curvature_volume_of_curvatureBias_eq_zero C hcurvatureBias,
      exact_chart_pair_equation_of_pairConsistency_eq_zero C hpairConsistency⟩

#print axioms exact_count_density_volume_of_countWindow_eq_zero
#print axioms exact_curvature_volume_of_curvatureBias_eq_zero
#print axioms exact_chart_pair_equation_of_pairConsistency_eq_zero
#print axioms exact_local_geometry_of_zero_windows

end


end UnifiedTheory.Audit.KFCausalCSpecHauptvermutungZeroWindowExact
