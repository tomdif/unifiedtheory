/-
  Audit/KFCausalCSpecHauptvermutungDiagonalNoGo.lean

  LEGACY DIAGONAL NO-GO AND DISTINCT-PAIR NON-VACUITY REGRESSION

  The repaired physical Hauptvermutung certificate imposes its interval-count
  laws only on distinct event pairs and records `G x x = 0` separately.  This
  file keeps the old diagonal obstruction as a regression theorem: adding the
  legacy all-pairs chart and concentration laws back to a repaired certificate
  again forces `1 <= countWindow` on every nonempty event domain.

  The second half constructs an explicit exact certificate on two events and
  one chart with zero count, curvature, and pair-consistency windows.  Thus the
  repaired interface is not merely free of the old proof of contradiction; it
  has a concrete nontrivial finite inhabitant whose displayed distortion is
  exactly zero.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDiagonalNoGo

open Filter Topology
open UnifiedTheory.Audit.KFCausalCSpecGluing
open UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

/-! ## 1. The forbidden legacy all-pairs laws -/

/-- The two legacy fields that caused the diagonal obstruction.  They are
deliberately separated from the repaired certificate rather than provided by a
conversion back to the old interface. -/
structure LegacyAllPairsIntervalLaws
    {X Y chart : Type*}
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (C : PhysicalGrowthHauptvermutungCertificate X Y chart) : Prop where
  chart_count_eq : ∀ i x x',
    C.B (C.chart i x - C.chart i x') (C.chart i x - C.chart i x') =
      Real.sqrt (24 * C.count i x x' / (Real.pi * C.density))
  count_concentration : ∀ i x x',
    |C.count i x x' / (C.density * C.volume i x x') - 1| ≤ C.countWindow

/-- Under the forbidden legacy chart law, a diagonal interval count vanishes. -/
theorem legacy_count_diagonal_eq_zero
    {X Y chart : Type*}
    [AddCommGroup Y] [Module ℝ Y] [Fintype chart] [Nonempty chart]
    (C : PhysicalGrowthHauptvermutungCertificate X Y chart)
    (L : LegacyAllPairsIntervalLaws C) (i : chart) (x : X) :
    C.count i x x = 0 := by
  have hchart := L.chart_count_eq i x x
  have harg_nonneg :
      0 ≤ 24 * C.count i x x / (Real.pi * C.density) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) (C.count_nonneg i x x))
      (mul_pos Real.pi_pos C.density_pos).le
  have hsqrt :
      Real.sqrt (24 * C.count i x x / (Real.pi * C.density)) = 0 := by
    simpa using hchart.symm
  have harg_nonpos :
      24 * C.count i x x / (Real.pi * C.density) ≤ 0 :=
    Real.sqrt_eq_zero'.mp hsqrt
  have harg_zero :
      24 * C.count i x x / (Real.pi * C.density) = 0 :=
    le_antisymm harg_nonpos harg_nonneg
  have hden : Real.pi * C.density ≠ 0 :=
    mul_ne_zero (ne_of_gt Real.pi_pos) (ne_of_gt C.density_pos)
  rcases div_eq_zero_iff.mp harg_zero with hnum | hden_zero
  · rcases mul_eq_zero.mp hnum with h24 | hcount
    · norm_num at h24
    · exact hcount
  · exact (hden hden_zero).elim

/-- Reintroducing all-pairs concentration recreates the unit diagonal floor. -/
theorem legacy_one_le_countWindow
    {X Y chart : Type*}
    [Nonempty X] [AddCommGroup Y] [Module ℝ Y]
    [Fintype chart] [Nonempty chart]
    (C : PhysicalGrowthHauptvermutungCertificate X Y chart)
    (L : LegacyAllPairsIntervalLaws C) :
    1 ≤ C.countWindow := by
  let i : chart := Classical.choice inferInstance
  let x : X := Classical.choice inferInstance
  have hcount : C.count i x x = 0 := legacy_count_diagonal_eq_zero C L i x
  have hconcentration := L.count_concentration i x x
  simpa [hcount] using hconcentration

/-- No sequence carrying the forbidden legacy laws can have a vanishing count
window on a nonempty event domain. -/
theorem legacy_not_countWindow_tendsto_zero
    {X Y chart : Type*}
    [Nonempty X] [AddCommGroup Y] [Module ℝ Y]
    [Fintype chart] [Nonempty chart]
    (C : ℕ → PhysicalGrowthHauptvermutungCertificate X Y chart)
    (L : ∀ n, LegacyAllPairsIntervalLaws (C n)) :
    ¬ Tendsto (fun n => (C n).countWindow) atTop (nhds 0) := by
  intro hzero
  have hlt : ∀ᶠ n in atTop, (C n).countWindow < (1 / 2 : ℝ) :=
    (tendsto_order.1 hzero).2 (1 / 2 : ℝ) (by norm_num)
  rw [eventually_atTop] at hlt
  rcases hlt with ⟨n, hn⟩
  have hn' := hn n le_rfl
  have hfloor : 1 ≤ (C n).countWindow := legacy_one_le_countWindow (C n) (L n)
  linarith

/-! ## 2. A concrete two-event exact certificate -/

/-- Multiplication as a symmetric real bilinear form. -/
noncomputable def realMulBilinear : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => x * y
      map_add' := by
        intro y z
        ring
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    dsimp
    ring
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro z
    dsimp
    ring

/-- The two-event source interval: zero on the diagonal and one off it. -/
def finTwoInterval (x x' : Fin 2) : ℝ := if x = x' then 0 else 1

/-- The one-dimensional coordinate of a two-event chart. -/
def finTwoCoordinate (x : Fin 2) : ℝ := x.1

/-- Exact count used on the unique nontrivial interval. -/
noncomputable def finTwoCount (x x' : Fin 2) : ℝ :=
  if x = x' then 0 else Real.pi / 24

/-- Exact flat small-diamond volume used on the unique nontrivial interval. -/
noncomputable def finTwoVolume (x x' : Fin 2) : ℝ :=
  if x = x' then 0 else Real.pi / 24

private theorem pi_div_twentyFour_pos : 0 < Real.pi / 24 := by positivity

private theorem count_chart_ratio :
    (24 : ℝ) * (Real.pi / 24) / Real.pi = 1 := by
  field_simp [ne_of_gt Real.pi_pos]

private theorem finTwoCoordinate_bilinear_eq_one_of_ne
    (x x' : Fin 2) (h : x ≠ x') :
    realMulBilinear (finTwoCoordinate x - finTwoCoordinate x')
      (finTwoCoordinate x - finTwoCoordinate x') = 1 := by
  fin_cases x <;> fin_cases x' <;>
    simp_all [realMulBilinear, finTwoCoordinate]

/-- An explicit nontrivial repaired certificate: two distinct events, one chart,
and all three displayed error channels exactly zero. -/
noncomputable def finTwoExactCertificate :
    PhysicalGrowthHauptvermutungCertificate (Fin 2) ℝ (Fin 1) where
  B := realMulBilinear
  B_symm := by
    intro x y
    simp [realMulBilinear]
    ring
  G := finTwoInterval
  pairConsistency := 0
  countWindow := 0
  curvatureBias := 0
  scale := 1
  density := 1
  density_pos := by norm_num
  countWindow_nonneg := by norm_num
  curvatureBias_nonneg := by norm_num
  scale_nonneg := by norm_num
  pairConsistency_nonneg := by norm_num
  chart := fun _ x => finTwoCoordinate x
  count := fun _ x x' => finTwoCount x x'
  volume := fun _ x x' => finTwoVolume x x'
  G_self := by
    intro x
    simp [finTwoInterval]
  G_pos := by
    intro x x' h
    simp [finTwoInterval, h]
  G_le_scale := by
    intro x x'
    by_cases h : x = x'
    · simp [finTwoInterval, h]
    · simp [finTwoInterval, h]
  chart_count_eq := by
    intro i x x' h
    rw [finTwoCoordinate_bilinear_eq_one_of_ne x x' h]
    simp only [finTwoCount, if_neg h, mul_one]
    rw [count_chart_ratio, Real.sqrt_one]
  count_nonneg := by
    intro i x x'
    by_cases h : x = x'
    · simp [finTwoCount, h]
    · simp [finTwoCount, h, pi_div_twentyFour_pos.le]
  volume_pos := by
    intro i x x' h
    simpa [finTwoVolume, h] using pi_div_twentyFour_pos
  count_concentration := by
    intro i x x' h
    simp [finTwoCount, finTwoVolume, h, ne_of_gt pi_div_twentyFour_pos]
  curvature_bias_bound := by
    intro i x x' h
    simp [finTwoVolume, finTwoInterval, h, ne_of_gt pi_div_twentyFour_pos]
  chart_pair_consistency := by
    intro i j x x' h
    have hij : i = j := Subsingleton.elim i j
    subst j
    simp [realMulBilinear]

/-- The repaired interface has a concrete non-singleton inhabitant. -/
theorem nonempty_finTwoExactCertificate :
    Nonempty (PhysicalGrowthHauptvermutungCertificate (Fin 2) ℝ (Fin 1)) :=
  ⟨finTwoExactCertificate⟩

/-- The concrete witness has no residual window and zero displayed distortion. -/
theorem finTwoExactCertificate_zero_channels :
    finTwoExactCertificate.countWindow = 0 ∧
      finTwoExactCertificate.curvatureBias = 0 ∧
      finTwoExactCertificate.pairConsistency = 0 ∧
      finTwoExactCertificate.distortionBound = 0 := by
  simp [finTwoExactCertificate,
    PhysicalGrowthHauptvermutungCertificate.distortionBound]

/-- The generic repaired bridge certifies the concrete witness as an exact
global isometry, including its separately handled diagonal. -/
theorem finTwoExactCertificate_applies :
    finTwoExactCertificate.QuantitativeHauptvermutungAppliesToPhysicalGrowth := by
  exact
    PhysicalGrowthHauptvermutungCertificate.applies_quantitative_hauptvermutung
      finTwoExactCertificate

#print axioms legacy_count_diagonal_eq_zero
#print axioms legacy_one_le_countWindow
#print axioms legacy_not_countWindow_tendsto_zero
#print axioms nonempty_finTwoExactCertificate
#print axioms finTwoExactCertificate_zero_channels
#print axioms finTwoExactCertificate_applies

end UnifiedTheory.Audit.KFCausalCSpecHauptvermutungDiagonalNoGo
