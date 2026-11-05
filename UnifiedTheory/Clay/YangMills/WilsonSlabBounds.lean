/- Explicit finite-cutoff bounds for the actual interacting SU(2) slab kernel.
The volume dependence remains visible and does not supply a physical gap. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabOperator
import UnifiedTheory.Clay.YangMills.WilsonEnergyDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabBounds
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator
open WilsonSingleLinkStaples WilsonEnergyDensity

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem spatialPlane_card : Fintype.card SpatialPlane = 3 := by decide

/-- The actual fundamental character defect lies in [0,4]. -/
theorem characterDefect_bounds (g : WilsonSlabOperator.Q) :
    0 ≤ 2 - (character g).re ∧ 2 - (character g).re ≤ 4 := by
  constructor
  · simpa only [UnitaryHolonomyDefect.defect, representation_character, Fintype.card_fin,
      Nat.cast_ofNat] using UnitaryHolonomyDefect.defect_nonneg representation g
  · simpa only [UnitaryHolonomyDefect.defect, representation_character, Fintype.card_fin,
      Nat.cast_ofNat, show 2 * (2 : ℝ) = 4 by norm_num] using
      UnitaryHolonomyDefect.defect_le representation g

theorem potential_bounds (u : Slice n) :
    0 ≤ potential character 2 u ∧
      potential character 2 u ≤ 12 * (Fintype.card (SpatialVertex n) : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun p _ => (characterDefect_bounds (spatialHolonomy u x p.1.1 p.1.2)).1))
  · calc
      _ ≤ ∑ _x : SpatialVertex n, ∑ _p : SpatialPlane, (4 : ℝ) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum
          (fun p _ => (characterDefect_bounds (spatialHolonomy u x p.1.1 p.1.2)).2))
      _ = _ := by simp [spatialPlane_card]; ring

theorem temporalAction_bounds (u v : Slice n) (h : SliceGauge n WilsonSlabOperator.Q) :
    0 ≤ temporalAction character 2 u v h ∧
      temporalAction character 2 u v h ≤ 12 * (Fintype.card (SpatialVertex n) : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun i _ => (characterDefect_bounds (temporalHolonomy u v h x i)).1))
  · calc
      _ ≤ ∑ _x : SpatialVertex n, ∑ _i : Fin 3, (4 : ℝ) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum
          (fun i _ => (characterDefect_bounds (temporalHolonomy u v h x i)).2))
      _ = _ := by simp; ring

theorem slabAction_bounds (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n)
    (h : SliceGauge n WilsonSlabOperator.Q) :
    0 ≤ slabAction character β 2 u v h ∧
      slabAction character β 2 u v h ≤ 24 * β * (Fintype.card (SpatialVertex n) : ℝ) := by
  have hu := potential_bounds n u
  have hv := potential_bounds n v
  have ht := temporalAction_bounds n u v h
  unfold slabAction
  constructor
  · exact mul_nonneg hβ (add_nonneg
      (add_nonneg (div_nonneg hu.1 (by norm_num)) ht.1) (div_nonneg hv.1 (by norm_num)))
  · have hsum : potential character 2 u / 2 + temporalAction character 2 u v h +
        potential character 2 v / 2 ≤ 24 * (Fintype.card (SpatialVertex n) : ℝ) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hsum hβ]

/-- Temporal-link integration preserves the explicit uniform kernel bounds. -/
theorem kernel_bounds (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) ≤
      kernel character β 2 u v ∧ kernel character β 2 u v ≤ 1 := by
  have hi : Integrable
      (fun h : SliceGauge n WilsonSlabOperator.Q => Real.exp (-slabAction character β 2 u v h))
      temporalHaar := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold slabAction temporalAction temporalHolonomy
    have hc : Continuous character := character_continuous
    fun_prop
  constructor
  · have h := integral_mono (integrable_const
      (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))))) hi (fun h => by
        apply Real.exp_le_exp.mpr
        linarith [(slabAction_bounds n β hβ u v h).2])
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  · have h := integral_mono hi (integrable_const (1 : ℝ)) (fun h => by
      apply Real.exp_le_one_iff.mpr
      linarith [(slabAction_bounds n β hβ u v h).1])
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem kernelMap_norm_le_one (β : ℝ) (hβ : 0 ≤ β) : ‖kernelMap n β‖ ≤ 1 := by
  apply (ContinuousMap.norm_le (kernelMap n β) (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro uv
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (kernel_bounds n β hβ uv.1 uv.2).2
  · exact (kernel_positive character character_continuous β 2 uv.1 uv.2).le

theorem transfer_norm_le_one (β : ℝ) (hβ : 0 ≤ β) : ‖transfer n β‖ ≤ 1 :=
  (WilsonSlabOperator.transfer_norm_le n β).trans (kernelMap_norm_le_one n β hβ)

theorem kernel_mass_lower (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) ≤
      ∫ uv, kernelMap n β uv
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) := by
  have h := integral_mono (integrable_const
    (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))))
    ((kernelMap n β).continuous.integrable_of_hasCompactSupport
      (μ := (WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n))
      (HasCompactSupport.of_compactSpace _))
    (fun uv => (kernel_bounds n β hβ uv.1 uv.2).1)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

/-- The normalized product Haar constant test has norm at most one. -/
theorem constant_norm_le_one :
    ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ))‖ ≤ 1 := by
  have h := (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ).le_opNorm
    (1 : C(Slice n, ℂ))
  rw [norm_one, mul_one] at h
  exact h.trans (CompactKernelOperator.embedding_norm_le (WilsonSlabOperator.measure n))

/-- Explicit bounds for the finite-cutoff transfer normalization. The lower
bound degenerates exponentially in coupling times spatial volume. -/
theorem transfer_norm_bounds (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ))) ≤ ‖transfer n β‖ ∧
      ‖transfer n β‖ ≤ 1 := by
  refine ⟨(kernel_mass_lower n β hβ).trans ?_, transfer_norm_le_one n β hβ⟩
  let e := ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ))
  have he : ‖e‖ ≤ 1 := constant_norm_le_one n
  have ht : ‖transfer n β e‖ ≤ ‖transfer n β‖ := by
    exact ((transfer n β).le_opNorm e).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg (transfer n β)))
  have hi := re_inner_le_norm (𝕜 := ℂ) e (transfer n β e)
  change (inner ℂ (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ)))
    (transfer n β (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ
      (1 : C(Slice n, ℂ))))).re ≤ ‖e‖ * ‖transfer n β e‖ at hi
  rw [transfer_one_pairing, Complex.ofReal_re] at hi
  exact hi.trans (by
    simpa only [one_mul] using
      mul_le_mul he ht (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

end
end UnifiedTheory.Clay.YangMills.WilsonSlabBounds
