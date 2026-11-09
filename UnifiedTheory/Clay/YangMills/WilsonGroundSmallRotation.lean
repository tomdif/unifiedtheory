/- Quantitative quasi-invariance of the actual slice ground law under
small link rotations. Constants are conservative and independent of volume. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget
import UnifiedTheory.Clay.YangMills.WilsonMixedGroundResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalInfluence WilsonSymmetricLinkChange WilsonVarianceResponse
open WilsonGroundHeatBath WilsonPhysicalVariance CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem trace_shift_bound (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n)
    (x : SpatialVertex n) (i j : Fin 3) :
    |(WilsonSingleLinkStaples.character (spatialHolonomy (shift n e q u) x i j)).re-
      (WilsonSingleLinkStaples.character (spatialHolonomy u x i j)).re| ≤ 8*‖(q : ℍ)-1‖ := by
  have ht := WilsonPlaquetteTransport.character_difference
    (spatialHolonomy (shift n e q u) x i j) (spatialHolonomy u x i j)
  have hd := (holonomy_variation n e q u x i j).1
  change ‖((spatialHolonomy (shift n e q u) x i j : Q) : ℍ)-
    ((spatialHolonomy u x i j : Q) : ℍ)‖ ≤ 4*‖(q : ℍ)-1‖ at hd
  unfold WilsonPlaquetteTransport.chord at ht
  linarith

/-- The estimate permits repeated word occurrences; no lattice nondegeneracy is needed. -/
theorem potential_shift_bound (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    |potential WilsonSingleLinkStaples.character 2 (shift n e q u)-
      potential WilsonSingleLinkStaples.character 2 u| ≤ 32*‖(q : ℍ)-1‖ := by
  classical
  let D : SpatialVertex n × SpatialPlane → ℝ := fun p =>
    (WilsonSingleLinkStaples.character (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re-
      (WilsonSingleLinkStaples.character (spatialHolonomy (shift n e q u) p.1 p.2.1.1 p.2.1.2)).re
  have he : potential WilsonSingleLinkStaples.character 2 (shift n e q u)-
      potential WilsonSingleLinkStaples.character 2 u = ∑ p, D p := by
    simp only [D, Fintype.sum_prod_type, ← Finset.sum_sub_distrib, potential]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hz (p : SpatialVertex n × SpatialPlane)
      (hp : p ∉ WilsonSlabLocalComparison.affected n e.1 e.2) : D p = 0 := by
    have h := WilsonSlabLocalComparison.holonomy_unchanged n Q e.1 e.2 p hp u
      (shift n e q u) (fun j hj => (shift_away n e q u j hj).symm)
    dsimp only [D]
    rw [h, sub_self]
  have hs : (∑ p, D p) = ∑ p ∈ WilsonSlabLocalComparison.affected n e.1 e.2, D p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hz p hp)
  have hd (p : SpatialVertex n × SpatialPlane) : |D p| ≤ 8*‖(q : ℍ)-1‖ := by
    simpa only [D, abs_sub_comm] using trace_shift_bound n e q u p.1 p.2.1.1 p.2.1.2
  rw [he, hs]
  calc
    _ ≤ ∑ p ∈ WilsonSlabLocalComparison.affected n e.1 e.2, |D p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ WilsonSlabLocalComparison.affected n e.1 e.2, 8*‖(q : ℍ)-1‖ :=
      Finset.sum_le_sum (fun p _ => hd p)
    _ = ((WilsonSlabLocalComparison.affected n e.1 e.2).card : ℝ)*(8*‖(q : ℍ)-1‖) := by simp
    _ ≤ _ := by
      have hc : ((WilsonSlabLocalComparison.affected n e.1 e.2).card : ℝ) ≤ 4 :=
        by exact_mod_cast WilsonSlabLocalComparison.affected_card n e.1 e.2
      nlinarith [norm_nonneg ((q : ℍ)-1)]

theorem spatialWeight_shift (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    spatialWeight WilsonSingleLinkStaples.character β 2 (shift n e q u) ≤
      Real.exp (16*β*‖(q : ℍ)-1‖)*spatialWeight WilsonSingleLinkStaples.character β 2 u := by
  have h := mul_le_mul_of_nonneg_left (abs_le.mp (potential_shift_bound n e q u)).1 hβ
  unfold spatialWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem ground_shift (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    ground n β hβ (shift n e q u) ≤ Real.exp (18*β*‖(q : ℍ)-1‖)*ground n β hβ u := by
  have hw := spatialWeight_shift n β hβ e q u
  have hz := rowPartition_geometric n β hβ (shift n e q u) u
  rw [shift_cost] at hz
  have hp := mul_le_mul hw hz (rowPartition_pos n β hβ (shift n e q u)).le
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have he : (Real.exp (16*β*‖(q : ℍ)-1‖)*spatialWeight WilsonSingleLinkStaples.character β 2 u)*
      (Real.exp (2*β*‖(q : ℍ)-1‖)*rowPartition n β hβ u) =
      Real.exp (18*β*‖(q : ℍ)-1‖)*
        (spatialWeight WilsonSingleLinkStaples.character β 2 u*rowPartition n β hβ u) := by
    rw [show 18*β*‖(q : ℍ)-1‖ = 16*β*‖(q : ℍ)-1‖+2*β*‖(q : ℍ)-1‖ by ring,
      Real.exp_add]
    ring
  rw [he, rowPartition_ground, rowPartition_ground] at hp
  have ht := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  nlinarith

theorem ground_square_shift (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    (ground n β hβ (shift n e q u))^2 ≤ Real.exp (36*β*‖(q : ℍ)-1‖)*(ground n β hβ u)^2 := by
  have h := (sq_le_sq₀ (ground_pos n β hβ _).le
    (mul_nonneg (Real.exp_pos _).le (ground_pos n β hβ u).le)).mpr (ground_shift n β hβ e q u)
  have he : (Real.exp (18*β*‖(q : ℍ)-1‖))^2 = Real.exp (36*β*‖(q : ℍ)-1‖) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he] using h

omit [NeZero n] in
theorem shift_inverse (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    shift n e q⁻¹ (shift n e q u) = u := by
  funext j
  by_cases h : j = e
  · subst j
    simp only [shift_at, inv_mul_cancel_left]
  · simp only [shift_away n e _ _ j h]

omit n [NeZero n] in
theorem inverse_distance (q : Q) : ‖((q⁻¹ : Q) : ℍ)-1‖ = ‖(q : ℍ)-1‖ := by
  change ‖star (q : ℍ)-(1 : ℍ)‖ = _
  simpa only [star_sub, star_one] using norm_star ((q : ℍ)-1)

/-- Quasi-invariance of the actual g^2 law, not a replacement Gibbs measure. -/
theorem shifted_integral_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (F : Slice n → ℝ)
    (hF : Continuous F) (hF0 : ∀ u, 0 ≤ F u) :
    (∫ u, F (shift n e q u) ∂groundLaw n β hβ) ≤
      Real.exp (36*β*‖(q : ℍ)-1‖)*(∫ u, F u ∂groundLaw n β hβ) := by
  rw [groundLaw, GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n)
    (ground n β hβ) (ground n β hβ).continuous,
    GroundStateDirichlet.stationary_integral (WilsonSlabOperator.measure n)
      (ground n β hβ) (ground n β hβ).continuous]
  have he := shift_integral n e q
    (fun u => (ground n β hβ (shift n e q⁻¹ u))^2 * F u)
  simp only [shift_inverse] at he
  rw [he, ← integral_const_mul]
  apply integral_mono
    (continuous_integrable (WilsonSlabOperator.measure n) _
      ((((ground n β hβ).continuous.comp (shift_continuous n e q⁻¹)).pow 2).mul hF))
    (continuous_integrable (WilsonSlabOperator.measure n) _
      (continuous_const.mul (((ground n β hβ).continuous.pow 2).mul hF)))
  intro u
  have h := ground_square_shift n β hβ e q⁻¹ u
  rw [inverse_distance] at h
  dsimp only [Pi.mul_apply, Function.comp_apply]
  nlinarith [mul_le_mul_of_nonneg_right h (hF0 u)]

/-- Any local finite-difference energy is paid for by actual ground-law variance. -/
theorem response_le_variance (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (f : C(Slice n, ℝ)) :
    responseEnergy n β hβ e q f ≤
      2*(Real.exp (36*β*‖(q : ℍ)-1‖)+1)*variance n β hβ f := by
  letI := groundLaw_probability n β hβ
  let m := ∫ u, f u ∂groundLaw n β hβ
  let F := fun u : Slice n => (f u-m)^2
  have hF : Continuous F := (f.continuous.sub continuous_const).pow 2
  have hv : (∫ u, F u ∂groundLaw n β hβ) = variance n β hβ f := by
    rw [variance, ProbabilityTheory.variance_eq_integral f.continuous.measurable.aemeasurable]
  have hs := shifted_integral_le n β hβ e q F hF (fun u => sq_nonneg (f u-m))
  have hi1 := continuous_integrable (groundLaw n β hβ) (fun u => 2*F (shift n e q u))
    (continuous_const.mul (hF.comp (shift_continuous n e q)))
  have hi2 := continuous_integrable (groundLaw n β hβ) (fun u => 2*F u)
    (continuous_const.mul hF)
  have hc := integral_mono
    (continuous_integrable (groundLaw n β hβ) _
      (((f.continuous.comp (shift_continuous n e q)).sub f.continuous).pow 2))
    (hi1.add hi2) (fun u => show (f (shift n e q u)-f u)^2 ≤
      2*F (shift n e q u)+2*F u by
        dsimp only [F]
        nlinarith [sq_nonneg (f (shift n e q u)+f u-2*m)])
  have he := integral_add hi1 hi2
  simp only [Pi.add_apply] at he hc
  rw [he, integral_const_mul, integral_const_mul, hv] at hc
  rw [hv] at hs
  simp only [Function.comp_apply] at hc
  change (∫ u, (f (shift n e q u)-f u)^2 ∂groundLaw n β hβ) ≤ _
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation
