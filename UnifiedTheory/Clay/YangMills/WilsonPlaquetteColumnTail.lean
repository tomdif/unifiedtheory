/- Actual source-sensitive localization for one spatial plaquette defect.
Reversibility and the two-step residual convert the proved input decay into
an arbitrary-source estimate, retaining the explicit non-small loss cost. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay CompactDensityEntropy SpatialPlaquetteCutGeometry
open WilsonHighFieldReduction (mass_step_le cutoff_mass_le residual_le_loss)
open WilsonPlaquetteColumnDecay

variable (n : ℕ) [NeZero n]

def rate (β R : ℝ) : ℝ := (SU2GaussianMass.cap β)^2 * Real.exp (-β * R)

theorem rate_nonneg (β R : ℝ) : 0 ≤ rate β R := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem cutoff_output (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (χ f : C(Slice (2 * n), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, SpatialWilsonPlaquetteKernels.defect n q u < R → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * step (2 * n) β (by linarith) f) ≤
      rate β R * mass (2 * n) β (by linarith) f := by
  apply WilsonCutoffCover.cutoff_output (2 * n) β (by linarith) χ (rate β R)
    (rate_nonneg β R) hχ _ f
  intro h hh
  exact mass_decay n q hq β hβ R h (fun u hu => hh u (hs u hu))

theorem source_cutoff (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (χ f : C(Slice (2 * n), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, SpatialWilsonPlaquetteKernels.defect n q u < R → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * f) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * rate β R * mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  let P2 := step (2 * n) β h0 (step (2 * n) β h0 f)
  have hi := WilsonCutoffCover.mass_split (2 * n) β h0 χ f P2
  have ha := (cutoff_mass_le (2 * n) β h0 χ (f-P2) hχ).trans (residual_le_loss (2 * n) β h0 f)
  have hb := (cutoff_output n q hq β hβ R χ (step (2 * n) β h0 f) hχ hs).trans
    (mul_le_mul_of_nonneg_left (mass_step_le (2 * n) β h0 f) (rate_nonneg β R))
  change mass (2 * n) β h0 (χ*P2) ≤ _ at hb
  linarith

def cutoff (q : Plaquette n) (R : ℝ) : C(Slice (2 * n), ℝ) :=
  ⟨fun u => min 1 (max 0 ((SpatialWilsonPlaquetteKernels.defect n q u - R) / R)),
    continuous_const.min (continuous_const.max
      (((SpatialWilsonPlaquetteKernels.defect_continuous n q).sub continuous_const).div_const _))⟩

omit [NeZero n] in
theorem cutoff_range (q : Plaquette n) (R : ℝ) (u : Slice (2 * n)) :
    cutoff n q R u ∈ Set.Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

omit [NeZero n] in
theorem cutoff_supported (q : Plaquette n) (R : ℝ) (hR : 0 < R) (u : Slice (2 * n))
    (hu : SpatialWilsonPlaquetteKernels.defect n q u < R) : cutoff n q R u = 0 := by
  change min 1 (max 0 ((SpatialWilsonPlaquetteKernels.defect n q u - R) / R)) = 0
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.le) hR.le)]
  norm_num

omit [NeZero n] in
theorem cutoff_one (q : Plaquette n) (R : ℝ) (hR : 0 < R) (u : Slice (2 * n))
    (hu : 2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q u) : cutoff n q R u = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  apply (le_div_iff₀ hR).mpr
  change 1 * R ≤ SpatialWilsonPlaquetteKernels.defect n q u - R
  linarith

/-- Isolated spatial defects are now controlled with the actual source
weight and ground law. The loss coefficient is two, not an absorption epsilon. -/
theorem source_tail (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, {v : Slice (2 * n) | 2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q v}.indicator
      (fun v => (f v)^2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * rate β R * mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  letI := groundLaw_probability (2 * n) β h0
  have hi : (∫ u, {v : Slice (2 * n) | 2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q v}.indicator
      (fun v => (f v)^2) u ∂groundLaw (2 * n) β h0) ≤
      mass (2 * n) β h0 (cutoff n q R * f) := by
    apply integral_mono
    · exact (continuous_integrable (groundLaw (2 * n) β h0) _ (f.continuous.pow 2)).indicator
        (isClosed_le continuous_const
          (SpatialWilsonPlaquetteKernels.defect_continuous n q)).measurableSet
    · exact continuous_integrable (groundLaw (2 * n) β h0) _ ((cutoff n q R * f).continuous.pow 2)
    · intro u
      by_cases hu : 2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q u
      · rw [Set.indicator_of_mem (s := {v : Slice (2 * n) |
          2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q v}) hu]
        simp only [ContinuousMap.mul_apply, cutoff_one n q R hR u hu, one_mul, le_refl]
      · rw [Set.indicator_of_notMem (s := {v : Slice (2 * n) |
          2 * R ≤ SpatialWilsonPlaquetteKernels.defect n q v}) hu]
        exact sq_nonneg _
  exact hi.trans (source_cutoff n q hq β hβ R (cutoff n q R) f
    (cutoff_range n q R) (cutoff_supported n q R hR))

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnTail
