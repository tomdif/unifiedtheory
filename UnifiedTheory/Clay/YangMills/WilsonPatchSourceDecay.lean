/- Actual source decay for a simultaneous aligned spatial patch. Every
marked column is removed in one justified reflection comparison. The rate
retains the original full ground and eigenvalue and the number of defects. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnTail
import UnifiedTheory.Clay.YangMills.CompactKernelDomination
import UnifiedTheory.Clay.YangMills.WilsonCutoffCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHighFieldDecay WilsonTemporalGauge
open WilsonPositiveGroundState CompactKernelOperator SpatialPlaquetteCutGeometry
open SpatialWilsonPatchWeights SpatialWilsonReflectionKernel SpatialWilsonColumnTransfer
open WilsonPlaquetteColumnDecay (source source_norm output_norm)
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]

theorem boundary_restore (S : Finset (Plaquette n)) (β : ℝ) (u : Slice (2 * n)) :
    SpatialWilsonColumnTransfer.boundary n (fun _ => β) u =
      SpatialWilsonColumnTransfer.boundary n (omitted n S β) u *
        Real.exp (-(β / 2) * patchDefect n S u) := by
  classical
  change weight n (fun _ => β / 2) u = weight n (fun p => omitted n S β p / 2) u * _
  rw [omitted_half, weight_restore]

theorem raw_factor (S : Finset (Plaquette n)) (β : ℝ) (u v : Slice (2 * n)) :
    rawKernel character β 2 u v =
      Real.exp (-(β / 2) * patchDefect n S u) *
        SpatialWilsonColumnTransfer.kernelMap n (omitted n S β) β (u,v) *
        Real.exp (-(β / 2) * patchDefect n S v) := by
  rw [← constant_kernelMap n β u v]
  change SpatialWilsonColumnTransfer.boundary n (fun _ => β) u * _ *
    SpatialWilsonColumnTransfer.boundary n (fun _ => β) v = _
  rw [boundary_restore n S β u, boundary_restore n S β v]
  simp only [SpatialWilsonColumnTransfer.kernelMap, ContinuousMap.coe_mk]
  ring

theorem raw_high (S : Finset (Plaquette n)) (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (u v : Slice (2 * n))
    (hv : R ≤ patchDefect n S v) :
    rawKernel character β 2 u v ≤ Real.exp (-β * R / 2) *
      SpatialWilsonColumnTransfer.kernelMap n (omitted n S β) β (u,v) := by
  have hu : Real.exp (-(β / 2) * patchDefect n S u) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (patchDefect_nonneg n S u)
  have hw : Real.exp (-(β / 2) * patchDefect n S v) ≤
      Real.exp (-β * R / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hv hβ]
  rw [raw_factor n S]
  have hk := (kernelMap_pos n (omitted n S β) β u v).le
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_right hu hk) hw (Real.exp_pos _).le
    (by simpa using hk : 0 ≤ 1 * SpatialWilsonColumnTransfer.kernelMap n (omitted n S β) β (u,v))
  simpa only [one_mul, mul_comm] using hh

theorem input_bound (S : Finset (Plaquette n)) (β : ℝ) (hβ : 0 ≤ β) (R : ℝ)
    (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, patchDefect n S u < R → f u = 0) :
    ‖SpatialWilsonColumnTransfer.transfer n (fun _ => β) β
      (ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
        (complexify (source n β hβ f)))‖ ≤
      Real.exp (-β * R / 2) * ‖SpatialWilsonColumnTransfer.transfer n (omitted n S β) β‖ *
        ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
          (complexify (source n β hβ f))‖ := by
  apply CompactKernelDomination.input_domination
    (WilsonSlabOperator.measure (2 * n)) _ _ _ (Real.exp_pos _).le
  intro u v
  by_cases hv : R ≤ patchDefect n S v
  · have hh := mul_le_mul_of_nonneg_right (raw_high n S β hβ R u v hv)
      (norm_nonneg (complexify (source n β hβ f) v))
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, constant_kernelMap,
      abs_of_pos (rawKernel_pos _ _ _ _ _), mul_assoc] using hh
  · simp only [source, complexify, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
      hs v (lt_of_not_ge hv), mul_zero, Complex.ofReal_zero, norm_zero, le_refl]

/-- Supported decay for the total defect of an aligned patch, with no exterior-volume price. -/
theorem mass_decay (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, patchDefect n S u < R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      ((SU2GaussianMass.cap β) ^ S.card) ^ 2 * Real.exp (-β * R) *
        mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  have hi := input_bound n S β h0 R f hs
  have hc := SpatialWilsonPatchNorm.polynomial_norm n S hS β hβ
  have hh := hi.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, output_norm, source_norm] at hsq
  have he : (Real.exp (-β * R / 2)) ^ 2 = Real.exp (-β * R) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hsq
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector (2 * n) β h0).1)).mp
  convert hsq using 1
  ring

omit [NeZero n] in
theorem patchDefect_lower (S : Finset (Plaquette n)) (R : ℝ) (u : Slice (2 * n))
    (h : ∀ p ∈ S, R ≤ SpatialWilsonPlaquetteKernels.defect n p u) :
    (S.card : ℝ) * R ≤ patchDefect n S u := by
  have hs := Finset.sum_le_sum h
  simpa only [Finset.sum_const, nsmul_eq_mul] using hs

omit [NeZero n] in
theorem rate_cardinality (S : Finset (Plaquette n)) (β R : ℝ) :
    ((SU2GaussianMass.cap β) ^ S.card) ^ 2 * Real.exp (-β * ((S.card : ℝ) * R)) =
      (WilsonPlaquetteColumnTail.rate β R) ^ S.card := by
  have he : -β * ((S.card : ℝ) * R) = (S.card : ℝ) * (-β * R) := by ring
  rw [he, Real.exp_nat_mul]
  simp only [WilsonPlaquetteColumnTail.rate, mul_pow, ← pow_mul, Nat.mul_comm]

/-- Every marked plaquette is large. The resulting rate is the kth power
of the single-defect rate, with the actual squared source mass retained. -/
theorem intersection_decay (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, (∃ p ∈ S, SpatialWilsonPlaquetteKernels.defect n p u < R) → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (WilsonPlaquetteColumnTail.rate β R) ^ S.card * mass (2 * n) β (by linarith) f := by
  have h := mass_decay n S hS β hβ ((S.card : ℝ) * R) f (by
    intro u hu
    apply hs u
    by_contra! hn
    exact (not_lt_of_ge (patchDefect_lower n S R u hn)) hu)
  rwa [rate_cardinality] at h

theorem intersection_loss (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, (∃ p ∈ S, SpatialWilsonPlaquetteKernels.defect n p u < R) → f u = 0) :
    (1 - (WilsonPlaquetteColumnTail.rate β R) ^ S.card) * mass (2 * n) β (by linarith) f ≤
      loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have h := intersection_decay n S hS β hβ R f hs
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay
