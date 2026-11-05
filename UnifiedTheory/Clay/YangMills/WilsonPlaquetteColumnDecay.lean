/- Actual input decay for a single large spatial plaquette defect. The new
polynomial column-normalization bound removes the old exponential boundary
price. Original ground amplitudes and the original full eigenvalue are retained. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonColumnNorm
import UnifiedTheory.Clay.YangMills.CompactKernelDomination
import UnifiedTheory.Clay.YangMills.WilsonCutoffCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnDecay
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHighFieldDecay WilsonTemporalGauge
open WilsonPositiveGroundState CompactKernelOperator SpatialPlaquetteCutGeometry
open SpatialWilsonInsertion SpatialWilsonReflectionKernel SpatialWilsonColumnTransfer
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]

theorem boundary_restore (q : Plaquette n) (β : ℝ) (u : Slice (2 * n)) :
    SpatialWilsonColumnTransfer.boundary n (fun _ => β) u =
      SpatialWilsonColumnTransfer.boundary n (omitted n q β) u *
        Real.exp (-(β / 2) * SpatialWilsonPlaquetteKernels.defect n q u) := by
  classical
  have he : (fun p => omitted n q β p / 2) = omitted n q (β / 2) := by
    funext p
    by_cases hp : p = q <;> simp [omitted, hp]
  change weight n (fun _ => β / 2) u = weight n (fun p => omitted n q β p / 2) u * _
  rw [he, weight_restore]

theorem raw_factor (q : Plaquette n) (β : ℝ) (u v : Slice (2 * n)) :
    rawKernel character β 2 u v =
      Real.exp (-(β / 2) * SpatialWilsonPlaquetteKernels.defect n q u) *
        SpatialWilsonColumnTransfer.kernelMap n (omitted n q β) β (u,v) *
        Real.exp (-(β / 2) * SpatialWilsonPlaquetteKernels.defect n q v) := by
  rw [← constant_kernelMap n β u v]
  change SpatialWilsonColumnTransfer.boundary n (fun _ => β) u * _ *
    SpatialWilsonColumnTransfer.boundary n (fun _ => β) v = _
  rw [boundary_restore n q β u, boundary_restore n q β v]
  simp only [SpatialWilsonColumnTransfer.kernelMap, ContinuousMap.coe_mk]
  ring

theorem raw_high (q : Plaquette n) (β : ℝ) (hβ : 0 ≤ β) (R : ℝ) (u v : Slice (2 * n))
    (hv : R ≤ SpatialWilsonPlaquetteKernels.defect n q v) :
    rawKernel character β 2 u v ≤ Real.exp (-β * R / 2) *
      SpatialWilsonColumnTransfer.kernelMap n (omitted n q β) β (u,v) := by
  have hu : Real.exp (-(β / 2) * SpatialWilsonPlaquetteKernels.defect n q u) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (WilsonSlabBounds.characterDefect_bounds _).1
  have hw : Real.exp (-(β / 2) * SpatialWilsonPlaquetteKernels.defect n q v) ≤
      Real.exp (-β * R / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hv hβ]
  rw [raw_factor n q]
  have hk := (kernelMap_pos n (omitted n q β) β u v).le
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_right hu hk) hw (Real.exp_pos _).le
    (by simpa using hk : 0 ≤ 1 * SpatialWilsonColumnTransfer.kernelMap n (omitted n q β) β (u,v))
  simpa only [one_mul, mul_comm] using hh

def source (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice (2 * n), ℝ)) : C(Slice (2 * n), ℝ) :=
  ground (2 * n) β hβ * f

theorem source_norm (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice (2 * n), ℝ)) :
    ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
      (complexify (source n β hβ f))‖^2 = mass (2 * n) β hβ f := by
  rw [real_embedding_norm_sq, mass_ground]
  rfl

theorem source_output (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice (2 * n), ℝ)) (u : Slice (2 * n)) :
    realSmoothing (WilsonSlabOperator.measure (2 * n))
      (SpatialWilsonColumnTransfer.kernelMap n (fun _ => β) β) (source n β hβ f) u =
      ‖WilsonSlabOperator.transfer (2 * n) β‖ * source n β hβ (step (2 * n) β hβ f) u := by
  rw [realSmoothing_integral]
  simp only [constant_kernelMap, source, ContinuousMap.mul_apply]
  have h := (eq_div_iff (PositiveKernelGroundState.transfer_top_eigenvector
    (2 * n) β hβ).1.ne').mp (ground_step (2 * n) β hβ f u)
  simp_rw [mul_assoc] at h
  linarith

theorem output_norm (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice (2 * n), ℝ)) :
    ‖SpatialWilsonColumnTransfer.transfer n (fun _ => β) β
      (ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
        (complexify (source n β hβ f)))‖^2 =
      ‖WilsonSlabOperator.transfer (2 * n) β‖^2 * mass (2 * n) β hβ (step (2 * n) β hβ f) := by
  change ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
    (smoothing _ (SpatialWilsonColumnTransfer.kernelMap n (fun _ => β) β)
      (ContinuousMap.toLp 2 _ ℂ (complexify (source n β hβ f))))‖^2 = _
  rw [← complexify_realSmoothing, real_embedding_norm_sq]
  simp_rw [source_output, mul_pow]
  rw [integral_const_mul, ← real_embedding_norm_sq, source_norm]

theorem input_bound (q : Plaquette n) (β : ℝ) (hβ : 0 ≤ β) (R : ℝ)
    (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, SpatialWilsonPlaquetteKernels.defect n q u < R → f u = 0) :
    ‖SpatialWilsonColumnTransfer.transfer n (fun _ => β) β
      (ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
        (complexify (source n β hβ f)))‖ ≤
      Real.exp (-β * R / 2) * ‖SpatialWilsonColumnTransfer.transfer n (omitted n q β) β‖ *
        ‖ContinuousMap.toLp 2 (WilsonSlabOperator.measure (2 * n)) ℂ
          (complexify (source n β hβ f))‖ := by
  apply CompactKernelDomination.input_domination
    (WilsonSlabOperator.measure (2 * n)) _ _ _ (Real.exp_pos _).le
  intro u v
  by_cases hv : R ≤ SpatialWilsonPlaquetteKernels.defect n q v
  · have hh := mul_le_mul_of_nonneg_right (raw_high n q β hβ R u v hv)
      (norm_nonneg (complexify (source n β hβ f) v))
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, constant_kernelMap,
      abs_of_pos (rawKernel_pos _ _ _ _ _), mul_assoc] using hh
  · simp only [source, complexify, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
      hs v (lt_of_not_ge hv), mul_zero, Complex.ofReal_zero, norm_zero, le_refl]

/-- A single spatial defect now has true supported-source decay at polynomial
normalization cost. No defect density or exterior-volume threshold appears. -/
theorem mass_decay (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, SpatialWilsonPlaquetteKernels.defect n q u < R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (SU2GaussianMass.cap β)^2 * Real.exp (-β * R) * mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  have hi := input_bound n q β h0 R f hs
  have hc := SpatialWilsonColumnNorm.polynomial_norm n q hq β hβ
  have hh := hi.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simp only [mul_pow, output_norm, source_norm] at hsq
  have he : (Real.exp (-β * R / 2))^2 = Real.exp (-β * R) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hsq
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector (2 * n) β h0).1)).mp
  convert hsq using 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnDecay
