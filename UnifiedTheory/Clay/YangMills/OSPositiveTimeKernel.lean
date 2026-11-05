/- The actual scalar reflected Schwartz kernel carries forward time shifts.
The bounds and adjointness are consequences of hierarchy bounds and stationarity;
no contraction, null-space descent, or Hamiltonian is assumed. -/
import UnifiedTheory.Clay.YangMills.OSTestTranslation
import UnifiedTheory.Clay.YangMills.OSKernelShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 PeriodicCellSampling
open CellTranslationCovariance SchwartzTranslations WilsonReflectedTensor
open CountableCorrelationCompactness PositiveKernelForm KernelHilbertCompletion
open scoped NNReal BigOperators

def Supported (m : ℕ) (f : CorrelationTest m) : Prop :=
  ∃ R : ℝ, ∀ x, f x ≠ 0 → ∀ j, 0 ≤ point m j x 0 ∧ point m j x 0 ≤ R

/-- Every order is allowed, and the finite upper time bound may vary with the label. -/
def Label := Σ m : ℕ, {f : CorrelationTest m // Supported m f}

def shift (t : ℝ≥0) (i : Label) : Label :=
  ⟨i.1, translationCLM (timeVector i.1 t) i.2.1, by
    obtain ⟨R, hR⟩ := i.2.2
    refine ⟨R+t, fun x hx j => ?_⟩
    have h := hR (x-timeVector i.1 t) hx j
    change 0 ≤ x (j,0) ∧ x (j,0) ≤ R + t
    change 0 ≤ (x-timeVector i.1 t) (j,0) ∧ (x-timeVector i.1 t) (j,0) ≤ R at h
    have he : (x-timeVector i.1 t) (j,0) = x (j,0)-t := by
      simp [timeVector]
    rw [he] at h
    constructor <;> linarith [t.coe_nonneg]⟩

@[simp] theorem shift_zero (i : Label) : shift 0 i = i := by
  change @Eq (Σ m : ℕ, {f : CorrelationTest m // Supported m f}) _ _
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  ext x
  simp [shift, translationCLM_apply, OSTestTranslation.timeVector_zero]

theorem shift_add (s t : ℝ≥0) (i : Label) : shift s (shift t i) = shift (s+t) i := by
  change @Eq (Σ m : ℕ, {f : CorrelationTest m // Supported m f}) _ _
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Subtype.ext
  exact OSTestTranslation.translation_add i.1 s t i.2.1

def kernel (W : Hierarchy) (plane : Plane) (p : Label × Label) : ℂ :=
  W.correlation (p.1.1+p.2.1)
    (reflectedTensor p.1.1 p.2.1 0 plane p.1.2.1 p.2.2.1)

def Positive (W : Hierarchy) (plane : Plane) : Prop :=
  GramPositive (fun i j => (i,j)) (kernel W plane)

def positiveKernel (W : Hierarchy) (plane : Plane) (hp : Positive W plane) :
    PositiveKernel Label := ⟨kernel W plane, hp⟩

def Stationary (W : Hierarchy) : Prop :=
  ∀ m t f, W.correlation m (translationCLM (timeVector m t) f) = W.correlation m f

def Bounded (W : Hierarchy) (B : ℝ≥0) : Prop :=
  ∀ m f, ‖W.correlation m f‖ ≤ BoundedKernelDistribution.boundSeminorm volume (B^m) f

theorem kernel_shift (W : Hierarchy) (plane : Plane) (ht : Stationary W)
    (s t : ℝ≥0) (i j : Label) :
    kernel W plane (shift s i, shift t j) = kernel W plane (i, shift (s+t) j) := by
  unfold kernel shift
  dsimp only
  rw [OSTestTranslation.reflectedTensor_shift, ht]
  rfl

theorem kernel_symmetric (W : Hierarchy) (plane : Plane) (ht : Stationary W)
    (t : ℝ≥0) (i j : Label) :
    kernel W plane (shift t i,j) = kernel W plane (i,shift t j) := by
  simpa only [shift_zero, add_zero] using kernel_shift W plane ht t 0 i j

def labelBound (B : ℝ≥0) (i : Label) : ℝ :=
  (B : ℝ)^i.1 * BoundedKernelDistribution.l1Seminorm volume i.2.1

theorem labelBound_nonneg (B : ℝ≥0) (i : Label) : 0 ≤ labelBound B i :=
  mul_nonneg (pow_nonneg B.coe_nonneg _) (apply_nonneg _ _)

theorem kernel_bound (W : Hierarchy) (plane : Plane) (B : ℝ≥0) (hb : Bounded W B)
    (t : ℝ≥0) (i j : Label) :
    ‖kernel W plane (shift t i,shift t j)‖ ≤ labelBound B i * labelBound B j := by
  apply (hb _ _).trans
  change BoundedKernelDistribution.boundSeminorm volume (B^(i.1+j.1))
    (reflectedTensor i.1 j.1 0 plane
      (translationCLM (timeVector i.1 t) i.2.1)
      (translationCLM (timeVector j.1 t) j.2.1)) ≤ _
  simp only [BoundedKernelDistribution.boundSeminorm, Seminorm.smul_apply, NNReal.smul_def]
  rw [OSTestTranslation.l1_reflectedTensor,
    OSTestTranslation.l1_translation, OSTestTranslation.l1_translation]
  simp only [labelBound, smul_eq_mul, NNReal.coe_mul, NNReal.coe_pow, pow_add]
  exact le_of_eq (by ring)

/-- The abstract bounded-orbit argument is instantiated with this actual
reflected hierarchy. In particular, its null-space descent is a conclusion. -/
def shiftData (W : Hierarchy) (plane : Plane) (B : ℝ≥0)
    (hp : Positive W plane) (ht : Stationary W) (hb : Bounded W B) :
    OSKernelShift.ShiftData (positiveKernel W plane hp) where
  shift := shift
  zero := shift_zero
  add := shift_add
  symmetric := kernel_symmetric W plane ht
  bound := labelBound B
  bound_nonneg := labelBound_nonneg B
  kernel_bound := kernel_bound W plane B hb

/-- Strong Schwartz continuity supplies the kernel continuity needed for a
strongly continuous OS semigroup. -/
theorem kernel_shift_continuous (W : Hierarchy) (plane : Plane) (i j : Label) :
    Continuous (fun t : ℝ≥0 => kernel W plane (shift t i,j)) := by
  have ht : Continuous (fun t : ℝ≥0 => translationCLM (timeVector i.1 t) i.2.1) :=
    (continuous_translation_tests i.2.1).comp
      ((ContinuumTimeTranslation.timeVector_continuous i.1).comp NNReal.continuous_coe)
  exact (W.correlation (i.1+j.1)).continuous.comp
    ((SchwartzConfigurationTensor.continuous_tensor_left i.1 j.1 j.2.1).comp
      ((SchwartzConfigurationConjugation.conjugation_continuous i.1).comp
        ((AffineCellReflection.reflectionPullback i.1 0 plane).continuous.comp ht)))

theorem positive_of_finite_form (W : Hierarchy) (plane : Plane)
    (hp : ∀ (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
      (coeff : Fin l → ℂ) (R : Fin l → ℝ),
      (∀ i x, test i x ≠ 0 → ∀ j,
        0 ≤ point (order i) j x 0 ∧ point (order i) j x 0 ≤ R i) →
      0 ≤ (∑ i, ∑ j, star (coeff i) * coeff j *
        W.correlation (order i + order j)
          (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
      (∑ i, ∑ j, star (coeff i) * coeff j *
        W.correlation (order i + order j)
          (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0) :
    Positive W plane := by
  intro l index coeff
  choose R hR using fun i => (index i).2.2
  exact (hp l (fun i => (index i).1) (fun i => (index i).2.1) coeff R hR).symm

end
end UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel
