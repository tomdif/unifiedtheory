/- Concrete translation identities and uniform L1 bounds for the actual
conjugate-reflected Schwartz tensors. These are the analytic inputs for OS
contraction, rather than a postulated transfer operator. -/
import UnifiedTheory.Clay.YangMills.BareSchwingerCandidate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSTestTranslation
noncomputable section
open MeasureTheory ContinuumControl CellTranslationCovariance SchwartzTranslations
open SchwartzConfigurationTensor SchwartzConfigurationConjugation AffineCellReflection
open WilsonReflectedTensor PeriodicLattice4
open scoped NNReal

@[simp] theorem timeVector_zero (m : ℕ) : timeVector m 0 = 0 := by
  ext p
  simp [timeVector]

theorem timeVector_add (m : ℕ) (s t : ℝ) :
    timeVector m (s+t) = timeVector m s + timeVector m t := by
  ext p
  by_cases hp : p.2 = 0 <;> simp [timeVector, hp]

@[simp] theorem timeVector_neg (m : ℕ) (s : ℝ) : timeVector m (-s) = -timeVector m s := by
  ext p
  by_cases hp : p.2 = 0 <;> simp [timeVector, hp]

theorem translation_add (m : ℕ) (s t : ℝ) (f : CorrelationTest m) :
    translationCLM (timeVector m s) (translationCLM (timeVector m t) f) =
      translationCLM (timeVector m (s+t)) f := by
  ext x
  simp only [translationCLM_apply, timeVector_add]
  congr 1
  abel

@[simp] theorem split_timeVector (m n : ℕ) (t : ℝ) :
    split m n (timeVector (m+n) t) = (timeVector m t, timeVector n t) := by
  apply Prod.ext <;> ext p <;> rfl

@[simp] theorem reflect_timeVector (m : ℕ) (t : ℝ) :
    linearReflection m (timeVector m t) = -timeVector m t := by
  ext p
  rw [linearReflection_apply]
  by_cases hp : p.2 = 0 <;> simp [timeVector, hp]

/-- Moving both arguments forward is equivalent, in a stationary reflected
hierarchy, to moving the second argument by the sum of the two times. -/
theorem reflectedTensor_shift (m n : ℕ) (plane : Plane) (s t : ℝ)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    reflectedTensor m n 0 plane (translationCLM (timeVector m s) f)
      (translationCLM (timeVector n t) g) =
    translationCLM (timeVector (m+n) (-s))
      (reflectedTensor m n 0 plane f (translationCLM (timeVector n (s+t)) g)) := by
  ext z
  simp only [reflectedTensor, tensor_apply, conjugation_apply, reflectionPullback_zero,
    translationCLM_apply]
  change star (f (linearReflection m (split m n z).1 - timeVector m s)) *
      g ((split m n z).2 - timeVector n t) =
    star (f (linearReflection m (split m n (z - timeVector (m+n) (-s))).1)) *
      g ((split m n (z - timeVector (m+n) (-s))).2 - timeVector n (s+t))
  simp only [map_sub, map_neg, split_timeVector, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_neg, Prod.snd_neg, reflect_timeVector,
    timeVector_neg, neg_neg, timeVector_add]
  congr 2
  abel

theorem l1_translation (m : ℕ) (t : ℝ) (f : CorrelationTest m) :
    BoundedKernelDistribution.l1Seminorm volume (translationCLM (timeVector m t) f) =
      BoundedKernelDistribution.l1Seminorm volume f := by
  rw [BoundedKernelDistribution.l1Seminorm_apply, BoundedKernelDistribution.l1Seminorm_apply]
  exact integral_sub_right_eq_self (fun x => ‖f x‖) (timeVector m t)

theorem l1_conjugation (m : ℕ) (f : CorrelationTest m) :
    BoundedKernelDistribution.l1Seminorm volume (conjugation m f) =
      BoundedKernelDistribution.l1Seminorm volume f := by
  simp only [BoundedKernelDistribution.l1Seminorm_apply, conjugation_apply, norm_star]

theorem l1_reflection (m : ℕ) (plane : Plane) (f : CorrelationTest m) :
    BoundedKernelDistribution.l1Seminorm volume (reflectionPullback m 0 plane f) =
      BoundedKernelDistribution.l1Seminorm volume f := by
  rw [BoundedKernelDistribution.l1Seminorm_apply, BoundedKernelDistribution.l1Seminorm_apply]
  simpa only [reflectionEquiv_apply, reflectionPullback_apply] using
    (reflection_preserves_volume m 0 plane).integral_comp
      (reflectionEquiv m 0 plane).measurableEmbedding (fun x => ‖f x‖)

theorem l1_tensor (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    BoundedKernelDistribution.l1Seminorm volume (tensor m n f g) =
      BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  simp only [BoundedKernelDistribution.l1Seminorm_apply]
  rw [← (concat_preserves_volume m n).integral_comp
    (concat m n).toHomeomorph.measurableEmbedding (fun z => ‖tensor m n f g z‖)]
  dsimp only
  simp only [tensor_apply, split_concat, norm_mul]
  exact integral_prod_mul (μ := volume) (ν := volume) (fun x => ‖f x‖) (fun y => ‖g y‖)

theorem l1_reflectedTensor (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    BoundedKernelDistribution.l1Seminorm volume (reflectedTensor m n 0 plane f g) =
      BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  rw [reflectedTensor, l1_tensor, l1_conjugation, l1_reflection]

end
end UnifiedTheory.Clay.YangMills.OSTestTranslation
