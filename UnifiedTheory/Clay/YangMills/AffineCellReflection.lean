/- Exact affine reflection on all-order Schwartz correlation tests.
The coordinate map preserves volume; shifted pullbacks converge in the full
Schwartz topology and hence in the continuous L1 seminorm as spacing vanishes. -/
import UnifiedTheory.Clay.YangMills.CellReflectionCovariance
import UnifiedTheory.Clay.YangMills.SchwartzTranslations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.AffineCellReflection
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open CellReflectionCovariance SchwartzTranslations
open scoped Topology

def linearReflection (m : ℕ) : Configuration m ≃ₗᵢ[ℝ] Configuration m :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun jμ : Fin m × Fin 4 =>
    if jμ.2 = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem linearReflection_apply (m : ℕ) (x : Configuration m) (jμ : Fin m × Fin 4) :
    linearReflection m x jμ = if jμ.2 = 0 then -x jμ else x jμ := by
  by_cases h : jμ.2 = 0 <;> simp [linearReflection,
    LinearIsometryEquiv.piLpCongrRight_apply, h]

def offsetVector (m : ℕ) (s : ℝ) : Configuration m :=
  WithLp.toLp 2 (fun jμ => if jμ.2 = 0 then s else 0)

theorem offsetVector_continuous (m : ℕ) : Continuous (offsetVector m) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro jμ
  by_cases h : jμ.2 = 0
  · simpa only [h, if_true] using (continuous_id : Continuous (fun s : ℝ => s))
  · simpa only [h, if_false] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

@[simp] theorem offsetVector_zero (m : ℕ) : offsetVector m 0 = 0 := by
  ext jμ
  simp [offsetVector]

theorem reflectPoints_decomposition (m : ℕ) (a : ℝ) (plane : Plane) (x : Configuration m) :
    reflectPoints m a plane x = linearReflection m x + offsetVector m (cellOffset a plane) := by
  ext jμ
  rcases jμ with ⟨j, μ⟩
  rw [PiLp.add_apply, linearReflection_apply]
  by_cases h : μ = 0
  · subst μ
    simp [reflectPoints, offsetVector, sub_eq_add_neg, add_comm]
  · simp [reflectPoints, offsetVector, h]

@[simp] theorem reflectPoints_twice (m : ℕ) (a : ℝ) (plane : Plane) (x : Configuration m) :
    reflectPoints m a plane (reflectPoints m a plane x) = x := by
  ext jμ
  rcases jμ with ⟨j, μ⟩
  by_cases h : μ = 0
  · subst μ
    simp [reflectPoints]
  · simp [reflectPoints, h]

theorem reflectPoints_continuous (m : ℕ) (a : ℝ) (plane : Plane) :
    Continuous (reflectPoints m a plane) := by
  have he : reflectPoints m a plane =
      fun x => linearReflection m x + offsetVector m (cellOffset a plane) :=
    funext (reflectPoints_decomposition m a plane)
  rw [he]
  exact (linearReflection m).continuous.add continuous_const

def reflectionEquiv (m : ℕ) (a : ℝ) (plane : Plane) : Configuration m ≃ᵐ Configuration m where
  toFun := reflectPoints m a plane
  invFun := reflectPoints m a plane
  left_inv := reflectPoints_twice m a plane
  right_inv := reflectPoints_twice m a plane
  measurable_toFun := (reflectPoints_continuous m a plane).measurable
  measurable_invFun := (reflectPoints_continuous m a plane).measurable

@[simp] theorem reflectionEquiv_apply (m : ℕ) (a : ℝ) (plane : Plane) (x : Configuration m) :
    reflectionEquiv m a plane x = reflectPoints m a plane x := rfl

theorem reflection_preserves_volume (m : ℕ) (a : ℝ) (plane : Plane) :
    MeasurePreserving (reflectionEquiv m a plane) volume volume := by
  have h := (measurePreserving_add_right (volume : Measure (Configuration m))
    (offsetVector m (cellOffset a plane))).comp (linearReflection m).measurePreserving
  convert h using 1
  funext x
  exact reflectPoints_decomposition m a plane x

def linearPullback (m : ℕ) : CorrelationTest m →L[ℂ] CorrelationTest m :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linearReflection m).toContinuousLinearEquiv

def reflectionPullback (m : ℕ) (a : ℝ) (plane : Plane) :
    CorrelationTest m →L[ℂ] CorrelationTest m :=
  (linearPullback m).comp (translationCLM (-offsetVector m (cellOffset a plane)))

@[simp] theorem reflectionPullback_apply (m : ℕ) (a : ℝ) (plane : Plane)
    (f : CorrelationTest m) (x : Configuration m) :
    reflectionPullback m a plane f x = f (reflectPoints m a plane x) := by
  change f (linearReflection m x - -offsetVector m (cellOffset a plane)) = _
  rw [sub_neg_eq_add, ← reflectPoints_decomposition]

@[simp] theorem reflectionPullback_twice (m : ℕ) (a : ℝ) (plane : Plane)
    (f : CorrelationTest m) : reflectionPullback m a plane (reflectionPullback m a plane f) = f := by
  ext x
  simp only [reflectionPullback_apply, reflectPoints_twice]

theorem reflectionPullback_zero (m : ℕ) (plane : Plane) (f : CorrelationTest m) :
    reflectionPullback m 0 plane f = linearPullback m f := by
  ext x
  simp only [reflectionPullback_apply, reflectPoints_decomposition, cellOffset, ite_self,
    offsetVector_zero, add_zero]
  rfl

/-- Convergence is in every Schwartz seminorm, not only at point evaluations. -/
theorem reflectionPullback_tendsto_zero (m : ℕ) (plane : Plane) (f : CorrelationTest m)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => reflectionPullback m (a k) plane f) atTop
      (𝓝 (reflectionPullback m 0 plane f)) := by
  have ho : Tendsto (fun k => cellOffset (a k) plane) atTop (𝓝 0) := by
    by_cases h : plane.1.1 = 0
    · simpa only [cellOffset, h, if_true] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [cellOffset, h, if_false] using ha
  have hv : Tendsto (fun k => -offsetVector m (cellOffset (a k) plane)) atTop
      (𝓝 (0 : Configuration m)) := by
    simpa only [offsetVector_zero, neg_zero] using
      (((offsetVector_continuous m).tendsto 0).comp ho).neg
  have ht := (tendsto_translation_zero f).comp hv
  have hl := (linearPullback m).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, reflectionPullback_zero] using hl

theorem reflectionPullback_l1_difference_tendsto_zero (m : ℕ) (plane : Plane)
    (f : CorrelationTest m) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => BoundedKernelDistribution.l1Seminorm volume
      (reflectionPullback m (a k) plane f - reflectionPullback m 0 plane f)) atTop (𝓝 0) := by
  have ht := (reflectionPullback_tendsto_zero m plane f a ha).sub
    (tendsto_const_nhds (x := reflectionPullback m 0 plane f))
  have h := (BoundedKernelDistribution.l1Seminorm_continuous
    (volume : Measure (Configuration m))).continuousAt.tendsto.comp ht
  simpa only [sub_self, map_zero] using h

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

/-- Exact actual-regulator reflection as a pullback of Schwartz tests. -/
theorem reflected_smearing_identity (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (χ : G → ℂ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (m : ℕ) (f : CorrelationTest m)
    (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m f
      (PeriodicTimeReflection.reflectConfiguration N G U) =
    WilsonSmearedObservable.observable G N a plane (realPartCharacter G χ) m
      (reflectionPullback m a plane f) U := by
  rw [reflected_observable_integral G N a ha plane χ hχ hinv,
    WilsonSmearedObservable.observable_integral]
  have h := (reflection_preserves_volume m a plane).integral_comp
    (reflectionEquiv m a plane).measurableEmbedding
    (fun x => WilsonSmearedObservable.word G N (realPartCharacter G χ) m
      (sampleConfiguration m N a plane x) U * reflectionPullback m a plane f x)
  simpa only [reflectionEquiv_apply, reflectionPullback_apply, reflectPoints_twice] using h

end
end UnifiedTheory.Clay.YangMills.AffineCellReflection
