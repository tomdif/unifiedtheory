/- Constructed smooth compact cutoffs preserve positive-time support. Their
L1 approximation, including mixed reflected tensors, suffices for the uniform
bare hierarchy bound; no full Schwartz-topology density claim is needed. -/
import UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PositiveTimeCutoff
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open WilsonReflectedTensor SchwartzConfigurationTensor SchwartzConfigurationConjugation
open AffineCellReflection
open scoped Topology NNReal

/-- Support in the closed positive half-space in every time coordinate,
without any upper time bound. -/
def Supported (m : ℕ) (f : CorrelationTest m) : Prop :=
  ∀ x, f x ≠ 0 → ∀ j, 0 ≤ point m j x 0

def bump (m R : ℕ) : ContDiffBump (0 : Configuration m) :=
  ⟨(R : ℝ)+1, (R : ℝ)+2, by positivity, by linarith⟩

def cutoff (m R : ℕ) (f : CorrelationTest m) : CorrelationTest m :=
  ((bump m R).hasCompactSupport.smul_right (f' := (f : Configuration m → ℂ))).toSchwartzMap ((bump m R).contDiff.smul (f.smooth ⊤))

@[simp] theorem cutoff_apply (m R : ℕ) (f : CorrelationTest m) (x : Configuration m) :
    cutoff m R f x = bump m R x • f x := rfl

theorem cutoff_bound (m R : ℕ) (f : CorrelationTest m) (x : Configuration m) :
    ‖cutoff m R f x‖ ≤ ‖f x‖ := by
  rw [cutoff_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (bump m R).nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) (bump m R).le_one

theorem cutoff_eventually_eq (m : ℕ) (f : CorrelationTest m) (x : Configuration m) :
    ∀ᶠ R : ℕ in atTop, cutoff m R f x = f x := by
  have ht : Tendsto (fun R : ℕ => (R : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop ‖x‖)] with R hR
  have h := (bump m R).one_of_mem_closedBall (by
    change dist x 0 ≤ (R : ℝ)+1
    simpa only [dist_zero_right] using (show ‖x‖ ≤ (R : ℝ)+1 by linarith))
  rw [cutoff_apply, h, one_smul]

theorem cutoff_slab (m R : ℕ) (f : CorrelationTest m) (hf : Supported m f) :
    ∀ x, cutoff m R f x ≠ 0 → ∀ j,
      0 ≤ point m j x 0 ∧ point m j x 0 ≤ (R : ℝ)+2 := by
  intro x hx j
  have hfx : f x ≠ 0 := by
    intro h
    apply hx
    rw [cutoff_apply, h, smul_zero]
  have hbx : bump m R x ≠ 0 := by
    intro h
    apply hx
    rw [cutoff_apply, h, zero_smul]
  have hmem : x ∈ Function.support (bump m R) := hbx
  rw [(bump m R).support_eq, Metric.mem_ball, dist_zero_right] at hmem
  refine ⟨hf x hfx j, ?_⟩
  exact (le_abs_self _).trans ((PiLp.norm_apply_le x (j,0)).trans hmem.le)

theorem cutoff_supported (m R : ℕ) (f : CorrelationTest m) (hf : Supported m f) :
    OSPositiveTimeKernel.Supported m (cutoff m R f) :=
  ⟨(R : ℝ)+2, cutoff_slab m R f hf⟩

/-- A dominated, eventually exact approximation is sufficient in the L1
seminorm controlling the actual bare hierarchy. -/
theorem l1_convergence (m : ℕ) (f : CorrelationTest m) (seq : ℕ → CorrelationTest m)
    (hb : ∀ R x, ‖seq R x‖ ≤ ‖f x‖)
    (he : ∀ x, ∀ᶠ R in atTop, seq R x = f x) :
    Tendsto (fun R => BoundedKernelDistribution.l1Seminorm volume (seq R - f))
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun R x => ‖seq R x - f x‖) (f := fun _ => (0 : ℝ))
    (fun x => 2 * ‖f x‖)
    (fun R => ((seq R).continuous.sub f.continuous).norm.aestronglyMeasurable)
    (f.integrable.norm.const_mul 2)
    (fun R => Eventually.of_forall (fun x => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb R x])))
    (Eventually.of_forall (fun x => tendsto_const_nhds.congr'
      ((he x).mono (fun R hR => by simp only [hR, sub_self, norm_zero]))))
  simpa only [BoundedKernelDistribution.l1Seminorm_apply, SchwartzMap.sub_apply,
    integral_zero] using h

theorem cutoff_l1_tendsto (m : ℕ) (f : CorrelationTest m) :
    Tendsto (fun R => BoundedKernelDistribution.l1Seminorm volume (cutoff m R f - f))
      atTop (𝓝 0) :=
  l1_convergence m f (fun R => cutoff m R f) (fun R => cutoff_bound m R f)
    (cutoff_eventually_eq m f)

theorem reflected_cutoff_bound (m n R : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) (x : Configuration (m+n)) :
    ‖reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g) x‖ ≤
      ‖reflectedTensor m n 0 plane f g x‖ := by
  simp only [reflectedTensor, tensor_apply, conjugation_apply, reflectionPullback_apply,
    norm_mul, norm_star]
  exact mul_le_mul (cutoff_bound m R f _) (cutoff_bound n R g _)
    (norm_nonneg _) (norm_nonneg _)

theorem reflected_cutoff_eventually_eq (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) (x : Configuration (m+n)) :
    ∀ᶠ R in atTop, reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g) x =
      reflectedTensor m n 0 plane f g x := by
  filter_upwards [cutoff_eventually_eq m f
    (CellReflectionCovariance.reflectPoints m 0 plane (split m n x).1),
    cutoff_eventually_eq n g (split m n x).2] with R hf hg
  simp only [reflectedTensor, tensor_apply, conjugation_apply, reflectionPullback_apply]
  rw [hf, hg]

theorem reflected_cutoff_l1_tendsto (m n : ℕ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun R => BoundedKernelDistribution.l1Seminorm volume
      (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g) -
        reflectedTensor m n 0 plane f g)) atTop (𝓝 0) :=
  l1_convergence (m+n) (reflectedTensor m n 0 plane f g)
    (fun R => reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g))
    (fun R => reflected_cutoff_bound m n R plane f g)
    (reflected_cutoff_eventually_eq m n plane f g)

end
end UnifiedTheory.Clay.YangMills.PositiveTimeCutoff
