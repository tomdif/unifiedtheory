/- Full positive-time reflection positivity from constructed Schwartz-density.
Unlike the earlier bare L1 extension, this works for any continuous hierarchy,
including limits controlled by arbitrary continuous Schwartz seminorms. -/
import UnifiedTheory.Clay.YangMills.SchwartzCutoffDensity
import UnifiedTheory.Clay.YangMills.SchwartzTensorContinuity
import UnifiedTheory.Clay.YangMills.FullPositiveTimeReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullSchwartzReflection
noncomputable section
open Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open WilsonReflectedTensor CountableCorrelationCompactness PositiveKernelForm
open scoped Topology

def cutoff (m R : ℕ) (f : CorrelationTest m) : CorrelationTest m :=
  SchwartzCutoffDensity.cutoff (Configuration m) R f

theorem cutoff_slab (m R : ℕ) (f : CorrelationTest m)
    (hf : PositiveTimeCutoff.Supported m f) :
    ∀ x, cutoff m R f x ≠ 0 → ∀ j,
      0 ≤ point m j x 0 ∧ point m j x 0 ≤ 2 * SchwartzCutoffDensity.radius R := by
  intro x hx j
  have hfx : f x ≠ 0 := by
    intro h
    apply hx
    simp only [cutoff, SchwartzCutoffDensity.cutoff_apply, h, mul_zero]
  refine ⟨hf x hfx j, ?_⟩
  exact (le_abs_self _).trans ((PiLp.norm_apply_le x (j,0)).trans
    (SchwartzCutoffDensity.cutoff_support_bound (Configuration m) R f x hx).le)

theorem cutoff_supported (m R : ℕ) (f : CorrelationTest m)
    (hf : PositiveTimeCutoff.Supported m f) :
    OSPositiveTimeKernel.Supported m (cutoff m R f) :=
  ⟨2 * SchwartzCutoffDensity.radius R, cutoff_slab m R f hf⟩

theorem correlation_cutoff_tendsto (W : Hierarchy) (plane : Plane) (m n : ℕ)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun R => W.correlation (m+n)
      (reflectedTensor m n 0 plane (cutoff m R f) (cutoff n R g))) atTop
      (𝓝 (W.correlation (m+n) (reflectedTensor m n 0 plane f g))) :=
  (W.correlation (m+n)).continuous.continuousAt.tendsto.comp
    (SchwartzTensorContinuity.reflected_tensor_tendsto m n 0 plane _ _ f g
      (SchwartzCutoffDensity.cutoff_tendsto (Configuration m) f)
      (SchwartzCutoffDensity.cutoff_tendsto (Configuration n) g))

/-- Mixed orders and arbitrary complex coefficients, with no upper time bound
and no special bare L1 estimate. -/
theorem finite_form_positive (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane)
    (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
    (coeff : Fin l → ℂ) (hs : ∀ i, PositiveTimeCutoff.Supported (order i) (test i)) :
    0 ≤ (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
    (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  let c (R : ℕ) (p : Fin l × Fin l) := W.correlation (order p.1+order p.2)
    (reflectedTensor (order p.1) (order p.2) 0 plane
      (cutoff (order p.1) R (test p.1)) (cutoff (order p.2) R (test p.2)))
  let w (p : Fin l × Fin l) := W.correlation (order p.1+order p.2)
    (reflectedTensor (order p.1) (order p.2) 0 plane (test p.1) (test p.2))
  have hc : CoordinateConvergence c w := fun p =>
    correlation_cutoff_tendsto W plane (order p.1) (order p.2) (test p.1) (test p.2)
  have hpos (R : ℕ) : 0 ≤ (gramValue (fun i j => (i,j)) (c R) l id coeff).re ∧
      (gramValue (fun i j => (i,j)) (c R) l id coeff).im = 0 := by
    exact (hp l (fun i => ⟨order i, cutoff (order i) R (test i),
      cutoff_supported (order i) R (test i) (hs i)⟩) coeff).symm
  have ht := gramValue_tendsto c w hc (fun i j => (i,j)) l id coeff
  change 0 ≤ (gramValue (fun i j => (i,j)) w l id coeff).re ∧
    (gramValue (fun i j => (i,j)) w l id coeff).im = 0
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (Eventually.of_forall (fun R => (hpos R).1))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall (fun R => (hpos R).2.symm)))

/-- Bounded-slab positivity extends to all positive-time Schwartz tests of the
same continuous hierarchy, using the proved cutoff construction. -/
theorem positive_of_positive (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane) : FullPositiveTimeReflection.Positive W plane := by
  intro l index coeff
  exact (finite_form_positive W plane hp l (fun i => (index i).1)
    (fun i => (index i).2.1) coeff (fun i => (index i).2.2)).symm

end
end UnifiedTheory.Clay.YangMills.FullSchwartzReflection
