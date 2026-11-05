/- Common all-order limits of actual cutoff-dependent Wilson insertions.
Uniform continuous Schwartz-seminorm bounds and dense test families are
explicit analytic/formalization inputs. Positivity is derived from the actual
Wilson law, rather than assumed for a limiting positive kernel. -/
import UnifiedTheory.Clay.YangMills.RenormalizedWilsonHierarchy
import UnifiedTheory.Clay.YangMills.HierarchyCompactness
import UnifiedTheory.Clay.YangMills.UltrafilterHierarchyCompactness
import UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedWilsonLimit
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 CellReflectionCovariance
open CountableCorrelationCompactness WilsonReflectedTensor
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The bound may be any fixed continuous seminorm at each order; the
finite-cutoff pointwise character bounds B(k) are allowed to diverge. -/
theorem exists_hierarchy_limit
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ) (plane : Plane)
    (ψ : ℕ → G → ℂ) (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (d : ∀ m, ℕ → CorrelationTest m) (hd : ∀ m, DenseRange (d m)) :
    ∃ (W : Hierarchy) (phi : ℕ → ℕ), StrictMono phi ∧
      WeakConvergence (fun k => RenormalizedWilsonHierarchy.realHierarchy G
        (N (phi k)) (a (phi k)) plane (ψ (phi k)) χ hcχ (B (phi k)) (hB (phi k))
        (beta (phi k)) (offset (phi k))) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ p m f) ∧
      ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x := by
  obtain ⟨W,phi,hphi,hW,hbound⟩ := HierarchyCompactness.exists_weak_hierarchy_subsequence
    (fun k => RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) p hp hb d hd
  refine ⟨W,phi,hphi,hW,hbound,fun f => ?_⟩
  apply tendsto_nhds_unique (hW 0 f)
  simpa only [Function.comp_apply, RenormalizedWilsonHierarchy.realHierarchy,
    RenormalizedWilsonHierarchy.hierarchy_order_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x, f x) atTop (𝓝 (∫ x, f x)))

/-- Exact actual moments converge with the moving lattice reflection.
The uniform seminorm is essential; finite-cutoff bounds B(k) alone do not suffice. -/
theorem reflected_pair_tendsto
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0)
    (ha0 : Tendsto a atTop (𝓝 0)) (plane : Plane)
    (ψ : ℕ → G → ℂ) (hcψ : ∀ k, Continuous (ψ k))
    (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
    (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
    (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => RenormalizedWilsonHierarchy.realHierarchy G (N k)
      (a k) plane (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) W)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun k => ∫ U,
      star (WilsonSmearedObservable.observable G (N k) (a k) plane (realPartCharacter G (ψ k))
        m f (PeriodicTimeReflection.reflectConfiguration (N k) G U)) *
      WilsonSmearedObservable.observable G (N k) (a k) plane (realPartCharacter G (ψ k)) n g U
        ∂wilsonLaw (N k) G χ (beta k) (offset k)) atTop
      (𝓝 (W.correlation (m+n) (reflectedTensor m n 0 plane f g))) := by
  simp_rw [RenormalizedWilsonHierarchy.reflected_pair_eq_hierarchy G _ _ (ha _) plane
    _ χ (hcψ _) hcχ (hψ _) (hinvψ _) _ (hB _)]
  exact MovingTestLimit.hierarchy_moving_limit _ W hW p hp hb
    (m+n) (reflectedTensor m n 0 plane f g)
    (fun k => reflectedTensor m n (a k) plane f g)
    (reflectedTensor_tendsto_zero m n plane f g a ha0)

theorem reflected_pair_eq_half_kernel (n : ℕ) [NeZero n] (a : ℝ) (plane : Plane)
    (ψ χ : G → ℂ) (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re) (beta offset : ℝ)
    {ι : Type*} (order : ι → ℕ) (test : (i : ι) → CorrelationTest (order i)) (i j : ι)
    (hi : ClosedHalfSmearing.Supported n a plane (order i) (test i))
    (hj : ClosedHalfSmearing.Supported n a plane (order j) (test j)) :
    (∫ U, star (WilsonSmearedObservable.observable G (2*n) a plane ψ (order i) (test i)
      (PeriodicTimeReflection.reflectConfiguration (2*n) G U)) *
      WilsonSmearedObservable.observable G (2*n) a plane ψ (order j) (test j) U
        ∂wilsonLaw (2*n) G χ beta offset) =
      ReflectedWilsonKernel.kernel n G χ beta offset
        (WilsonReflectedJointLimit.family n G a plane ψ order test) (some i,some j) := by
  simp_rw [ClosedHalfSmearing.half_identification n G a plane ψ (order i) (test i) hi,
    ClosedHalfSmearing.half_identification n G a plane ψ (order j) (test j) hj,
    ReflectedWilsonKernel.positiveObservable_eq_reflected]
  exact WilsonReflectedJointLimit.integral_reflection n G χ hcχ hχ hinvχ beta offset
    (fun U => star (PeriodicSiteReflection.observable n G
      (ClosedHalfSmearing.halfObservable n G a plane ψ (order i) (test i))
      (PeriodicTimeReflection.reflectConfiguration (2*n) G U)) *
      PeriodicSiteReflection.observable n G
      (ClosedHalfSmearing.halfObservable n G a plane ψ (order j) (test j)) U)

/-- Full finite mixed-order positivity comes from the actual Wilson measure,
even though the insertion and its finite-cutoff bound change with k. -/
theorem finite_form_positive
    (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (ha0 : Tendsto a atTop (𝓝 0)) (plane : Plane)
    (ψ : ℕ → G → ℂ) (hcψ : ∀ k, Continuous (ψ k))
    (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
    (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => RenormalizedWilsonHierarchy.realHierarchy G (2 * period k)
      (a k) plane (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) W)
    (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
    (coeff : Fin l → ℂ)
    (hs : ∀ i, ∀ᶠ k in atTop,
      ClosedHalfSmearing.Supported (period k) (a k) plane (order i) (test i)) :
    0 ≤ (∑ i, ∑ j, star (coeff i)*coeff j * W.correlation (order i+order j)
      (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
    (∑ i, ∑ j, star (coeff i)*coeff j * W.correlation (order i+order j)
      (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  let c (k : ℕ) (ij : Fin l × Fin l) :=
    (RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation
      (order ij.1+order ij.2)
      (reflectedTensor (order ij.1) (order ij.2) (a k) plane (test ij.1) (test ij.2))
  let w (ij : Fin l × Fin l) := W.correlation (order ij.1+order ij.2)
    (reflectedTensor (order ij.1) (order ij.2) 0 plane (test ij.1) (test ij.2))
  have hc : CoordinateConvergence c w := by
    intro ij
    exact MovingTestLimit.hierarchy_moving_limit _ W hW p hp hb _ _ _
      (reflectedTensor_tendsto_zero _ _ plane (test ij.1) (test ij.2) a ha0)
  have hsall := eventually_all.mpr hs
  have hpositive : ∀ᶠ k in atTop,
      0 ≤ (gramValue (fun i j => (i,j)) (c k) l id coeff).re ∧
      (gramValue (fun i j => (i,j)) (c k) l id coeff).im = 0 := by
    filter_upwards [hsall] with k hk
    let F := WilsonReflectedJointLimit.family (period k) G (a k) plane
      (realPartCharacter G (ψ k)) order test
    let K := ReflectedWilsonKernel.kernel (period k) G χ (beta k) (offset k) F
    have he (i j : Fin l) : c k (i,j) = K (some i,some j) :=
      (RenormalizedWilsonHierarchy.reflected_pair_eq_hierarchy G _ _ (ha k) plane
        (ψ k) χ (hcψ k) hcχ (hψ k) (hinvψ k) (B k) (hB k) (beta k) (offset k)
        (order i) (order j) (test i) (test j)).symm.trans
      (reflected_pair_eq_half_kernel G (period k) (a k) plane
        (realPartCharacter G (ψ k)) χ hcχ hχ hinvχ (beta k) (offset k)
        order test i j (hk i) (hk j))
    have heform : gramValue (fun i j => (i,j)) (c k) l id coeff =
        gramValue (fun i j => (i,j)) K l (fun i => some i) coeff := by
      simp only [gramValue, id_eq]
      simp_rw [he]
    rw [heform]
    exact (ReflectedWilsonKernel.kernel_positive (period k) G χ hcχ hχ hinvχ
      (beta k) (offset k) F (WilsonReflectedJointLimit.family_continuous
        (period k) G (a k) plane (realPartCharacter G (ψ k))
        (realPart_continuous G (ψ k) (hcψ k)) order test) l (fun i => some i) coeff).symm
  have ht := gramValue_tendsto c w hc (fun i j => (i,j)) l id coeff
  change 0 ≤ (gramValue (fun i j => (i,j)) w l id coeff).re ∧
    (gramValue (fun i j => (i,j)) w l id coeff).im = 0
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (hpositive.mono (fun _ h => h.1))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht)
      (tendsto_const_nhds.congr' (hpositive.mono (fun _ h => h.2.symm)))


theorem reflected_pair_tendsto_along
    (l : Filter ℕ) (hle : l ≤ atTop)
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0)
    (ha0 : Tendsto a atTop (𝓝 0)) (plane : Plane)
    (ψ : ℕ → G → ℂ) (hcψ : ∀ k, Continuous (ψ k))
    (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
    (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
    (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (W : Hierarchy)
    (hW : UltrafilterHierarchyCompactness.WeakAlong l (fun k => RenormalizedWilsonHierarchy.realHierarchy G (N k)
      (a k) plane (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) W)
    (m n : ℕ) (f : CorrelationTest m) (g : CorrelationTest n) :
    Tendsto (fun k => ∫ U,
      star (WilsonSmearedObservable.observable G (N k) (a k) plane (realPartCharacter G (ψ k))
        m f (PeriodicTimeReflection.reflectConfiguration (N k) G U)) *
      WilsonSmearedObservable.observable G (N k) (a k) plane (realPartCharacter G (ψ k)) n g U
        ∂wilsonLaw (N k) G χ (beta k) (offset k)) l
      (𝓝 (W.correlation (m+n) (reflectedTensor m n 0 plane f g))) := by
  simp_rw [RenormalizedWilsonHierarchy.reflected_pair_eq_hierarchy G _ _ (ha _) plane
    _ χ (hcψ _) hcχ (hψ _) (hinvψ _) _ (hB _)]
  exact UltrafilterHierarchyCompactness.moving_test_limit l
    (fun k => (RenormalizedWilsonHierarchy.realHierarchy G (N k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation (m+n))
    (p (m+n)) (hp (m+n)) (fun k f => hb k (m+n) f)
    (reflectedTensor m n 0 plane f g) (fun k => reflectedTensor m n (a k) plane f g)
    ((reflectedTensor_tendsto_zero m n plane f g a ha0).mono_left hle) _ (hW (m+n) _)


theorem finite_form_positive_along
    (q : Filter ℕ) [NeBot q] (hq : q ≤ atTop)
    (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (ha0 : Tendsto a atTop (𝓝 0)) (plane : Plane)
    (ψ : ℕ → G → ℂ) (hcψ : ∀ k, Continuous (ψ k))
    (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
    (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation m f‖ ≤ p m f)
    (W : Hierarchy)
    (hW : UltrafilterHierarchyCompactness.WeakAlong q (fun k => RenormalizedWilsonHierarchy.realHierarchy G (2 * period k)
      (a k) plane (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)) W)
    (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
    (coeff : Fin l → ℂ)
    (hs : ∀ i, ∀ᶠ k in atTop,
      ClosedHalfSmearing.Supported (period k) (a k) plane (order i) (test i)) :
    0 ≤ (∑ i, ∑ j, star (coeff i)*coeff j * W.correlation (order i+order j)
      (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
    (∑ i, ∑ j, star (coeff i)*coeff j * W.correlation (order i+order j)
      (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  let c (k : ℕ) (ij : Fin l × Fin l) :=
    (RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane
      (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation
      (order ij.1+order ij.2)
      (reflectedTensor (order ij.1) (order ij.2) (a k) plane (test ij.1) (test ij.2))
  let w (ij : Fin l × Fin l) := W.correlation (order ij.1+order ij.2)
    (reflectedTensor (order ij.1) (order ij.2) 0 plane (test ij.1) (test ij.2))
  have hc : ∀ ij, Tendsto (fun k => c k ij) q (𝓝 (w ij)) := by
    intro ij
    exact UltrafilterHierarchyCompactness.moving_test_limit q
      (fun k => (RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane
        (ψ k) χ hcχ (B k) (hB k) (beta k) (offset k)).correlation (order ij.1+order ij.2))
      (p _) (hp _) (fun k f => hb k _ f) _ _
      ((reflectedTensor_tendsto_zero _ _ plane (test ij.1) (test ij.2) a ha0).mono_left hq)
      _ (hW _ _)
  have hsall := eventually_all.mpr hs
  have hpositive : ∀ᶠ k in atTop,
      0 ≤ (gramValue (fun i j => (i,j)) (c k) l id coeff).re ∧
      (gramValue (fun i j => (i,j)) (c k) l id coeff).im = 0 := by
    filter_upwards [hsall] with k hk
    let F := WilsonReflectedJointLimit.family (period k) G (a k) plane
      (realPartCharacter G (ψ k)) order test
    let K := ReflectedWilsonKernel.kernel (period k) G χ (beta k) (offset k) F
    have he (i j : Fin l) : c k (i,j) = K (some i,some j) :=
      (RenormalizedWilsonHierarchy.reflected_pair_eq_hierarchy G _ _ (ha k) plane
        (ψ k) χ (hcψ k) hcχ (hψ k) (hinvψ k) (B k) (hB k) (beta k) (offset k)
        (order i) (order j) (test i) (test j)).symm.trans
      (reflected_pair_eq_half_kernel G (period k) (a k) plane
        (realPartCharacter G (ψ k)) χ hcχ hχ hinvχ (beta k) (offset k)
        order test i j (hk i) (hk j))
    have heform : gramValue (fun i j => (i,j)) (c k) l id coeff =
        gramValue (fun i j => (i,j)) K l (fun i => some i) coeff := by
      simp only [gramValue, id_eq]
      simp_rw [he]
    rw [heform]
    exact (ReflectedWilsonKernel.kernel_positive (period k) G χ hcχ hχ hinvχ
      (beta k) (offset k) F (WilsonReflectedJointLimit.family_continuous
        (period k) G (a k) plane (realPartCharacter G (ψ k))
        (realPart_continuous G (ψ k) (hcψ k)) order test) l (fun i => some i) coeff).symm
  have ht : Tendsto (fun k => gramValue (fun i j => (i,j)) (c k) l id coeff) q
      (𝓝 (gramValue (fun i j => (i,j)) w l id coeff)) := by
    unfold gramValue
    exact tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _
      (fun j _ => tendsto_const_nhds.mul (hc (i,j))))
  change 0 ≤ (gramValue (fun i j => (i,j)) w l id coeff).re ∧
    (gramValue (fun i j => (i,j)) w l id coeff).im = 0
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (hq (hpositive.mono (fun _ h => h.1)))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht)
      (tendsto_const_nhds.congr' (hq (hpositive.mono (fun _ h => h.2.symm))))

end
end UnifiedTheory.Clay.YangMills.RenormalizedWilsonLimit
