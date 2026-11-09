/- Finite complex reflection Gram forms of the actual limiting real-character
bare hierarchy are positive. Mixed orders and arbitrary finite coefficients
are included. Half support, vanishing spacing, and the actual weak limit are
explicit; no dynamics, clustering, or nontriviality assertion is added. -/
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor
import UnifiedTheory.Clay.YangMills.WilsonReflectedJointLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonHierarchyReflectionPositivity
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 CellReflectionCovariance
open CountableCorrelationCompactness WilsonReflectedTensor
open scoped Topology NNReal ENNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Full finite complex Gram positivity for selected positive-half Schwartz
polynomials of possibly different orders, proved for every actual weak limit
along vanishing nonzero spacings. -/
theorem finite_form_positive
    (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (ha0 : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℕ → ℝ)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (2 * period k) (a k) plane χ hcχ B hB
      (beta k) (offset k)) W)
    (l : ℕ) (order : Fin l → ℕ) (test : (i : Fin l) → CorrelationTest (order i))
    (coeff : Fin l → ℂ)
    (hs : ∀ i, ∀ᶠ k in atTop,
      ClosedHalfSmearing.Supported (period k) (a k) plane (order i) (test i)) :
    0 ≤ (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).re ∧
    (∑ i, ∑ j, star (coeff i) * coeff j *
      W.correlation (order i + order j)
        (reflectedTensor (order i) (order j) 0 plane (test i) (test j))).im = 0 := by
  let c (k : ℕ) (p : Fin l × Fin l) :=
    (realHierarchy G (2 * period k) (a k) plane χ hcχ B hB (beta k) (offset k)).correlation
      (order p.1 + order p.2)
      (reflectedTensor (order p.1) (order p.2) (a k) plane (test p.1) (test p.2))
  let w (p : Fin l × Fin l) := W.correlation (order p.1 + order p.2)
    (reflectedTensor (order p.1) (order p.2) 0 plane (test p.1) (test p.2))
  have hc : CoordinateConvergence c w := by
    intro p
    simpa only [reflected_pair_eq_hierarchy G _ _ (ha _) plane χ hcχ hχ hinv B hB] using
      reflected_pair_tendsto G (fun k => 2 * period k) a ha ha0 plane χ hcχ hχ hinv
        B hB beta offset W hW (order p.1) (order p.2) (test p.1) (test p.2)
  have hsall : ∀ᶠ k in atTop, ∀ i,
      ClosedHalfSmearing.Supported (period k) (a k) plane (order i) (test i) :=
    eventually_all.mpr hs
  have hp : ∀ᶠ k in atTop,
      0 ≤ (gramValue (fun i j => (i,j)) (c k) l id coeff).re ∧
      (gramValue (fun i j => (i,j)) (c k) l id coeff).im = 0 := by
    filter_upwards [hsall] with k hk
    let F := WilsonReflectedJointLimit.family (period k) G (a k) plane
      (realPartCharacter G χ) order test
    let K := ReflectedWilsonKernel.kernel (period k) G (realPartCharacter G χ)
      (beta k) (offset k) F
    have he (i j : Fin l) : c k (i,j) = K (some i, some j) :=
      (reflected_pair_eq_hierarchy G (2 * period k) (a k) (ha k) plane χ hcχ hχ hinv
        B hB (beta k) (offset k) (order i) (order j) (test i) (test j)).symm.trans
      (WilsonReflectedJointLimit.reflected_pair_eq_half_kernel (period k) G (a k) plane
        (realPartCharacter G χ) (realPart_continuous G χ hcχ) (realPart_class G χ hχ)
        (realPart_inverse G χ hinv) (beta k) (offset k) order test i j (hk i) (hk j))
    have heform : gramValue (fun i j => (i,j)) (c k) l id coeff =
        gramValue (fun i j => (i,j)) K l (fun i => some i) coeff := by
      simp only [gramValue, id_eq]
      simp_rw [he]
    rw [heform]
    exact (ReflectedWilsonKernel.kernel_positive (period k) G (realPartCharacter G χ)
      (realPart_continuous G χ hcχ) (realPart_class G χ hχ) (realPart_inverse G χ hinv)
      (beta k) (offset k) F
      (WilsonReflectedJointLimit.family_continuous (period k) G (a k) plane
        (realPartCharacter G χ) (realPart_continuous G χ hcχ) order test)
      l (fun i => some i) coeff).symm
  have ht := gramValue_tendsto c w hc (fun i j => (i,j)) l id coeff
  change 0 ≤ (gramValue (fun i j => (i,j)) w l id coeff).re ∧
    (gramValue (fun i j => (i,j)) w l id coeff).im = 0
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
      (hp.mono (fun _ h => h.1))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp ht)
      (tendsto_const_nhds.congr' (hp.mono (fun _ h => h.2.symm)))

theorem diagonal_positive
    (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (ha : ∀ k, a k ≠ 0) (ha0 : Tendsto a atTop (𝓝 0))
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (beta offset : ℕ → ℝ)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (2 * period k) (a k) plane χ hcχ B hB
      (beta k) (offset k)) W)
    (m : ℕ) (f : CorrelationTest m)
    (hs : ∀ᶠ k in atTop, ClosedHalfSmearing.Supported (period k) (a k) plane m f) :
    0 ≤ (W.correlation (m+m) (reflectedTensor m m 0 plane f f)).re ∧
      (W.correlation (m+m) (reflectedTensor m m 0 plane f f)).im = 0 := by
  simpa only [Fin.sum_univ_one, star_one, one_mul] using
    finite_form_positive G period a ha ha0 plane χ hcχ hχ hinv B hB beta offset W hW
      1 (fun _ => m) (fun _ => f) (fun _ => 1) (fun _ => hs)

end
end UnifiedTheory.Clay.YangMills.WilsonHierarchyReflectionPositivity
