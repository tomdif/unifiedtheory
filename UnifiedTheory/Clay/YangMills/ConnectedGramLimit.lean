/- Connected fluctuations survive a common Gram-kernel limit. The variance
identity is proved from probability integration; the positive floor in the
abstract extraction theorem is explicitly an input. -/
import UnifiedTheory.Clay.YangMills.KernelHilbertCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ConnectedGramLimit
noncomputable section
open MeasureTheory Filter ProbabilityGramCompactness CountableCorrelationCompactness
open PositiveKernelForm KernelHilbertCompletion
open scoped Topology

section OneMeasure
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem centered_square_integral (f : X → ℂ) (hf : Continuous f) :
    ∫ x, star (f x - ∫ y, f y ∂μ) * (f x - ∫ y, f y ∂μ) ∂μ =
      (∫ x, star (f x) * f x ∂μ) - star (∫ x, f x ∂μ) * (∫ x, f x ∂μ) := by
  let m := ∫ x, f x ∂μ
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun x => star (f x)) μ := (hf.star).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hq : Integrable (fun x => star (f x) * f x) μ :=
    (hf.star.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : X) : star (f x - m) * (f x - m) =
      (star (f x) * f x - star (f x) * m) - star m * f x + star m * m := by
    rw [star_sub]
    ring
  change (∫ x, star (f x - m) * (f x - m) ∂μ) = _
  simp_rw [he]
  rw [integral_add, integral_sub, integral_sub, integral_mul_const, integral_const_mul]
  rotate_left
  · exact hq
  · exact hs.mul_const m
  · exact hq.sub (hs.mul_const m)
  · exact hi.const_mul (star m)
  · exact (hq.sub (hs.mul_const m)).sub (hi.const_mul (star m))
  · exact integrable_const _
  simp only [integral_const, probReal_univ, one_smul, Complex.star_def, integral_conj]
  dsimp [m]
  ring

theorem complex_variance_identity (f : X → ℂ) (hf : Continuous f) :
    (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ) =
      ((∫ x, star (f x) * f x ∂μ) -
        star (∫ x, f x ∂μ) * (∫ x, f x ∂μ)).re := by
  rw [← centered_square_integral μ f hf]
  have hi : Integrable
      (fun x => star (f x - ∫ y, f y ∂μ) * (f x - ∫ y, f y ∂μ)) μ :=
    ((hf.sub continuous_const).star.mul (hf.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change _ = RCLike.re (∫ x, star (f x - ∫ y, f y ∂μ) *
    (f x - ∫ y, f y ∂μ) ∂μ)
  rw [← integral_re hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change _ = (star (f x - ∫ y, f y ∂μ) * (f x - ∫ y, f y ∂μ)).re
    simpa only [Complex.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using
      congrArg Complex.re (Complex.conj_mul' (f x - ∫ y, f y ∂μ)).symm)

theorem gram_variance_identity (F : ι → X → ℂ) (hF : ∀ i, Continuous (F i))
    (u i : ι) (hu : ∀ x, F u x = 1) :
    (∫ x, ‖F i x - ∫ y, F i y ∂μ‖ ^ 2 ∂μ) =
      (kernel μ F (i, i) - kernel μ F (i, u) * kernel μ F (u, i)).re := by
  rw [complex_variance_identity μ (F i) (hF i)]
  simp only [kernel, hu, star_one, one_mul, mul_one, Complex.star_def, integral_conj]
end OneMeasure

variable {ι : Type*}

theorem connected_floor_survives (c : ℕ → ι × ι → ℂ) (w : ι × ι → ℂ)
    (hc : CoordinateConvergence c w) (u i : ι) (eta : ℝ)
    (hf : ∀ k, eta ≤ (c k (i, i) - c k (i, u) * c k (u, i)).re) :
    eta ≤ (w (i, i) - w (i, u) * w (u, i)).re :=
  ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp
    ((hc (i, i)).sub ((hc (i, u)).mul (hc (u, i))))) (Eventually.of_forall hf)

section Family
variable [Countable ι] {X : ℕ → Type*}
  [∀ k, TopologicalSpace (X k)] [∀ k, CompactSpace (X k)]
  [∀ k, MeasurableSpace (X k)] [∀ k, BorelSpace (X k)]
  (μ : ∀ k, Measure (X k)) [∀ k, IsProbabilityMeasure (μ k)]
  (F : ∀ k, ι → X k → ℂ) (hF : ∀ k i, Continuous (F k i))
  (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hb : ∀ k i x, ‖F k i x‖ ≤ B i)

include hF hB hb in
/-- A proved uniform centered floor forces a non-vacuum state in the actual
completed kernel Hilbert space, rather than merely a nonzero unit coordinate. -/
theorem exists_nontrivial_hilbert_kernel (u i : ι) (hu : ∀ k x, F k u x = 1)
    (eta : ℝ) (heta : 0 < eta)
    (hv : ∀ k, eta ≤ ∫ x, ‖F k i x - ∫ y, F k i y ∂μ k‖ ^ 2 ∂μ k) :
    ∃ (K : PositiveKernel ι) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence (fun k => kernel (μ (phi k)) (F (phi k))) K.value ∧
      (∀ p, ‖K.value p‖ ≤ B p.1 * B p.2) ∧ K.value (u, u) = 1 ∧
      eta ≤ connectedVariance K u i ∧
      canonical K i ∉ Submodule.span ℂ ({vacuum K u} : Set (Hilbert K)) := by
  obtain ⟨w, phi, hphi, hc, hbnd, hp, hn⟩ :=
    exists_normalized_positive_kernel_limit μ F hF B hB hb u hu
  let K : PositiveKernel ι := ⟨w, hp⟩
  have hv' : eta ≤ connectedVariance K u i :=
    connected_floor_survives _ _ hc u i eta (fun k => by
      rw [← gram_variance_identity (μ (phi k)) (F (phi k)) (hF (phi k)) u i (hu (phi k))]
      exact hv (phi k))
  exact ⟨K, phi, hphi, hc, hbnd, hn, hv',
    canonical_not_vacuum_span K u i hn (heta.trans_le hv')⟩
end Family

end
end UnifiedTheory.Clay.YangMills.ConnectedGramLimit
