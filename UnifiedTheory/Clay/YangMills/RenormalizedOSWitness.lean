/- An actual connected reflected Wilson lower bound survives renormalized
weak convergence and gives a nonzero vector orthogonal to the normalized OS
vacuum. Uniform renormalized bounds and the positive floor remain hypotheses;
neither is inferred from ordinary variance or the bare bounded hierarchy. -/
import UnifiedTheory.Clay.YangMills.RenormalizedWilsonLimit
import UnifiedTheory.Clay.YangMills.ReflectedDefectBound
import UnifiedTheory.Clay.YangMills.OSVacuumSector

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedOSWitness
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 CellReflectionCovariance
open WilsonReflectedTensor OSPositiveTimeKernel KernelHilbertCompletion OSFactorizedCollapse
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem observable_vacuum (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ψ : G → ℂ) (U : RegulatedGauge.Configuration (Vertex N) G) :
    WilsonSmearedObservable.observable G N a plane ψ 0 vacuumTest U = 1 := by
  rw [WilsonSmearedObservable.observable_integral]
  simp only [WilsonSmearedObservable.word, Fin.prod_univ_zero, one_mul, vacuumTest_apply]
  change (∫ _ : EuclideanSpace ℝ (Fin 0 × Fin 4), (1 : ℂ)) = 1
  rw [volume_euclideanSpace_eq_dirac]
  simp

/-- The connected form is identified with the same action-preserving
renormalized hierarchy, including its actual one-point subtractions. -/
theorem connected_identity (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ψ χ : G → ℂ) (hcψ : Continuous ψ) (hcχ : Continuous χ)
    (hψ : RegulatedGauge.ClassFunction G ψ) (hinvψ : ∀ g, (ψ g⁻¹).re = (ψ g).re)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re)
    (B : ℝ≥0) (hB : ∀ g, ‖ψ g‖ ≤ B) (beta offset : ℝ) (f g : CorrelationTest 1) :
    ReflectedWilsonRenormalization.reflectedForm G N a plane (realPartCharacter G ψ)
      χ beta offset f g =
      (RenormalizedWilsonHierarchy.realHierarchy G N a plane ψ χ hcχ B hB beta offset).correlation 2 (reflectedTensor 1 1 a plane f g) -
      star ((RenormalizedWilsonHierarchy.realHierarchy G N a plane ψ χ hcχ B hB
        beta offset).correlation 1 f) *
      (RenormalizedWilsonHierarchy.realHierarchy G N a plane ψ χ hcχ B hB
        beta offset).correlation 1 g := by
  let μ := wilsonLaw N G χ beta offset
  let F := WilsonSmearedObservable.observable G N a plane (realPartCharacter G ψ) 1 f
  let H := WilsonSmearedObservable.observable G N a plane (realPartCharacter G ψ) 1 g
  letI := wilsonLaw_probability N G χ hcχ beta offset
  have hF : Continuous F := WilsonSmearedObservable.observable_continuous G N a plane _
    (realPart_continuous G ψ hcψ) 1 f
  have hH : Continuous H := WilsonSmearedObservable.observable_continuous G N a plane _
    (realPart_continuous G ψ hcψ) 1 g
  have hR := PeriodicPlaquetteReflection.wilsonLaw_preserves_reflection N G χ hcχ hχ hinvχ
    beta offset
  have hm : (∫ U, F (PeriodicTimeReflection.reflectConfiguration N G U) ∂μ) =
      ∫ U, F U ∂μ :=
    hR.integral_comp (MeasurableEquiv.ofInvolutive _
      (PeriodicTimeReflection.reflectConfiguration_involutive N G) hR.measurable).measurableEmbedding F
  have he := ReflectedDefectBound.centered_pair_integral μ
    (fun U => F (PeriodicTimeReflection.reflectConfiguration N G U)) H
    (hF.comp (ReflectedDefectBound.continuous_reflection G N)) hH
  rw [hm] at he
  change (∫ U, star (F (PeriodicTimeReflection.reflectConfiguration N G U) - ∫ V, F V ∂μ) *
    (H U - ∫ V, H V ∂μ) ∂μ) = _
  rw [he]
  rw [RenormalizedWilsonHierarchy.reflected_pair_eq_hierarchy G N a ha plane ψ χ
    hcψ hcχ hψ hinvψ B hB beta offset]
  congr 1
  rw [RenormalizedWilsonHierarchy.expectation_eq_hierarchy G N a plane
    (realPartCharacter G ψ) χ (realPart_continuous G ψ hcψ) hcχ B
    (realPart_bound G ψ B hB) beta offset,
    RenormalizedWilsonHierarchy.expectation_eq_hierarchy G N a plane
    (realPartCharacter G ψ) χ (realPart_continuous G ψ hcψ) hcχ B
    (realPart_bound G ψ B hB) beta offset]
  rfl

variable (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
  (ψ : ℕ → G → ℂ) (χ : G → ℂ) (hcχ : Continuous χ)
  (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)

def sequence : ℕ → Hierarchy := fun k =>
  RenormalizedWilsonHierarchy.realHierarchy G (2 * period k) (a k) plane (ψ k)
    χ hcχ (B k) (hB k) (beta k) (offset k)

variable (l : Filter ℕ) [NeBot l] (hle : l ≤ atTop)
  (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
  (hcψ : ∀ k, Continuous (ψ k)) (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
  (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
  (hχ : RegulatedGauge.ClassFunction G χ) (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re)
  (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
  (hb : ∀ k m f, ‖(sequence G period a plane ψ χ hcχ B hB beta offset k).correlation m f‖ ≤ p m f)
  (W : Hierarchy) (hW : UltrafilterHierarchyCompactness.WeakAlong l (sequence G period a plane ψ χ hcχ B hB beta offset) W)

include hle ha ha0 hcψ hψ hinvψ hχ hinvχ hp hb hW in
theorem positive
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop) :
    OSPositiveTimeKernel.Positive W plane := by
  apply positive_of_finite_form W plane
  intro count order test coeff R hs
  apply RenormalizedWilsonLimit.finite_form_positive_along G l hle period a (fun k => (ha k).ne')
    ha0 plane ψ hcψ hψ hinvψ χ hcχ hχ hinvχ B hB beta offset p hp hb W hW
    count order test coeff
  intro i
  exact PositiveCellSupport.eventually_supported period a ha hlarge plane
    (order i) (test i) (R i) (hs i)

include hle ha ha0 hcψ hψ hinvψ hχ hinvχ hp hb hW in
theorem connected_tendsto (f g : CorrelationTest 1) :
    Tendsto (fun k => ReflectedWilsonRenormalization.reflectedForm G (2 * period k) (a k)
      plane (realPartCharacter G (ψ k)) χ (beta k) (offset k) f g) l
      (𝓝 (W.correlation 2 (reflectedTensor 1 1 0 plane f g) -
        star (W.correlation 1 f) * W.correlation 1 g)) := by
  simp_rw [connected_identity G _ _ (ha _).ne' plane _ χ (hcψ _) hcχ (hψ _)
    (hinvψ _) hχ hinvχ _ (hB _)]
  apply Tendsto.sub
  · exact UltrafilterHierarchyCompactness.moving_test_limit l
      (fun k => (sequence G period a plane ψ χ hcχ B hB beta offset k).correlation 2)
      (p 2) (hp 2) (fun k f => hb k 2 f) _ _
      ((reflectedTensor_tendsto_zero 1 1 plane f g a ha0).mono_left hle) _ (hW 2 _)
  · exact (hW 1 f).star.mul (hW 1 g)

include hle ha ha0 hcψ hψ hinvψ hp hb hW in
theorem kernel_unit_left (i : OSPositiveTimeKernel.Label) :
    OSPositiveTimeKernel.kernel W plane (vacuumLabel,i) = W.correlation i.1 i.2.1 := by
  have hr := RenormalizedWilsonLimit.reflected_pair_tendsto_along G l hle (fun k => 2 * period k)
    a (fun k => (ha k).ne') ha0 plane ψ hcψ hψ hinvψ χ hcχ B hB beta offset
    p hp hb W hW 0 i.1 vacuumTest i.2.1
  simp only [observable_vacuum, star_one, one_mul] at hr
  have he (k : ℕ) := RenormalizedWilsonHierarchy.expectation_eq_hierarchy G (2 * period k)
    (a k) plane (realPartCharacter G (ψ k)) χ (realPart_continuous G (ψ k) (hcψ k))
    hcχ (B k) (realPart_bound G (ψ k) (B k) (hB k)) (beta k) (offset k) i.1 i.2.1
  simp_rw [he] at hr
  exact tendsto_nhds_unique hr (hW i.1 i.2.1)

include hle ha ha0 hcψ hψ hinvψ hχ hinvχ hp hb hW in
/-- A positive reflected lower floor gives an actual nonzero completed OS
state orthogonal to the unit vacuum. This is stronger than ordinary variance. -/
theorem exists_nonzero_orthogonal
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (eta : ℝ) (heta : 0 < eta)
    (hfloor : ∀ᶠ k in atTop, eta ≤
      (ReflectedWilsonRenormalization.reflectedForm G (2 * period k) (a k)
        plane (realPartCharacter G (ψ k)) χ (beta k) (offset k) f f).re) :
    ∃ hpos : OSPositiveTimeKernel.Positive W plane,
      ∃ v : Hilbert (positiveKernel W plane hpos),
        v ≠ 0 ∧ inner ℂ (OSVacuumSector.vacuum W plane hpos) v = 0 ∧ eta ≤ ‖v‖^2 := by
  have hpos := positive G period a plane ψ χ hcχ B hB beta offset
    l hle ha ha0 hcψ hψ hinvψ hχ hinvχ p hp hb W hW hlarge
  let K := positiveKernel W plane hpos
  let i : OSPositiveTimeKernel.Label := ⟨1,f,hf⟩
  have hu : K.value (vacuumLabel,vacuumLabel) = 1 :=
    OSVacuumSector.kernel_vacuum W plane hpos hn
  have hmean : K.value (vacuumLabel,i) = W.correlation 1 f :=
    kernel_unit_left G period a plane ψ χ hcχ B hB beta offset
      l hle ha ha0 hcψ hψ hinvψ p hp hb W hW i
  have hmeanR : K.value (i,vacuumLabel) = star (W.correlation 1 f) := by
    rw [← PositiveKernelForm.kernel_hermitian K i vacuumLabel, hmean]
  have hc := connected_tendsto G period a plane ψ χ hcχ B hB beta offset
    l hle ha ha0 hcψ hψ hinvψ hχ hinvχ p hp hb W hW f f
  have hlim := ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hc) (hle hfloor)
  have hvar : eta ≤ connectedVariance K vacuumLabel i := by
    unfold connectedVariance
    rw [hmeanR,hmean]
    exact hlim
  refine ⟨hpos, KernelHilbertCompletion.centered K vacuumLabel i,
    centered_ne_zero_of_variance_pos K vacuumLabel i hu (heta.trans_le hvar),
    centered_orthogonal K vacuumLabel i hu, ?_⟩
  rw [centered_norm_sq K vacuumLabel i hu]
  exact hvar

end
end UnifiedTheory.Clay.YangMills.RenormalizedOSWitness
