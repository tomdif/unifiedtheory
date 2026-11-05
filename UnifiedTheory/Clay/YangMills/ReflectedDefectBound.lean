/- Quantitative actual centered reflected Wilson forms are controlled by the
mean plaquette defect. This provides a rate input for renormalized fixed tests;
it does not assert a positive fluctuation limit or physical field identification. -/
import UnifiedTheory.Clay.YangMills.BareDefectHierarchy
import UnifiedTheory.Clay.YangMills.ReflectedWilsonRenormalization
import UnifiedTheory.Clay.YangMills.OSTestTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ReflectedDefectBound
noncomputable section
open MeasureTheory Filter ContinuumControl RegulatedGauge PeriodicLattice4
open PeriodicTimeReflection PeriodicPlaquetteReflection
open WilsonReflectedTensor CellReflectionCovariance WilsonCrossingKernel UnitaryCharacterObservables
open SchwartzConfigurationTensor SchwartzConfigurationConjugation AffineCellReflection
open BareDefectHierarchy ReflectedWilsonRenormalization
open scoped Topology NNReal

theorem l1_reflection (m : ℕ) (a : ℝ) (plane : Plane) (f : CorrelationTest m) :
    BoundedKernelDistribution.l1Seminorm volume (reflectionPullback m a plane f) =
      BoundedKernelDistribution.l1Seminorm volume f := by
  rw [BoundedKernelDistribution.l1Seminorm_apply, BoundedKernelDistribution.l1Seminorm_apply]
  simpa only [reflectionEquiv_apply, reflectionPullback_apply] using
    (reflection_preserves_volume m a plane).integral_comp
      (reflectionEquiv m a plane).measurableEmbedding (fun x => ‖f x‖)

theorem l1_reflectedTensor (m n : ℕ) (a : ℝ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    BoundedKernelDistribution.l1Seminorm volume (reflectedTensor m n a plane f g) =
      BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  rw [reflectedTensor, OSTestTranslation.l1_tensor, OSTestTranslation.l1_conjugation,
    l1_reflection]

theorem integral_reflectedTensor (m n : ℕ) (a : ℝ) (plane : Plane)
    (f : CorrelationTest m) (g : CorrelationTest n) :
    (∫ z, reflectedTensor m n a plane f g z) = star (∫ x, f x) * ∫ y, g y := by
  rw [reflectedTensor, ← integral_concat]
  simp only [tensor_apply, split_concat]
  trans (∫ x, conjugation m (reflectionPullback m a plane f) x) * ∫ y, g y
  · exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x => conjugation m (reflectionPullback m a plane f) x) (fun y => g y)
  congr 1
  simp only [conjugation_apply, Complex.star_def]
  rw [integral_conj]
  congr 1
  simpa only [reflectionEquiv_apply, reflectionPullback_apply] using
    (reflection_preserves_volume m a plane).integral_comp
      (reflectionEquiv m a plane).measurableEmbedding (fun x => f x)

section Probability
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem centered_pair_integral (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x, star (f x - ∫ y, f y ∂μ) * (g x - ∫ y, g y ∂μ) ∂μ) =
      (∫ x, star (f x) * g x ∂μ) - star (∫ x, f x ∂μ) * ∫ y, g y ∂μ := by
  let mf := ∫ x, f x ∂μ
  let mg := ∫ x, g x ∂μ
  have hgI : Integrable g μ := hg.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun x => star (f x)) μ := hf.star.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hp : Integrable (fun x => star (f x) * g x) μ :=
    (hf.star.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (x : X) : star (f x-mf)*(g x-mg) =
      (star (f x)*g x-star (f x)*mg)-star mf*g x+star mf*mg := by
    rw [star_sub]
    ring
  change (∫ x, star (f x-mf)*(g x-mg) ∂μ) = _
  simp_rw [he]
  rw [integral_add, integral_sub, integral_sub, integral_mul_const, integral_const_mul]
  rotate_left
  · exact hp
  · exact hs.mul_const mg
  · exact hp.sub (hs.mul_const mg)
  · exact hgI.const_mul (star mf)
  · exact (hp.sub (hs.mul_const mg)).sub (hgI.const_mul (star mf))
  · exact integrable_const _
  simp only [integral_const, probReal_univ, one_smul, Complex.star_def, integral_conj]
  dsimp [mf, mg]
  ring
end Probability

variable (G : Type*) [Group G] (N : ℕ) [NeZero N]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {d : Type*} [Fintype d] [DecidableEq d]

theorem continuous_reflection : Continuous (reflectConfiguration N G) := by
  apply continuous_pi
  intro e
  change Continuous (fun U : RegulatedGauge.Configuration (Vertex N) G =>
    if e.2.2.val = 0 then (U (edgeEquiv N e))⁻¹ else U (edgeEquiv N e))
  split_ifs
  · exact (continuous_apply _).inv
  · exact continuous_apply _

/-- Exact centering dictionary in the original unitary-character action law. -/
theorem reflectedForm_identity (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℝ) (f g : CorrelationTest 1) :
    reflectedForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) f g =
      (unitaryHierarchy N a plane ρ hρ beta).correlation 2 (reflectedTensor 1 1 a plane f g) -
        star ((unitaryHierarchy N a plane ρ hρ beta).correlation 1 f) *
          (unitaryHierarchy N a plane ρ hρ beta).correlation 1 g := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)
  let F := WilsonSmearedObservable.observable G N a plane
    (realPartCharacter G (unitaryCharacter ρ)) 1 f
  let H := WilsonSmearedObservable.observable G N a plane
    (realPartCharacter G (unitaryCharacter ρ)) 1 g
  letI := wilsonLaw_probability N G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d)
  have hc := realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)
  have hF : Continuous F := WilsonSmearedObservable.observable_continuous G N a plane _ hc 1 f
  have hH : Continuous H := WilsonSmearedObservable.observable_continuous G N a plane _ hc 1 g
  have hp := wilsonLaw_preserves_reflection N G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
    (unitaryCharacter_inverse_re G ρ) beta (Fintype.card d)
  have hm : (∫ U, F (reflectConfiguration N G U) ∂μ) = ∫ U, F U ∂μ :=
    hp.integral_comp (MeasurableEquiv.ofInvolutive _ (reflectConfiguration_involutive N G)
      hp.measurable).measurableEmbedding F
  have he := centered_pair_integral μ (fun U => F (reflectConfiguration N G U)) H
    (hF.comp (continuous_reflection G N)) hH
  rw [hm] at he
  change (∫ U, star (F (reflectConfiguration N G U) - ∫ V, F V ∂μ) *
    (H U - ∫ V, H V ∂μ) ∂μ) = _
  rw [he]
  have hpair := reflected_pair_eq_hierarchy G N a ha plane (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
    (unitaryCharacter_inverse_re G ρ) (Fintype.card d) (fun z => unitary_trace_bound (ρ z))
    beta (Fintype.card d) 1 1 f g
  have hfmean := WilsonSmearedObservable.expectation_eq_hierarchy G N a plane
    (realPartCharacter G (unitaryCharacter ρ)) hc (Fintype.card d)
    (realPart_bound G _ (Fintype.card d) (fun z => unitary_trace_bound (ρ z)))
    beta (Fintype.card d) 1 f
  have hgmean := WilsonSmearedObservable.expectation_eq_hierarchy G N a plane
    (realPartCharacter G (unitaryCharacter ρ)) hc (Fintype.card d)
    (realPart_bound G _ (Fintype.card d) (fun z => unitary_trace_bound (ρ z)))
    beta (Fintype.card d) 1 g
  exact congrArg₂ (fun p q : ℂ => p-q)
    hpair (congrArg₂ (fun p q : ℂ => star p*q) hfmean hgmean)

/-- Elementary connected-product estimate, used with actual moment errors. -/
theorem connected_norm_le (C A B alpha beta : ℂ) :
    ‖C-star A*B‖ ≤ ‖C-star alpha*beta‖ +
      ‖A-alpha‖*‖B‖ + ‖alpha‖*‖B-beta‖ := by
  have he : C-star A*B =
      (C-star alpha*beta) - star (A-alpha)*B - star alpha*(B-beta) := by
    rw [star_sub]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (by simp only [norm_mul, norm_star, le_refl]))
      (by simp only [norm_mul, norm_star, le_refl]))

/-- A quantitative fixed-smear bound in the original interacting Wilson law.
All spacing dependence remains explicit; no fluctuation lower bound is claimed. -/
theorem reflectedForm_bound (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℝ) (f g : CorrelationTest 1) :
    ‖reflectedForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) f g‖ ≤
      24 * (Fintype.card d : ℝ) *
        (∫ U, WilsonAverageDefect.averageDefect N G ρ U
          ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) *
        BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  let S := unitaryHierarchy N a plane ρ hρ beta
  let D : ℝ := Fintype.card d
  let delta := ∫ U, WilsonAverageDefect.averageDefect N G ρ U
    ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)
  let F := BoundedKernelDistribution.l1Seminorm volume f
  let H := BoundedKernelDistribution.l1Seminorm volume g
  let alpha := (Fintype.card d : ℂ) * ∫ x, f x
  let eta := (Fintype.card d : ℂ) * ∫ x, g x
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hdelta : 0 ≤ delta := integral_nonneg (WilsonAverageDefect.average_nonneg N G ρ)
  have hF : 0 ≤ F := apply_nonneg _ _
  have hH : 0 ≤ H := apply_nonneg _ _
  have heconstant : (Fintype.card d : ℂ)^2 * (∫ x, reflectedTensor 1 1 a plane f g x) =
      star alpha * eta := by
    rw [integral_reflectedTensor]
    dsimp [alpha, eta]
    simp only [star_mul, star_natCast, Complex.star_def, map_mul, map_natCast, pow_two]
    ring
  have htwo : ‖S.correlation 2 (reflectedTensor 1 1 a plane f g) - star alpha*eta‖ ≤
      12 * D * delta * F * H := by
    have h := hierarchy_difference_average N a plane ρ hρ beta 2
      (reflectedTensor 1 1 a plane f g)
    rw [heconstant, l1_reflectedTensor 1 1 a plane f g] at h
    norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at h
    convert h using 1 <;> dsimp [D, delta, F, H, S] <;> ring
  have hferror : ‖S.correlation 1 f - alpha‖ ≤ 6 * delta * F := by
    have h := hierarchy_difference_average N a plane ρ hρ beta 1 f
    simpa only [Nat.sub_self, pow_zero, pow_one, Nat.cast_one, one_mul] using h
  have hgerror : ‖S.correlation 1 g - eta‖ ≤ 6 * delta * H := by
    have h := hierarchy_difference_average N a plane ρ hρ beta 1 g
    simpa only [Nat.sub_self, pow_zero, pow_one, Nat.cast_one, one_mul] using h
  have hmean : ‖S.correlation 1 g‖ ≤ D * H := by
    have h := WilsonCellHierarchy.hierarchy_uniform_bound G N a plane
      (realPartCharacter G (unitaryCharacter ρ))
      (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)) (Fintype.card d)
      (realPart_bound G _ (Fintype.card d) (fun z => unitary_trace_bound (ρ z)))
      beta (Fintype.card d) 1 g
    simpa only [BoundedKernelDistribution.boundSeminorm, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul, pow_one, NNReal.coe_natCast] using h
  have halpha : ‖alpha‖ ≤ D * F := by
    dsimp only [alpha]
    rw [norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ hD
    exact (norm_integral_le_integral_norm f).trans_eq
      (BoundedKernelDistribution.l1Seminorm_apply volume f).symm
  rw [reflectedForm_identity G N a ha plane ρ hρ beta f g]
  have h := connected_norm_le (S.correlation 2 (reflectedTensor 1 1 a plane f g))
    (S.correlation 1 f) (S.correlation 1 g) alpha eta
  refine h.trans ?_
  have hprod1 := mul_le_mul hferror hmean (norm_nonneg _) (by positivity : 0 ≤ 6*delta*F)
  have hprod2 := mul_le_mul halpha hgerror (norm_nonneg _) (mul_nonneg hD hF)
  refine (add_le_add (add_le_add htwo hprod1) hprod2).trans_eq ?_
  change 12*D*delta*F*H + (6*delta*F)*(D*H) + (D*F)*(6*delta*H) = 24*D*delta*F*H
  ring

end
end UnifiedTheory.Clay.YangMills.ReflectedDefectBound
