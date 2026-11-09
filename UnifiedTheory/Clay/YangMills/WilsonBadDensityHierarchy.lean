/- Shrinking-density sector removal for the actual mean-centered a^-4
Wilson hierarchy on every full Schwartz test, at every fixed order.
This supplies uniform seminorm bounds for the exceptional sector only.
The retained sector, contact renormalization and a nonzero limit remain open. -/
import UnifiedTheory.Clay.YangMills.WilsonBadDensityContinuum
import UnifiedTheory.Clay.YangMills.MeanCenteredWilsonMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBadDensityHierarchy
noncomputable section
open MeasureTheory Filter PeriodicLattice4 WilsonSingleLinkStaples ContinuumControl
open WilsonEnergyDensity WilsonRemainderDensityTail WilsonBadDensityContinuum
open UnitaryCharacterObservables CellReflectionCovariance WilsonReflectedTensor
open scoped Topology NNReal

variable (n : ℕ) [NeZero n]

/-- The existing same-law mean subtraction, with the actual a^-4 field scaling. -/
def insertion (β a : ℝ) (plane : Plane) : Q → ℂ :=
  MeanCenteredWilsonMoments.insertion (Fin 2) Q n plane representation β (a ^ 4)⁻¹

theorem insertion_continuous (β a : ℝ) (plane : Plane) : Continuous (insertion n β a plane) :=
  RenormalizedWilsonHierarchy.affine_continuous Q _
    (realPart_continuous Q _ (unitaryCharacter_continuous representation representation_continuous))
    _ _

def observable (β a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) :=
  WilsonSmearedObservable.observable Q n a plane (insertion n β a plane) m f

theorem observable_continuous (β a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    Continuous (observable n β a plane m f) :=
  WilsonSmearedObservable.observable_continuous Q n a plane _ (insertion_continuous n β a plane) m f

/-- All full Schwartz tests are covered, including colliding insertion coordinates. -/
theorem observable_bound (β a : ℝ) (ha : 0 < a) (plane : Plane) (m : ℕ)
    (f : CorrelationTest m) (U : RegulatedGauge.Configuration (Vertex n) Q) :
    ‖observable n β a plane m f U‖ ≤
      ((4 : ℝ) ^ m * ∫ x, ‖f x‖) * (a ^ (4 * m))⁻¹ := by
  let B : ℝ≥0 := ⟨4 * (a ^ 4)⁻¹, by positivity⟩
  have hb (g : Q) : ‖insertion n β a plane g‖ ≤ B := by
    have h := MeanCenteredWilsonMoments.insertion_bound (Fin 2) Q n plane representation
      representation_continuous β (a ^ 4)⁻¹ g
    norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
    simpa [insertion, B, abs_of_pos (by positivity : 0 < (a ^ 4)⁻¹), mul_comm] using h
  have h := WilsonSmearedObservable.observable_bound Q n a plane (insertion n β a plane) B hb m f U
  change ‖observable n β a plane m f U‖ ≤
    (B : ℝ) ^ m * BoundedKernelDistribution.l1Seminorm volume f at h
  rw [BoundedKernelDistribution.l1Seminorm_apply] at h
  apply h.trans_eq
  simp only [B, NNReal.coe_mk]
  rw [mul_pow, inv_pow, ← pow_mul]
  ring

/-- Exact identification with the repository's actual mean-centered hierarchy. -/
theorem expectation_eq_hierarchy (β a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    (∫ U, observable n β a plane m f U ∂wilsonLaw n Q character β 2) =
      (MeanCenteredWilsonMoments.hierarchy (Fin 2) Q n a plane representation
        representation_continuous β (a ^ 4)⁻¹).correlation m f := by
  apply RenormalizedWilsonHierarchy.expectation_eq_hierarchy Q n a plane _ _
    (insertion_continuous n β a plane)

variable [Fact (1 < n)]

def badSector (β a : ℝ) (plane : Plane) (m : ℕ) (f : CorrelationTest m) : ℂ :=
  ∫ U in largeDensity n β (vanishingLevel β), observable n β a plane m f U
    ∂wilsonLaw n Q character β 2

/-- The full-test exceptional contribution has an explicit L1-seminorm estimate. -/
theorem badSector_bound (β a : ℝ) (hβ : 0 < β) (ha : 0 < a)
    (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    ‖badSector n β a plane m f‖ ≤
      ((4 : ℝ) ^ m * (a ^ (4 * m))⁻¹ * Real.exp (-(Fintype.card (Vertex n) : ℝ))) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have h := norm_setIntegral_le_of_norm_le_const (measure_lt_top
    (wilsonLaw n Q character β 2) (largeDensity n β (vanishingLevel β)))
    (fun U _ => observable_bound n β a ha plane m f U)
  apply h.trans
  have hp := mul_le_mul_of_nonneg_left (vanishingLevel_probability_bound n β hβ)
    (show 0 ≤ ((4 : ℝ) ^ m * ∫ x, ‖f x‖) * (a ^ (4 * m))⁻¹ by positivity)
  simpa only [BoundedKernelDistribution.l1Seminorm_apply,
    mul_assoc, mul_left_comm, mul_comm] using hp

theorem badSector_cutoff_bound (β a : ℝ) (hβ : 0 < β) (ha : 0 < a)
    (hbox : 1 ≤ (n : ℝ) * a) (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    ‖badSector n β a plane m f‖ ≤
      ((4 : ℝ) ^ m * ((a ^ (4 * m))⁻¹ * Real.exp (-a⁻¹))) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  apply (badSector_bound n β a hβ ha plane m f).trans
  have he := Real.exp_le_exp.mpr (neg_le_neg (inverse_spacing_le_volume n a ha hbox))
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (show 0 ≤ (4 : ℝ) ^ m * (a ^ (4 * m))⁻¹ by positivity))
    (show 0 ≤ BoundedKernelDistribution.l1Seminorm volume f by
      rw [BoundedKernelDistribution.l1Seminorm_apply]; positivity)
  simpa only [mul_assoc] using h

omit [NeZero n] [Fact (1 < n)] in
/-- The exceptional sector has a derived fixed continuous seminorm at every order.
No analogous bound on the retained sector is included in this statement. -/
theorem badSector_uniform_seminorms
    (N : ℕ → ℕ) [∀ k, NeZero (N k)] [∀ k, Fact (1 < N k)]
    (a β : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hβ : ∀ k, 0 < β k) (hbox : ∀ k, 1 ≤ (N k : ℝ) * a k) (plane : Plane) :
    ∃ p : ∀ m, Seminorm ℂ (CorrelationTest m), (∀ m, Continuous (p m)) ∧
      ∀ k m (f : CorrelationTest m), ‖badSector (N k) (β k) (a k) plane m f‖ ≤ p m f := by
  have hb (m : ℕ) : ∃ C : ℝ≥0, ∀ k,
      (a k ^ (4 * m))⁻¹ * Real.exp (-(a k)⁻¹) ≤ C := by
    have ht : Tendsto (fun k => (a k ^ (4 * m))⁻¹ * Real.exp (-(a k)⁻¹)) atTop (𝓝 0) := by
      simpa using cutoff_exponential_tendsto a ha ha0 (4 * m) 1 (by norm_num)
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    exact ⟨⟨max C 0, le_max_right _ _⟩,
      fun k => (hC (Set.mem_range_self k)).trans (le_max_left _ _)⟩
  choose C hC using hb
  refine ⟨fun m => BoundedKernelDistribution.boundSeminorm volume (4 ^ m * C m),
    fun m => BoundedKernelDistribution.boundSeminorm_continuous volume _, ?_⟩
  intro k m f
  apply (badSector_cutoff_bound (N k) (β k) (a k) (hβ k) (ha k) (hbox k) plane m f).trans
  change _ ≤ ((4 : ℝ≥0) ^ m * C m : ℝ≥0) * BoundedKernelDistribution.l1Seminorm volume f
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  gcongr
  exact hC m k

omit [NeZero n] [Fact (1 < n)] in
/-- This proves disappearance of the actual exceptional hierarchy on every full test. -/
theorem badSector_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    Tendsto (fun i => badSector (N i) (β i) (a i) plane m f) l (𝓝 0) := by
  apply vanishing_sector_integral_tendsto N a β ha ha0 hβ hbox
    ((4 : ℝ) ^ m * ∫ x, ‖f x‖) (4 * m) (by positivity)
  exact fun i U => observable_bound (N i) (β i) (a i) (ha i) plane m f U

omit [NeZero n] [Fact (1 < n)] in
/-- The full hierarchy and its shrinking-density restriction differ by a vanishing distribution.
Neither convergence nor a nonzero limit of that restriction is assumed proved. -/
theorem hierarchy_sector_removal {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (plane : Plane) (m : ℕ) (f : CorrelationTest m) :
    Tendsto (fun i =>
      (MeanCenteredWilsonMoments.hierarchy (Fin 2) Q (N i) (a i) plane representation
        representation_continuous (β i) (a i ^ 4)⁻¹).correlation m f -
      ∫ U in (largeDensity (N i) (β i) (vanishingLevel (β i)))ᶜ,
        observable (N i) (β i) (a i) plane m f U
          ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  have he (i : ι) :
      (MeanCenteredWilsonMoments.hierarchy (Fin 2) Q (N i) (a i) plane representation
        representation_continuous (β i) (a i ^ 4)⁻¹).correlation m f -
      (∫ U in (largeDensity (N i) (β i) (vanishingLevel (β i)))ᶜ,
        observable (N i) (β i) (a i) plane m f U
          ∂wilsonLaw (N i) Q character (β i) 2) =
      badSector (N i) (β i) (a i) plane m f := by
    letI := wilsonLaw_probability (N i) Q character character_continuous (β i) 2
    rw [← expectation_eq_hierarchy]
    have h := integral_add_compl (largeDensity_measurable (N i) (β i) (vanishingLevel (β i)))
      ((observable_continuous (N i) (β i) (a i) plane m f).integrable_of_hasCompactSupport
        (μ := wilsonLaw (N i) Q character (β i) 2) (HasCompactSupport.of_compactSpace _))
    exact sub_eq_iff_eq_add.mpr (by simpa only [badSector] using h.symm)
  simp_rw [he]
  exact badSector_tendsto N a β ha ha0 hβ hbox plane m f

end
end UnifiedTheory.Clay.YangMills.WilsonBadDensityHierarchy
