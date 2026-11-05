/- The high-density remainder sector makes no contribution to fixed-order
physically rescaled Wilson source moments in the continuum limit. This is
a sector-removal theorem, not convergence of the complementary sector. -/
import UnifiedTheory.Clay.YangMills.WilsonRemainderDensityTail
import UnifiedTheory.Clay.YangMills.WilsonSchwartzCovariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBadDensityContinuum
noncomputable section
open MeasureTheory Filter RegulatedGauge LocalFields PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks WilsonRemainderDensityTail WilsonBlockNoiseKernel
open scoped Topology

/-- Exponential suppression beats every fixed power of the ultraviolet cutoff. -/
theorem cutoff_exponential_tendsto {ι : Type*} {l : Filter ι}
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (p : ℕ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun i => (a i ^ p)⁻¹ * Real.exp (-t * (a i)⁻¹)) l (𝓝 0) := by
  have hi : Tendsto (fun i => (a i)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ha0, Eventually.of_forall ha⟩)
  simpa only [Function.comp_def, Real.rpow_natCast, inv_pow] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p : ℝ) t ht).comp hi

variable (n : ℕ) [NeZero n]

/-- A noncollapsing physical side length implies more than enough lattice volume. -/
theorem inverse_spacing_le_volume (a : ℝ) (ha : 0 < a) (hbox : 1 ≤ (n : ℝ) * a) :
    a⁻¹ ≤ (Fintype.card (Vertex n) : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hi : a⁻¹ ≤ (n : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ ha]
    exact hbox
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc
      _ = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hn (by norm_num : 1 ≤ 4)
  simpa [Vertex] using hi.trans hp

/-- Actual cell integration gives a uniform deterministic bound for every Schwartz source. -/
theorem source_norm_bound (a : ℝ) (plane : Plane) (f : TestFunction)
    (U : Configuration (Vertex n) Q) :
    ‖source n (WilsonPhysicalCellWeights.weight n a plane f) U‖ ≤ 4 * ∫ x, ‖f x‖ := by
  rw [source_expansion]
  calc
    _ ≤ ∑ p, ‖WilsonPhysicalCellWeights.weight n a plane f p * source n (basis n p) U‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p, |WilsonPhysicalCellWeights.weight n a plane f p| * 4 := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (source_basis_bounds n p U).1]
      exact mul_le_mul_of_nonneg_left (source_basis_bounds n p U).2 (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (WilsonPhysicalCellWeights.weight_budget n a plane f)
        (by norm_num)

def centeredSource (β a : ℝ) (plane : Plane) (f : TestFunction)
    (U : Configuration (Vertex n) Q) : ℝ :=
  source n (WilsonPhysicalCellWeights.weight n a plane f) U -
    ∫ W, source n (WilsonPhysicalCellWeights.weight n a plane f) W
      ∂wilsonLaw n Q character β 2

theorem centeredSource_continuous (β a : ℝ) (plane : Plane) (f : TestFunction) :
    Continuous (centeredSource n β a plane f) :=
  (source_continuous n _).sub continuous_const

theorem centeredSource_norm_bound (β a : ℝ) (plane : Plane) (f : TestFunction)
    (U : Configuration (Vertex n) Q) :
    ‖centeredSource n β a plane f U‖ ≤ 8 * ∫ x, ‖f x‖ := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hm : ‖∫ W, source n (WilsonPhysicalCellWeights.weight n a plane f) W
      ∂wilsonLaw n Q character β 2‖ ≤ 4 * ∫ x, ‖f x‖ := by
    simpa using norm_integral_le_of_norm_le_const
      (μ := wilsonLaw n Q character β 2) (Eventually.of_forall (source_norm_bound n a plane f))
  exact (norm_sub_le _ _).trans (by linarith [source_norm_bound n a plane f U])

variable [Fact (1 < n)]

/-- Every polynomially bounded insertion is suppressed on this actual Wilson event. -/
theorem sector_integral_bound (β a t M : ℝ) (p : ℕ) (ha : 0 < a) (hβ : 1 ≤ β)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hbox : 1 ≤ (n : ℝ) * a)
    (hsmall : WilsonRemainderDensity.envelope β ≤ 3 * t)
    (F : Configuration (Vertex n) Q → ℝ)
    (hF : ∀ U, ‖F U‖ ≤ M * (a ^ p)⁻¹) :
    ‖∫ U in largeDensity n β t, F U ∂wilsonLaw n Q character β 2‖ ≤
      M * ((a ^ p)⁻¹ * Real.exp (-t * a⁻¹)) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hs : 1 ≤ Real.sqrt β := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hβ
  have hv := inverse_spacing_le_volume n a ha hbox
  have he : Real.exp (-Real.sqrt β * t * (Fintype.card (Vertex n) : ℝ)) ≤
      Real.exp (-t * a⁻¹) := by
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hv ht
    have h2 := mul_le_mul_of_nonneg_right hs
      (show 0 ≤ t * (Fintype.card (Vertex n) : ℝ) by positivity)
    nlinarith
  calc
    _ ≤ (M * (a ^ p)⁻¹) * (wilsonLaw n Q character β 2).real (largeDensity n β t) :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun U _ => hF U)
    _ ≤ (M * (a ^ p)⁻¹) * Real.exp (-t * a⁻¹) :=
      mul_le_mul_of_nonneg_left
        ((largeDensity_probability_bound n β t (by linarith) hsmall).trans he) (by positivity)
    _ = _ := by ring

omit [NeZero n] [Fact (1 < n)] in
/-- No tuning relation between beta and the cutoff is needed for this sector alone. -/
theorem sector_integral_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (t M : ℝ) (p : ℕ) (ht : 0 < t) (hM : 0 ≤ M)
    (F : ∀ i, Configuration (Vertex (N i)) Q → ℝ)
    (hF : ∀ i U, ‖F i U‖ ≤ M * (a i ^ p)⁻¹) :
    Tendsto (fun i => ∫ U in largeDensity (N i) (β i) t, F i U
      ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using (cutoff_exponential_tendsto a ha ha0 p t ht).const_mul M)
  · exact Eventually.of_forall (fun _ => norm_nonneg _)
  · filter_upwards [hβ.eventually (eventually_ge_atTop (1 : ℝ)), hbox,
      (WilsonRemainderDensity.envelope_tendsto.comp hβ).eventually
        (gt_mem_nhds (show (0 : ℝ) < 3 * t by positivity))] with i hi hbi hsi
    simpa only [neg_mul] using sector_integral_bound (N i) (β i) (a i) t M p
      (ha i) hi ht.le hM hbi hsi.le
      (F i) (hF i)

/-- A fixed-order product of actual mean-centered physical Schwartz cell sources. -/
def momentIntegrand (m : ℕ) (β a : ℝ) (planes : Fin m → Plane)
    (f : Fin m → TestFunction) (U : Configuration (Vertex n) Q) : ℝ :=
  (a ^ (4 * m))⁻¹ * ∏ j, centeredSource n β a (planes j) (f j) U

omit [Fact (1 < n)] in
theorem momentIntegrand_continuous (m : ℕ) (β a : ℝ) (planes : Fin m → Plane)
    (f : Fin m → TestFunction) : Continuous (momentIntegrand n m β a planes f) :=
  continuous_const.mul (continuous_finset_prod _
    (fun j _ => centeredSource_continuous n β a (planes j) (f j)))

omit [Fact (1 < n)] in
theorem momentIntegrand_norm_bound (m : ℕ) (β a : ℝ) (ha : 0 < a)
    (planes : Fin m → Plane) (f : Fin m → TestFunction)
    (U : Configuration (Vertex n) Q) :
    ‖momentIntegrand n m β a planes f U‖ ≤
      (∏ j, (8 * ∫ x, ‖f j x‖)) * (a ^ (4 * m))⁻¹ := by
  unfold momentIntegrand
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (a ^ (4 * m))⁻¹),
    norm_prod, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j _
  exact centeredSource_norm_bound n β a (planes j) (f j) U

omit [NeZero n] [Fact (1 < n)] in
/-- At every fixed order, the high-density sector of the actual rescaled moments vanishes. -/
theorem moment_bad_sector_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (t : ℝ) (ht : 0 < t) (m : ℕ) (planes : Fin m → Plane) (f : Fin m → TestFunction) :
    Tendsto (fun i => ∫ U in largeDensity (N i) (β i) t,
      momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  apply sector_integral_tendsto N a β ha ha0 hβ hbox t (∏ j, (8 * ∫ x, ‖f j x‖)) (4 * m) ht
    (Finset.prod_nonneg (fun _ _ => by positivity))
  exact fun i U => momentIntegrand_norm_bound (N i) m (β i) (a i) (ha i) planes f U

omit [NeZero n] [Fact (1 < n)] in
/-- Removing this sector changes each full physical tensor moment by a vanishing quantity.
This does not assert that either full or retained moment converges. -/
theorem moment_sector_removal {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (t : ℝ) (ht : 0 < t) (m : ℕ) (planes : Fin m → Plane) (f : Fin m → TestFunction) :
    Tendsto (fun i =>
      (∫ U, momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) -
      ∫ U in (largeDensity (N i) (β i) t)ᶜ,
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  have he (i : ι) :
      (∫ U, momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) -
      (∫ U in (largeDensity (N i) (β i) t)ᶜ,
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2) =
      ∫ U in largeDensity (N i) (β i) t,
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2 := by
    letI := wilsonLaw_probability (N i) Q character character_continuous (β i) 2
    have h := integral_add_compl (largeDensity_measurable (N i) (β i) t)
      ((momentIntegrand_continuous (N i) m (β i) (a i) planes f).integrable_of_hasCompactSupport
        (μ := wilsonLaw (N i) Q character (β i) 2) (HasCompactSupport.of_compactSpace _))
    linarith
  simp_rw [he]
  exact moment_bad_sector_tendsto N a β ha ha0 hβ hbox t ht m planes f

omit [NeZero n] [Fact (1 < n)] in
/-- Polynomial insertions vanish even on the exceptional sector with shrinking threshold. -/
theorem vanishing_sector_integral_tendsto {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (M : ℝ) (p : ℕ) (hM : 0 ≤ M)
    (F : ∀ i, Configuration (Vertex (N i)) Q → E)
    (hF : ∀ i U, ‖F i U‖ ≤ M * (a i ^ p)⁻¹) :
    Tendsto (fun i => ∫ U in largeDensity (N i) (β i) (vanishingLevel (β i)), F i U
      ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hu : Tendsto (fun i => M * ((a i ^ p)⁻¹ * Real.exp (-(a i)⁻¹))) l (𝓝 0) := by
    simpa using (cutoff_exponential_tendsto a ha ha0 p 1 (by norm_num)).const_mul M
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => norm_nonneg _)
  · filter_upwards [hβ.eventually (eventually_gt_atTop (0 : ℝ)), hbox] with i hi hbi
    letI := wilsonLaw_probability (N i) Q character character_continuous (β i) 2
    have hp := (vanishingLevel_probability_bound (N i) (β i) hi).trans
      (Real.exp_le_exp.mpr (neg_le_neg (inverse_spacing_le_volume (N i) (a i) (ha i) hbi)))
    calc
      _ ≤ (M * (a i ^ p)⁻¹) * (wilsonLaw (N i) Q character (β i) 2).real
          (largeDensity (N i) (β i) (vanishingLevel (β i))) :=
        norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun U _ => hF i U)
      _ ≤ (M * (a i ^ p)⁻¹) * Real.exp (-(a i)⁻¹) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hM (inv_nonneg.mpr (pow_nonneg (ha i).le p)))
      _ = _ := by ring

omit [NeZero n] [Fact (1 < n)] in
theorem moment_vanishing_sector_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (m : ℕ) (planes : Fin m → Plane) (f : Fin m → TestFunction) :
    Tendsto (fun i => ∫ U in largeDensity (N i) (β i) (vanishingLevel (β i)),
      momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  apply vanishing_sector_integral_tendsto N a β ha ha0 hβ hbox
    (∏ j, (8 * ∫ x, ‖f j x‖)) (4 * m) (Finset.prod_nonneg (fun _ _ => by positivity))
  exact fun i U => momentIntegrand_norm_bound (N i) m (β i) (a i) (ha i) planes f U

omit [NeZero n] [Fact (1 < n)] in
/-- The full physical moments and their restriction to a shrinking-density sector differ
by a quantity tending to zero. Convergence on the retained sector is still required. -/
theorem moment_vanishing_sector_removal {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (a β : ι → ℝ) (ha : ∀ i, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hβ : Tendsto β l atTop) (hbox : ∀ᶠ i in l, 1 ≤ (N i : ℝ) * a i)
    (m : ℕ) (planes : Fin m → Plane) (f : Fin m → TestFunction) :
    Tendsto (fun i =>
      (∫ U, momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) -
      ∫ U in (largeDensity (N i) (β i) (vanishingLevel (β i)))ᶜ,
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2) l (𝓝 0) := by
  have he (i : ι) :
      (∫ U, momentIntegrand (N i) m (β i) (a i) planes f U
        ∂wilsonLaw (N i) Q character (β i) 2) -
      (∫ U in (largeDensity (N i) (β i) (vanishingLevel (β i)))ᶜ,
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2) =
      ∫ U in largeDensity (N i) (β i) (vanishingLevel (β i)),
        momentIntegrand (N i) m (β i) (a i) planes f U
          ∂wilsonLaw (N i) Q character (β i) 2 := by
    letI := wilsonLaw_probability (N i) Q character character_continuous (β i) 2
    have h := integral_add_compl (largeDensity_measurable (N i) (β i) (vanishingLevel (β i)))
      ((momentIntegrand_continuous (N i) m (β i) (a i) planes f).integrable_of_hasCompactSupport
        (μ := wilsonLaw (N i) Q character (β i) 2) (HasCompactSupport.of_compactSpace _))
    linarith
  simp_rw [he]
  exact moment_vanishing_sector_tendsto N a β ha ha0 hβ hbox m planes f

end
end UnifiedTheory.Clay.YangMills.WilsonBadDensityContinuum
