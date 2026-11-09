/- Quantitative control of actual bare real-character Wilson correlations by
the expected unitary plaquette defect. The finite product and smearing bounds
are proved here; their scaling consequences require actual defect concentration. -/
import UnifiedTheory.Clay.YangMills.WilsonWeakCouplingDefect
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BareDefectHierarchy
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonMomentBounds
open CellReflectionCovariance WilsonReflectedTensor WilsonCrossingKernel UnitaryCharacterObservables
open UnitaryHolonomyDefect ContinuumControl
open scoped Topology NNReal

theorem norm_prod_sub_pow (D : ℝ) (hD : 0 ≤ D) (m : ℕ) (z : Fin m → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ D) :
    ‖(∏ j, z j) - (D : ℂ)^m‖ ≤ D^(m-1) * ∑ j, ‖z j - (D : ℂ)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp [Fin.prod_univ_succ, Fin.sum_univ_succ]
    | succ k =>
      have hi := ih (fun j => z j.succ) (fun j => hz j.succ)
      have he : z 0 * (∏ j : Fin (k+1), z j.succ) - (D : ℂ)^(k+1+1) =
          z 0 * ((∏ j : Fin (k+1), z j.succ) - (D : ℂ)^(k+1)) +
            (z 0 - (D : ℂ)) * (D : ℂ)^(k+1) := by
        rw [pow_succ]
        ring
      calc
        _ = ‖z 0 * ((∏ j : Fin (k+1), z j.succ) - (D : ℂ)^(k+1)) +
            (z 0 - (D : ℂ)) * (D : ℂ)^(k+1)‖ := by rw [Fin.prod_univ_succ, he]
        _ ≤ ‖z 0‖ * ‖(∏ j : Fin (k+1), z j.succ) - (D : ℂ)^(k+1)‖ +
            ‖z 0 - (D : ℂ)‖ * D^(k+1) := by
          simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hD] using norm_add_le
              (z 0 * ((∏ j : Fin (k+1), z j.succ) - (D : ℂ)^(k+1)))
              ((z 0 - (D : ℂ)) * (D : ℂ)^(k+1))
        _ ≤ D * (D^k * ∑ j : Fin (k+1), ‖z j.succ - (D : ℂ)‖) +
            ‖z 0 - (D : ℂ)‖ * D^(k+1) := by
          gcongr
          · exact hz 0
          · simpa only [Nat.add_sub_cancel] using hi
        _ = _ := by
          simp only [Fin.sum_univ_succ, Nat.add_sub_cancel, pow_succ]
          ring

variable {d G : Type*} [Fintype d] [DecidableEq d] [Group G]

theorem real_character_difference (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    ‖realPartCharacter G (unitaryCharacter ρ) g - (Fintype.card d : ℂ)‖ = defect ρ g := by
  change ‖((unitaryCharacter ρ g).re : ℂ) - (Fintype.card d : ℂ)‖ = _
  rw [show (Fintype.card d : ℂ) = ((Fintype.card d : ℝ) : ℂ) by simp,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos (by have h := defect_nonneg ρ g; dsimp [defect] at h; linarith)]
  dsimp [defect]
  ring

theorem real_character_bound (ρ : G →* Matrix.unitaryGroup d ℂ) (g : G) :
    ‖realPartCharacter G (unitaryCharacter ρ) g‖ ≤ (Fintype.card d : ℝ) := by
  change ‖((unitaryCharacter ρ g).re : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (unitary_trace_bound (ρ g))

def plaquetteDefect (N : ℕ) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (p : PlaquetteIndex N) (U : Configuration (Vertex N) G) : ℝ :=
  defect ρ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G U) (loops N p))

theorem word_difference (N : ℕ) [NeZero N] (ρ : G →* Matrix.unitaryGroup d ℂ)
    (m : ℕ) (q : Fin m → PlaquetteIndex N) (U : Configuration (Vertex N) G) :
    ‖WilsonSmearedObservable.word G N (realPartCharacter G (unitaryCharacter ρ)) m q U -
      (Fintype.card d : ℂ)^m‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ∑ j, plaquetteDefect N ρ (q j) U := by
  have h := norm_prod_sub_pow (Fintype.card d : ℝ) (Nat.cast_nonneg _) m
    (fun j => loopObservable (Vertex N) G (realPartCharacter G (unitaryCharacter ρ)) (loops N (q j)) U)
    (fun j => real_character_bound ρ _)
  simpa only [WilsonSmearedObservable.word, loopObservable, wilson,
    real_character_difference, plaquetteDefect, Complex.ofReal_natCast] using h

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem law_real_character (N : ℕ) [NeZero N]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (beta offset : ℝ) :
    wilsonLaw N G (realPartCharacter G (unitaryCharacter ρ)) beta offset =
      wilsonLaw N G (unitaryCharacter ρ) beta offset := rfl

/-- Actual Wilson moment error, including repeated and overlapping plaquettes. -/
theorem coefficient_difference (N : ℕ) [NeZero N]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta offset eps : ℝ)
    (heps : ∀ p, (∫ U, plaquetteDefect N ρ p U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta offset) ≤ eps)
    (m : ℕ) (q : Fin m → PlaquetteIndex N) :
    ‖WilsonCellHierarchy.coefficient G N (realPartCharacter G (unitaryCharacter ρ))
      beta offset m q - (Fintype.card d : ℂ)^m‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ((m : ℝ) * eps) := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta offset
  letI := wilsonLaw_probability N G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) beta offset
  have hw : Integrable
      (WilsonSmearedObservable.word G N (realPartCharacter G (unitaryCharacter ρ)) m q) μ :=
    (WilsonSmearedObservable.word_continuous G N _
      (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)) m q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (p : PlaquetteIndex N) : Integrable (plaquetteDefect N ρ p) μ :=
    (WilsonAverageDefect.plaquette_continuous N G ρ hρ p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := integrable_finset_sum Finset.univ (fun j _ => hp (q j))
  have hb := norm_integral_le_of_norm_le
    (hs.const_mul ((Fintype.card d : ℝ)^(m-1)))
    (Eventually.of_forall (word_difference N ρ m q))
  have he : WilsonCellHierarchy.coefficient G N
      (realPartCharacter G (unitaryCharacter ρ)) beta offset m q -
      (Fintype.card d : ℂ)^m =
      ∫ U, WilsonSmearedObservable.word G N
        (realPartCharacter G (unitaryCharacter ρ)) m q U - (Fintype.card d : ℂ)^m ∂μ := by
    rw [integral_sub hw (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  rw [he]
  refine hb.trans ?_
  rw [integral_const_mul, integral_finset_sum _ (fun j _ => hp (q j))]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ ∑ _ : Fin m, eps := Finset.sum_le_sum (fun j _ => heps (q j))
    _ = (m : ℝ) * eps := by simp

/-- The actual unitary real-character hierarchy, with its dimension bound. -/
def unitaryHierarchy (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (beta : ℝ) : Hierarchy :=
  realHierarchy G N a plane (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ)
    (Fintype.card d) (fun g => unitary_trace_bound (ρ g)) beta (Fintype.card d)

/-- A fixed Schwartz smearing cannot amplify a uniformly small plaquette defect. -/
theorem hierarchy_difference (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta eps : ℝ)
    (heps : ∀ p, (∫ U, plaquetteDefect N ρ p U
      ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) ≤ eps)
    (m : ℕ) (f : CorrelationTest m) :
    ‖(unitaryHierarchy N a plane ρ hρ beta).correlation m f -
      (Fintype.card d : ℂ)^m * ∫ x, f x‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ((m : ℝ) * eps) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  let K := WilsonCellHierarchy.kernel G N a plane
    (realPartCharacter G (unitaryCharacter ρ)) beta (Fintype.card d) m
  have hK : Integrable (fun x => K x * f x) volume :=
    BoundedKernelDistribution.kernel_integrable volume K
      (WilsonCellHierarchy.kernel_measurable G N a plane _ beta _ m)
      ((Fintype.card d : ℝ≥0)^m)
      (by
        intro x
        exact WilsonCellHierarchy.kernel_bound G N a plane _
          (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)) (Fintype.card d)
          (realPart_bound G _ (Fintype.card d) (fun g => unitary_trace_bound (ρ g))) beta _ m x) f
  have he : (unitaryHierarchy N a plane ρ hρ beta).correlation m f -
      (Fintype.card d : ℂ)^m * ∫ x, f x =
      ∫ x, (K x - (Fintype.card d : ℂ)^m) * f x := by
    simp_rw [sub_mul]
    rw [integral_sub hK (f.integrable.const_mul _), integral_const_mul]
    rfl
  rw [he, BoundedKernelDistribution.l1Seminorm_apply, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (f.integrable.norm.const_mul _)
  exact Eventually.of_forall (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (coefficient_difference N ρ hρ beta _ eps heps m
        (PeriodicCellSampling.sampleConfiguration m N a plane x)) (norm_nonneg _))

/-- The preceding estimate uses the actual translation-invariant Wilson measure. -/
theorem hierarchy_difference_average (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℝ) (m : ℕ) (f : CorrelationTest m) :
    ‖(unitaryHierarchy N a plane ρ hρ beta).correlation m f -
      (Fintype.card d : ℂ)^m * ∫ x, f x‖ ≤
      (Fintype.card d : ℝ)^(m-1) * ((m : ℝ) *
        (6 * ∫ U, WilsonAverageDefect.averageDefect N G ρ U
          ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d))) *
        BoundedKernelDistribution.l1Seminorm volume f :=
  hierarchy_difference N a plane ρ hρ beta _
    (fun p => WilsonAverageDefect.mean_plaquette_le_six_average N G ρ hρ beta _ p) m f

/-- Actual concentration forces every bare fixed-Schwartz correlation to the
constant dimension field, uniformly over arbitrary changing lattice periods and
spacings. This makes no claim about centered and rescaled continuum fields. -/
theorem hierarchy_tendsto_constant (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop)
    (m : ℕ) (f : CorrelationTest m) :
    Tendsto (fun k => (unitaryHierarchy (period k) (a k) plane ρ hρ (beta k)).correlation m f)
      atTop (𝓝 ((Fintype.card d : ℂ)^m * ∫ x, f x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _)
    (fun k => hierarchy_difference_average (period k) (a k) plane ρ hρ (beta k) m f)
  have h := WilsonWeakCouplingDefect.average_expectation_tendsto_zero G ρ hρ period beta hbeta
  convert (((h.const_mul 6).const_mul (m : ℝ)).const_mul
    ((Fintype.card d : ℝ)^(m-1))).mul_const
      (BoundedKernelDistribution.l1Seminorm volume f) using 1 <;> simp

/-- Any actual weak limit on the growing-coefficient trajectory is this same
constant hierarchy; no separate existence or field-identification premise occurs. -/
theorem weak_limit_eq_constant (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (a : ℕ → ℝ) (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop)
    (W : Hierarchy)
    (hW : WeakConvergence (fun k => unitaryHierarchy (period k) (a k) plane ρ hρ (beta k)) W)
    (m : ℕ) (f : CorrelationTest m) :
    W.correlation m f = (Fintype.card d : ℂ)^m * ∫ x, f x :=
  tendsto_nhds_unique (hW m f)
    (hierarchy_tendsto_constant period a plane ρ hρ beta hbeta m f)

end
end UnifiedTheory.Clay.YangMills.BareDefectHierarchy
