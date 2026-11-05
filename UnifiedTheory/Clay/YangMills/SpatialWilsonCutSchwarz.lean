/- Actual finite-history reflection Cauchy--Schwarz and the first chessboard
step for arbitrary interior plaquette perturbations. All kinetic terms and
the original reflection-positive background are retained. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelSchwarz
import UnifiedTheory.Clay.YangMills.SpatialWilsonHalfCopies

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonCutSchwarz
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSingleLinkStaples SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels SpatialWilsonReflectionKernel
open SpatialWilsonHistoryKernel SpatialWilsonCutProfiles PositiveKernelInsertion

variable (n : ℕ) [NeZero n] (T : Type*) [Fintype T]

omit [Fintype T] in
local instance halfHistoryBorel [Countable T] : BorelSpace (HalfHistory n T) := Pi.borelSpace

variable {E : Type*} [Fintype E]

def pairing (γ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T)
    (f g : HalfHistory n T → ℝ) : ℝ :=
  ∫ z, f z.1 * density n T γ β l r (assembleHistory n T z) * g z.2
    ∂(halfMeasure n T).prod (halfMeasure n T)

theorem pairing_complex (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f g : HalfHistory n T → ℝ) :
    PositiveKernelSchwarz.mixed (halfMeasure n T) (historyKernel n T γ hγ β hβ l r)
      (fun a => (f a : ℂ)) (fun a => (g a : ℂ)) = (pairing n T γ β l r f g : ℂ) := by
  unfold PositiveKernelSchwarz.mixed pairing
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [historyKernel_value n T γ hγ hr β hβ l r]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]

theorem reflection_schwarz (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f g : HalfHistory n T → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (pairing n T γ β l r f g)^2 ≤
      pairing n T γ β l r f f * pairing n T γ β l r g g := by
  have h := PositiveKernelSchwarz.schwarz (halfMeasure n T)
    (historyKernel n T γ hγ β hβ l r)
    (historyKernel_continuous n T γ hγ hr β hβ l r)
    (fun a => (f a : ℂ)) (fun a => (g a : ℂ))
    (Complex.continuous_ofReal.comp hf) (Complex.continuous_ofReal.comp hg)
  change ‖PositiveKernelSchwarz.mixed (halfMeasure n T)
    (historyKernel n T γ hγ β hβ l r) (fun a => (f a : ℂ)) (fun a => (g a : ℂ))‖^2 ≤
    (PositiveKernelSchwarz.mixed (halfMeasure n T)
      (historyKernel n T γ hγ β hβ l r) (fun a => (f a : ℂ)) (fun a => (f a : ℂ))).re *
    (PositiveKernelSchwarz.mixed (halfMeasure n T)
      (historyKernel n T γ hγ β hβ l r) (fun a => (g a : ℂ)) (fun a => (g a : ℂ))).re at h
  simpa only [pairing_complex n T γ hγ hr β hβ l r, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Complex.ofReal_re] using h

def partition (γ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T) : ℝ :=
  ∫ u, density n T γ β l r u ∂measure n T

def halfSource (δ : T → Plaquette n → ℝ) (a : HalfHistory n T) : ℝ :=
  ∏ t, Real.exp (action n (δ t) (assemble n Q (a t,a t)))

omit [Fintype E] in
theorem halfSource_continuous (δ : T → Plaquette n → ℝ) :
    Continuous (halfSource n T δ) := by
  unfold halfSource action
  apply continuous_finset_prod
  intro t _
  apply Real.continuous_exp.comp
  apply continuous_finset_sum
  intro p _
  exact continuous_const.mul ((defect_continuous n p).comp
    ((assemble_continuous n Q).comp ((continuous_apply t).prodMk (continuous_apply t))))

theorem density_perturb (γ δ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T)
    (u : History n T) :
    density n T (fun t p => γ t p - δ t p) β l r u =
      density n T γ β l r u * ∏ t, Real.exp (action n (δ t) (u t)) := by
  simp only [density, weight_perturb, Finset.prod_mul_distrib]
  ring

theorem partition_factor (γ δ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T)
    (f g : HalfHistory n T → ℝ)
    (hf : ∀ a b, (∏ t, Real.exp (action n (δ t) (assemble n Q (a t, b t)))) = f a * g b) :
    partition n T (fun t p => γ t p - δ t p) β l r = pairing n T γ β l r f g := by
  rw [partition, ← integral_assembleHistory n T _ (density_continuous n T _ β l r)]
  unfold pairing
  apply integral_congr_ae
  filter_upwards [] with z
  rw [density_perturb]
  change density n T γ β l r (assembleHistory n T z) *
    (∏ t, Real.exp (action n (δ t) (assemble n Q (z.1 t,z.2 t)))) = _
  rw [hf]
  ring

theorem partition_split (γ δ : T → Plaquette n → ℝ)
    (hδ : ∀ t p, Crossing n p → δ t p = 0) (β : E → ℝ) (l r : E → T) :
    partition n T (fun t p => γ t p - δ t p) β l r =
      pairing n T γ β l r (halfSource n T (fun t => positivePart n (δ t)))
        (halfSource n T (fun t => negativePart n (δ t))) := by
  apply partition_factor
  intro a b
  simp only [action_split n _ (hδ _) (a _) (b _), Real.exp_add,
    Finset.prod_mul_distrib, halfSource]

theorem partition_positive (γ δ : T → Plaquette n → ℝ)
    (hδ : ∀ t p, Crossing n p → δ t p = 0) (β : E → ℝ) (l r : E → T) :
    partition n T (fun t p => γ t p - doubled n (positivePart n (δ t)) p) β l r =
      pairing n T γ β l r (halfSource n T (fun t => positivePart n (δ t)))
        (halfSource n T (fun t => positivePart n (δ t))) := by
  apply partition_factor
  intro a b
  simp only [positive_doubled_action n _ (hδ _) (a _) (b _), Real.exp_add,
    Finset.prod_mul_distrib, halfSource]

theorem partition_negative (γ δ : T → Plaquette n → ℝ)
    (hδ : ∀ t p, Crossing n p → δ t p = 0) (β : E → ℝ) (l r : E → T) :
    partition n T (fun t p => γ t p - doubled n (negativePart n (δ t)) p) β l r =
      pairing n T γ β l r (halfSource n T (fun t => negativePart n (δ t)))
        (halfSource n T (fun t => negativePart n (δ t))) := by
  apply partition_factor
  intro a b
  simp only [negative_doubled_action n _ (hδ _) (a _) (b _), Real.exp_add,
    Finset.prod_mul_distrib, halfSource]

/-- A genuine partition inequality for an arbitrary noncoplanar interior
perturbation. The geometric iteration and its entropy bound are separate. -/
theorem partition_schwarz (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (δ : T → Plaquette n → ℝ) (hδ : ∀ t p, Crossing n p → δ t p = 0)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    (partition n T (fun t p => γ t p - δ t p) β l r)^2 ≤
      partition n T (fun t p => γ t p - doubled n (positivePart n (δ t)) p) β l r *
      partition n T (fun t p => γ t p - doubled n (negativePart n (δ t)) p) β l r := by
  rw [partition_split n T γ δ hδ, partition_positive n T γ δ hδ,
    partition_negative n T γ δ hδ]
  exact reflection_schwarz n T γ hγ hr β hβ l r _ _
    (halfSource_continuous n T _) (halfSource_continuous n T _)

/-- Every nonnegative inhomogeneous Wilson profile obeys the cut inequality,
including arbitrary deletions on both periodic crossing seams. -/
theorem partition_copies (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    (partition n T γ β l r)^2 ≤
      partition n T (fun t => SpatialWilsonHalfCopies.copyPositive n (γ t)) β l r *
      partition n T (fun t => SpatialWilsonHalfCopies.copyNegative n (γ t)) β l r := by
  have h := partition_schwarz n T (fun t => SpatialWilsonHalfCopies.crossingPart n (γ t))
    (fun t => SpatialWilsonHalfCopies.crossing_nonneg n (γ t) (hγ t))
    (fun t => SpatialWilsonHalfCopies.crossing_invariant n (γ t))
    (fun t p => -SpatialWilsonHalfCopies.interiorPart n (γ t) p)
    (fun t p hp => by simp only [SpatialWilsonHalfCopies.interior_crossing n (γ t) p hp, neg_zero])
    β hβ l r
  simpa only [SpatialWilsonHalfCopies.perturbation_original,
    (SpatialWilsonHalfCopies.perturbation_copies n _ _).1,
    (SpatialWilsonHalfCopies.perturbation_copies n _ _).2] using h

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonCutSchwarz
