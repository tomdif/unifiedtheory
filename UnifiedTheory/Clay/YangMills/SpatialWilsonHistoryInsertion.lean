/- Restoring an actual spatial plaquette column in a finite temporal Wilson
history costs one exact Haar mass per slice. The kinetic interactions and all
other spatial plaquettes are retained. Both half-history sources and the
original coarse Haar partition functions are treated. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryKernel
import UnifiedTheory.Clay.YangMills.SU2FiniteInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryInsertion
noncomputable section
open MeasureTheory WilsonTimeSlab SpatialHalfEdgeSplit SpatialPlaquetteCutGeometry
open SpatialPlaquetteHalfPaths SpatialWilsonPlaquetteKernels SpatialWilsonInsertion
open SpatialWilsonHistoryKernel WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion WilsonReflectionForm SU2FiniteInsertion

variable (n : ℕ) [NeZero n] (T : Type*) [Fintype T]
  {E : Type*} [Fintype E]

omit [Fintype T] in
local instance halfHistoryBorel [Countable T] : BorelSpace (HalfHistory n T) := Pi.borelSpace
omit [Fintype T] in
local instance historyBorel [Countable T] : BorelSpace (History n T) := Pi.borelSpace

def path (q : Plaquette n) (t : T) (a : HalfHistory n T) : Q :=
  halfPath Q n q.1 q.2.val.2 (a t)

omit [Fintype T] in
theorem path_continuous (q : Plaquette n) (t : T) : Continuous (path n T q t) :=
  (halfPath_continuous Q n q.1 q.2.val.2).comp (continuous_apply t)

theorem density_restore (q : Plaquette n) (s : ℝ) (β : E → ℝ) (l r : E → T)
    (u : History n T) :
    density n T (fun _ _ => s) β l r u =
      density n T (fun _ => omitted n q s) β l r u *
        ∏ t, Real.exp (-s * defect n q (u t)) := by
  unfold density
  simp_rw [weight_restore n q s]
  rw [Finset.prod_mul_distrib]
  ring

theorem density_assemble_restore (q : Plaquette n) (hq : Crossing n q) (s : ℝ)
    (β : E → ℝ) (l r : E → T) (a b : HalfHistory n T) :
    density n T (fun _ _ => s) β l r (assembleHistory n T (a,b)) =
      density n T (fun _ => omitted n q s) β l r (assembleHistory n T (a,b)) *
        ∏ t, SU2CrossingHaarFloor.kernel s (path n T q t a) (path n T q t b) := by
  rw [density_restore]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  exact crossing_factor n q hq s (a t) (b t)

def cutKernel (q : Plaquette n) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) : PositiveKernel (HalfHistory n T) :=
  historyKernel n T (fun _ => omitted n q s) (fun _ => omitted_nonneg n q s hs) β hβ l r

theorem cutKernel_continuous (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    Continuous (cutKernel n T q s hs β hβ l r).value :=
  historyKernel_continuous n T _ _ (fun _ => omitted_reflection n q hq s) β hβ l r

theorem augmented_value (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) (a b : HalfHistory n T) :
    (finiteAugment s hs (cutKernel n T q s hs β hβ l r) (path n T q)).value (a,b) =
      (density n T (fun _ _ => s) β l r (assembleHistory n T (a,b)) : ℂ) := by
  rw [finiteAugment_value]
  change (historyKernel n T (fun _ => omitted n q s) _ β hβ l r).value (a,b) * _ = _
  rw [historyKernel_value n T _ _ (fun _ => omitted_reflection n q hq s),
    ← Complex.ofReal_mul, ← density_assemble_restore n T q hq s β l r a b]

variable (μ : Measure (HalfHistory n T)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem cut_form (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) (f : HalfHistory n T → ℂ) :
    form μ (cutKernel n T q s hs β hβ l r) f = reflectionForm μ
      (fun a b => density n T (fun _ => omitted n q s) β l r (assembleHistory n T (a,b))) f := by
  unfold form reflectionForm cutKernel
  apply integral_congr_ae
  filter_upwards [] with z
  rw [historyKernel_value n T _ _ (fun _ => omitted_reflection n q hq s)]

omit [IsFiniteMeasure μ] in
theorem augmented_form (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) (f : HalfHistory n T → ℂ) :
    form μ (finiteAugment s hs (cutKernel n T q s hs β hβ l r) (path n T q)) f =
      reflectionForm μ
        (fun a b => density n T (fun _ _ => s) β l r (assembleHistory n T (a,b))) f := by
  unfold form reflectionForm
  apply integral_congr_ae
  filter_upwards [] with z
  rw [augmented_value n T q hq]

/-- The exact mass cost is one factor per slice, with arbitrary other
nonnegative temporal couplings and no dependence on spatial volume. -/
theorem column_floor (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) (hf : Continuous f) :
    (SU2GaussianMass.mass s)^(Fintype.card T) *
      (reflectionForm μ (fun a b => density n T (fun _ => omitted n q s) β l r
        (assembleHistory n T (a,b))) f).re ≤
      (reflectionForm μ (fun a b => density n T (fun _ _ => s) β l r
        (assembleHistory n T (a,b))) f).re := by
  have hi := finite_floor μ s hs (cutKernel n T q s hs β hβ l r)
    (cutKernel_continuous n T q hq s hs β hβ l r) (path n T q)
    (path_continuous n T q) f hf
  rwa [cut_form n T μ q hq, augmented_form n T μ q hq] at hi

theorem column_removal (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 3 / 4 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) (hf : Continuous f) :
    (reflectionForm μ (fun a b => density n T (fun _ => omitted n q s) β l r
        (assembleHistory n T (a,b))) f).re ≤
      (SU2GaussianMass.cap s)^(Fintype.card T) *
        (reflectionForm μ (fun a b => density n T (fun _ _ => s) β l r
          (assembleHistory n T (a,b))) f).re := by
  have hi := finite_removal μ s hs (cutKernel n T q s (by linarith) β hβ l r)
    (cutKernel_continuous n T q hq s (by linarith) β hβ l r) (path n T q)
    (path_continuous n T q) f hf
  rwa [cut_form n T μ q hq, augmented_form n T μ q hq] at hi

omit [IsFiniteMeasure μ] in
theorem constant_source_form (γ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T) :
    (reflectionForm (halfMeasure n T)
      (fun a b => density n T γ β l r (assembleHistory n T (a,b))) (fun _ => 1)).re =
      ∫ u, density n T γ β l r u ∂measure n T := by
  unfold reflectionForm
  simp only [star_one, one_mul, mul_one, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_assembleHistory n T _ (density_continuous n T γ β l r)

omit [IsFiniteMeasure μ] in
theorem partition_floor (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    (SU2GaussianMass.mass s)^(Fintype.card T) *
      (∫ u, density n T (fun _ => omitted n q s) β l r u ∂measure n T) ≤
      ∫ u, density n T (fun _ _ => s) β l r u ∂measure n T := by
  have hi := column_floor n T (halfMeasure n T) q hq s hs β hβ l r
    (fun _ => 1) continuous_const
  rwa [constant_source_form, constant_source_form] at hi

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryInsertion
