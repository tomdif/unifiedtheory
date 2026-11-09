/- Simultaneous insertion of every column in an aligned spatial patch into
an actual finite temporal history. All other spatial and kinetic factors are
retained, with one Haar mass for each marked plaquette at each time. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights
import UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory
noncomputable section
open MeasureTheory WilsonTimeSlab SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels
open SpatialWilsonPatchWeights SpatialWilsonHistoryKernel WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion WilsonReflectionForm SU2FiniteInsertion

variable (n : ℕ) [NeZero n] (T : Type*) [Fintype T] {E : Type*} [Fintype E]

omit [Fintype T] in
local instance halfHistoryBorel [Countable T] : BorelSpace (HalfHistory n T) := Pi.borelSpace

def path (S : Finset (Plaquette n)) (p : T × S) (a : HalfHistory n T) : Q :=
  SpatialWilsonHistoryInsertion.path n T p.2.val p.1 a

omit [Fintype T] in
theorem path_continuous (S : Finset (Plaquette n)) (p : T × S) :
    Continuous (path n T S p) := SpatialWilsonHistoryInsertion.path_continuous n T p.2.val p.1

theorem density_restore (S : Finset (Plaquette n)) (s : ℝ) (β : E → ℝ) (l r : E → T)
    (u : History n T) :
    density n T (fun _ _ => s) β l r u = density n T (fun _ => omitted n S s) β l r u *
      ∏ p : T × S, Real.exp (-s * defect n p.2.val (u p.1)) := by
  unfold density
  simp_rw [weight_restore_product n S s]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]
  ring

theorem density_assemble_restore (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (β : E → ℝ) (l r : E → T) (a b : HalfHistory n T) :
    density n T (fun _ _ => s) β l r (assembleHistory n T (a,b)) =
      density n T (fun _ => omitted n S s) β l r (assembleHistory n T (a,b)) *
        ∏ p : T × S, SU2CrossingHaarFloor.kernel s (path n T S p a) (path n T S p b) := by
  rw [density_restore]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact crossing_factor n p.2.val (hS _ p.2.property) s (a p.1) (b p.1)

def cutKernel (S : Finset (Plaquette n)) (s : ℝ) (hs : 0 ≤ s)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) : PositiveKernel (HalfHistory n T) :=
  historyKernel n T (fun _ => omitted n S s) (fun _ => omitted_nonneg n S s hs) β hβ l r

theorem cutKernel_continuous (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    Continuous (cutKernel n T S s hs β hβ l r).value :=
  historyKernel_continuous n T _ _ (fun _ => omitted_reflection n S hS s) β hβ l r

theorem augmented_value (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (a b : HalfHistory n T) :
    (finiteAugment s hs (cutKernel n T S s hs β hβ l r) (path n T S)).value (a,b) =
      (density n T (fun _ _ => s) β l r (assembleHistory n T (a,b)) : ℂ) := by
  rw [finiteAugment_value]
  change (historyKernel n T (fun _ => omitted n S s) _ β hβ l r).value (a,b) * _ = _
  rw [historyKernel_value n T _ _ (fun _ => omitted_reflection n S hS s),
    ← Complex.ofReal_mul, ← density_assemble_restore n T S hS s β l r a b]

variable (μ : Measure (HalfHistory n T)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem cut_form (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) :
    form μ (cutKernel n T S s hs β hβ l r) f = reflectionForm μ
      (fun a b => density n T (fun _ => omitted n S s) β l r (assembleHistory n T (a,b))) f := by
  unfold form reflectionForm cutKernel
  apply integral_congr_ae
  filter_upwards [] with z
  rw [historyKernel_value n T _ _ (fun _ => omitted_reflection n S hS s)]

omit [IsFiniteMeasure μ] in
theorem augmented_form (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) :
    form μ (finiteAugment s hs (cutKernel n T S s hs β hβ l r) (path n T S)) f =
      reflectionForm μ
        (fun a b => density n T (fun _ _ => s) β l r (assembleHistory n T (a,b))) f := by
  unfold form reflectionForm
  apply integral_congr_ae
  filter_upwards [] with z
  rw [augmented_value n T S hS]

/-- The whole aligned patch is restored simultaneously against its proved
reflection-positive background, for arbitrary complex half-history sources. -/
theorem patch_floor (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) (hf : Continuous f) :
    (SU2GaussianMass.mass s) ^ (Fintype.card T * S.card) *
      (reflectionForm μ (fun a b => density n T (fun _ => omitted n S s) β l r
        (assembleHistory n T (a,b))) f).re ≤
      (reflectionForm μ (fun a b => density n T (fun _ _ => s) β l r
        (assembleHistory n T (a,b))) f).re := by
  have hi := finite_floor μ s hs (cutKernel n T S s hs β hβ l r)
    (cutKernel_continuous n T S hS s hs β hβ l r) (path n T S)
    (path_continuous n T S) f hf
  simpa only [cut_form n T μ S hS, augmented_form n T μ S hS,
    Fintype.card_prod, Fintype.card_coe] using hi

theorem patch_removal (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 3 / 4 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) (hf : Continuous f) :
    (reflectionForm μ (fun a b => density n T (fun _ => omitted n S s) β l r
      (assembleHistory n T (a,b))) f).re ≤
      (SU2GaussianMass.cap s) ^ (Fintype.card T * S.card) *
        (reflectionForm μ (fun a b => density n T (fun _ _ => s) β l r
          (assembleHistory n T (a,b))) f).re := by
  have hi := finite_removal μ s hs (cutKernel n T S s (by linarith) β hβ l r)
    (cutKernel_continuous n T S hS s (by linarith) β hβ l r) (path n T S)
    (path_continuous n T S) f hf
  simpa only [cut_form n T μ S hS, augmented_form n T μ S hS,
    Fintype.card_prod, Fintype.card_coe] using hi

omit [IsFiniteMeasure μ] in
theorem partition_floor (S : Finset (Plaquette n)) (hS : Aligned n S)
    (s : ℝ) (hs : 0 ≤ s) (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    (SU2GaussianMass.mass s) ^ (Fintype.card T * S.card) *
      (∫ u, density n T (fun _ => omitted n S s) β l r u ∂measure n T) ≤
      ∫ u, density n T (fun _ _ => s) β l r u ∂measure n T := by
  have hi := patch_floor n T (halfMeasure n T) S hS s hs β hβ l r (fun _ => 1) continuous_const
  rwa [SpatialWilsonHistoryInsertion.constant_source_form,
    SpatialWilsonHistoryInsertion.constant_source_form] at hi

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory
