/- Actual finite Wilson temporal networks as positive kernels across the
same spatial midpoint plane. This retains all temporal interactions and
permits independent reflection-invariant spatial couplings at every slice. -/
import UnifiedTheory.Clay.YangMills.SpatialTemporalReflectionKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryKernel
noncomputable section
open MeasureTheory WilsonTimeSlab SpatialHalfEdgeSplit SpatialPlaquetteCutGeometry
open WilsonSingleLinkStaples PositiveKernelForm PositiveKernelInsertion
open SpatialTemporalLinkKernels SpatialTemporalReflectionKernel

variable (n : ℕ) [NeZero n] (T : Type*) [Fintype T]

abbrev HalfHistory := T → Half n Q
abbrev History := T → SpatialLinks (2 * n) Q

omit [Fintype T] in
local instance halfHistoryBorel [Countable T] : BorelSpace (HalfHistory n T) := Pi.borelSpace
omit [Fintype T] in
local instance historyBorel [Countable T] : BorelSpace (History n T) := Pi.borelSpace

def assembleHistory (z : HalfHistory n T × HalfHistory n T) : History n T :=
  fun t => assemble n Q (z.1 t,z.2 t)

def halfMeasure : Measure (HalfHistory n T) := Measure.pi (fun _ => halfHaar n Q)
def measure : Measure (History n T) := Measure.pi (fun _ => WilsonSlabGauge.spatialHaar)

instance halfMeasure_probability : IsProbabilityMeasure (halfMeasure n T) := by
  unfold halfMeasure
  infer_instance

instance measure_probability : IsProbabilityMeasure (measure n T) := by
  unfold measure
  infer_instance

theorem assembleHistory_preserving : MeasurePreserving (assembleHistory n T)
    ((halfMeasure n T).prod (halfMeasure n T)) (measure n T) := by
  have hr := (measurePreserving_arrowProdEquivProdArrow (Half n Q) (Half n Q) T
    (fun _ => halfHaar n Q) (fun _ => halfHaar n Q)).symm
  have hp := measurePreserving_pi
    (fun _ : T => (halfHaar n Q).prod (halfHaar n Q))
    (fun _ : T => WilsonSlabGauge.spatialHaar)
    (fun _ => assemble_preserving n Q)
  exact hp.comp hr

omit [Fintype T] in
theorem assembleHistory_continuous : Continuous (assembleHistory n T) := by
  apply continuous_pi
  intro t
  exact (assemble_continuous n Q).comp
    (((continuous_apply t).comp continuous_fst).prodMk
      ((continuous_apply t).comp continuous_snd))

theorem integral_assembleHistory (F : History n T → ℝ) (hF : Continuous F) :
    (∫ z, F (assembleHistory n T z) ∂(halfMeasure n T).prod (halfMeasure n T)) =
      ∫ u, F u ∂measure n T := by
  have hp := assembleHistory_preserving n T
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm

variable {E : Type*} [Fintype E]

def density (γ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T) (u : History n T) : ℝ :=
  (∏ t, SpatialWilsonReflectionKernel.weight n (γ t) (u t)) *
    ∏ e, kineticWeight character (β e) 2 (u (l e)) (u (r e))

def historyKernel (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) : PositiveKernel (HalfHistory n T) :=
  product (finiteProduct (fun t =>
    pullback (SpatialWilsonReflectionKernel.positiveKernel n (γ t) (hγ t)) (fun a => a t)))
    (finiteProduct (fun e => pullback (kineticKernel n (β e) (hβ e)) (fun a => (a (l e),a (r e)))))

theorem historyKernel_value (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) (a b : HalfHistory n T) :
    (historyKernel n T γ hγ β hβ l r).value (a,b) =
      (density n T γ β l r (assembleHistory n T (a,b)) : ℂ) := by
  simp only [historyKernel, product_value, finiteProduct_value, pullback,
    SpatialWilsonReflectionKernel.positiveKernel_value n _ _ (hr _), kineticKernel_value,
    ← Complex.ofReal_prod, ← Complex.ofReal_mul]
  rfl

theorem density_continuous (γ : T → Plaquette n → ℝ) (β : E → ℝ) (l r : E → T) :
    Continuous (density n T γ β l r) := by
  unfold density
  apply Continuous.mul
  · exact continuous_finset_prod Finset.univ (fun t _ =>
      (SpatialWilsonReflectionKernel.weight_continuous n (γ t)).comp (continuous_apply t))
  · apply continuous_finset_prod Finset.univ
    intro e _
    have hk : Continuous (fun uv : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q =>
        kineticWeight character (β e) 2 uv.1 uv.2) := by
      unfold kineticWeight kineticAction
      apply Real.continuous_exp.comp
      apply continuous_const.mul
      exact continuous_finset_sum Finset.univ (fun i _ => defect_continuous n i)
    exact hk.comp (f := fun u : History n T => (u (l e),u (r e)))
      ((continuous_apply (l e)).prodMk (continuous_apply (r e)))

theorem historyKernel_continuous (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T) :
    Continuous (historyKernel n T γ hγ β hβ l r).value := by
  have hc := Complex.continuous_ofReal.comp
    ((density_continuous n T γ β l r).comp (assembleHistory_continuous n T))
  exact hc.congr (fun z => (historyKernel_value n T γ hγ hr β hβ l r z.1 z.2).symm)

/-- A finite actual Wilson history is reflection positive for every
continuous complex half-history source, including omitted-plaquette histories. -/
theorem reflection_nonneg (γ : T → Plaquette n → ℝ) (hγ : ∀ t p, 0 ≤ γ t p)
    (hr : ∀ t p, γ t (reflectPlaquette n p) = γ t p)
    (β : E → ℝ) (hβ : ∀ e, 0 ≤ β e) (l r : E → T)
    (f : HalfHistory n T → ℂ) (hf : Continuous f) :
    0 ≤ (WilsonReflectionForm.reflectionForm (halfMeasure n T)
      (fun a b => density n T γ β l r (assembleHistory n T (a,b))) f).re := by
  have hn := (form_nonneg (halfMeasure n T) (historyKernel n T γ hγ β hβ l r)
    (historyKernel_continuous n T γ hγ hr β hβ l r) f hf).1
  convert hn using 1
  unfold WilsonReflectionForm.reflectionForm form
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [historyKernel_value n T γ hγ hr β hβ l r]

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryKernel
