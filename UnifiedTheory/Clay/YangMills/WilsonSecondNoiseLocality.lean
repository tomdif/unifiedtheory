/- Exact locality of the second removed Wilson covariance under the true induced
law. The second selected block is star-separated, so its actual conditional
measure is a product. This imposes no locality on the final retained covariance. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteResponseSupport
import UnifiedTheory.Clay.YangMills.WilsonResponseStencilLocality
import UnifiedTheory.Clay.YangMills.WilsonSuccessiveNoiseKernel
import UnifiedTheory.Clay.YangMills.CoordinateSupport
import UnifiedTheory.Clay.YangMills.WilsonInducedProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSecondNoiseLocality
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonSingleLinkStaples WilsonBlockNoiseKernel WilsonSuccessiveNoiseKernel
open WilsonIndependentBlocks WilsonInducedSupport WilsonPlaquetteResponseSupport
open WilsonInducedProduct LocalFields PeriodicCellSampling

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- Only selected second-stage coordinates can vary within a second fiber. -/
def fiberSupport (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n) : Finset T :=
  Finset.univ.filter (fun e => e.val.val ∈ responseSupport n S p)

omit [NeZero n] in
theorem mem_fiberSupport (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n) (e : T) :
    e ∈ fiberSupport n S T p ↔ e.val.val ∈ responseSupport n S p := by
  simp only [fiberSupport, Finset.mem_filter, Finset.mem_univ, true_and]

omit [NeZero n] in
theorem fiberSupport_disjoint (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p q : PlaquetteIndex n)
    (hpq : Disjoint (responseSupport n S p) (responseSupport n S q)) :
    Disjoint (fiberSupport n S T p) (fiberSupport n S T q) := by
  apply Finset.disjoint_left.mpr
  intro e hep heq
  exact Finset.disjoint_left.mp hpq (mem_fiberSupport n S T p e |>.mp hep)
    (mem_fiberSupport n S T q e |>.mp heq)

/-- The literal nested first response is the same normalized response on retained coordinates. -/
theorem first_eq_outside_response (β : ℝ) (S : Finset (Edge (Vertex n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n)
    (z : Outside (G := Q) T × Inside (G := Q) T) :
    first n β S T (basis n p) z =
      GibbsMarginalTower.response (insideMeasure S (compactHaar Q))
        (splitAction n Q character β 2 S)
        (fun w => WilsonIndependentBlocks.plaquetteTerm n Q character 2 (assemble S w) p)
        (assemble T z) := by
  have hs : source n (basis n p) =
      (fun U => WilsonIndependentBlocks.plaquetteTerm n Q character 2 U p) :=
    funext (source_basis n p)
  rw [first, hs, firstResponse_eq_response]
  unfold WilsonPlaquetteResponseSupport.response
  congr 1
  funext e
  exact assemble_outside S _ e.val e.property

/-- The actual first plaquette response uses only the projected geometric support in each fiber. -/
theorem first_fiber_dependsOn (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (p : PlaquetteIndex n)
    (r : Outside (G := Q) T) :
    DependsOn (fun V : Inside (G := Q) T => first n β S T (basis n p) (r, V))
      (fiberSupport n S T p : Set T) := by
  intro V W hVW
  change first n β S T (basis n p) (r, V) = first n β S T (basis n p) (r, W)
  rw [first_eq_outside_response, first_eq_outside_response]
  apply outside_response_dependsOn n Q character character_continuous β 2 S hS p
  intro e he
  by_cases heT : e ∈ T
  · rw [assemble_inside T _ e heT, assemble_inside T _ e heT]
    exact hVW ⟨e, heT⟩ (mem_fiberSupport n S T p ⟨e, heT⟩ |>.mpr
      (mem_outsideSupport n S p e |>.mp he))
  · rw [assemble_outside T _ e heT, assemble_outside T _ e heT]


/-- Disjoint projected response supports have zero conditional covariance under
 the actual second-fiber law, whose factorization is proved from the induced action. -/
theorem conditional_zero_of_disjoint (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (p q : PlaquetteIndex n)
    (hpq : Disjoint (fiberSupport n S T p) (fiberSupport n S T q))
    (r : Outside (G := Q) T) :
    GibbsCrossCovariance.conditionalCovariance (insideMeasure T (compactHaar Q))
      (retainedAction n Q character β 2 S T)
      (first n β S T (basis n p)) (first n β S T (basis n q)) r = 0 := by
  let U := assemble T (r, fun _ => (1 : Q))
  let A := WilsonRetainedLawComparison.evolvedAction n Q character β 2 S
  let ν : T → Measure Q := fun i => CompactGibbsContinuity.law (compactHaar Q)
    (fun v => A (Function.update U i.val v) - A U)
  have hA : Continuous A := WilsonRetainedLawComparison.evolvedAction_continuous
    n Q character character_continuous β 2 S
  have hν (i : T) : IsProbabilityMeasure (ν i) := by
    apply CompactGibbsContinuity.law_probability
    exact (hA.comp (by fun_prop)).sub continuous_const
  letI : ∀ i, IsProbabilityMeasure (ν i) := hν
  have hprod := second_fiber_product_law n Q character character_continuous β 2 S hS T hT r
  change CompactGibbsContinuity.law (insideMeasure T (compactHaar Q))
    (fun V => retainedAction n Q character β 2 S T (r, V)) = Measure.pi ν at hprod
  have hret : Continuous (retainedAction n Q character β 2 S T) :=
    GibbsMarginalTower.effectiveAction_continuous _ _
      (splitActionTwo_continuous n Q character character_continuous β 2 S T)
  unfold GibbsCrossCovariance.conditionalCovariance
  simp only [GibbsMarginalTower.response_eq_expectation _ _ _ hret r]
  rw [hprod]
  exact sub_eq_zero.mpr (CoordinateSupport.integral_mul_of_disjoint ν
    (fiberSupport n S T p) (fiberSupport n S T q) hpq
    (fun V => first n β S T (basis n p) (r, V))
    (fun V => first n β S T (basis n q) (r, V))
    ((first_continuous n β S T (basis n p)).comp (continuous_const.prodMk continuous_id))
    ((first_continuous n β S T (basis n q)).comp (continuous_const.prodMk continuous_id))
    (first_fiber_dependsOn n β S hS T p r) (first_fiber_dependsOn n β S hS T q r))

/-- The actual second removed covariance vanishes for disjoint first-response neighborhoods. -/
theorem zero_of_disjoint (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (p q : PlaquetteIndex n)
    (hpq : Disjoint (responseSupport n S p) (responseSupport n S q)) :
    coefficient n β S T p q = 0 :=
  coefficient_zero_of_conditional n β S T p q
    (conditional_zero_of_disjoint n β S hS T hT p q (fiberSupport_disjoint n S T p q hpq))

/-- Literal sampled second-stage coefficients have physical range ten lattice spacings,
with periodic wrapping excluded explicitly. No retained-covariance locality is asserted. -/
theorem physical_zero_far (β : ℝ) (S : Finset (Edge (Vertex n)))
    (hS : Independent n (S.image (edgeCoord n)))
    (T : Finset {e : Edge (Vertex n) // e ∉ S}) (hT : NextSeparated n S T)
    (a R : ℝ) (ha : 0 < a) (hperiod : 2 * R + 5 * a < (n : ℝ) * a)
    (plane plane' : Plane) (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hfar : 10 * a < ‖x - y‖) :
    coefficient n β S T (sample n a plane x) (sample n a plane' y) = 0 :=
  zero_of_disjoint n β S hS T hT _ _
    (WilsonResponseStencilLocality.responseSupport_disjoint_far
      n S a R ha hperiod plane plane' x y hx hy hfar)

end
end UnifiedTheory.Clay.YangMills.WilsonSecondNoiseLocality
