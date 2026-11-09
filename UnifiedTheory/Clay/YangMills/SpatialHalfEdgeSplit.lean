/- Independent reflected half-edge coordinates for the actual spatial
slice. The assembly is a Haar-preserving surjection with redundant midpoint
variables, not a gauge-fixing bijection. Swapping halves is exactly the
coarse spatial link reflection, including orientation inversion. -/
import UnifiedTheory.Clay.YangMills.HaarHalfEdges
import UnifiedTheory.Clay.YangMills.SpatialHalfEdgeGeometry
import UnifiedTheory.Clay.YangMills.WilsonSlabGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SpatialHalfEdgeSplit
noncomputable section
open MeasureTheory RegulatedGauge WilsonTimeSlab SpatialHalfEdgeGeometry

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]

abbrev Half := PositiveHalf n → G

def join (z : Half n G × Half n G) (e : HalfEdge (2 * n)) : G :=
  Sum.elim z.1 z.2 (split n e)

omit [Group G] in
theorem join_positive (z : Half n G × Half n G) (e : PositiveHalf n) :
    join n G z e.val = z.1 e := by
  change Sum.elim z.1 z.2 (split n (glue n (Sum.inl e))) = _
  rw [split_glue]
  rfl

omit [Group G] in
theorem join_negative (z : Half n G × Half n G) (e : PositiveHalf n) :
    join n G z (reflectHalf (2 * n) e.val) = z.2 e := by
  change Sum.elim z.1 z.2 (split n (glue n (Sum.inr e))) = _
  rw [split_glue]
  rfl

omit [Group G] in
theorem join_swap (z : Half n G × Half n G) (e : HalfEdge (2 * n)) :
    join n G (z.2,z.1) e = join n G z (reflectHalf (2 * n) e) := by
  obtain ⟨p,rfl⟩ := (piecesEquiv n).surjective e
  cases p with
  | inl p => exact (join_positive n G _ p).trans (join_negative n G z p).symm
  | inr p =>
    change join n G (z.2,z.1) (reflectHalf (2 * n) p.val) =
      join n G z (reflectHalf (2 * n) (reflectHalf (2 * n) p.val))
    rw [join_negative, reflectHalf_involutive, join_positive]

def assemble (z : Half n G × Half n G) : SpatialLinks (2 * n) G :=
  HaarHalfEdges.coarsen G (join n G z)

def reflection (u : SpatialLinks (2 * n) G) (e : Link (2 * n)) : G :=
  if e.2 = 0 then (u (reflectLink (2 * n) e))⁻¹ else u (reflectLink (2 * n) e)

omit [NeZero n] in
theorem coarsen_reflection (U : HalfEdge (2 * n) → G) :
    HaarHalfEdges.coarsen G (fun e => U (reflectHalf (2 * n) e)) =
      reflection n G (HaarHalfEdges.coarsen G U) := by
  funext e
  by_cases he : e.2 = 0 <;>
    simp [HaarHalfEdges.coarsen, reflectHalf, reflection, he]

theorem assemble_reflection (z : Half n G × Half n G) :
    assemble n G (z.2,z.1) = reflection n G (assemble n G z) := by
  have he : join n G (z.2,z.1) = fun e => join n G z (reflectHalf (2 * n) e) :=
    funext (join_swap n G z)
  rw [assemble, he, coarsen_reflection]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [Group G] [IsTopologicalGroup G] in
theorem join_continuous : Continuous (join n G) := by
  apply continuous_pi
  intro e
  change Continuous (fun z : Half n G × Half n G => Sum.elim z.1 z.2 (split n e))
  cases split n e with
  | inl p => exact (continuous_apply p).comp continuous_fst
  | inr p => exact (continuous_apply p).comp continuous_snd

theorem assemble_continuous : Continuous (assemble n G) :=
  (HaarHalfEdges.coarsen_continuous G).comp (join_continuous n G)

variable [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def halfHaar : Measure (Half n G) := Measure.pi (fun _ => compactHaar G)

instance halfHaar_probability : IsProbabilityMeasure (halfHaar n G) := by
  unfold halfHaar
  infer_instance

theorem join_preserving : MeasurePreserving (join n G)
    ((halfHaar n G).prod (halfHaar n G))
    (Measure.pi (fun _ : HalfEdge (2 * n) => compactHaar G)) := by
  have hp := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : PositiveHalf n ⊕ PositiveHalf n => compactHaar G)
  have hr := measurePreserving_piCongrLeft
    (fun _ : HalfEdge (2 * n) => compactHaar G) (piecesEquiv n)
  convert hr.comp hp using 1
  funext z e
  simp only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp [join, piecesEquiv, Equiv.sumPiEquivProdPi]
  cases split n e <;> rfl

/-- Both halves are genuinely independent Haar draws before the Wilson
weight is inserted, and their coarsening has exactly the original Haar law. -/
theorem assemble_preserving : MeasurePreserving (assemble n G)
    ((halfHaar n G).prod (halfHaar n G))
    (WilsonSlabGauge.spatialHaar (n := 2 * n) (G := G)) :=
  (HaarHalfEdges.coarsen_preserving G).comp (join_preserving n G)

theorem integral_assemble (F : SpatialLinks (2 * n) G → ℝ) (hF : Continuous F) :
    (∫ z, F (assemble n G z) ∂(halfHaar n G).prod (halfHaar n G)) =
      ∫ u, F u ∂WilsonSlabGauge.spatialHaar := by
  have hp := assemble_preserving n G
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm

end
end UnifiedTheory.Clay.YangMills.SpatialHalfEdgeSplit
