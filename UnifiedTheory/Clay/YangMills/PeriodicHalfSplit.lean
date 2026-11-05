/- Exact boundary/positive/negative link coordinates for site reflection.
The negative coordinates include temporal-link inversion so reflection becomes
the literal swap of two copies of the positive-half configuration space. -/
import UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicHalfSplit
noncomputable section
open PeriodicLattice4 PeriodicTimeReflection PeriodicHalfGeometry RegulatedGauge MeasureTheory

variable (n : ℕ) [NeZero n]

abbrev BoundaryIndex := {p : Index n // Boundary n p}
abbrev PositiveIndex := {p : Index n // Positive n p}
abbrev Pieces := BoundaryIndex n ⊕ (PositiveIndex n ⊕ PositiveIndex n)

instance boundaryFintype : Fintype (BoundaryIndex n) := Fintype.ofFinite _
instance positiveFintype : Fintype (PositiveIndex n) := Fintype.ofFinite _

theorem reflected_positive_not_boundary (p : PositiveIndex n) :
    ¬ Boundary n (reflectIndex (2 * n) p.val) := by
  intro hb
  have he := boundary_fixed n (reflectIndex (2 * n) p.val) hb
  rw [reflectIndex_involutive] at he
  exact positive_reflection_disjoint n p.val p.property (he ▸ p.property)

def glueIndex : Pieces n → Index n
  | Sum.inl b => b.val
  | Sum.inr (Sum.inl p) => p.val
  | Sum.inr (Sum.inr p) => reflectIndex (2 * n) p.val

def splitIndex (p : Index n) : Pieces n := by
  classical
  exact if hb : Boundary n p then Sum.inl ⟨p, hb⟩ else
    if hp : Positive n p then Sum.inr (Sum.inl ⟨p, hp⟩) else
      Sum.inr (Sum.inr ⟨reflectIndex (2 * n) p,
        nonboundary_nonpositive_reflect_positive n p hb hp⟩)

theorem split_glue (p : Pieces n) : splitIndex n (glueIndex n p) = p := by
  classical
  rcases p with b | p | p
  · simp [glueIndex, splitIndex, b.property]
  · simp [glueIndex, splitIndex, positive_not_boundary n p.val p.property, p.property]
  · simp only [glueIndex, splitIndex, dif_neg (reflected_positive_not_boundary n p),
      dif_neg (positive_reflection_disjoint n p.val p.property)]
    congr 2
    exact Subtype.ext (reflectIndex_involutive (2 * n) p.val)

theorem glue_split (p : Index n) : glueIndex n (splitIndex n p) = p := by
  classical
  by_cases hb : Boundary n p
  · simp [splitIndex, hb, glueIndex]
  · by_cases hp : Positive n p
    · simp [splitIndex, hb, hp, glueIndex]
    · simp only [splitIndex, dif_neg hb, dif_neg hp, glueIndex]
      exact reflectIndex_involutive (2 * n) p

def piecesEquiv : Pieces n ≃ Index n where
  toFun := glueIndex n
  invFun := splitIndex n
  left_inv := split_glue n
  right_inv := glue_split n

variable (G : Type*) [Group G]

abbrev BoundaryConfiguration := BoundaryIndex n → G
abbrev HalfConfiguration := PositiveIndex n → G
abbrev SplitConfiguration :=
  BoundaryConfiguration n G × (HalfConfiguration n G × HalfConfiguration n G)

def linkAt (U : Configuration (Vertex (2 * n)) G) (p : Index n) : G :=
  U ((edgeCoordinates (2 * n)).symm p)

def flip (p : Index n) (g : G) : G := if p.2 = 0 then g⁻¹ else g

omit [NeZero n] in
theorem flip_involutive (p : Index n) : Function.Involutive (flip n G p) := by
  intro g
  by_cases hp : p.2 = 0 <;> simp [flip, hp]

omit [NeZero n] in
theorem flip_reflected (p : Index n) (g : G) :
    flip n G (reflectIndex (2 * n) p) g = flip n G p g := rfl

omit [NeZero n] in
theorem linkAt_reflection (U : Configuration (Vertex (2 * n)) G) (p : Index n) :
    linkAt n G (reflectConfiguration (2 * n) G U) p =
      flip n G p (linkAt n G U (reflectIndex (2 * n) p)) := by
  rfl

def splitConfiguration (U : Configuration (Vertex (2 * n)) G) : SplitConfiguration n G :=
  (fun b => linkAt n G U b.val,
    (fun p => linkAt n G U p.val,
      fun p => flip n G p.val (linkAt n G U (reflectIndex (2 * n) p.val))))

def pieceValues (z : SplitConfiguration n G) : Pieces n → G
  | Sum.inl b => z.1 b
  | Sum.inr (Sum.inl p) => z.2.1 p
  | Sum.inr (Sum.inr p) => flip n G p.val (z.2.2 p)

def assemble (z : SplitConfiguration n G) : Configuration (Vertex (2 * n)) G :=
  fun e => pieceValues n G z (splitIndex n (edgeCoordinates (2 * n) e))

theorem assemble_boundary (z : SplitConfiguration n G) (b : BoundaryIndex n) :
    linkAt n G (assemble n G z) b.val = z.1 b := by
  change pieceValues n G z (splitIndex n ((edgeCoordinates (2 * n))
    ((edgeCoordinates (2 * n)).symm b.val))) = _
  rw [Equiv.apply_symm_apply]
  change pieceValues n G z (splitIndex n (glueIndex n (Sum.inl b))) = _
  rw [split_glue]
  rfl

theorem assemble_positive (z : SplitConfiguration n G) (p : PositiveIndex n) :
    linkAt n G (assemble n G z) p.val = z.2.1 p := by
  change pieceValues n G z (splitIndex n ((edgeCoordinates (2 * n))
    ((edgeCoordinates (2 * n)).symm p.val))) = _
  rw [Equiv.apply_symm_apply]
  change pieceValues n G z (splitIndex n (glueIndex n (Sum.inr (Sum.inl p)))) = _
  rw [split_glue]
  rfl

theorem assemble_negative (z : SplitConfiguration n G) (p : PositiveIndex n) :
    linkAt n G (assemble n G z) (reflectIndex (2 * n) p.val) = flip n G p.val (z.2.2 p) := by
  change pieceValues n G z (splitIndex n ((edgeCoordinates (2 * n))
    ((edgeCoordinates (2 * n)).symm (reflectIndex (2 * n) p.val)))) = _
  rw [Equiv.apply_symm_apply]
  change pieceValues n G z (splitIndex n (glueIndex n (Sum.inr (Sum.inr p)))) = _
  rw [split_glue]
  rfl

theorem split_assemble (z : SplitConfiguration n G) :
    splitConfiguration n G (assemble n G z) = z := by
  apply Prod.ext
  · funext b
    exact assemble_boundary n G z b
  · apply Prod.ext
    · funext p
      exact assemble_positive n G z p
    · funext p
      change flip n G p.val (linkAt n G (assemble n G z) (reflectIndex (2 * n) p.val)) = _
      rw [assemble_negative, flip_involutive]

theorem assemble_split (U : Configuration (Vertex (2 * n)) G) :
    assemble n G (splitConfiguration n G U) = U := by
  funext e
  obtain ⟨p, hp⟩ := (piecesEquiv n).surjective (edgeCoordinates (2 * n) e)
  have he : e = (edgeCoordinates (2 * n)).symm (glueIndex n p) := by
    change glueIndex n p = (edgeCoordinates (2 * n)) e at hp
    rw [hp]
    exact (Equiv.symm_apply_apply _ e).symm
  rw [he]
  rcases p with b | p | p
  · exact assemble_boundary n G _ b
  · exact assemble_positive n G _ p
  · change linkAt n G (assemble n G (splitConfiguration n G U))
      (reflectIndex (2 * n) p.val) = _
    rw [assemble_negative]
    exact flip_involutive n G p.val _

def configurationEquiv : Configuration (Vertex (2 * n)) G ≃ SplitConfiguration n G where
  toFun := splitConfiguration n G
  invFun := assemble n G
  left_inv := assemble_split n G
  right_inv := split_assemble n G

omit [NeZero n] in
/-- In the constructed coordinates reflection is exactly the half swap, with boundary fixed. -/
theorem split_reflection (U : Configuration (Vertex (2 * n)) G) :
    splitConfiguration n G (reflectConfiguration (2 * n) G U) =
      ((splitConfiguration n G U).1,
        ((splitConfiguration n G U).2.2, (splitConfiguration n G U).2.1)) := by
  apply Prod.ext
  · funext b
    change linkAt n G (reflectConfiguration (2 * n) G U) b.val = linkAt n G U b.val
    rw [linkAt_reflection, boundary_fixed n b.val b.property]
    simp [flip, b.property.1]
  · apply Prod.ext
    · funext p
      exact linkAt_reflection n G U p.val
    · funext p
      change flip n G p.val (linkAt n G (reflectConfiguration (2 * n) G U)
        (reflectIndex (2 * n) p.val)) = _
      rw [linkAt_reflection, flip_reflected, reflectIndex_involutive, flip_involutive]
      rfl

theorem reflect_assemble (z : SplitConfiguration n G) :
    reflectConfiguration (2 * n) G (assemble n G z) =
      assemble n G (z.1, (z.2.2, z.2.1)) := by
  apply (configurationEquiv n G).injective
  change splitConfiguration n G _ = splitConfiguration n G _
  rw [split_reflection, split_assemble, split_assemble]

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [NeZero n] in
theorem continuous_flip (p : Index n) : Continuous (flip n G p) := by
  change Continuous (fun g : G => if p.2 = 0 then g⁻¹ else g)
  by_cases hp : p.2 = 0
  · simpa only [PeriodicHalfSplit.flip, hp, if_true] using
      (continuous_inv : Continuous (Inv.inv : G → G))
  · simpa only [PeriodicHalfSplit.flip, hp, if_false] using
      (continuous_id : Continuous (id : G → G))

omit [NeZero n] in
theorem continuous_splitConfiguration : Continuous (splitConfiguration n G) := by
  refine Continuous.prodMk (continuous_pi (fun b => continuous_apply _)) ?_
  refine Continuous.prodMk (continuous_pi (fun p => continuous_apply _)) ?_
  exact continuous_pi (fun p => (continuous_flip n G p.val).comp (continuous_apply _))

theorem continuous_assemble : Continuous (assemble n G) := by
  apply continuous_pi
  intro e
  change Continuous (fun z : SplitConfiguration n G =>
    pieceValues n G z (splitIndex n (edgeCoordinates (2 * n) e)))
  cases splitIndex n (edgeCoordinates (2 * n) e) with
  | inl b => exact (continuous_apply b).comp continuous_fst
  | inr p =>
    cases p with
    | inl p => exact (continuous_apply p).comp (continuous_fst.comp continuous_snd)
    | inr p =>
      exact (continuous_flip n G p.val).comp
        ((continuous_apply p).comp (continuous_snd.comp continuous_snd))

variable [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def boundaryMeasure : Measure (BoundaryConfiguration n G) :=
  Measure.pi (fun _ : BoundaryIndex n => compactHaar G)

def halfMeasure : Measure (HalfConfiguration n G) :=
  Measure.pi (fun _ : PositiveIndex n => compactHaar G)

instance boundaryMeasure_probability : IsProbabilityMeasure (boundaryMeasure n G) := by
  unfold boundaryMeasure
  infer_instance

instance halfMeasure_probability : IsProbabilityMeasure (halfMeasure n G) := by
  unfold halfMeasure
  infer_instance

def reindexPieces (U : Configuration (Vertex (2 * n)) G) : Pieces n → G :=
  fun p => linkAt n G U (glueIndex n p)

def orientPieces (U : Pieces n → G) (p : Pieces n) : G :=
  (match p with
    | Sum.inl _ => id
    | Sum.inr (Sum.inl _) => id
    | Sum.inr (Sum.inr p) => flip n G p.val) (U p)

def packPieces (U : Pieces n → G) : SplitConfiguration n G :=
  (fun b => U (Sum.inl b), (fun p => U (Sum.inr (Sum.inl p)),
    fun p => U (Sum.inr (Sum.inr p))))

theorem reindexPieces_preserves :
    MeasurePreserving (reindexPieces n G) (referenceMeasure G (Vertex (2 * n)))
      (Measure.pi (fun _ : Pieces n => compactHaar G)) := by
  let E := (piecesEquiv n).trans (edgeCoordinates (2 * n)).symm
  have h := measurePreserving_piCongrLeft (fun _ : Pieces n => compactHaar G) E.symm
  convert h using 1
  funext U p
  simp [reindexPieces, linkAt, E, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rfl

theorem orientPieces_preserves :
    MeasurePreserving (orientPieces n G) (Measure.pi (fun _ : Pieces n => compactHaar G))
      (Measure.pi (fun _ : Pieces n => compactHaar G)) := by
  refine measurePreserving_pi (fun _ : Pieces n => compactHaar G)
    (fun _ : Pieces n => compactHaar G)
    (f := fun p => match p with
      | Sum.inl _ => id
      | Sum.inr (Sum.inl _) => id
      | Sum.inr (Sum.inr p) => flip n G p.val) ?_
  intro p
  rcases p with b | p | p
  · exact MeasurePreserving.id _
  · exact MeasurePreserving.id _
  · change MeasurePreserving (fun g : G => if p.val.2 = 0 then g⁻¹ else g)
      (compactHaar G) (compactHaar G)
    by_cases hp : p.val.2 = 0
    · simpa only [flip, hp, if_true] using compactHaar_preserves_inv G
    · simpa only [flip, hp, if_false] using MeasurePreserving.id (compactHaar G)

theorem packPieces_preserves :
    MeasurePreserving (packPieces n G) (Measure.pi (fun _ : Pieces n => compactHaar G))
      ((boundaryMeasure n G).prod ((halfMeasure n G).prod (halfMeasure n G))) := by
  have h₁ := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Pieces n => G)).symm
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Pieces n => compactHaar G))
  have h₂ := MeasurePreserving.symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : PositiveIndex n ⊕ PositiveIndex n => G)).symm
    (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : PositiveIndex n ⊕ PositiveIndex n => compactHaar G))
  exact ((MeasurePreserving.id (boundaryMeasure n G)).prod h₂).comp h₁

/-- Exact independent Haar boundary/half factorization for the actual lattice links. -/
theorem splitConfiguration_preserves :
    MeasurePreserving (splitConfiguration n G) (referenceMeasure G (Vertex (2 * n)))
      ((boundaryMeasure n G).prod ((halfMeasure n G).prod (halfMeasure n G))) :=
  (packPieces_preserves n G).comp ((orientPieces_preserves n G).comp (reindexPieces_preserves n G))

end
end UnifiedTheory.Clay.YangMills.PeriodicHalfSplit
