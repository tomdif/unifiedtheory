/-
  LayerB/DefectSector.lean — Defect sector of the parent object

  Defines the minimal defect infrastructure needed for the
  Defect-to-Source Bridge Theorem:

  - BFDefectData: source (K) and dressing (P) projections of a defect
  - NullDefectData: focusing/bias projection of a defect
  - DefectBlock: extends ParentU with defects, stability, projections,
    and the source-focusing compatibility law

  The key axiom-free content: a stable defect is simultaneously
  visible as BF source data and null focusing bias, and these
  two views agree under a common response functional.
-/
import UnifiedTheory.LayerB.ParentU

namespace UnifiedTheory.LayerB

open LayerA

/-! ### Defect projection data -/

/-- BF-side projection of a defect: source (K) and dressing (P) parts.
    Lives in the same module as the BF field space. -/
structure BFDefectData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Source-capable (K-type) component -/
  Kpart : V
  /-- Dressing (P-type) component -/
  Ppart : V

/-- Null-side projection of a defect: a real-valued focusing bias.
    Positive = converging, negative = diverging. -/
structure NullDefectData where
  /-- Focusing/expansion bias contributed by this defect -/
  bias : ℝ

/-! ### Response functionals -/

/-- Source strength: extracts a real number from the K-part of a defect.
    This measures how much the defect contributes to the gravitational
    source term on the BF side. -/
structure SourceMeasure (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The linear functional extracting source strength -/
  measure : V →ₗ[ℝ] ℝ

/-- Bias strength: extracts a real number from the null-side bias.
    For the bridge theorem, this is just the bias value itself
    (possibly rescaled). -/
def biasMeasure (nd : NullDefectData) (scale : ℝ) : ℝ :=
  scale * nd.bias

/-! ### Defect block -/

/-- **DefectBlock**: extends the parent object with defect structure.

    A defect d has:
    - BF projection: (Kd, Pd) in the field space V
    - Null projection: βd (focusing bias)
    - Stability predicate
    - Source-focusing compatibility: the source strength of Kd
      equals the (scaled) bias strength of βd for stable defects
    - Dressing neutrality: Pd does not contribute source strength -/
structure DefectBlock
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Type of defects -/
  Defect : Type*
  /-- Stability predicate -/
  Stable : Defect → Prop
  /-- BF-side projection -/
  toBF : Defect → BFDefectData V
  /-- Null-side projection -/
  toNull : Defect → NullDefectData
  /-- Source strength functional -/
  sourceMeas : SourceMeasure V
  /-- Bias scale factor -/
  biasScale : ℝ
  /-- **Source-focusing compatibility**: for stable defects,
      the BF source strength equals the null focusing strength -/
  sourceMatchesBias :
    ∀ d, Stable d →
      sourceMeas.measure (toBF d).Kpart = biasMeasure (toNull d) biasScale
  /-- **Dressing neutrality**: the P-part carries zero source strength -/
  dressingNeutral :
    ∀ d, Stable d →
      sourceMeas.measure (toBF d).Ppart = 0

/-! ### Extended parent with matter -/

/-- **MatterParentU**: ParentU extended with a defect sector.
    This is the parent object for the matter emergence theorems. -/
structure MatterParentU
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (T : Type*) (Ω : Type*)
    [AddCommGroup T] [Module ℝ T]
    [AddCommGroup Ω] [Module ℝ Ω]
    extends ParentU V T Ω where
  /-- The defect sector -/
  defects : DefectBlock V

end UnifiedTheory.LayerB
