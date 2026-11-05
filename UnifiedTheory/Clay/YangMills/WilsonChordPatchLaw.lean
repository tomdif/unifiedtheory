/- Genuine normalized Haar-cap coordinates with a fixed exterior. Tilting
this product reference measure retains the full interacting Wilson action. -/
import UnifiedTheory.Clay.YangMills.FiniteProductContraction
import UnifiedTheory.Clay.YangMills.WilsonPatchMinimumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonChordPatchLaw
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonPatchNeighborhood
open scoped Quaternion ENNReal

variable (n : ℕ)
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

abbrev Coordinates (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :=
  ∀ e : {e : SpatialVertex n × Fin 3 // e ∈ S}, QuaternionCapContraction.Cap (v₀ e.1) ε

def baseMeasure (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    Measure (Coordinates n S v₀ ε) :=
  Measure.pi (fun e => QuaternionCapContraction.measure (v₀ e.1) ε)

theorem base_probability (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) : IsProbabilityMeasure (baseMeasure n S v₀ ε) := by
  letI (e : {e : SpatialVertex n × Fin 3 // e ∈ S}) :
      IsProbabilityMeasure (QuaternionCapContraction.measure (v₀ e.1) ε) :=
    QuaternionCapContraction.measure_probability _ ε hε
  unfold baseMeasure
  infer_instance

def assemble (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (x : Coordinates n S v₀ ε) : Slice n :=
  WilsonBlockMarginal.assemble S ((fun e => v₀ e.1), (fun e => (x e).1))

theorem assemble_inside (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (x : Coordinates n S v₀ ε) (e : SpatialVertex n × Fin 3) (he : e ∈ S) :
    assemble n S v₀ ε x e = (x ⟨e, he⟩).1 :=
  WilsonBlockMarginal.assemble_inside S _ e he

theorem assemble_outside (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (x : Coordinates n S v₀ ε) (e : SpatialVertex n × Fin 3) (he : e ∉ S) :
    assemble n S v₀ ε x e = v₀ e := WilsonBlockMarginal.assemble_outside S _ e he

theorem assemble_continuous (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    Continuous (assemble n S v₀ ε) := by
  apply continuous_pi
  intro e
  by_cases he : e ∈ S
  · simpa only [assemble_inside n S v₀ ε _ e he] using
      (continuous_subtype_val.comp (continuous_apply (⟨e, he⟩ : {e // e ∈ S})))
  · simpa only [assemble_outside n S v₀ ε _ e he] using
      (continuous_const : Continuous (fun _ : Coordinates n S v₀ ε => v₀ e))

theorem assemble_mem (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 ≤ ε) (x : Coordinates n S v₀ ε) :
    assemble n S v₀ ε x ∈ region n S v₀ ε := by
  refine ⟨fun e he => assemble_outside n S v₀ ε x e he, ?_⟩
  intro e
  by_cases he : e ∈ S
  · rw [assemble_inside n S v₀ ε x e he]
    exact (x ⟨e, he⟩).2
  · rw [assemble_outside n S v₀ ε x e he, sub_self, norm_zero]
    exact hε

def lift (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (v : Slice n) (hv : v ∈ region n S v₀ ε) : Coordinates n S v₀ ε :=
  fun e => ⟨v e.1, hv.2 e.1⟩

theorem assemble_lift (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (v : Slice n) (hv : v ∈ region n S v₀ ε) :
    assemble n S v₀ ε (lift n S v₀ ε v hv) = v := by
  funext e
  by_cases he : e ∈ S
  · rw [assemble_inside n S v₀ ε _ e he]
    rfl
  · rw [assemble_outside n S v₀ ε _ e he, hv.1 e he]

def contract (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (hε : ε ^ 2 < 2) (z x : Coordinates n S v₀ ε) : Coordinates n S v₀ ε :=
  fun e => QuaternionCapContraction.contract (v₀ e.1) ε hε (z e) (x e)

theorem contract_continuous (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (hε : ε ^ 2 < 2) (z : Coordinates n S v₀ ε) :
    Continuous (contract n S v₀ ε hε z) :=
  continuous_pi (fun e => (QuaternionCapContraction.contract_continuous
    (v₀ e.1) ε hε (z e)).comp (continuous_apply e))

theorem contract_map_bound (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ^ 2 < 2) (z : Coordinates n S v₀ ε) :
    (baseMeasure n S v₀ ε).map (contract n S v₀ ε hε z) ≤
      (81 : ℝ≥0∞) ^ S.card • baseMeasure n S v₀ ε := by
  letI (e : {e : SpatialVertex n × Fin 3 // e ∈ S}) :
      IsProbabilityMeasure (QuaternionCapContraction.measure (v₀ e.1) ε) :=
    QuaternionCapContraction.measure_probability _ ε hε0
  have hh := FiniteProductContraction.pi_map_bound
    (fun e : {e : SpatialVertex n × Fin 3 // e ∈ S} =>
      QuaternionCapContraction.measure (v₀ e.1) ε)
    (fun e => QuaternionCapContraction.contract (v₀ e.1) ε hε (z e))
    (fun e => (QuaternionCapContraction.contract_continuous (v₀ e.1) ε hε (z e)).measurable)
    81 (fun e => QuaternionCapContraction.measure_map_bound (v₀ e.1) ε hε (z e))
  simpa only [Fintype.card_coe, ENNReal.coe_ofNat] using hh

def law (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (A : Slice n → ℝ) : Measure (Coordinates n S v₀ ε) :=
  CompactGibbsContinuity.law (baseMeasure n S v₀ ε) (A ∘ assemble n S v₀ ε)

theorem law_probability (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A : Slice n → ℝ) (hA : Continuous A) :
    IsProbabilityMeasure (law n S v₀ ε A) := by
  letI := base_probability n S v₀ ε hε
  exact CompactGibbsContinuity.law_probability _ _ (hA.comp (assemble_continuous n S v₀ ε))

end
end UnifiedTheory.Clay.YangMills.WilsonChordPatchLaw
