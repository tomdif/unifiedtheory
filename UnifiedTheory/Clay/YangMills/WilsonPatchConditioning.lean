/- The fixed-exterior Haar patch is exactly the interior Gibbs measure
conditioned on its chord event. This event has positive reference mass;
its probability under the unrestricted interacting law is retained. -/
import UnifiedTheory.Clay.YangMills.GibbsConditionedLaw
import UnifiedTheory.Clay.YangMills.WilsonPatchCovariance
import UnifiedTheory.Clay.YangMills.GibbsEventCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchConditioning
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonChordPatchLaw
open QuaternionCapContraction
open scoped Quaternion ENNReal

theorem pi_conditioning {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (E : ∀ i, Set (X i))
    (hp : ∀ i, μ i (E i) ≠ 0) :
    Measure.pi (fun i => ProbabilityTheory.cond (μ i) (E i)) =
      ProbabilityTheory.cond (Measure.pi μ) (Set.univ.pi E) := by
  letI (i : I) := ProbabilityTheory.cond_isProbabilityMeasure (hp i)
  apply Measure.pi_eq
  intro T hT
  rw [ProbabilityTheory.cond_apply' (.univ_pi hT), ← Set.pi_inter_distrib,
    Measure.pi_pi, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun i _ _ _ _ => Or.inl (hp i)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (ProbabilityTheory.cond_apply' (hT i) (μ i)).symm

theorem cap_preserving (b : Q) (ε : ℝ) :
    MeasurePreserving (Subtype.val : Cap b ε → Q) (QuaternionCapContraction.measure b ε)
      (ProbabilityTheory.cond QuaternionHaarDoubling.haar (cap b ε)) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [QuaternionCapContraction.measure, Measure.map_smul, raw_mass, raw,
    map_comap_subtype_coe (cap_closed b ε).measurableSet]
  rfl

variable (n : ℕ)
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

abbrev Inside (S : Finset (SpatialVertex n × Fin 3)) :=
  WilsonBlockMarginal.Inside (G := Q) S

abbrev haar (S : Finset (SpatialVertex n × Fin 3)) : Measure (Inside n S) :=
  WilsonBlockMarginal.insideMeasure S QuaternionHaarDoubling.haar

def event (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) : Set (Inside n S) :=
  Set.univ.pi (fun e => cap (v₀ e.1) ε)

theorem event_measurable (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    MeasurableSet (event n S v₀ ε) :=
  MeasurableSet.univ_pi (fun e => (cap_closed (v₀ e.1) ε).measurableSet)

theorem event_nonzero (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) : haar n S (event n S v₀ ε) ≠ 0 := by
  rw [event, Measure.pi_pi]
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  rw [← raw_mass]
  exact (raw_pos (v₀ e.1) ε hε).ne'

def forget (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (x : Coordinates n S v₀ ε) : Inside n S := fun e => (x e).1

theorem forget_continuous (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    Continuous (forget n S v₀ ε) :=
  continuous_pi (fun e => continuous_subtype_val.comp (continuous_apply e))

theorem forget_injective (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ) :
    Function.Injective (forget n S v₀ ε) := by
  intro x y h
  funext e
  exact Subtype.ext (congrFun h e)

theorem base_preserving (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) :
    MeasurePreserving (forget n S v₀ ε) (baseMeasure n S v₀ ε)
      (ProbabilityTheory.cond (haar n S) (event n S v₀ ε)) := by
  have hh := measurePreserving_pi
    (fun e : {e : SpatialVertex n × Fin 3 // e ∈ S} =>
      QuaternionCapContraction.measure (v₀ e.1) ε)
    (fun e : {e : SpatialVertex n × Fin 3 // e ∈ S} =>
      ProbabilityTheory.cond QuaternionHaarDoubling.haar (cap (v₀ e.1) ε))
    (fun e => cap_preserving (v₀ e.1) ε)
  rw [pi_conditioning _ _ (fun e => by
    rw [← raw_mass]
    exact (raw_pos (v₀ e.1) ε hε).ne')] at hh
  exact hh

def insert (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (x : Inside n S) : Slice n :=
  WilsonBlockMarginal.assemble S ((fun e => v₀ e.1), x)

theorem insert_continuous (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) :
    Continuous (insert n S v₀) :=
  (WilsonBlockMarginal.assemble_continuous S).comp (continuous_const.prodMk continuous_id)

theorem insert_forget (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (ε : ℝ)
    (x : Coordinates n S v₀ ε) :
    insert n S v₀ (forget n S v₀ ε x) = assemble n S v₀ ε x := rfl

/-- This is the unrestricted interior law, with the same fixed exterior. -/
def interiorLaw (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n) (A : Slice n → ℝ) :
    Measure (Inside n S) := CompactGibbsContinuity.law (haar n S) (A ∘ insert n S v₀)

theorem interior_probability (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (A : Slice n → ℝ) (hA : Continuous A) : IsProbabilityMeasure (interiorLaw n S v₀ A) :=
  CompactGibbsContinuity.law_probability _ _ (hA.comp (insert_continuous n S v₀))

/-- Exact identification of the previously constructed capped Wilson law. -/
theorem law_preserving (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A : Slice n → ℝ) (hA : Continuous A) :
    MeasurePreserving (forget n S v₀ ε) (law n S v₀ ε A)
      (ProbabilityTheory.cond (interiorLaw n S v₀ A) (event n S v₀ ε)) := by
  have he := ((forget_continuous n S v₀ ε).isClosedEmbedding
    (forget_injective n S v₀ ε)).measurableEmbedding
  have hh := GibbsConditionedLaw.weightedLaw_transport (base_preserving n S v₀ ε hε) he
    (fun x => Real.exp (-A (insert n S v₀ x)))
    ((hA.comp (insert_continuous n S v₀)).neg.rexp.measurable)
  change MeasurePreserving _ (law n S v₀ ε A)
    (CompactGibbsContinuity.law (ProbabilityTheory.cond (haar n S) (event n S v₀ ε))
      (A ∘ insert n S v₀)) at hh
  rw [GibbsConditionedLaw.law_cond _ _ (hA.comp (insert_continuous n S v₀))
    _ (event_measurable n S v₀ ε) (event_nonzero n S v₀ ε hε)] at hh
  exact hh

theorem conditioned_integral (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A : Slice n → ℝ) (hA : Continuous A) (F : Slice n → ℝ) :
    (∫ x, F (insert n S v₀ x) ∂ProbabilityTheory.cond
      (interiorLaw n S v₀ A) (event n S v₀ ε)) =
      ∫ x, F (assemble n S v₀ ε x) ∂law n S v₀ ε A := by
  exact ((law_preserving n S v₀ ε hε A hA).integral_comp
    (((forget_continuous n S v₀ ε).isClosedEmbedding
      (forget_injective n S v₀ ε)).measurableEmbedding) (F ∘ insert n S v₀)).symm

theorem conditioned_covariance (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε : 0 < ε) (A : Slice n → ℝ) (hA : Continuous A) (F G : Slice n → ℝ) :
    GibbsCrossCovariance.covariance
      (ProbabilityTheory.cond (interiorLaw n S v₀ A) (event n S v₀ ε))
      (F ∘ insert n S v₀) (G ∘ insert n S v₀) =
    GibbsCrossCovariance.covariance (law n S v₀ ε A)
      (F ∘ assemble n S v₀ ε) (G ∘ assemble n S v₀ ε) := by
  unfold GibbsCrossCovariance.covariance
  simp only [Function.comp_apply]
  rw [conditioned_integral n S v₀ ε hε A hA (fun v => F v * G v),
    conditioned_integral n S v₀ ε hε A hA F, conditioned_integral n S v₀ ε hε A hA G]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchConditioning
