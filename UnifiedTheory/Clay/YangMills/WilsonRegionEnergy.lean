/- Local Wilson energy geometry for arbitrary finite edge regions.
The boundary cost is explicit and is not discarded for arbitrary exterior data. -/
import UnifiedTheory.Clay.YangMills.WilsonRemainderDensityTail
import UnifiedTheory.Clay.YangMills.WilsonInducedSupport
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal
import UnifiedTheory.Clay.YangMills.GibbsConstantShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonRegionEnergy
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks WilsonInducedSupport SingleLinkWilsonOscillation
open WilsonEnergyDensity WilsonBlockMarginal SU2StarEnergy WilsonRemainderDensity
open UnitaryHaarNeighborhood

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

def touching (B : Finset (Edge (Vertex n))) : Finset (PlaquetteIndex n) :=
  B.biUnion (fun e => affected n (edgeCoord n e).1 (edgeCoord n e).2)

theorem mem_touching (B : Finset (Edge (Vertex n))) (p : PlaquetteIndex n) :
    p ∈ touching n B ↔ ∃ e ∈ B, e ∈ plaquetteEdges n p := by
  simp only [touching, Finset.mem_biUnion, mem_plaquetteEdges]

theorem touching_card (B : Finset (Edge (Vertex n))) : (touching n B).card ≤ 6 * B.card := by
  calc
    _ ≤ ∑ e ∈ B, (affected n (edgeCoord n e).1 (edgeCoord n e).2).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ B, 6 := Finset.sum_le_sum (fun e _ => affected_card n _ _)
    _ = _ := by simp [mul_comm]

def interior (B : Finset (Edge (Vertex n))) : Finset (PlaquetteIndex n) :=
  (touching n B).filter (fun p => plaquetteEdges n p ⊆ B)

def boundary (B : Finset (Edge (Vertex n))) : Finset (PlaquetteIndex n) :=
  touching n B \ interior n B

omit [NeZero n] in
theorem interior_subset (B : Finset (Edge (Vertex n))) : interior n B ⊆ touching n B :=
  Finset.filter_subset _ _

def energy (B : Finset (Edge (Vertex n))) (U : Configuration (Vertex n) Q) : ℝ :=
  ∑ p ∈ touching n B, plaquetteTerm n Q character 2 U p

omit [NeZero n] in
theorem energy_continuous (B : Finset (Edge (Vertex n))) : Continuous (energy n B) :=
  continuous_finset_sum _ (fun p _ => continuous_const.sub
    (Complex.continuous_re.comp (WilsonMomentBounds.loopObservable_continuous
      (Vertex n) Q character character_continuous (loops n p))))

theorem term_nonneg (U : Configuration (Vertex n) Q) (p : PlaquetteIndex n) :
    0 ≤ plaquetteTerm n Q character 2 U p := by
  rw [← plaquetteDefect_eq_term]
  exact WilsonAverageDefect.plaquette_nonneg n Q representation p U

theorem energy_nonneg (B : Finset (Edge (Vertex n))) (U : Configuration (Vertex n) Q) :
    0 ≤ energy n B U := Finset.sum_nonneg (fun p _ => term_nonneg n U p)

/-- Summing regional star energies counts a touched plaquette at most four times. -/
theorem star_sum_bound (B : Finset (Edge (Vertex n))) (U : Configuration (Vertex n) Q) :
    (∑ e ∈ B, starEnergy n (edgeCoord n e).1 (edgeCoord n e).2 U) ≤ 4 * energy n B U := by
  have he (e : Edge (Vertex n)) : starEnergy n (edgeCoord n e).1 (edgeCoord n e).2 U =
      ∑ p, if p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2 then
        plaquetteTerm n Q character 2 U p else 0 := by
    unfold starEnergy
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp
  simp_rw [he]
  rw [Finset.sum_comm]
  have hf (p : PlaquetteIndex n) :
      B.filter (fun e => p ∈ affected n (edgeCoord n e).1 (edgeCoord n e).2) =
        plaquetteEdges n p ∩ B := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, mem_plaquetteEdges, and_comm]
  simp_rw [← Finset.sum_filter, hf, Finset.sum_const, nsmul_eq_mul]
  have hr : 4 * energy n B U =
      ∑ p, if p ∈ touching n B then 4 * plaquetteTerm n Q character 2 U p else 0 := by
    unfold energy
    rw [Finset.mul_sum, ← Finset.sum_filter]
    congr 1
    ext p
    simp
  rw [hr]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : p ∈ touching n B
  · rw [if_pos hp]
    apply mul_le_mul_of_nonneg_right _ (term_nonneg n U p)
    exact_mod_cast (Finset.card_le_card Finset.inter_subset_left).trans (plaquetteEdges_card n p)
  · have hz : plaquetteEdges n p ∩ B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact hp ((mem_touching n B p).mpr
        ⟨e, (Finset.mem_inter.mp he).2, (Finset.mem_inter.mp he).1⟩)
    simp [hp, hz]

def density (B : Finset (Edge (Vertex n))) (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  (∑ e ∈ B, fractionalRemainder n (edgeCoord n e).1 (edgeCoord n e).2 β U) / B.card

theorem density_continuous (B : Finset (Edge (Vertex n))) (β : ℝ) :
    Continuous (density n B β) :=
  (continuous_finset_sum _ (fun e _ =>
    fractionalRemainder_continuous n (edgeCoord n e).1 (edgeCoord n e).2 β)).div_const _

theorem density_energy_bound [Fact (1 < n)] (B : Finset (Edge (Vertex n))) (β : ℝ)
    (hβ : 0 < β) (U : Configuration (Vertex n) Q) :
    (B.card : ℝ) * density n B β U ≤ 2 * Real.sqrt β * energy n B U := by
  by_cases hB : B.Nonempty
  · have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
    unfold density
    rw [mul_div_cancel₀ _ hc]
    calc
      _ ≤ ∑ e ∈ B, Real.sqrt β / 2 * starEnergy n (edgeCoord n e).1 (edgeCoord n e).2 U :=
        Finset.sum_le_sum (fun e _ => fractionalRemainder_energy_bound n _ _ β hβ U)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        have h := mul_le_mul_of_nonneg_left (star_sum_bound n B U)
          (show 0 ≤ Real.sqrt β / 2 by positivity)
        nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    simp [density, energy, touching]

/-- All plaquettes outside the touched set are constant on the genuine fiber. -/
theorem untouched_constant (B : Finset (Edge (Vertex n))) (r : Outside (G := Q) B)
    (v w : Inside (G := Q) B) (p : PlaquetteIndex n) (hp : p ∉ touching n B) :
    plaquetteTerm n Q character 2 (assemble B (r,v)) p =
      plaquetteTerm n Q character 2 (assemble B (r,w)) p := by
  apply plaquetteTerm_dependsOn n Q character 2 p
  intro e he
  have hb : e ∉ B := fun h => hp ((mem_touching n B p).mpr ⟨e,h,he⟩)
  simp only [assemble_outside B _ e hb]

/-- No exterior normalization is lost: the full fiber action differs by an additive constant. -/
theorem fiber_action_split (B : Finset (Edge (Vertex n))) (β : ℝ)
    (r : Outside (G := Q) B) (v : Inside (G := Q) B) :
    splitAction n Q character β 2 B (r,v) =
      (β * ∑ p ∈ Finset.univ \ touching n B,
        plaquetteTerm n Q character 2 (assemble B (r,fun _ => 1)) p) +
        β * energy n B (assemble B (r,v)) := by
  change β * (∑ p, plaquetteTerm n Q character 2 (assemble B (r,v)) p) = _
  have h := Finset.sum_sdiff (Finset.subset_univ (touching n B))
    (f := fun p => plaquetteTerm n Q character 2 (assemble B (r,v)) p)
  have he : (∑ p ∈ Finset.univ \ touching n B,
      plaquetteTerm n Q character 2 (assemble B (r,v)) p) =
      ∑ p ∈ Finset.univ \ touching n B,
        plaquetteTerm n Q character 2 (assemble B (r,fun _ => 1)) p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact untouched_constant n B r v _ p (Finset.mem_sdiff.mp hp).2
  rw [he] at h
  unfold energy
  simpa only [mul_add] using congrArg (fun x : ℝ => β * x) h.symm

def fiberLaw (B : Finset (Edge (Vertex n))) (β : ℝ) (r : Outside (G := Q) B) :=
  CompactGibbsContinuity.law (insideMeasure B (compactHaar Q))
    (fun v => splitAction n Q character β 2 B (r,v))

theorem fiberLaw_local (B : Finset (Edge (Vertex n))) (β : ℝ) (r : Outside (G := Q) B) :
    fiberLaw n B β r = CompactGibbsContinuity.law (insideMeasure B (compactHaar Q))
      (fun v => β * energy n B (assemble B (r,v))) := by
  unfold fiberLaw
  simp_rw [fiber_action_split]
  apply GibbsConstantShift.law_const_add
  exact continuous_const.mul ((energy_continuous n B).comp
    ((assemble_continuous B).comp (continuous_const.prodMk continuous_id)))

end
end UnifiedTheory.Clay.YangMills.WilsonRegionEnergy
