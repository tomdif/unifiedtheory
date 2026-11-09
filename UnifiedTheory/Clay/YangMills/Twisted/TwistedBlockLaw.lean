/- A statement about the law of the blocked field, uniform in the volume. Except on an event of probability
exponentially small in the volume, all but a small fraction of blocked links lie within `4δ` of their
two-link line. The fraction is `8 (log cap(24β) + t)/(β δ²)` per link. It inherits the worst-case constants of the
block map, so it degrades under iteration even where the numerics show stable defects. It describes where the
blocked field lies, not its density, and gives no effective action. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw
noncomputable section
open PeriodicLattice4 TwistedFlat TwistedHessian TwistedStability TwistedLandau TwistedCovariant
open TwistedLocalization TwistedBadSet TwistedBlockMap
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q)
open Classical

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The eight links whose blocked value can depend on a given plaquette. -/
def neighbours (p : PlaquetteIndex (2 * n)) : Finset (V' × Fin 4) :=
  Finset.univ.image fun i : Fin 2 × Fin 4 =>
    let μ := if i.1 = 0 then p.2.1.1 else p.2.1.2
    let ν := if i.1 = 0 then p.2.1.2 else p.2.1.1
    let z := p.1
    (![z, back z μ, step (2 * n) z ν, step (2 * n) (back z μ) ν] i.2, μ)

theorem card_neighbours (p : PlaquetteIndex (2 * n)) : (neighbours n p).card ≤ 8 := by
  refine Finset.card_image_le.trans ?_
  simp

/-- Blocked links that may depend on a bad plaquette. -/
def notGood (U : V' → Fin 4 → Q) (δ : ℝ) : Finset (V' × Fin 4) :=
  Finset.univ.filter fun l => ¬ LinkGood U δ l.1 l.2

/-- A cell with large defect is a bad plaquette, with the link among its neighbours. -/
theorem mem_of_cell (U : V' → Fin 4 → Q) (δ : ℝ) (x : V') (μ ν : Fin 4) (hne : ν ≠ μ) (z : V')
    (hc : δ < TwistedBlockMap.cd U μ ν z)
    (hx : x = z ∨ x = back z μ ∨ x = step (2 * n) z ν ∨ x = step (2 * n) (back z μ) ν) :
    (x, μ) ∈ (badPlaq n U δ).biUnion (neighbours n) := by
  have hi : ∃ j : Fin 4, ![z, back z μ, step (2 * n) z ν, step (2 * n) (back z μ) ν] j = x := by
    rcases hx with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  obtain ⟨j, hj⟩ := hi
  rcases lt_or_gt_of_ne hne.symm with h | h
  · refine Finset.mem_biUnion.2 ⟨(z, ⟨(μ, ν), h⟩), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      simpa only [TwistedBlockMap.cd, h, if_true] using hc
    · refine Finset.mem_image.2 ⟨(0, j), Finset.mem_univ _, ?_⟩
      simp only [if_true]
      rw [hj]
  · have hn : ¬ μ < ν := not_lt.2 h.le
    refine Finset.mem_biUnion.2 ⟨(z, ⟨(ν, μ), h⟩), ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      simpa only [TwistedBlockMap.cd, hn, if_false] using hc
    · refine Finset.mem_image.2 ⟨(1, j), Finset.mem_univ _, ?_⟩
      simp only [one_ne_zero, if_false]
      rw [hj]

theorem notGood_subset (U : V' → Fin 4 → Q) (δ : ℝ) :
    notGood n U δ ⊆ (badPlaq n U δ).biUnion (neighbours n) := by
  rintro ⟨x, μ⟩ hl
  have hng : ¬ LinkGood U δ x μ := (Finset.mem_filter.1 hl).2
  unfold LinkGood at hng
  push_neg at hng
  obtain ⟨ν, hν, hb⟩ := hng
  by_cases h1 : TwistedBlockMap.cd U μ ν x ≤ δ
  · by_cases h2 : TwistedBlockMap.cd U μ ν (step (2 * n) x μ) ≤ δ
    · by_cases h3 : TwistedBlockMap.cd U μ ν (back x ν) ≤ δ
      · have h4 := hb h1 h2 h3
        refine mem_of_cell n U δ x μ ν hν _ h4 (Or.inr (Or.inr (Or.inr ?_)))
        rw [back_step, step_back]
      · refine mem_of_cell n U δ x μ ν hν _ (not_le.1 h3) (Or.inr (Or.inr (Or.inl ?_)))
        rw [step_back]
    · refine mem_of_cell n U δ x μ ν hν _ (not_le.1 h2) (Or.inr (Or.inl ?_))
      rw [back_step]
  · exact mem_of_cell n U δ x μ ν hν _ (not_le.1 h1) (Or.inl rfl)

theorem card_notGood_le (U : V' → Fin 4 → Q) (δ : ℝ) :
    (notGood n U δ).card ≤ 8 * (badPlaq n U δ).card := by
  refine (Finset.card_le_card (notGood_subset n U δ)).trans ?_
  have h := Finset.card_biUnion_le_card_mul (badPlaq n U δ) (neighbours n) 8
    fun p _ => card_neighbours n p
  exact h.trans_eq (Nat.mul_comm _ _)

/-- **The blocked field stays near its lines, on most links, uniformly in the volume.** -/
theorem measure_blocked_links (β δ t : ℝ) (hβ : 1 / 32 ≤ β) (hδ0 : 0 ≤ δ) :
    twistedLaw n β {U | 8 * ((linkCount n : ℝ) *
        (Real.log (SU2GaussianMass.cap (24 * β)) + t) / β) ≤
        ((notGood n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(t * linkCount n))) := by
  refine (MeasureTheory.measure_mono fun U hU => ?_).trans (measure_bad_density n β δ t hβ hδ0)
  change (linkCount n : ℝ) * (Real.log (SU2GaussianMass.cap (24 * β)) + t) / β ≤
    ((badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2
  have hU' : 8 * ((linkCount n : ℝ) * (Real.log (SU2GaussianMass.cap (24 * β)) + t) / β) ≤
    ((notGood n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2 := hU
  have hc : ((notGood n (linkValue (2 * n) Q U) δ).card : ℝ) ≤
      8 * ((badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) := by
    exact_mod_cast card_notGood_le n _ δ
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg δ)
  linarith only [hU', hm]

/-- A link outside `notGood` has its blocked value within `4δ` of the line. -/
theorem close_of_not_notGood (U : V' → Fin 4 → Q) (α : ℝ) (hα : 0 ≤ α) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / 2) (l : V' × Fin 4) (hl : l ∉ notGood n U δ) :
    d (blockLink U α l.1 l.2) (lineU U l.2 l.1) ≤ 4 * δ := by
  have hg : LinkGood U δ l.1 l.2 := by
    by_contra h
    exact hl (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  exact (blockLink_close U α hα δ hδ0 hδ l.2 l.1 hg).2

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockLaw
