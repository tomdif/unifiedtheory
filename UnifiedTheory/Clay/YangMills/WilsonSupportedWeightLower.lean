/- Occupied-link Cauchy control retains the number of source plaquettes,
instead of the ambient lattice volume. All incidence sets are the actual
four-dimensional periodic Wilson geometry. -/
import UnifiedTheory.Clay.YangMills.WilsonSmoothSourceObstruction
import UnifiedTheory.Clay.YangMills.WilsonCompactCellCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSupportedWeightLower
noncomputable section
open MeasureTheory PeriodicLattice4 WilsonIndependentBlocks WilsonInfluenceGeometry
open WilsonCellWeightLower

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

/-- Only links incident to one of the supplied source plaquettes are occupied. -/
def occupiedLinks (P : Finset (PlaquetteIndex n)) : Finset (Link n) :=
  P.biUnion (incidentLinks n)

omit [NeZero n] [Fact (1 < n)] in
theorem occupied_card (P : Finset (PlaquetteIndex n)) :
    (occupiedLinks n P).card ≤ 4 * P.card := by
  apply Finset.card_biUnion_le.trans
  calc
    (∑ p ∈ P, (incidentLinks n p).card) ≤ ∑ _p ∈ P, 4 :=
      Finset.sum_le_sum (fun p _ => incidentLinks_card_le n p)
    _ = _ := by simp [Nat.mul_comm]

omit [Fact (1 < n)] in
/-- No source weight is lost outside the occupied set. -/
theorem linkWeight_zero_outside (P : Finset (PlaquetteIndex n))
    (w : PlaquetteIndex n → ℝ) (hw : ∀ p ∉ P, w p = 0)
    (e : Link n) (he : e ∉ occupiedLinks n P) : linkWeight n w e = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  apply hw p
  intro hP
  apply he
  exact Finset.mem_biUnion.mpr ⟨p, hP,
    (mem_incidentLinks n p e).mpr ((affected_iff_incident n p e).mp hp)⟩

theorem occupied_sum (P : Finset (PlaquetteIndex n))
    (w : PlaquetteIndex n → ℝ) (hw : ∀ p ∉ P, w p = 0) :
    (∑ e ∈ occupiedLinks n P, linkWeight n w e) = 4 * ∑ p, w p := by
  rw [← sum_linkWeight n w]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  exact linkWeight_zero_outside n P w hw e he

/-- The Cauchy denominator is the actual source support size, with no ambient volume. -/
theorem supported_square_bound (P : Finset (PlaquetteIndex n))
    (w : PlaquetteIndex n → ℝ) (hw : ∀ p ∉ P, w p = 0) :
    4 * (∑ p, w p)^2 ≤ (P.card : ℝ) * ∑ e : Link n, (linkWeight n w e)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (occupiedLinks n P)
    (fun _ => (1 : ℝ)) (linkWeight n w)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [occupied_sum n P w hw] at h
  have hc : ((occupiedLinks n P).card : ℝ) ≤ 4 * (P.card : ℝ) := by
    exact_mod_cast occupied_card n P
  have hs : (∑ e ∈ occupiedLinks n P, (linkWeight n w e)^2) ≤
      ∑ e : Link n, (linkWeight n w e)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => sq_nonneg _)
  have hm := mul_le_mul hc hs
    (Finset.sum_nonneg (fun e _ => sq_nonneg (linkWeight n w e))) (by positivity)
  nlinarith


/-- Finite source support replaces the ambient lattice-volume denominator
in the actual rescaled Wilson second-moment floor. -/
theorem supported_secondMoment_lower (P : Finset (PlaquetteIndex n))
    (w : PlaquetteIndex n → ℝ) (hw : ∀ p ∉ P, w p = 0) (hwpos : ∀ p, 0 ≤ w p)
    (β Z c : ℝ) (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72) :
    Z^2 * (∑ p, w p)^2 / (768 * (P.card : ℝ) * β^2) ≤
      WilsonSmoothSourceObstruction.secondMoment n β Z c w := by
  by_cases hP : P.card = 0
  · simp only [hP, Nat.cast_zero, mul_zero, zero_mul, div_zero]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hP
  have hweight : 4 * (∑ p, w p)^2 / (P.card : ℝ) ≤
      ∑ e : Link n, (linkWeight n w e)^2 := by
    apply (div_le_iff₀ hPpos).mpr
    simpa only [mul_comm] using supported_square_bound n P w hw
  have hnoise := WilsonSmoothSourceObstruction.annealed_sum_lower n β w hwpos hβ henergy
  have htotal := WilsonIndependentVariance.renormalized_second_moment_lower n β Z c w heven
  calc
    _ = (Z^2 / 8) * ((4 * (∑ p, w p)^2 / (P.card : ℝ)) / (384 * β^2)) := by ring
    _ ≤ (Z^2 / 8) * ((∑ e : Link n, (linkWeight n w e)^2) / (384 * β^2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hweight (by positivity))
        (by positivity)
    _ ≤ (Z^2 / 8) * (∑ e : Link n,
        ∫ U, SU2AnnealedVariance.originalVariance n e.1 e.2 β w U
          ∂wilsonLaw n WilsonSingleLinkStaples.Q WilsonSingleLinkStaples.character β 2) :=
      mul_le_mul_of_nonneg_left hnoise (by positivity)
    _ ≤ WilsonSmoothSourceObstruction.secondMoment n β Z c w := by
      change Z^2 * (∑ e : Link n,
        ∫ U, SU2AnnealedVariance.originalVariance n e.1 e.2 β w U
          ∂wilsonLaw n WilsonSingleLinkStaples.Q WilsonSingleLinkStaples.character β 2) ≤
        8 * WilsonSmoothSourceObstruction.secondMoment n β Z c w at htotal
      linarith


/-- One fixed smooth physical test has ultraviolet noise independently of the
ambient volume, despite every real identity counterterm. -/
theorem classical_compact_witness_lower (β a c : ℝ) (plane : Plane)
    (heven : 2 ∣ n) (hβ : 5 ≤ β)
    (henergy : WilsonEnergyDensity.energyEnvelope β ≤ 1 / 72)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (a^4)⁻¹ / (768 * 9^4 * β^2) ≤
      WilsonSmoothSourceObstruction.secondMoment n β (a^4)⁻¹ c
        (WilsonPhysicalCellWeights.weight n a plane witnessTest) := by
  let P := WilsonCompactCellCount.cells n a plane
  let w := WilsonPhysicalCellWeights.weight n a plane witnessTest
  have hsupp : ∀ x, witnessTest x ≠ 0 → ‖x‖ ≤ 2 := by
    intro x hx
    by_contra h
    exact hx (witnessTest_eq_zero_of_norm_ge x (le_of_lt (lt_of_not_ge h)))
  have hw : ∀ p ∉ P, w p = 0 :=
    WilsonCompactCellCount.weight_supported n a plane ha witnessTest hsupp
  have hm : (∑ p, w p) = 1 := by
    simpa only [witnessTest_integral, Complex.one_re] using
      WilsonPhysicalCellWeights.weight_sum n a plane witnessTest
  have h := supported_secondMoment_lower n P w hw
    (weight_nonneg n a plane witnessTest witnessTest_nonneg)
    β (a^4)⁻¹ c heven hβ henergy
  rw [hm, one_pow, mul_one] at h
  have hP : 0 < (P.card : ℝ) := by
    have hmem := WilsonCompactCellCount.sample_mem n a plane ha 0
      (by simp : ‖(0 : LocalFields.Spacetime)‖ ≤ 2)
    exact_mod_cast Finset.card_pos.mpr ⟨_, hmem⟩
  have hcard : (P.card : ℝ) ≤ (9 / a)^4 :=
    WilsonCompactCellCount.cells_card_bound n a plane ha ha1
  have hβpos : 0 < β := by linarith
  have hden : 768 * (P.card : ℝ) * β^2 ≤ 768 * (9 / a)^4 * β^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num))
      (sq_nonneg β)
  calc
    _ = ((a^4)⁻¹)^2 / (768 * (9 / a)^4 * β^2) := by
      field_simp [ha.ne', hβpos.ne']
    _ ≤ ((a^4)⁻¹)^2 / (768 * (P.card : ℝ) * β^2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ ≤ _ := h

end
end UnifiedTheory.Clay.YangMills.WilsonSupportedWeightLower
