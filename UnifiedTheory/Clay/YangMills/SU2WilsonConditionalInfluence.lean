/-
Finite bounded-test influence for the actual normalized Wilson conditional law.
The actual Haar/staple identity is used; changing one affected unit staple costs
at most 2 beta times the test oscillation, independently of lattice volume.
The last theorem specifies the unchanged other staples explicitly. A complete
lattice neighbor enumeration and a Gibbs comparison theorem are separate steps.
No physical transfer-time gap or weak-coupling estimate is asserted.
-/
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import UnifiedTheory.Clay.YangMills.SU2InducedAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2WilsonConditionalInfluence
noncomputable section
open MeasureTheory SU2QuaternionEquivalence SU2HaarTilt SU2InducedAction
open scoped Quaternion RealInnerProductSpace

/-- Finite bounded-test influence of the actual normalized SU(2) Haar law. -/
theorem tilt_expectation_difference (β : ℝ) (A B : ℍ) (hβ : 0 ≤ β)
    (G : UnitQuaternion → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂tiltLaw β B) - (∫ q, G q ∂tiltLaw β A)| ≤
      β * (d - c) * ‖B - A‖ := by
  let D := B - A
  have hb (q : UnitQuaternion) : insertion β D q ∈
      Set.Icc (-(2 * β * ‖D‖)) (2 * β * ‖D‖) := by
    apply abs_le.mp
    unfold insertion
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * β)]
    have h := abs_real_inner_le_norm (q : ℍ) D
    rw [CStarRing.norm_of_mem_unitary q.property, one_mul] at h
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hD : 0 ≤ 2 * β * ‖D‖ := by positivity
  have h := CompactGibbsOscillation.source_expectation_difference haar
    (baseAction β A) (insertion β D) G (baseAction_continuous β A)
    (insertion_continuous β D) hG (-(2 * β * ‖D‖)) (2 * β * ‖D‖) c d
    (by linarith) hcd hb hGb
  unfold CompactGibbsSource.expectation at h
  rw [source_law, source_law] at h
  simp only [one_smul, zero_smul, add_zero] at h
  have he : A + D = B := by dsimp only [D]; abel
  rw [he] at h
  convert h using 1
  dsimp only [D]
  ring

/-- Replacing a single unit staple costs at most twice beta times the test oscillation. -/
theorem one_staple_difference (β : ℝ) (R : ℍ) (v w : UnitQuaternion) (hβ : 0 ≤ β)
    (G : UnitQuaternion → ℝ) (hG : Continuous G) (c d : ℝ) (hcd : c ≤ d)
    (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂tiltLaw β (R + w)) - (∫ q, G q ∂tiltLaw β (R + v))| ≤
      2 * β * (d - c) := by
  have h := tilt_expectation_difference β (R + v) (R + w) hβ G hG c d hcd hGb
  have hn : ‖(R + (w : ℍ)) - (R + (v : ℍ))‖ ≤ 2 := by
    rw [add_sub_add_left_eq_sub]
    calc
      ‖(w : ℍ) - v‖ ≤ ‖(w : ℍ)‖ + ‖(v : ℍ)‖ := norm_sub_le _ _
      _ = 2 := by rw [CStarRing.norm_of_mem_unitary w.property,
        CStarRing.norm_of_mem_unitary v.property]; norm_num
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg hβ (sub_nonneg.mpr hcd))
  exact h.trans (by nlinarith [hm])

open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonSingleLinkStaples
open SingleLinkWilsonOscillation SU2WilsonConditionalSource
variable (n : ℕ) [NeZero n] [Fact (1 < n)]

/-- Actual Wilson conditional laws, with the exterior action cancelled by the proved dictionary. -/
theorem conditional_expectation_difference (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r s : Exterior n Q x μ) (hβ : 0 ≤ β) (G : Q → ℝ) (hG : Continuous G)
    (c d : ℝ) (hcd : c ≤ d) (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂conditionalLaw n x μ β s) -
      (∫ q, G q ∂conditionalLaw n x μ β r)| ≤
      β * (d - c) * ‖exteriorStaple n x μ s - exteriorStaple n x μ r‖ := by
  rw [conditionalLaw_eq_tiltLaw, conditionalLaw_eq_tiltLaw]
  exact tilt_expectation_difference β _ _ hβ G hG c d hcd hGb

omit [NeZero n] [Fact (1 < n)] in
/-- The difference of actual staple sums when exactly one affected staple can change. -/
theorem exteriorStaple_difference_single (x : Vertex n) (μ : Fin 4)
    (r s : Exterior n Q x μ) (p₀ : PlaquetteIndex n) (hp₀ : p₀ ∈ affected n x μ)
    (hsame : ∀ p ∈ affected n x μ, p ≠ p₀ →
      staple n Q (exteriorConfig n x μ s) x μ p =
        staple n Q (exteriorConfig n x μ r) x μ p) :
    exteriorStaple n x μ s - exteriorStaple n x μ r =
      (staple n Q (exteriorConfig n x μ s) x μ p₀ : ℍ) -
        (staple n Q (exteriorConfig n x μ r) x μ p₀ : ℍ) := by
  classical
  unfold exteriorStaple stapleSum weightedStaple
  simp only [one_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single p₀
  · intro p hp hne
    rw [hsame p hp hne, sub_self]
  · exact fun h => (h hp₀).elim

/-- Bounded-test influence for the actual Wilson law, with no replacement measure supplied. -/
theorem conditional_single_staple_influence (x : Vertex n) (μ : Fin 4) (β : ℝ)
    (r s : Exterior n Q x μ) (p₀ : PlaquetteIndex n) (hp₀ : p₀ ∈ affected n x μ)
    (hsame : ∀ p ∈ affected n x μ, p ≠ p₀ →
      staple n Q (exteriorConfig n x μ s) x μ p =
        staple n Q (exteriorConfig n x μ r) x μ p)
    (hβ : 0 ≤ β) (G : Q → ℝ) (hG : Continuous G)
    (c d : ℝ) (hcd : c ≤ d) (hGb : ∀ q, G q ∈ Set.Icc c d) :
    |(∫ q, G q ∂conditionalLaw n x μ β s) -
      (∫ q, G q ∂conditionalLaw n x μ β r)| ≤ 2 * β * (d - c) := by
  have h := conditional_expectation_difference n x μ β r s hβ G hG c d hcd hGb
  rw [exteriorStaple_difference_single n x μ r s p₀ hp₀ hsame] at h
  have hn : ‖(staple n Q (exteriorConfig n x μ s) x μ p₀ : ℍ) -
      (staple n Q (exteriorConfig n x μ r) x μ p₀ : ℍ)‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    rw [CStarRing.norm_of_mem_unitary (staple n Q (exteriorConfig n x μ s) x μ p₀).property,
      CStarRing.norm_of_mem_unitary (staple n Q (exteriorConfig n x μ r) x μ p₀).property]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg hβ (sub_nonneg.mpr hcd))
  exact h.trans (by nlinarith [hm])

end
end UnifiedTheory.Clay.YangMills.SU2WilsonConditionalInfluence
