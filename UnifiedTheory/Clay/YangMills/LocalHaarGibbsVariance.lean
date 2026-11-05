/- A volume-independent local Gibbs fluctuation floor. The external space
and its action are arbitrary: the bound depends only on the oscillation of
the local action and a fixed Haar observable. A lattice application must
identify its one-link factorization; bounded coupling is not weak coupling. -/
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison
import UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalHaarGibbsVariance
noncomputable section
open MeasureTheory RegulatedGauge LocalGibbsComparison HaarCenteredFluctuation

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

def localLaw (S : Y → ℝ) (L : Y × G → ℝ) : Measure (Y × G) :=
  weightedLaw (ν.prod (compactHaar G))
    (localWeight (fun y => Real.exp (-S y)) (fun z => Real.exp (-L z)))

def observable (χ : G → ℂ) (A B : Y → G) (z : Y × G) : ℂ :=
  χ (A z.1 * z.2 * B z.1)

theorem centered_lower (S : Y → ℝ) (hS : Continuous S)
    (L : Y × G → ℝ) (hL : Continuous L) (C : ℝ) (hC : ∀ z, |L z| ≤ C)
    (χ : G → ℂ) (hχ : Continuous χ) (A B : Y → G) (hA : Continuous A) (hB : Continuous B)
    (m : ℂ) :
    Real.exp (-2 * C) * haarFluctuation G χ ≤
      ∫ z, ‖observable G χ A B z - m‖ ^ 2 ∂localLaw G ν S L := by
  have ha : Continuous (fun y => Real.exp (-S y)) := Real.continuous_exp.comp hS.neg
  have hb : Continuous (fun z => Real.exp (-L z)) := Real.continuous_exp.comp hL.neg
  have hai : 0 < ∫ y, Real.exp (-S y) ∂ν :=
    integral_exp_pos (ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hlo (z : Y × G) : Real.exp (-C) ≤ Real.exp (-L z) :=
    Real.exp_le_exp.mpr (neg_le_neg (le_abs_self (L z) |>.trans (hC z)))
  have hup (z : Y × G) : Real.exp (-L z) ≤ Real.exp C :=
    Real.exp_le_exp.mpr ((neg_le_abs (L z)).trans (hC z))
  have hobs : Continuous (observable G χ A B) :=
    hχ.comp (((hA.comp continuous_fst).mul continuous_snd).mul (hB.comp continuous_fst))
  have he := local_expectation_lower (compactHaar G) ν _ ha
    (fun y => (Real.exp_pos _).le) hai _ hb (Real.exp (-C)) (Real.exp C)
    (Real.exp_pos _) (Real.exp_pos _) hlo hup (fun z => ‖observable G χ A B z - m‖ ^ 2)
    ((hobs.sub continuous_const).norm.pow 2) (fun z => sq_nonneg _)
    (haarFluctuation G χ) (ProbabilityTheory.variance_nonneg _ _)
    (fun y => haar_center_lower G χ hχ (A y) (B y) m)
  have hc : Real.exp (-C) / Real.exp C = Real.exp (-2 * C) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  simpa only [hc] using he

theorem variance_lower (S : Y → ℝ) (hS : Continuous S)
    (L : Y × G → ℝ) (hL : Continuous L) (C : ℝ) (hC : ∀ z, |L z| ≤ C)
    (χ : G → ℂ) (hχ : Continuous χ) (A B : Y → G) (hA : Continuous A) (hB : Continuous B) :
    Real.exp (-2 * C) * haarFluctuation G χ ≤
      ∫ z, ‖observable G χ A B z - ∫ t, observable G χ A B t ∂localLaw G ν S L‖ ^ 2
        ∂localLaw G ν S L :=
  centered_lower G ν S hS L hL C hC χ hχ A B hA hB _

theorem positive_uniform_floor (χ : G → ℂ) (hχ : Continuous χ) (g h : G)
    (hne : (χ g).re ≠ (χ h).re) (C : ℝ) :
    0 < Real.exp (-2 * C) * haarFluctuation G χ :=
  mul_pos (Real.exp_pos _) (haarFluctuation_pos G χ hχ g h hne)

end
end UnifiedTheory.Clay.YangMills.LocalHaarGibbsVariance
