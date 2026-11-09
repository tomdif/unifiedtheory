/- Compactification of finite spacetime force measures. A common
subsequence exists for every countable window family with eventual mass
bounds; possible escaped mass is retained on the compact square boundary. -/
import UnifiedTheory.Audit.KFCausalCompactFiniteMeasureSubsequence
import UnifiedTheory.Audit.KFCausalSpacetimeForcePair
import UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

abbrev Square := KFCausalCompactifiedForceMeasure.Spectrum × KFCausalCompactifiedForceMeasure.Spectrum

def embed (z : ℝ × ℝ) : Square :=
  (KFCausalCompactifiedForceMeasure.embed z.1,KFCausalCompactifiedForceMeasure.embed z.2)

theorem embed_continuous : Continuous embed :=
  (KFCausalCompactifiedForceMeasure.embed_continuous.comp continuous_fst).prodMk
    (KFCausalCompactifiedForceMeasure.embed_continuous.comp continuous_snd)

def compactify (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] : FiniteMeasure Square :=
  ⟨μ.map embed,Measure.isFiniteMeasure_map μ embed⟩

theorem compactify_mass (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    ((compactify μ).mass : ℝ) = μ.real Set.univ := by
  change (μ.map embed).real Set.univ = _
  rw [Measure.real,Measure.map_apply embed_continuous.measurable MeasurableSet.univ,Set.preimage_univ]
  rfl

def pullback (q : Square →ᵇ ℂ) : (ℝ × ℝ) →ᵇ ℂ := q.compContinuous ⟨embed,embed_continuous⟩

theorem compactify_test (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (q : Square →ᵇ ℂ) :
    (∫ x, q x ∂(compactify μ : Measure Square)) = ∫ p, pullback q p ∂μ := by
  exact integral_map embed_continuous.measurable.aemeasurable q.continuous.aestronglyMeasurable

theorem pair_subsequence {K : Type*} [Countable K] (F : ℕ → K → Pair)
    (hb : ∀ k, ∃ C : ℝ, ∀ᶠ n in atTop, (F n k).mass ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P N : K → FiniteMeasure Square,
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).positive) atTop (𝓝 (P k))) ∧
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).negative) atTop (𝓝 (N k))) ∧
      (∀ k (q : Square →ᵇ ℂ), Tendsto (fun n => (F (φ n) k).evaluate (pullback q)) atTop
        (𝓝 (((∫ x, q x ∂(P k : Measure Square))-(∫ x, q x ∂(N k : Measure Square)))/2))) := by
  let M (n : ℕ) (j : Bool × K) : FiniteMeasure Square :=
    if j.1 then compactify (F n j.2).positive else compactify (F n j.2).negative
  have hM : ∀ j, ∃ C : ℝ, ∀ᶠ n in atTop, ((M n j).mass : ℝ) ≤ C := by
    intro j
    obtain ⟨C,hC⟩ := hb j.2
    refine ⟨C,hC.mono (fun n hn => ?_)⟩
    cases j with | mk d k =>
      cases d <;> simp only [M,Bool.false_eq_true,if_false,if_true,compactify_mass]
      · exact (le_add_of_nonneg_left measureReal_nonneg).trans hn
      · exact (le_add_of_nonneg_right measureReal_nonneg).trans hn
  obtain ⟨φ,hφ,ν,hν⟩ := KFCausalCompactFiniteMeasureSubsequence.common_subsequence M hM
  have hP (k : K) : Tendsto (fun n => compactify (F (φ n) k).positive) atTop (𝓝 (ν (true,k))) :=
    hν (true,k)
  have hN (k : K) : Tendsto (fun n => compactify (F (φ n) k).negative) atTop (𝓝 (ν (false,k))) :=
    hν (false,k)
  refine ⟨φ,hφ,(fun k => ν (true,k)),(fun k => ν (false,k)),hP,hN,?_⟩
  intro k q
  have hp := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hP k) q
  have hn := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hN k) q
  simpa only [compactify_test,Pair.evaluate] using (hp.sub hn).div_const 2

#print axioms embed_continuous
#print axioms compactify_mass
#print axioms compactify_test
#print axioms pair_subsequence
end
end UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
