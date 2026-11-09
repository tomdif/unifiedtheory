/- Compactified finite momentum measures retain possible escaped mass at
the two endpoints. A common subsequence is derived for every countable
family with eventual mass bounds. No tightness on the real line is assumed. -/
import UnifiedTheory.Audit.KFCausalCompactFiniteMeasureSubsequence
import UnifiedTheory.Audit.KFCausalNeutralForceMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)

abbrev Spectrum := Set.Icc (-(Real.pi/2)) (Real.pi/2)

instance : Nonempty Spectrum := ⟨⟨0,by constructor <;> linarith [Real.pi_pos]⟩⟩

def embed (p : ℝ) : Spectrum :=
  ⟨Real.arctan p,⟨(Real.neg_pi_div_two_lt_arctan p).le,(Real.arctan_lt_pi_div_two p).le⟩⟩

theorem embed_continuous : Continuous embed := Real.continuous_arctan.subtype_mk _

def compactify (μ : Measure ℝ) [IsFiniteMeasure μ] : FiniteMeasure Spectrum :=
  ⟨μ.map embed,Measure.isFiniteMeasure_map μ embed⟩

theorem compactify_mass (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ((compactify μ).mass : ℝ) = μ.real Set.univ := by
  change (μ.map embed).real Set.univ = _
  rw [Measure.real,Measure.map_apply embed_continuous.measurable MeasurableSet.univ,Set.preimage_univ]
  rfl

def pullback (q : Spectrum →ᵇ ℂ) : ℝ →ᵇ ℂ := q.compContinuous ⟨embed,embed_continuous⟩

theorem compactify_test (μ : Measure ℝ) [IsFiniteMeasure μ] (q : Spectrum →ᵇ ℂ) :
    (∫ x, q x ∂(compactify μ : Measure Spectrum)) = ∫ p, pullback q p ∂μ := by
  exact integral_map embed_continuous.measurable.aemeasurable q.continuous.aestronglyMeasurable

theorem pair_subsequence {K : Type*} [Countable K] (F : ℕ → K → FluxPair)
    (hb : ∀ k, ∃ C : ℝ, ∀ᶠ n in atTop, (F n k).mass ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P N : K → FiniteMeasure Spectrum,
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).positive) atTop (𝓝 (P k))) ∧
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).negative) atTop (𝓝 (N k))) ∧
      (∀ k (q : Spectrum →ᵇ ℂ), Tendsto (fun n => (F (φ n) k).evaluate (pullback q)) atTop
        (𝓝 (((∫ x, q x ∂(P k : Measure Spectrum))-(∫ x, q x ∂(N k : Measure Spectrum)))/2))) := by
  let M (n : ℕ) (j : Bool × K) : FiniteMeasure Spectrum :=
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
  simpa only [compactify_test,FluxPair.evaluate] using (hp.sub hn).div_const 2

#print axioms embed_continuous
#print axioms compactify_mass
#print axioms compactify_test
#print axioms pair_subsequence
end
end UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
