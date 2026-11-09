/- Restricting a compactified force limit to finite momentum. Tests that
vanish at the compactification boundary have exactly their real-line
integrals; possible endpoint mass is retained separately, not assumed zero. -/
import UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalLocalForceMeasure
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)

def interior : Set Spectrum := {x | -(Real.pi/2) < (x:ℝ) ∧ (x:ℝ) < Real.pi/2}

theorem interior_measurable : MeasurableSet interior :=
  measurableSet_Ioo.preimage continuous_subtype_val.measurable

theorem tangent_measurable : Measurable (fun x : Spectrum => Real.tan (x:ℝ)) := by
  simp only [Real.tan_eq_sin_div_cos]
  exact (Real.continuous_sin.comp continuous_subtype_val).measurable.div
    (Real.continuous_cos.comp continuous_subtype_val).measurable

def finitePart (μ : FiniteMeasure Spectrum) : FiniteMeasure ℝ :=
  (μ.restrict interior).map (fun x => Real.tan (x:ℝ))

theorem finitePart_mass (μ : FiniteMeasure Spectrum) : (finitePart μ).mass ≤ μ.mass :=
  (FiniteMeasure.mass_map_le _ _).trans
    (by rw [FiniteMeasure.restrict_mass]; exact μ.apply_mono (Set.subset_univ interior))

theorem finitePart_test (μ : FiniteMeasure Spectrum) (q : Spectrum →ᵇ ℂ)
    (hq : ∀ x, x ∉ interior → q x = 0) :
    (∫ p, pullback q p ∂(finitePart μ : Measure ℝ)) = ∫ x, q x ∂(μ : Measure Spectrum) := by
  change (∫ p, pullback q p ∂(((μ : Measure Spectrum).restrict interior).map
    (fun x : Spectrum => Real.tan (x:ℝ)))) = _
  rw [integral_map tangent_measurable.aemeasurable (pullback q).continuous.aestronglyMeasurable]
  calc
    _ = ∫ x in interior, q x ∂(μ : Measure Spectrum) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem interior_measurable] with x hx
      change q (embed (Real.tan (x:ℝ))) = q x
      congr 1
      apply Subtype.ext
      exact Real.arctan_tan hx.1 hx.2
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hq

def finitePair (P N : FiniteMeasure Spectrum) : FluxPair where
  positive := finitePart P
  negative := finitePart N
  positive_finite := inferInstance
  negative_finite := inferInstance

theorem finitePair_test (P N : FiniteMeasure Spectrum) (q : Spectrum →ᵇ ℂ)
    (hq : ∀ x, x ∉ interior → q x = 0) :
    (finitePair P N).evaluate (pullback q) =
      ((∫ x, q x ∂(P : Measure Spectrum))-(∫ x, q x ∂(N : Measure Spectrum)))/2 := by
  exact congrArg₂ (fun a b : ℂ => (a-b)/2) (finitePart_test P q hq) (finitePart_test N q hq)

theorem local_pair_subsequence {K : Type*} [Countable K] (F : ℕ → K → FluxPair)
    (hb : ∀ k, ∃ C : ℝ, ∀ᶠ n in atTop, (F n k).mass ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P N : K → FiniteMeasure Spectrum,
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).positive) atTop (𝓝 (P k))) ∧
      (∀ k, Tendsto (fun n => compactify (F (φ n) k).negative) atTop (𝓝 (N k))) ∧
      (∀ k (q : Spectrum →ᵇ ℂ), (∀ x, x ∉ interior → q x = 0) →
        Tendsto (fun n => (F (φ n) k).evaluate (pullback q)) atTop
          (𝓝 ((finitePair (P k) (N k)).evaluate (pullback q)))) := by
  obtain ⟨φ,hφ,P,N,hP,hN,hq⟩ := pair_subsequence F hb
  refine ⟨φ,hφ,P,N,hP,hN,?_⟩
  intro k q hbq
  rw [finitePair_test _ _ q hbq]
  exact hq k q

#print axioms interior_measurable
#print axioms tangent_measurable
#print axioms finitePart_mass
#print axioms finitePart_test
#print axioms finitePair_test
#print axioms local_pair_subsequence
end
end UnifiedTheory.Audit.KFCausalLocalForceMeasure
