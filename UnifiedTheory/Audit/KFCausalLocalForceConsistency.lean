/- Weak compactified force limits preserve interval addition and mass
bounds. Restriction to finite momentum preserves addition as well. -/
import UnifiedTheory.Audit.KFCausalWeakForceBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalLocalForceConsistency
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology NNReal
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure
open UnifiedTheory.Audit.KFCausalLocalForceMeasure

theorem compactify_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    compactify (μ+ν) = compactify μ + compactify ν := by
  apply FiniteMeasure.toMeasure_injective
  exact Measure.map_add _ _ embed_continuous.measurable

theorem finitePart_add (μ ν : FiniteMeasure Spectrum) :
    finitePart (μ+ν) = finitePart μ + finitePart ν := by
  apply FiniteMeasure.toMeasure_injective
  change (((μ:Measure Spectrum)+(ν:Measure Spectrum)).restrict interior).map _ = _
  rw [Measure.restrict_add,Measure.map_add _ _ tangent_measurable]
  rfl

theorem finitePair_mass_bound (P N : FiniteMeasure Spectrum) :
    (finitePair P N).mass ≤ (P.mass:ℝ)+(N.mass:ℝ) := by
  have hp := finitePart_mass P
  have hn := finitePart_mass N
  change ((finitePart P).mass:ℝ)+((finitePart N).mass:ℝ) ≤ _
  exact add_le_add (by exact_mod_cast hp) (by exact_mod_cast hn)

theorem finitePair_add_evaluate (P₁ P₂ N₁ N₂ : FiniteMeasure Spectrum)
    (q : ℝ →ᵇ ℂ) :
    (finitePair (P₁+P₂) (N₁+N₂)).evaluate q =
      (finitePair P₁ N₁).evaluate q + (finitePair P₂ N₂).evaluate q := by
  simp only [FluxPair.evaluate,finitePair,finitePart_add,FiniteMeasure.toMeasure_add]
  rw [integral_add_measure (q.integrable _) (q.integrable _),
    integral_add_measure (q.integrable _) (q.integrable _)]
  ring

theorem compact_limit_add {K : Type*} (F : ℕ → K → FluxPair) (P N : K → FiniteMeasure Spectrum)
    (hP : ∀ i, Tendsto (fun n => compactify (F n i).positive) atTop (𝓝 (P i)))
    (hN : ∀ i, Tendsto (fun n => compactify (F n i).negative) atTop (𝓝 (N i)))
    (i j l : K)
    (ha : ∀ n, (F n l).positive = (F n i).positive+(F n j).positive ∧
      (F n l).negative = (F n i).negative+(F n j).negative) :
    P l = P i+P j ∧ N l = N i+N j := by
  constructor
  · apply tendsto_nhds_unique (hP l)
    convert (hP i).add (hP j) using 1
    funext n
    apply FiniteMeasure.toMeasure_injective
    change (F n l).positive.map embed = (F n i).positive.map embed + (F n j).positive.map embed
    rw [(ha n).1,Measure.map_add _ _ embed_continuous.measurable]
  · apply tendsto_nhds_unique (hN l)
    convert (hN i).add (hN j) using 1
    funext n
    apply FiniteMeasure.toMeasure_injective
    change (F n l).negative.map embed = (F n i).negative.map embed + (F n j).negative.map embed
    rw [(ha n).2,Measure.map_add _ _ embed_continuous.measurable]

theorem compact_limit_mass_bound (F : ℕ → FluxPair) (P N : FiniteMeasure Spectrum)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (C : ℝ) (hb : ∀ᶠ n in atTop, (F n).mass ≤ C) :
    (P.mass:ℝ)+(N.mass:ℝ) ≤ C := by
  have hp := (NNReal.continuous_coe.tendsto P.mass).comp hP.mass
  have hn := (NNReal.continuous_coe.tendsto N.mass).comp hN.mass
  apply le_of_tendsto (hp.add hn)
  simpa only [Function.comp_apply,compactify_mass,FluxPair.mass] using hb

theorem local_limit_mass_bound (F : ℕ → FluxPair) (P N : FiniteMeasure Spectrum)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (C : ℝ) (hb : ∀ᶠ n in atTop, (F n).mass ≤ C) :
    (finitePair P N).mass ≤ C :=
  (finitePair_mass_bound P N).trans (compact_limit_mass_bound F P N hP hN C hb)

#print axioms compactify_add
#print axioms finitePart_add
#print axioms finitePair_mass_bound
#print axioms finitePair_add_evaluate
#print axioms compact_limit_add
#print axioms compact_limit_mass_bound
#print axioms local_limit_mass_bound
end
end UnifiedTheory.Audit.KFCausalLocalForceConsistency
