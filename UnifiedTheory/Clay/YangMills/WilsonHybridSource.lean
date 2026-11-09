/- Hybrid approximation of the actual retained Wilson insertion. The
good-region estimate is a premise: no SU(2) Haar asymptotic remainder or
continuum existence theorem is asserted here. Exact later integrations
use the induced interacting action and its actual marginal probability. -/
import UnifiedTheory.Clay.YangMills.HybridSourceApproximation
import UnifiedTheory.Clay.YangMills.WilsonCrossCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonHybridSource
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonBlockMarginal
open WilsonCrossCovariance HybridSourceApproximation

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def hybridSource (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (b : Outside (G := G) S) : ℝ :=
  hybrid r₀ r₁ (r b) (retainedSource n G χ β c S f b) (P b)

def residualSource (χ : G → ℂ) (β c : ℝ) (S : Finset (Edge (Vertex n)))
    (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (b : Outside (G := G) S) : ℝ :=
  retainedSource n G χ β c S f b - hybridSource n G χ β c S f r₀ r₁ r P b

theorem retainedLaw_probability (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) : IsProbabilityMeasure (retainedLaw n G χ β c S) :=
  GibbsMarginalTower.marginal_probability _ _ _
    (splitAction_continuous n G χ hχ β c S)

theorem hybridSource_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (hr : Continuous r) (hP : Continuous P) :
    Continuous (hybridSource n G χ β c S f r₀ r₁ r P) :=
  hybrid_continuous r₀ r₁ r _ P hr (retainedSource_continuous n G χ hχ β c S f) hP

theorem residualSource_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (hr : Continuous r) (hP : Continuous P) :
    Continuous (residualSource n G χ β c S f r₀ r₁ r P) :=
  (retainedSource_continuous n G χ hχ β c S f).sub
    (hybridSource_continuous n G χ hχ β c S f r₀ r₁ r P hr hP)

omit [SecondCountableTopology G] in
theorem hybridSource_eq_exact (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (hcut : r₀ < r₁) (r P : Outside (G := G) S → ℝ)
    (b : Outside (G := G) S) (hb : r b ≤ r₀) :
    hybridSource n G χ β c S f r₀ r₁ r P b = retainedSource n G χ β c S f b :=
  hybrid_eq_exact r₀ r₁ (r b) hcut hb _ _

omit [SecondCountableTopology G] in
theorem hybridSource_eq_approximation (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (hcut : r₀ < r₁) (r P : Outside (G := G) S → ℝ)
    (b : Outside (G := G) S) (hb : r₁ ≤ r b) :
    hybridSource n G χ β c S f r₀ r₁ r P b = P b :=
  hybrid_eq_approximation r₀ r₁ (r b) hcut hb _ _

omit [SecondCountableTopology G] in
theorem residualSource_identity (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (b : Outside (G := G) S) :
    residualSource n G χ β c S f r₀ r₁ r P b =
      cutoff r₀ r₁ (r b) * (retainedSource n G χ β c S f b - P b) :=
  hybrid_error_identity r₀ r₁ (r b) _ _

omit [SecondCountableTopology G] in
/-- The removed conditional fluctuation is kept separate from the
retained approximation residual. -/
theorem original_error_decomposition (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ : ℝ)
    (r P : Outside (G := G) S → ℝ) (U : Configuration (Vertex n) G) :
    WilsonBlockIntegration.source n G χ c f U -
        hybridSource n G χ β c S f r₀ r₁ r P ((assemble S).symm U).1 =
      removedSource n G χ β c S f U +
        residualSource n G χ β c S f r₀ r₁ r P ((assemble S).symm U).1 := by
  unfold removedSource residualSource
  ring

omit [SecondCountableTopology G] in
/-- A supplied good-region bound controls the actual retained residual
globally, because the exact response is retained below the cutoff. -/
theorem residualSource_abs_le (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ ε : ℝ)
    (hcut : r₀ < r₁) (hε : 0 ≤ ε) (r P : Outside (G := G) S → ℝ)
    (hgood : ∀ b, r₀ ≤ r b → |retainedSource n G χ β c S f b - P b| ≤ ε)
    (b : Outside (G := G) S) :
    |residualSource n G χ β c S f r₀ r₁ r P b| ≤ ε := by
  simpa only [Real.norm_eq_abs] using
    hybrid_error_le r₀ r₁ (r b) ε hcut hε
      (retainedSource n G χ β c S f b) (P b) (hgood b)

omit [SecondCountableTopology G] in
theorem residualSource_sq_le (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ ε : ℝ)
    (hcut : r₀ < r₁) (hε : 0 ≤ ε) (r P : Outside (G := G) S → ℝ)
    (hgood : ∀ b, r₀ ≤ r b → |retainedSource n G χ β c S f b - P b| ≤ ε)
    (b : Outside (G := G) S) :
    (residualSource n G χ β c S f r₀ r₁ r P b)^2 ≤ ε^2 := by
  have h := residualSource_abs_le n G χ β c S f r₀ r₁ ε hcut hε r P hgood b
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε).2 h

/-- This square error is integrated against the actual correlated Wilson
marginal, with no auxiliary product-law comparison. -/
theorem retained_error_l2_bound (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (f : PlaquetteIndex n → ℝ) (r₀ r₁ ε : ℝ)
    (hcut : r₀ < r₁) (hε : 0 ≤ ε) (r P : Outside (G := G) S → ℝ)
    (hr : Continuous r) (hP : Continuous P)
    (hgood : ∀ b, r₀ ≤ r b → |retainedSource n G χ β c S f b - P b| ≤ ε) :
    (∫ b, (residualSource n G χ β c S f r₀ r₁ r P b)^2
      ∂retainedLaw n G χ β c S) ≤ ε^2 := by
  letI := retainedLaw_probability n G χ hχ β c S
  have hc := (residualSource_continuous n G χ hχ β c S f r₀ r₁ r P hr hP).pow 2
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := retainedLaw n G χ β c S)
  calc
    _ ≤ ∫ _b : Outside (G := G) S, ε^2 ∂retainedLaw n G χ β c S :=
      integral_mono hi (integrable_const _) (residualSource_sq_le n G χ β c S f r₀ r₁ ε
        hcut hε r P hgood)
    _ = ε^2 := by simp

omit [SecondCountableTopology G] in
/-- The first response in a second coordinate split is exactly the same
retained Wilson source, evaluated in those coordinates. -/
theorem firstResponse_source (χ : G → ℂ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (f : PlaquetteIndex n → ℝ) (p : Outside (G := G) T × Inside (G := G) T) :
    firstResponse n G χ β c S T (WilsonBlockIntegration.source n G χ c f) p =
      retainedSource n G χ β c S f (assemble T p) := rfl

/-- The hybrid error remains bounded after a second exact elimination
under the induced action. This is nonexpansion, not a strict contraction. -/
theorem second_error_l2_bound (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ)
    (S : Finset (Edge (Vertex n))) (T : Finset {e : Edge (Vertex n) // e ∉ S})
    (f : PlaquetteIndex n → ℝ) (r₀ r₁ ε : ℝ) (hcut : r₀ < r₁) (hε : 0 ≤ ε)
    (r P : Outside (G := G) S → ℝ) (hr : Continuous r) (hP : Continuous P)
    (hgood : ∀ b, r₀ ≤ r b → |retainedSource n G χ β c S f b - P b| ≤ ε) :
    (∫ z, (secondResponse n G χ β c S T
        (firstResponse n G χ β c S T (WilsonBlockIntegration.source n G χ c f)) z -
      secondResponse n G χ β c S T
        (hybridSource n G χ β c S f r₀ r₁ r P ∘ assemble T) z)^2
      ∂secondMarginal n G χ β c S T) ≤ ε^2 := by
  have hF := WilsonBlockIntegration.source_continuous n G χ hχ c f
  have hH := (hybridSource_continuous n G χ hχ β c S f r₀ r₁ r P hr hP).comp
    (assemble_continuous T)
  have h := wilson_nested_residual_bound n G χ hχ β c S T _ hF _ hH 0
  simp only [sub_zero, firstResponse_source, Function.comp_apply] at h
  apply h.trans
  letI : IsProbabilityMeasure (firstMarginal n G χ β c S T) :=
    GibbsMarginalTower.marginal_probability _ _ _
      (splitActionTwo_continuous n G χ hχ β c S T)
  have hi := (((residualSource_continuous n G χ hχ β c S f r₀ r₁ r P hr hP).comp
    (assemble_continuous T)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := firstMarginal n G χ β c S T)
  calc
    _ ≤ ∫ _p : Outside (G := G) T × Inside (G := G) T, ε^2
        ∂firstMarginal n G χ β c S T :=
      integral_mono hi (integrable_const _) (fun p =>
        residualSource_sq_le n G χ β c S f r₀ r₁ ε hcut hε r P hgood (assemble T p))
    _ = ε^2 := by simp

end
end UnifiedTheory.Clay.YangMills.WilsonHybridSource
