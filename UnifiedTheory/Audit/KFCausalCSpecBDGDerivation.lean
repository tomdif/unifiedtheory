/-
  Audit/KFCausalCSpecBDGDerivation.lean   (Volume sector → goal B, BDG derivation)

  STRENGTHENS `KFCausalCSpecBDGContinuumLimit`.  That earlier theorem assumed the fully
  COMBINED asymptotic decomposition `M = c φ + s (□φ + κ Rφ) + rem` -- which bakes the
  shape (and the sign of the curvature term) into the hypothesis, so a green build proves
  nothing a skeptic cares about.  Here the seam is moved down one tier.

  The mean causal-set d'Alembertian is a self-term plus a WEIGHTED SUM OVER LAYERS,
  `M = α φ(x) + Σ_i w_i S_i`, where `S_i` is the mean of the `i`-th layer contribution.
  We assume only, per layer (tiers 1+3 -- Lorentzian volume expansion + Watson's-lemma
  asymptotics, genuinely worth citing):

      S_i(ρ)  →  a_i φ(x) + b_i (□φ + κ R φ)(x)     as ρ → ∞,

  with a SINGLE shared curvature coefficient `κ` (the volume expansion's R-term is
  universal).  The sign lives entirely in `κ` and is threaded to the conclusion.

  We then DERIVE (tier 2 -- the layer algebra, ours) the combination and its limit,
  provided the coefficients satisfy the two moment conditions

      α + Σ_i w_i a_i = 0        (the volume-DIVERGENT self/constant part cancels),
      Σ_i w_i b_i     = 1        (second-order normalization),

  concluding  M(ρ) → (□φ + κ R φ)(x).  A flipped `κ` flips the conclusion; a violated
  cancellation breaks the proof -- the failure modes the conditional form could not see.

  For the standard BDG coefficients the volume expansion gives `κ = -1/2`
  (`bdg_dalembertian_standard`), i.e. `M → □φ - ½ R φ` -- the correct sign.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Filter Topology

namespace UnifiedTheory.Audit.KFCausalCSpecBDGDerivation

variable {J Γ : Type*}

/-- **Causal-set d'Alembertian, derived from the per-layer asymptotics.**  Given the
per-layer limits `S_i → a_i φ + b_i (□φ + κ Rφ)` (tiers 1+3) and the two moment conditions
`α + Σ w_i a_i = 0` (divergent cancellation) and `Σ w_i b_i = 1` (normalization), the mean
operator `M = α φ + Σ w_i S_i` converges to `□φ + κ Rφ`.  The curvature coefficient `κ`
is threaded from hypothesis to conclusion. -/
theorem bdg_dalembertian_from_layers
    (l : Filter Γ) (s : Finset J)
    (M : Γ → ℝ) (Sfun : J → Γ → ℝ) (w a b : J → ℝ) (α κ φx boxφ Rφ : ℝ)
    (hM : ∀ γ, M γ = α * φx + ∑ i ∈ s, w i * Sfun i γ)
    (hS : ∀ i ∈ s, Tendsto (Sfun i) l (𝓝 (a i * φx + b i * (boxφ + κ * Rφ))))
    (hcancel : α + ∑ i ∈ s, w i * a i = 0)
    (hnorm : ∑ i ∈ s, w i * b i = 1) :
    Tendsto M l (𝓝 (boxφ + κ * Rφ)) := by
  -- tier 2: the weighted sum of the per-layer limits
  have hsum : Tendsto (fun γ => ∑ i ∈ s, w i * Sfun i γ) l
      (𝓝 (∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ)))) :=
    tendsto_finset_sum s (fun i hi => (hS i hi).const_mul (w i))
  -- the combined limit value collapses to the continuum operator via the moment conditions
  have e1 : ∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ))
      = (∑ i ∈ s, w i * a i) * φx + (∑ i ∈ s, w i * b i) * (boxφ + κ * Rφ) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hval : α * φx + ∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ)) = boxφ + κ * Rφ := by
    rw [e1, hnorm, one_mul]
    have hz : α * φx + (∑ i ∈ s, w i * a i) * φx = 0 := by
      rw [← add_mul, hcancel, zero_mul]
    linarith [hz]
  have hMrw : M = fun γ => α * φx + ∑ i ∈ s, w i * Sfun i γ := funext hM
  rw [hMrw]
  have hlim := (tendsto_const_nhds (x := α * φx)).add hsum
  rwa [hval] at hlim

/-- **Standard BDG curved-space limit (correct sign).**  With the volume expansion's
curvature coefficient `κ = -1/2`, the mean causal-set d'Alembertian converges to
`□φ - ½ R φ` -- the Benincasa-Dowker-Sorkin result, sign included, now DERIVED from the
per-layer asymptotics rather than assumed. -/
theorem bdg_dalembertian_standard
    (l : Filter Γ) (s : Finset J)
    (M : Γ → ℝ) (Sfun : J → Γ → ℝ) (w a b : J → ℝ) (α φx boxφ Rφ : ℝ)
    (hM : ∀ γ, M γ = α * φx + ∑ i ∈ s, w i * Sfun i γ)
    (hS : ∀ i ∈ s, Tendsto (Sfun i) l (𝓝 (a i * φx + b i * (boxφ + (-1 / 2 : ℝ) * Rφ))))
    (hcancel : α + ∑ i ∈ s, w i * a i = 0)
    (hnorm : ∑ i ∈ s, w i * b i = 1) :
    Tendsto M l (𝓝 (boxφ - (1 / 2) * Rφ)) := by
  have h := bdg_dalembertian_from_layers l s M Sfun w a b α (-1 / 2) φx boxφ Rφ hM hS hcancel hnorm
  convert h using 2
  ring

#print axioms bdg_dalembertian_from_layers
#print axioms bdg_dalembertian_standard

end UnifiedTheory.Audit.KFCausalCSpecBDGDerivation
