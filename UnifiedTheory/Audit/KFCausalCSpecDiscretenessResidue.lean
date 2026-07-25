/-
  Audit/KFCausalCSpecDiscretenessResidue.lean   (Volume sector → goal C, derived signature)

  The discreteness signature, DERIVED from the same causal-set d'Alembertian `B` as goal
  B -- NOT postulated.  (A postulated propagation-defect term would sit in exactly the
  epistemic hole the goal-B derivation climbed out of.)

  Goal B took the leading order: `E[B_ρ φ] → □φ + κ R φ` as `ρ → ∞`, via the per-layer
  limits and two moment conditions.  The discreteness signature is the SUBLEADING residue
  of the SAME operator, one asymptotic order down.  Assume (same tiers, next order) that
  each per-layer contribution, after subtracting its continuum limit and rescaling by the
  discreteness scale `ε(ρ) = ρ^{-2/d} ~ ℓ²`, converges to a subleading coefficient `d_i`:

      (S_i(ρ) - [a_i φ + b_i (□φ + κ Rφ)]) / ε(ρ)  →  d_i.

  Using the SAME weights `w_i` and the SAME moment conditions `α + Σ w_i a_i = 0`,
  `Σ w_i b_i = 1` (so the continuum part cancels exactly), we DERIVE

      (E[B_ρ φ] - (□φ + κ Rφ)) / ε(ρ)  →  Σ_i w_i d_i,

  i.e. `E[B_ρ φ] = (□φ + κ Rφ) + ℓ² (Σ_i w_i d_i) + o(ℓ²)`.  The discreteness correction is
  the derived combination `Σ w_i d_i`, generically nonzero, scaling as `ℓ² = ρ^{-2/d}`.

  Because the sprinkling is Lorentz-invariant on average (unlike a lattice), this residue
  is a LORENTZ-INVARIANT discreteness effect: for a propagating mode it is a
  momentum-dependent correction to propagation of order `ℓ²`, the in-principle-observable
  handle -- and it is a consequence of `B`, not an added assumption.  (The specific
  magnitude needs the geometric `d_i`, from the same tier-1 volume expansion.)

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Filter Topology

namespace UnifiedTheory.Audit.KFCausalCSpecDiscretenessResidue

variable {J Γ : Type*}

/-- **Derived discreteness residue.**  From the per-layer subleading asymptotics
`(S_i - continuum_i)/ε → d_i` and the SAME goal-B moment conditions, the rescaled residue
of the mean causal-set d'Alembertian converges to the DERIVED defect `Σ_i w_i d_i`.  So
`E[B_ρ φ] = (□φ + κ Rφ) + ε(ρ)(Σ w_i d_i) + o(ε)` with `ε = ρ^{-2/d} ~ ℓ²`: the
discreteness correction is a consequence of `B`, not a postulate. -/
theorem bdg_discreteness_residue
    (l : Filter Γ) (s : Finset J)
    (M : Γ → ℝ) (Sfun : J → Γ → ℝ) (ε : Γ → ℝ)
    (w a b d : J → ℝ) (α κ φx boxφ Rφ : ℝ)
    (hM : ∀ γ, M γ = α * φx + ∑ i ∈ s, w i * Sfun i γ)
    (hcancel : α + ∑ i ∈ s, w i * a i = 0)
    (hnorm : ∑ i ∈ s, w i * b i = 1)
    (hres : ∀ i ∈ s, Tendsto
      (fun γ => (Sfun i γ - (a i * φx + b i * (boxφ + κ * Rφ))) / ε γ) l (𝓝 (d i))) :
    Tendsto (fun γ => (M γ - (boxφ + κ * Rφ)) / ε γ) l (𝓝 (∑ i ∈ s, w i * d i)) := by
  -- the SAME continuum collapse as goal B (leading moment conditions)
  have hval : α * φx + ∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ)) = boxφ + κ * Rφ := by
    have e1 : ∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ))
        = (∑ i ∈ s, w i * a i) * φx + (∑ i ∈ s, w i * b i) * (boxφ + κ * Rφ) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, hnorm, one_mul]
    have hz : α * φx + (∑ i ∈ s, w i * a i) * φx = 0 := by rw [← add_mul, hcancel, zero_mul]
    linarith [hz]
  -- the continuum part cancels exactly, so the rescaled residue IS the weighted rescaled sum
  have hfun : (fun γ => (M γ - (boxφ + κ * Rφ)) / ε γ)
      = fun γ => ∑ i ∈ s, w i * ((Sfun i γ - (a i * φx + b i * (boxφ + κ * Rφ))) / ε γ) := by
    funext γ
    have hnum : M γ - (boxφ + κ * Rφ)
        = ∑ i ∈ s, w i * (Sfun i γ - (a i * φx + b i * (boxφ + κ * Rφ))) := by
      rw [hM]
      have hexp : ∑ i ∈ s, w i * (Sfun i γ - (a i * φx + b i * (boxφ + κ * Rφ)))
          = ∑ i ∈ s, w i * Sfun i γ - ∑ i ∈ s, w i * (a i * φx + b i * (boxφ + κ * Rφ)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hexp]
      linarith [hval]
    rw [hnum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by rw [mul_div_assoc])
  rw [hfun]
  exact tendsto_finset_sum s (fun i hi => (hres i hi).const_mul (w i))

/-- **Standard-sign discreteness residue.**  With `κ = -1/2` (the BDG volume expansion),
the derived `ℓ²`-order correction sits on top of the correct continuum operator
`□φ - ½ R φ`. -/
theorem bdg_discreteness_residue_standard
    (l : Filter Γ) (s : Finset J)
    (M : Γ → ℝ) (Sfun : J → Γ → ℝ) (ε : Γ → ℝ)
    (w a b d : J → ℝ) (α φx boxφ Rφ : ℝ)
    (hM : ∀ γ, M γ = α * φx + ∑ i ∈ s, w i * Sfun i γ)
    (hcancel : α + ∑ i ∈ s, w i * a i = 0)
    (hnorm : ∑ i ∈ s, w i * b i = 1)
    (hres : ∀ i ∈ s, Tendsto
      (fun γ => (Sfun i γ - (a i * φx + b i * (boxφ + (-1 / 2 : ℝ) * Rφ))) / ε γ) l (𝓝 (d i))) :
    Tendsto (fun γ => (M γ - (boxφ - (1 / 2) * Rφ)) / ε γ) l (𝓝 (∑ i ∈ s, w i * d i)) := by
  have h := bdg_discreteness_residue l s M Sfun ε w a b d α (-1 / 2) φx boxφ Rφ
    hM hcancel hnorm hres
  have he : (boxφ + (-1 / 2 : ℝ) * Rφ) = boxφ - (1 / 2) * Rφ := by ring
  rwa [he] at h

#print axioms bdg_discreteness_residue
#print axioms bdg_discreteness_residue_standard

end UnifiedTheory.Audit.KFCausalCSpecDiscretenessResidue
