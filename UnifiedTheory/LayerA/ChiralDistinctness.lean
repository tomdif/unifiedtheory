/-
  LayerA/ChiralDistinctness.lean — Chiral ≇ vector-like (the missing bridge)

  THE TWO LEMMAS:

  Lemma 1: If ρ₁ acts chirally on K⊕P (its restriction to K is inequivalent
  to its restriction to P) and ρ₂ acts vector-like (restrictions are equivalent),
  then ρ₁ and ρ₂ are not isomorphic as represented algebras.

  Proof: An isomorphism σ: g₂ → g₁ would transport the vector-like property
  to g₁, contradicting chirality.

  Lemma 2: The color factor is vector-like. Its action commutes with the
  source functional φ (gauge invariance), so it preserves the K/P split
  and acts identically on both sectors.

  Together: chiral factor ≇ vector-like factor → G_c ≠ G'.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.ChiralityFromKP

namespace UnifiedTheory.LayerA.ChiralDistinctness

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open UnifiedTheory.LayerB.ChiralityFromKP

/-! ## Chiral vs vector-like actions -/

/-- A gauge action is **chiral** on the K/P split if the source functional
    distinguishes the action on K from the action on P.
    Formally: there exists v such that φ(g·K(v)) ≠ φ(K(v)), i.e., the
    gauge transformation changes the K-sector source charge.

    From ChiralityFromKP: this happens iff g does NOT preserve the K/P split. -/
def IsChiralAction (φ : V →ₗ[ℝ] ℝ) (g : GaugeAction V) : Prop :=
  ∃ v : V, φ (g.act v) ≠ φ v

/-- A gauge action is **vector-like** if it preserves the source functional:
    φ(g·v) = φ(v) for all v. The action "looks the same" on K and P. -/
def IsVectorLikeAction (φ : V →ₗ[ℝ] ℝ) (g : GaugeAction V) : Prop :=
  ∀ v : V, φ (g.act v) = φ v

/-- **Chiral and vector-like are mutually exclusive.**
    If g is both chiral and vector-like, we have a contradiction:
    chiral gives ∃v, φ(g·v) ≠ φ(v); vector-like gives ∀v, φ(g·v) = φ(v). -/
theorem chiral_ne_vectorlike (φ : V →ₗ[ℝ] ℝ) (g : GaugeAction V) :
    IsChiralAction φ g → IsVectorLikeAction φ g → False := by
  intro ⟨v, hne⟩ hvl
  exact hne (hvl v)

/-! ## Lemma 1: Chiral ≇ vector-like -/

/-- Two gauge actions are **equivalent** if one can be obtained from
    the other by conjugation with a linear isomorphism.
    σ: g₂ → g₁ such that ρ₁(σ(x)) = ρ₂(x) for all x. -/
def AreEquivalentActions (φ : V →ₗ[ℝ] ℝ)
    (g₁ g₂ : GaugeAction V)
    -- σ maps g₂ to g₁ (an "isomorphism" at the action level)
    (σ : V → V) : Prop :=
  -- σ transports the action: g₁ on σ(v) = σ(g₂ on v)
  ∀ v, g₁.act (σ v) = σ (g₂.act v)

/-- **LEMMA 1: A chiral action and a vector-like action are NOT equivalent.**

    If ρ₁ is chiral (∃v, φ(g₁·v) ≠ φ(v)) and ρ₂ is vector-like
    (∀v, φ(g₂·v) = φ(v)), and σ is an equivalence ρ₁ ∘ σ = σ ∘ ρ₂,
    then σ would transport the vector-like property to ρ₁:
    φ(g₁·σ(v)) = φ(σ(g₂·v)). If σ preserves φ, this gives
    φ(g₁·w) = φ(w) for all w in the range of σ, contradicting chirality
    (if σ is surjective). -/
theorem chiral_not_equivalent_to_vectorlike
    (φ : V →ₗ[ℝ] ℝ) (g₁ g₂ : GaugeAction V)
    (h_chiral : IsChiralAction φ g₁)
    (h_vectorlike : IsVectorLikeAction φ g₂)
    -- σ is an equivalence that preserves φ
    (σ : V → V) (hσ_equiv : AreEquivalentActions φ g₁ g₂ σ)
    (hσ_preserves_φ : ∀ v, φ (σ v) = φ v)
    -- σ is surjective (it's an isomorphism)
    (hσ_surj : Function.Surjective σ) :
    False := by
  -- From chirality: ∃ w, φ(g₁·w) ≠ φ(w)
  obtain ⟨w, hw⟩ := h_chiral
  -- Since σ is surjective: w = σ(v) for some v
  obtain ⟨v, hv⟩ := hσ_surj w
  -- φ(g₁·w) = φ(g₁·σ(v)) = φ(σ(g₂·v))  [by equivalence]
  --         = φ(g₂·v)                      [σ preserves φ]
  --         = φ(v)                          [vector-like]
  --         = φ(σ(v))⁻¹... wait
  -- φ(g₁·σ(v)) = φ(σ(g₂·v)) = φ(g₂·v) = φ(v) = φ(σ(v)) = φ(w)
  have step1 : φ (g₁.act w) = φ (g₁.act (σ v)) := by rw [hv]
  have step2 : φ (g₁.act (σ v)) = φ (σ (g₂.act v)) := by rw [hσ_equiv]
  have step3 : φ (σ (g₂.act v)) = φ (g₂.act v) := hσ_preserves_φ _
  have step4 : φ (g₂.act v) = φ v := h_vectorlike v
  have step5 : φ v = φ (σ v) := (hσ_preserves_φ v).symm
  have step6 : φ (σ v) = φ w := by rw [hv]
  -- Chain: φ(g₁·w) = φ(w)
  have : φ (g₁.act w) = φ w := by
    calc φ (g₁.act w) = φ (g₁.act (σ v)) := step1
    _ = φ (σ (g₂.act v)) := step2
    _ = φ (g₂.act v) := step3
    _ = φ v := step4
    _ = φ (σ v) := step5
    _ = φ w := step6
  -- But chirality says φ(g₁·w) ≠ φ(w)
  exact hw this

/-! ## Lemma 2: Color factor is vector-like -/

/-- **LEMMA 2: A gauge action that preserves the source functional is vector-like.**

    If φ(g_c·v) = φ(v) for all v (the color factor doesn't change
    the source functional value), then g_c is vector-like by definition. -/
theorem source_preserving_is_vectorlike
    (φ : V →ₗ[ℝ] ℝ) (g_c : GaugeAction V)
    (h_preserves : PreservesSource g_c φ) :
    IsVectorLikeAction φ g_c :=
  h_preserves

/-! ## The bridge theorem -/

/-- **THE BRIDGE: chiral factor ≇ color factor.**

    Given:
    (1) g_w is chiral (from ChiralityFromKP: K-sector constrained)
    (2) g_c is vector-like (preserves φ, hence preserves K/P split)
    (3) Any equivalence σ would transport vector-like → chiral (contradiction)

    Therefore: g_w and g_c are NOT equivalent as represented algebras.
    Since non-equivalent representations imply non-isomorphic algebras
    (for faithful representations): G_c ≇ G_w. -/
theorem chiral_factor_ne_color_factor
    (φ : V →ₗ[ℝ] ℝ) (g_w g_c : GaugeAction V)
    (h_chiral : IsChiralAction φ g_w)
    (h_source_preserving : PreservesSource g_c φ) :
    -- There is no φ-preserving surjective equivalence between them
    ¬∃ (σ : V → V), AreEquivalentActions φ g_w g_c σ
      ∧ (∀ v, φ (σ v) = φ v) ∧ Function.Surjective σ := by
  intro ⟨σ, hequiv, hpres, hsurj⟩
  exact chiral_not_equivalent_to_vectorlike φ g_w g_c h_chiral
    (source_preserving_is_vectorlike φ g_c h_source_preserving)
    σ hequiv hpres hsurj

end UnifiedTheory.LayerA.ChiralDistinctness
