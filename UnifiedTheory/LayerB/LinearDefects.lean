/-
  LayerB/LinearDefects.lean — Derive defect algebra from linearity

  The previous DefectBlock/ComposableDefectBlock STIPULATED:
    - sourceMatchesBias (per-defect)
    - dressingNeutral (per-defect)
    - compose_K_additive
    - compose_bias_additive
    - conjugate_K_neg
    - conjugate_bias_neg

  This file DERIVES all of them from five primitives:
    1. Defects are perturbations in a vector space V
    2. K_proj, P_proj are linear projections with K + P = id
    3. source_func, bias_func are linear functionals
    4. Bridge: source_func ∘ K_proj = biasScale • bias_func (ONE equation)
    5. Neutrality: source_func ∘ P_proj = 0 (ONE equation)
    6. Composition = addition of perturbations
    7. Conjugation = negation of perturbation

  From these, ALL Layer B algebra follows by linearity.
  No per-defect stipulations. Real mathematical derivation.
-/
import UnifiedTheory.LayerB.DefectComposition

namespace UnifiedTheory.LayerB

open LayerA

/-! ### The primitive structure -/

/-- A defect block where ALL algebra derives from linearity.
    Defects are perturbations; projections and functionals are linear. -/
structure LinearDefectBlock (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Type of defects -/
  Defect : Type*
  /-- Each defect is a perturbation in V -/
  perturbation : Defect → V
  /-- Stability predicate -/
  Stable : Defect → Prop
  /-- Source (K-channel) projection -/
  K_proj : V →ₗ[ℝ] V
  /-- Dressing (P-channel) projection -/
  P_proj : V →ₗ[ℝ] V
  /-- K + P = id (decomposition) -/
  decomp : ∀ v : V, v = K_proj v + P_proj v
  /-- Source strength functional -/
  source_func : V →ₗ[ℝ] ℝ
  /-- Focusing bias functional -/
  bias_func : V →ₗ[ℝ] ℝ
  /-- Bias scale factor -/
  biasScale : ℝ
  /-- THE BRIDGE: source of K-part = scaled bias (ONE structural equation) -/
  bridge : ∀ v : V, source_func (K_proj v) = biasScale * bias_func v
  /-- NEUTRALITY: source vanishes on P-part (ONE structural equation) -/
  neutral : ∀ v : V, source_func (P_proj v) = 0
  /-- Composition = addition of perturbations -/
  compose : Defect → Defect → Defect
  compose_pert : ∀ d₁ d₂, perturbation (compose d₁ d₂) = perturbation d₁ + perturbation d₂
  /-- Conjugation = negation of perturbation -/
  conjugate : Defect → Defect
  conjugate_pert : ∀ d, perturbation (conjugate d) = -(perturbation d)
  /-- Stability preservation -/
  compose_stable : ∀ d₁ d₂, Stable d₁ → Stable d₂ → Stable (compose d₁ d₂)
  conjugate_stable : ∀ d, Stable d → Stable (conjugate d)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (lb : LinearDefectBlock V)

/-! ### Derived BF and null projections -/

/-- BF data derived from linear projections. -/
def LinearDefectBlock.toBF (d : lb.Defect) : BFDefectData V where
  Kpart := lb.K_proj (lb.perturbation d)
  Ppart := lb.P_proj (lb.perturbation d)

/-- Null data derived from bias functional. -/
def LinearDefectBlock.toNull (d : lb.Defect) : NullDefectData where
  bias := lb.bias_func (lb.perturbation d)

/-- Source measure derived from source functional. -/
def LinearDefectBlock.sourceMeas : SourceMeasure V where
  measure := lb.source_func

/-! ### DERIVE the source-bias bridge (was an axiom, now a theorem) -/

/-- **Bridge theorem (DERIVED)**: source strength of K-part equals
    scaled bias, for EVERY defect. Follows from the single structural
    equation `bridge` applied to the defect's perturbation. -/
theorem LinearDefectBlock.sourceMatchesBias_derived (d : lb.Defect) (_ : lb.Stable d) :
    lb.source_func (lb.K_proj (lb.perturbation d)) =
    biasMeasure (lb.toNull d) lb.biasScale := by
  simp only [LinearDefectBlock.toNull, biasMeasure]
  exact lb.bridge (lb.perturbation d)

/-! ### DERIVE dressing neutrality (was an axiom, now a theorem) -/

/-- **Dressing neutrality (DERIVED)**: P-part has zero source strength.
    Follows from the single equation `neutral`. -/
theorem LinearDefectBlock.dressingNeutral_derived (d : lb.Defect) (_ : lb.Stable d) :
    lb.source_func (lb.P_proj (lb.perturbation d)) = 0 :=
  lb.neutral (lb.perturbation d)

/-! ### DERIVE charge additivity (was an axiom, now a theorem) -/

/-- **Charge additivity (DERIVED)**: follows from linearity of
    source_func and K_proj, plus composition = addition.
    NOT stipulated — derived from linearity. -/
theorem LinearDefectBlock.charge_additive_derived (d₁ d₂ : lb.Defect) :
    lb.source_func (lb.K_proj (lb.perturbation (lb.compose d₁ d₂))) =
    lb.source_func (lb.K_proj (lb.perturbation d₁)) +
    lb.source_func (lb.K_proj (lb.perturbation d₂)) := by
  rw [lb.compose_pert, map_add, map_add]

/-- **Bias additivity (DERIVED)**: follows from linearity of bias_func. -/
theorem LinearDefectBlock.bias_additive_derived (d₁ d₂ : lb.Defect) :
    lb.bias_func (lb.perturbation (lb.compose d₁ d₂)) =
    lb.bias_func (lb.perturbation d₁) + lb.bias_func (lb.perturbation d₂) := by
  rw [lb.compose_pert, map_add]

/-! ### DERIVE conjugation properties (were axioms, now theorems) -/

/-- **Conjugate negates charge (DERIVED)**: from linearity + negation. -/
theorem LinearDefectBlock.conjugate_K_neg_derived (d : lb.Defect) :
    lb.source_func (lb.K_proj (lb.perturbation (lb.conjugate d))) =
    -(lb.source_func (lb.K_proj (lb.perturbation d))) := by
  rw [lb.conjugate_pert, map_neg, map_neg]

/-- **Conjugate negates bias (DERIVED)**: from linearity + negation. -/
theorem LinearDefectBlock.conjugate_bias_neg_derived (d : lb.Defect) :
    lb.bias_func (lb.perturbation (lb.conjugate d)) =
    -(lb.bias_func (lb.perturbation d)) := by
  rw [lb.conjugate_pert, map_neg]

/-! ### Construct ComposableDefectBlock from LinearDefectBlock -/

/-- **Every LinearDefectBlock gives a ComposableDefectBlock.**
    All fields that were previously axioms are now derived from linearity.
    This is the key theorem: the defect algebra is a CONSEQUENCE of
    linear structure, not an independent postulate. -/
noncomputable def LinearDefectBlock.toComposable : ComposableDefectBlock V where
  Defect := lb.Defect
  Stable := lb.Stable
  toBF := lb.toBF
  toNull := lb.toNull
  sourceMeas := lb.sourceMeas
  biasScale := lb.biasScale
  sourceMatchesBias := fun d hd => by
    show lb.source_func (lb.K_proj (lb.perturbation d)) =
         biasMeasure (lb.toNull d) lb.biasScale
    exact lb.sourceMatchesBias_derived d hd
  dressingNeutral := fun d hd => by
    show lb.source_func (lb.P_proj (lb.perturbation d)) = 0
    exact lb.dressingNeutral_derived d hd
  compose := lb.compose
  compose_stable := lb.compose_stable
  compose_K_additive := fun d₁ d₂ => by
    show lb.source_func (lb.K_proj (lb.perturbation (lb.compose d₁ d₂))) =
         lb.source_func (lb.K_proj (lb.perturbation d₁)) +
         lb.source_func (lb.K_proj (lb.perturbation d₂))
    exact lb.charge_additive_derived d₁ d₂
  compose_bias_additive := fun d₁ d₂ => by
    show lb.bias_func (lb.perturbation (lb.compose d₁ d₂)) =
         lb.bias_func (lb.perturbation d₁) + lb.bias_func (lb.perturbation d₂)
    exact lb.bias_additive_derived d₁ d₂
  conjugate := lb.conjugate
  conjugate_stable := lb.conjugate_stable
  conjugate_K_neg := fun d => by
    show lb.source_func (lb.K_proj (lb.perturbation (lb.conjugate d))) =
         -(lb.source_func (lb.K_proj (lb.perturbation d)))
    exact lb.conjugate_K_neg_derived d
  conjugate_bias_neg := fun d => by
    show lb.bias_func (lb.perturbation (lb.conjugate d)) =
         -(lb.bias_func (lb.perturbation d))
    exact lb.conjugate_bias_neg_derived d

/-! ### The derivation theorem -/

/-- **Linearity derivation theorem.**
    The entire defect charge algebra — additivity, conjugation,
    bridge, neutrality — is a CONSEQUENCE of:
    (1) Perturbations live in a vector space
    (2) Projections and functionals are linear
    (3) One bridge equation: source ∘ K_proj = scale • bias
    (4) One neutrality equation: source ∘ P_proj = 0
    (5) Composition = addition, conjugation = negation

    No per-defect stipulations needed. -/
theorem linearity_derives_all (lb : LinearDefectBlock V) :
    let db := lb.toComposable
    -- Bridge holds for all defects
    (∀ d, lb.Stable d →
      db.sourceMeas.measure (db.toBF d).Kpart =
      biasMeasure (db.toNull d) db.biasScale)
    -- Dressing neutrality holds
    ∧ (∀ d, lb.Stable d →
        db.sourceMeas.measure (db.toBF d).Ppart = 0)
    -- Charge is additive
    ∧ (∀ d₁ d₂,
        db.sourceMeas.measure (db.toBF (db.compose d₁ d₂)).Kpart =
        db.sourceMeas.measure (db.toBF d₁).Kpart +
        db.sourceMeas.measure (db.toBF d₂).Kpart)
    -- Conjugate negates charge
    ∧ (∀ d,
        db.sourceMeas.measure (db.toBF (db.conjugate d)).Kpart =
        -(db.sourceMeas.measure (db.toBF d).Kpart)) := by
  exact ⟨
    fun d hd => lb.sourceMatchesBias_derived d hd,
    fun d hd => lb.dressingNeutral_derived d hd,
    fun d₁ d₂ => lb.charge_additive_derived d₁ d₂,
    fun d => lb.conjugate_K_neg_derived d
  ⟩

end UnifiedTheory.LayerB
