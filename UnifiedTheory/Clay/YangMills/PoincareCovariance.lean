/- Nonvacuous interfaces for a physical Poincare representation, together with
conditional consequences for translations and scalar observable correlations.
No representation satisfying these interfaces is constructed here. The joint
spectral condition, generators, and tensor-valued fields remain separate. -/
import UnifiedTheory.Clay.YangMills.PoincareTopology
import Mathlib.Analysis.InnerProductSpace.LinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PoincareCovariance
noncomputable section
open LocalFields PoincareKinematics PoincareTestAction PoincareTopology

def properTranslationHom : Multiplicative Spacetime →* ProperPoincare where
  toFun a := properTranslation a.toAdd
  map_one' := by
    apply Subtype.ext
    exact translation_zero
  map_mul' a b := by
    apply Subtype.ext
    exact translation_add a.toAdd b.toAdd

theorem properTranslation_add (a b : Spacetime) :
    properTranslation (a + b) = properTranslation a * properTranslation b :=
  properTranslationHom.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

theorem properTranslation_commute (a b : Spacetime) :
    Commute (properTranslation a) (properTranslation b) := by
  change properTranslation a * properTranslation b = properTranslation b * properTranslation a
  rw [← properTranslation_add, ← properTranslation_add, add_comm]

def lineTranslation (v : Spacetime) (t : ℝ) : ProperPoincare := properTranslation (t • v)

theorem lineTranslation_add (v : Spacetime) (s t : ℝ) :
    lineTranslation v (s + t) = lineTranslation v s * lineTranslation v t := by
  simp only [lineTranslation, add_smul, properTranslation_add]

theorem continuous_lineTranslation (v : Spacetime) : Continuous (lineTranslation v) :=
  continuous_properTranslation.comp (continuous_id.smul continuous_const)

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A candidate physical representation must be unitary, multiplicative, and
strongly continuous in the genuine coefficient topology on the proper
orthochronous spacetime group. There is deliberately no trivial witness. -/
structure StronglyContinuousUnitaryRepresentation where
  representation : ProperPoincare →* (H ≃ₗᵢ[ℂ] H)
  strong_continuity : ∀ u : H, Continuous (fun g => representation g u)

variable {H}

def translationRepresentation (U : StronglyContinuousUnitaryRepresentation H) :
    Multiplicative Spacetime →* (H ≃ₗᵢ[ℂ] H) :=
  U.representation.comp properTranslationHom

theorem strongly_continuous_translations (U : StronglyContinuousUnitaryRepresentation H)
    (u : H) : Continuous (fun a : Spacetime => U.representation (properTranslation a) u) :=
  (U.strong_continuity u).comp continuous_properTranslation

theorem strongly_continuous_line (U : StronglyContinuousUnitaryRepresentation H)
    (v : Spacetime) (u : H) :
    Continuous (fun t : ℝ => U.representation (lineTranslation v t) u) :=
  (U.strong_continuity u).comp (continuous_lineTranslation v)

theorem translation_operators_commute (U : StronglyContinuousUnitaryRepresentation H)
    (a b : Spacetime) :
    Commute (U.representation (properTranslation a))
      (U.representation (properTranslation b)) :=
  (properTranslation_commute a b).map U.representation

variable {Label : Type*} [CompleteSpace H] (S : FieldSystem Label H)

/-- A representation compatible with the chosen common field domain and
vacuum. These requirements do not follow from finite-chamber symmetries. -/
structure DomainRepresentation extends StronglyContinuousUnitaryRepresentation H where
  domain_invariant : ∀ (g : ProperPoincare) (u : S.domain), representation g (u : H) ∈ S.domain
  vacuum_invariant : ∀ g : ProperPoincare, representation g (S.vacuum : H) = S.vacuum

variable {S}

def domainAction (U : DomainRepresentation S) (g : ProperPoincare) :
    S.domain →ₗ[ℂ] S.domain where
  toFun u := ⟨U.representation g (u : H), U.domain_invariant g u⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (U.representation g) (u : H) (v : H)
  map_smul' c u := by
    apply Subtype.ext
    exact map_smul (U.representation g) c (u : H)

@[simp] theorem domainAction_coe (U : DomainRepresentation S) (g : ProperPoincare)
    (u : S.domain) : (domainAction U g u : H) = U.representation g (u : H) := rfl

@[simp] theorem domainAction_vacuum (U : DomainRepresentation S) (g : ProperPoincare) :
    domainAction U g S.vacuum = S.vacuum := by
  apply Subtype.ext
  exact U.vacuum_invariant g

/-- Covariance for scalar observable labels. Tensor and spinor multiplets
require their additional finite-dimensional Lorentz representation. -/
def ScalarCovariance (U : DomainRepresentation S) : Prop :=
  ∀ (g : ProperPoincare) (a : Label) (f : TestFunction) (u : S.domain),
    domainAction U g (S.field a f u) =
      S.field a (properTestAction g f) (domainAction U g u)

def transformWord (g : ProperPoincare) (w : List (Label × TestFunction)) :
    List (Label × TestFunction) :=
  w.map (fun af => (af.1, properTestAction g af.2))

theorem wordState_covariant (U : DomainRepresentation S) (hcov : ScalarCovariance U)
    (g : ProperPoincare) (w : List (Label × TestFunction)) :
    domainAction U g (wordState S w) = wordState S (transformWord g w) := by
  induction w with
  | nil => exact domainAction_vacuum U g
  | cons af w ih =>
    simp only [wordState, transformWord, List.map_cons]
    rw [hcov, ih]
    rfl

/-- Correlation invariance is a consequence of an actual covariant unitary
representation, domain preservation, and its invariant vacuum. -/
theorem vacuumCorrelation_covariant (U : DomainRepresentation S) (hcov : ScalarCovariance U)
    (g : ProperPoincare) (w : List (Label × TestFunction)) :
    vacuumCorrelation S (transformWord g w) = vacuumCorrelation S w := by
  unfold vacuumCorrelation
  rw [← wordState_covariant U hcov g w, domainAction_coe]
  have hinner := (U.representation g).inner_map_map (S.vacuum : H) (wordState S w : H)
  rw [U.vacuum_invariant] at hinner
  exact hinner

end
end UnifiedTheory.Clay.YangMills.PoincareCovariance
