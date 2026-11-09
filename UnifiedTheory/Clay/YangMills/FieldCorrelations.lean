/- Support, adjoint and local-exchange identities for full-domain field
correlations. The locality and adjoint laws remain hypotheses on a candidate. -/
import UnifiedTheory.Clay.YangMills.FieldAdjoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FieldCorrelations
noncomputable section
open UnifiedTheory.Clay.YangMills.LocalFields UnifiedTheory.Clay.YangMills.FieldAdjoints

theorem conjugation_support (f : TestFunction) :
    Function.support (testConjugation f) = Function.support f := by
  ext x
  simp [Function.mem_support, testConjugation_apply]

theorem conjugation_tsupport (f : TestFunction) : tsupport (testConjugation f) = tsupport f := by
  change closure (Function.support (testConjugation f)) = closure (Function.support f)
  rw [conjugation_support]

theorem spacelike_conjugation (f g : TestFunction) (h : SpacelikeSeparated f g) :
    SpacelikeSeparated (testConjugation f) (testConjugation g) := by
  simpa only [SpacelikeSeparated, conjugation_tsupport] using h

variable {Label H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjointWord_append (adj : Label → Label) (w v : List (Label × TestFunction)) :
    adjointWord adj (w ++ v) = adjointWord adj v ++ adjointWord adj w := by
  simp [adjointWord]

theorem adjointWord_involutive (adj : Label → Label) (ha : Function.Involutive adj) :
    Function.Involutive (adjointWord adj) := by
  intro w
  induction w with
  | nil => rfl
  | cons af w hw =>
    rcases af with ⟨a, f⟩
    rw [adjointWord_cons, adjointWord_append, hw]
    simp [adjointWord, ha a, testConjugation_involutive f]

theorem correlation_conjugate (S : FieldSystem Label H) (adj : Label → Label)
    (h : AdjointCompatible S adj) (w : List (Label × TestFunction)) :
    vacuumCorrelation S (adjointWord adj w) = star (vacuumCorrelation S w) := by
  have he := correlation_as_inner S adj h w []
  simp only [List.append_nil, wordState] at he
  rw [he]
  exact (inner_conj_symm (𝕜 := ℂ) (wordState S w : H) (S.vacuum : H)).symm

theorem wordAction_local_exchange (S : FieldSystem Label H) (h : Locality S)
    (left right : List (Label × TestFunction)) (a b : Label) (f g : TestFunction)
    (hs : SpacelikeSeparated f g) (u : S.domain) :
    wordAction S (left ++ (a, f) :: (b, g) :: right) u =
      wordAction S (left ++ (b, g) :: (a, f) :: right) u := by
  rw [wordAction_append, wordAction_append]
  change wordAction S left (S.field a f (S.field b g (wordAction S right u))) =
    wordAction S left (S.field b g (S.field a f (wordAction S right u)))
  rw [h a b f g hs]

theorem correlation_local_exchange (S : FieldSystem Label H) (h : Locality S)
    (left right : List (Label × TestFunction)) (a b : Label) (f g : TestFunction)
    (hs : SpacelikeSeparated f g) :
    vacuumCorrelation S (left ++ (a, f) :: (b, g) :: right) =
      vacuumCorrelation S (left ++ (b, g) :: (a, f) :: right) := by
  unfold vacuumCorrelation
  rw [← wordAction_vacuum, ← wordAction_vacuum,
    wordAction_local_exchange S h left right a b f g hs]

end
end UnifiedTheory.Clay.YangMills.FieldCorrelations
