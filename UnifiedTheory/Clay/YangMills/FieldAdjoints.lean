/- Adjoint compatibility and vacuum-word positivity on a genuine common
field domain. These implications require a supplied field system and its
adjoint relations; they do not construct Yang--Mills fields. -/
import UnifiedTheory.Clay.YangMills.LocalFields
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FieldAdjoints
noncomputable section
open UnifiedTheory.Clay.YangMills.LocalFields

def testConjugation : TestFunction →L⋆[ℂ] TestFunction :=
  SchwartzMap.mkCLM (σ := starRingEnd ℂ) (fun f x => star (f x))
    (by intro f g x; simp) (by intro c f x; simp [mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth _)) (by
      rintro ⟨k, n⟩
      refine ⟨{(k, n)}, 1, zero_le_one, ?_⟩
      intro f x
      simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply, one_mul]
      change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.conjLIE ∘ f) x‖ ≤ _
      rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
      exact SchwartzMap.le_seminorm ℂ k n f x)

theorem testConjugation_apply (f : TestFunction) (x : Spacetime) :
    testConjugation f x = star (f x) := rfl

theorem testConjugation_involutive : Function.Involutive testConjugation := by
  intro f
  ext x
  simp only [testConjugation_apply, star_star]

variable {Label H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def AdjointCompatible (S : FieldSystem Label H) (adj : Label → Label) : Prop :=
  ∀ a f (u v : S.domain), inner ℂ (S.field a f u : H) (v : H) =
    inner ℂ (u : H) (S.field (adj a) (testConjugation f) v : H)

def wordAction (S : FieldSystem Label H) : List (Label × TestFunction) → S.domain →ₗ[ℂ] S.domain
  | [] => LinearMap.id
  | (a, f) :: w => (S.field a f).comp (wordAction S w)

theorem wordAction_vacuum (S : FieldSystem Label H) (w : List (Label × TestFunction)) :
    wordAction S w S.vacuum = wordState S w := by
  induction w with
  | nil => rfl
  | cons af w hw => simpa only [wordAction, LinearMap.comp_apply, wordState, hw]

theorem wordAction_append (S : FieldSystem Label H) (w v : List (Label × TestFunction))
    (u : S.domain) : wordAction S (w ++ v) u = wordAction S w (wordAction S v u) := by
  induction w with
  | nil => rfl
  | cons af w hw =>
      simpa only [List.cons_append, wordAction, LinearMap.comp_apply] using
        (congrArg (S.field af.1 af.2) hw)

def adjointWord (adj : Label → Label) (w : List (Label × TestFunction)) :
    List (Label × TestFunction) := w.reverse.map (fun af => (adj af.1, testConjugation af.2))

theorem adjointWord_cons (adj : Label → Label) (a : Label) (f : TestFunction)
    (w : List (Label × TestFunction)) :
    adjointWord adj ((a, f) :: w) = adjointWord adj w ++ [(adj a, testConjugation f)] := by
  simp [adjointWord]

theorem word_adjoint (S : FieldSystem Label H) (adj : Label → Label)
    (h : AdjointCompatible S adj) (w : List (Label × TestFunction)) (u v : S.domain) :
    inner ℂ (wordAction S w u : H) (v : H) =
      inner ℂ (u : H) (wordAction S (adjointWord adj w) v : H) := by
  induction w generalizing u v with
  | nil => rfl
  | cons af w hw =>
    rcases af with ⟨a, f⟩
    change inner ℂ (S.field a f (wordAction S w u) : H) (v : H) = _
    rw [h, hw, adjointWord_cons, wordAction_append]
    rfl

theorem correlation_as_inner (S : FieldSystem Label H) (adj : Label → Label)
    (h : AdjointCompatible S adj) (w v : List (Label × TestFunction)) :
    vacuumCorrelation S (adjointWord adj w ++ v) =
      inner ℂ (wordState S w : H) (wordState S v : H) := by
  unfold vacuumCorrelation
  rw [← wordAction_vacuum, wordAction_append, ← word_adjoint S adj h,
    wordAction_vacuum, wordAction_vacuum]

variable {ι : Type*}

def wavepacket (S : FieldSystem Label H) (s : Finset ι)
    (w : ι → List (Label × TestFunction)) (c : ι → ℂ) : H :=
  ∑ i ∈ s, c i • (wordState S (w i) : H)

theorem gram_identity (S : FieldSystem Label H) (adj : Label → Label)
    (h : AdjointCompatible S adj) (s : Finset ι)
    (w : ι → List (Label × TestFunction)) (c : ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (c i) * c j * vacuumCorrelation S (adjointWord adj (w i) ++ w j)) =
      inner ℂ (wavepacket S s w c) (wavepacket S s w c) := by
  simp_rw [correlation_as_inner S adj h]
  simp only [wavepacket]
  rw [sum_inner]
  simp_rw [inner_smul_left, inner_sum, inner_smul_right, Finset.mul_sum]
  simp only [mul_assoc]
  rfl

theorem vacuum_word_positivity (S : FieldSystem Label H) (adj : Label → Label)
    (h : AdjointCompatible S adj) (s : Finset ι)
    (w : ι → List (Label × TestFunction)) (c : ι → ℂ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s,
      star (c i) * c j * vacuumCorrelation S (adjointWord adj (w i) ++ w j)).re := by
  rw [gram_identity S adj h]
  have he : (inner ℂ (wavepacket S s w c) (wavepacket S s w c)).re =
      ‖wavepacket S s w c‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [he]
  exact sq_nonneg _

end
end UnifiedTheory.Clay.YangMills.FieldAdjoints
