/- Actual pointwise complex conjugation on every correlation-test Schwartz
space, with its continuous conjugate-linear structure. -/
import UnifiedTheory.Clay.YangMills.ContinuumControl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzConfigurationConjugation
noncomputable section
open ContinuumControl

def conjugation (m : ℕ) : CorrelationTest m →L⋆[ℂ] CorrelationTest m :=
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

@[simp] theorem conjugation_apply (m : ℕ) (f : CorrelationTest m) (x : Configuration m) :
    conjugation m f x = star (f x) := rfl

theorem conjugation_involutive (m : ℕ) : Function.Involutive (conjugation m) := by
  intro f
  ext x
  simp only [conjugation_apply, star_star]

theorem conjugation_continuous (m : ℕ) : Continuous (conjugation m) :=
  (conjugation m).continuous

end
end UnifiedTheory.Clay.YangMills.SchwartzConfigurationConjugation
