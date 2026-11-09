/- A bounded two-sided resolvent below a strictly positive closed-form
Hamiltonian floor. The inverse is constructed by coercivity on the form space. -/
import UnifiedTheory.Audit.KFCausalClosedFormLowerBound
import UnifiedTheory.Audit.KFCausalCoerciveInverse
import UnifiedTheory.Clay.YangMills.SpectralGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveFormResolvent
noncomputable section
open KFCausalClosedGraphForm KFCausalCoerciveInverse KFCausalTensorSumEnergyFloor
open UnifiedTheory.Clay.YangMills.SpectralGap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


def shiftedForm (D : Data H K) (lam : ℝ) : FormSpace D →L[ℂ] FormSpace D :=
  1 - ((lam + 1 : ℝ) : ℂ) • (((embedding D)).adjoint.comp ((embedding D)))

theorem shifted_pairing (D : Data H K) (lam : ℝ) (u v : FormSpace D) :
    inner ℂ (shiftedForm D lam u) v =
      inner ℂ u v - ((lam + 1 : ℝ) : ℂ) * inner ℂ ((embedding D) u) ((embedding D) v) := by
  change inner ℂ (u - ((lam + 1 : ℝ) : ℂ) • ((embedding D)).adjoint ((embedding D) u)) v = _
  rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, ((embedding D)).adjoint_inner_left]

theorem shifted_symmetric (D : Data H K) (lam : ℝ) :
    (shiftedForm D lam).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℂ (shiftedForm D lam u) v = inner ℂ u (shiftedForm D lam v)
  rw [shifted_pairing]
  change _ = inner ℂ u (v - ((lam + 1 : ℝ) : ℂ) • ((embedding D)).adjoint ((embedding D) v))
  rw [inner_sub_right, inner_smul_right, ((embedding D)).adjoint_inner_right]

theorem shifted_diagonal (D : Data H K) (lam : ℝ) (u : FormSpace D) :
    (inner ℂ (shiftedForm D lam u) u).re = ‖(energyOutput D) u‖ ^ 2 - lam * ‖(embedding D) u‖ ^ 2 := by
  rw [shifted_pairing]
  have h1 : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  have h2 : (inner ℂ ((embedding D) u) ((embedding D) u)).re = ‖(embedding D) u‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) ((embedding D) u)
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, h1, h2]
  rw [form_norm_identity]
  ring

theorem shifted_coercive (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) (u : FormSpace D) :
    ((delta - lam) / (delta + 1)) * ‖u‖ ^ 2 ≤ (inner ℂ (shiftedForm D lam u) u).re := by
  rw [shifted_diagonal, div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < delta + 1)]
  have hb := KFCausalClosedFormLowerBound.lower_bound D delta hD u
  have hn := form_norm_identity D u
  have hp : 0 ≤ (lam + 1) * (‖(energyOutput D) u‖ ^ 2 - delta * ‖(embedding D) u‖ ^ 2) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hb)
  nlinarith

def shiftedUnit (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) : IsUnit (shiftedForm D lam) :=
  coercive_isUnit _ ((delta - lam) / (delta + 1))
    (div_pos (sub_pos.mpr hld) (by linarith))
    (shifted_coercive D delta lam hlam hld hD) (shifted_symmetric D lam)

def resolvent (D : Data H K) (lam : ℝ) : H →L[ℂ] H :=
  ((embedding D)).comp ((Ring.inverse (shiftedForm D lam)).comp ((embedding D)).adjoint)

def inverseForm (D : Data H K) (lam : ℝ) (y : H) : FormSpace D :=
  Ring.inverse (shiftedForm D lam) (((embedding D)).adjoint y)

theorem inverseForm_pairing (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) (y : H) (v : FormSpace D) :
    inner ℂ ((energyOutput D) (inverseForm D lam y)) ((energyOutput D) v) =
      inner ℂ (y + (lam : ℂ) • resolvent D lam y) ((embedding D) v) := by
  have he := congrArg (fun w => inner ℂ w v)
    (inverse_apply_right (shiftedForm D lam) (shiftedUnit D delta lam hlam hld hD)
      (((embedding D)).adjoint y))
  change inner ℂ (shiftedForm D lam (inverseForm D lam y)) v = inner ℂ (((embedding D)).adjoint y) v at he
  rw [shifted_pairing, ((embedding D)).adjoint_inner_left, form_inner_identity] at he
  change _ = inner ℂ (y + (lam : ℂ) • (embedding D) (inverseForm D lam y)) ((embedding D) v)
  rw [inner_add_left, inner_smul_left, Complex.conj_ofReal]
  push_cast at he
  linear_combination he

theorem right_graph (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) (y : H) :
    (resolvent D lam y, y + (lam : ℂ) • resolvent D lam y) ∈ (hamiltonian D).graph := by
  obtain ⟨hx, hy⟩ := (hamiltonian_domain_characterization D (inverseForm D lam y) _).mpr
    (inverseForm_pairing D delta lam hlam hld hD y)
  rw [LinearPMap.mem_graph_iff]
  exact ⟨⟨_, hx⟩, rfl, hy⟩

theorem shifted_formLift (D : Data H K) (lam : ℝ) (x : (hamiltonian D).domain) :
    shiftedForm D lam (formLift D x) = ((embedding D)).adjoint (hamiltonian D x - (lam : ℂ) • (x : H)) := by
  apply ext_inner_right ℂ
  intro v
  rw [shifted_pairing, form_inner_identity, embedding_formLift, hamiltonian_represents_form,
    ((embedding D)).adjoint_inner_left, inner_sub_left, inner_smul_left, Complex.conj_ofReal]
  push_cast
  ring

theorem left_inverse (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) (x : (hamiltonian D).domain) :
    resolvent D lam (hamiltonian D x - (lam : ℂ) • (x : H)) = x := by
  change (embedding D) (Ring.inverse (shiftedForm D lam)
    (((embedding D)).adjoint (hamiltonian D x - (lam : ℂ) • (x : H)))) = x
  rw [← shifted_formLift, inverse_apply_left _ (shiftedUnit D delta lam hlam hld hD),
    embedding_formLift]

def witness (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) : ResolventWitness (hamiltonian D) lam where
  inverse := resolvent D lam
  right_inverse := right_graph D delta lam hlam hld hD
  left_inverse := left_inverse D delta lam hlam hld hD

theorem resolvent_norm_bound (D : Data H K) (delta lam : ℝ) (hlam : 0 ≤ lam)
    (hld : lam < delta) (hD : LowerBound D delta) (y : H) :
    ‖resolvent D lam y‖ ≤ (delta - lam)⁻¹ * ‖y‖ := by
  obtain ⟨x, hx, hy⟩ := (hamiltonian D).mem_graph_iff.mp (right_graph D delta lam hlam hld hD y)
  dsimp only at hx hy
  have hb := hD x
  rw [hx, hy, inner_add_left, inner_smul_left, Complex.conj_ofReal] at hb
  have hn : (inner ℂ (resolvent D lam y) (resolvent D lam y)).re =
      ‖resolvent D lam y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hn] at hb
  have hi : (inner ℂ y (resolvent D lam y)).re ≤ ‖y‖ * ‖resolvent D lam y‖ :=
    re_inner_le_norm (𝕜 := ℂ) y (resolvent D lam y)
  by_cases hz : resolvent D lam y = 0
  · simp [hz, mul_nonneg (inv_nonneg.mpr (sub_pos.mpr hld).le) (norm_nonneg y)]
  · have hp : 0 < ‖resolvent D lam y‖ := norm_pos_iff.mpr hz
    apply (le_inv_mul_iff₀ (sub_pos.mpr hld)).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

end
end UnifiedTheory.Audit.KFCausalPositiveFormResolvent
