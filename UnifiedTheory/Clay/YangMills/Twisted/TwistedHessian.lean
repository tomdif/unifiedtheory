/- The quadratic form of the twisted action at the flat field, in colour components.
The adjoint action of `flatLink` is diagonal: each colour sees a flat Z2 line bundle
with one antiperiodic direction. On the gauge-orthogonal complement the form is
bounded below by `8 sin²(π/2N)`, uniformly in the gauge sector and with no zero mode.
This is a classical quadratic-form statement, not an estimate for the quantum measure. -/
import UnifiedTheory.Clay.YangMills.Twisted.CommutingShifts
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat CommutingShifts
open WilsonSingleLinkStaples (Q)
open scoped RealInnerProductSpace Quaternion

variable {N : ℕ} [NeZero N]

/-- Scalar sections of the colour bundle. -/
abbrev Section (N : ℕ) [NeZero N] := EuclideanSpace ℝ (Vertex N)

/-- The sign `-1` across `x κ = 0`. -/
def seam (κ : Fin 4) (x : Vertex N) : ℝ := if x κ = 0 then -1 else 1

/-- Colour-bundle sign on links; `e₁, e₂` record which transitions act nontrivially. -/
def eta (e₁ e₂ : Bool) (x : Vertex N) (μ : Fin 4) : ℝ :=
  if μ = 1 ∧ e₁ = true then seam 1 x else if μ = 2 ∧ e₂ = true then seam 2 x else 1

theorem seam_sq (κ : Fin 4) (x : Vertex N) : seam κ x * seam κ x = 1 := by
  unfold seam
  split_ifs <;> norm_num

theorem eta_sq (e₁ e₂ : Bool) (x : Vertex N) (μ : Fin 4) :
    eta e₁ e₂ x μ * eta e₁ e₂ x μ = 1 := by
  unfold eta
  split_ifs
  · exact seam_sq _ _
  · exact seam_sq _ _
  · norm_num

theorem eta_step_other (e₁ e₂ : Bool) (x : Vertex N) (μ κ : Fin 4) (h : κ ≠ μ) :
    eta e₁ e₂ (step N x κ) μ = eta e₁ e₂ x μ := by
  unfold eta seam
  by_cases h1 : μ = 1
  · subst h1
    simp [step_other x κ 1 (Ne.symm h)]
  · by_cases h2 : μ = 2
    · subst h2
      simp [step_other x κ 2 (Ne.symm h)]
    · simp [h1, h2]

theorem eta_flat (e₁ e₂ : Bool) (x : Vertex N) (μ ν : Fin 4) :
    eta e₁ e₂ x μ * eta e₁ e₂ (step N x μ) ν = eta e₁ e₂ x ν * eta e₁ e₂ (step N x ν) μ := by
  by_cases h : μ = ν
  · subst h
    rfl
  · rw [eta_step_other e₁ e₂ x ν μ h, eta_step_other e₁ e₂ x μ ν (Ne.symm h)]
    ring

theorem step_step_comm (x : Vertex N) (μ ν : Fin 4) :
    step N (step N x μ) ν = step N (step N x ν) μ := by
  simp only [step]
  abel

/-- Backward step, the inverse of `step`. -/
def back (x : Vertex N) (μ : Fin 4) : Vertex N := x - Pi.single μ 1

theorem back_step (x : Vertex N) (μ : Fin 4) : back (step N x μ) μ = x := by
  simp [back, step]

theorem step_back (x : Vertex N) (μ : Fin 4) : step N (back x μ) μ = x := by
  simp [back, step]

/-- Translation as an equivalence, for reindexing sums. -/
def stepEquiv (μ : Fin 4) : Vertex N ≃ Vertex N where
  toFun x := step N x μ
  invFun x := back x μ
  left_inv x := back_step x μ
  right_inv x := step_back x μ

/-- The covariant shift in direction `μ` on a colour bundle. -/
def colourShift (e₁ e₂ : Bool) (μ : Fin 4) : Shift (Section N) where
  T :=
    { toFun := fun φ => WithLp.toLp 2 fun x => eta e₁ e₂ x μ * φ (step N x μ)
      map_add' := by
        intro a b
        ext x
        simp [mul_add]
      map_smul' := by
        intro c a
        ext x
        simp
        ring }
  S :=
    { toFun := fun φ => WithLp.toLp 2 fun x => eta e₁ e₂ (back x μ) μ * φ (back x μ)
      map_add' := by
        intro a b
        ext x
        simp [mul_add]
      map_smul' := by
        intro c a
        ext x
        simp
        ring }
  adj := by
    intro φ ψ
    simp only [PiLp.inner_apply, LinearMap.coe_mk, AddHom.coe_mk, RCLike.inner_apply, conj_trivial]
    rw [← Equiv.sum_comp (stepEquiv (N := N) μ) (fun x => _ * (φ x))]
    apply Finset.sum_congr rfl
    intro x _
    simp only [stepEquiv, Equiv.coe_fn_mk, back_step]
    ring
  left := by
    intro φ
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, step_back]
    rw [← mul_assoc, eta_sq, one_mul]
  right := by
    intro φ
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, back_step]
    rw [← mul_assoc, eta_sq, one_mul]

theorem colourShift_T_apply (e₁ e₂ : Bool) (μ : Fin 4) (φ : Section N) (x : Vertex N) :
    (colourShift e₁ e₂ μ).T φ x = eta e₁ e₂ x μ * φ (step N x μ) := rfl

theorem colourShift_commute (e₁ e₂ : Bool) (μ ν : Fin 4) (φ : Section N) :
    (colourShift e₁ e₂ μ).T ((colourShift e₁ e₂ ν).T φ) =
      (colourShift e₁ e₂ ν).T ((colourShift e₁ e₂ μ).T φ) := by
  ext x
  simp only [colourShift_T_apply]
  rw [← mul_assoc, ← mul_assoc, eta_flat, step_step_comm]

theorem colourShift_pow (e₁ e₂ : Bool) (μ : Fin 4) (φ : Section N) (k : ℕ) (x : Vertex N) :
    (((colourShift e₁ e₂ μ).T ^ k) φ) x =
      (∏ i ∈ Finset.range k, eta e₁ e₂ (walk μ x i) μ) * φ (walk μ x k) := by
  induction k generalizing φ with
  | zero => simp [walk_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, colourShift_T_apply, Finset.prod_range_succ, walk_succ]
    ring

theorem prod_seam (κ : Fin 4) (x : Vertex N) :
    ∏ i ∈ Finset.range N, seam κ (walk κ x i) = -1 := by
  have h (i : ℕ) : seam κ (walk κ x i) = (-1 : ℝ) ^ (if x κ + (i : ZMod N) = 0 then 1 else 0) := by
    unfold seam
    rw [walk_apply_same]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_pow_eq_pow_sum, indicator_sum, pow_one]

/-- A colour bundle with the transition in direction 2 is antiperiodic in direction 2. -/
theorem colourShift_antiperiodic_two (e₁ : Bool) (φ : Section N) :
    ((colourShift e₁ true 2).T ^ N) φ = -φ := by
  ext x
  rw [colourShift_pow, walk_card]
  have h (i : ℕ) : eta e₁ true (walk 2 x i) 2 = seam 2 (walk 2 x i) := by
    simp [eta]
  simp only [h, prod_seam]
  simp

theorem colourShift_antiperiodic_one (e₂ : Bool) (φ : Section N) :
    ((colourShift true e₂ 1).T ^ N) φ = -φ := by
  ext x
  rw [colourShift_pow, walk_card]
  have h (i : ℕ) : eta true e₂ (walk 1 x i) 1 = seam 1 (walk 1 x i) := by
    simp [eta]
  simp only [h, prod_seam]
  simp

/-- The sharp constant of the twisted form, per colour. -/
def lam (N : ℕ) : ℝ := 4 * Real.sin (Real.pi / (2 * N)) ^ 2

theorem lam_pos (N : ℕ) [NeZero N] : 0 < lam N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h1 : 0 < Real.pi / (2 * N) := by positivity
  have h2 : Real.pi / (2 * N) < Real.pi := by
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    nlinarith [Real.pi_pos]
  have := Real.sin_pos_of_pos_of_lt_pi h1 h2
  unfold lam
  positivity

/-- The bundle of colour `a`: `i ↦ (F,T)`, `j ↦ (T,F)`, `k ↦ (T,T)`. -/
def bundle (a : Fin 3) : Bool × Bool := ![(false, true), (true, false), (true, true)] a

/-- The shifts of colour `a`. -/
def shifts (a : Fin 3) (μ : Fin 4) : Shift (Section N) :=
  colourShift (bundle a).1 (bundle a).2 μ

/-- Lower bound on `curl` plus `div`, for each colour. -/
theorem colour_bound (a : Fin 3) (ω : Fin 4 → Section N) :
    lam N * ∑ μ, ‖ω μ‖ ^ 2 ≤ curlEnergy (shifts a) ω + ‖div (shifts a) ω‖ ^ 2 := by
  have hNpos := NeZero.pos N
  have hb (κ : Fin 4) (h : ∀ φ : Section N, ((shifts a κ).T ^ N) φ = -φ) (x : Section N) :
      lam N * ‖x‖ ^ 2 ≤ ‖(shifts (N := N) a κ).D x‖ ^ 2 := by
    have := D_lower_bound (shifts (N := N) a κ) N hNpos h x
    rwa [two_sub_cos] at this
  have hc := fun μ ν φ => colourShift_commute (N := N) (bundle a).1 (bundle a).2 μ ν φ
  fin_cases a
  · exact energy_lower_bound _ hc ω 2 _ (hb 2 (fun φ => colourShift_antiperiodic_two _ φ))
  · exact energy_lower_bound _ hc ω 1 _ (hb 1 (fun φ => colourShift_antiperiodic_one _ φ))
  · exact energy_lower_bound _ hc ω 1 _ (hb 1 (fun φ => colourShift_antiperiodic_one _ φ))

/-- The twisted quadratic form on all colours, in the Hessian's normalization. -/
def hessianForm (Ω : Fin 3 → Fin 4 → Section N) : ℝ :=
  2 * ∑ a, curlEnergy (shifts a) (Ω a)

/-- Coercivity on the gauge-orthogonal complement, the exact numerical constant. -/
theorem hessian_coercive (Ω : Fin 3 → Fin 4 → Section N)
    (hdiv : ∀ a, div (shifts a) (Ω a) = 0) :
    8 * Real.sin (Real.pi / (2 * N)) ^ 2 * ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 ≤ hessianForm Ω := by
  have h (a : Fin 3) := colour_bound a (Ω a)
  simp only [hdiv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => h a)
  rw [← Finset.mul_sum] at hs
  unfold hessianForm
  unfold lam at hs
  nlinarith

/-- No zero modes: a form with vanishing curl and divergence is zero. -/
theorem no_zero_modes (Ω : Fin 3 → Fin 4 → Section N)
    (hdiv : ∀ a, div (shifts a) (Ω a) = 0) (hcurl : hessianForm Ω = 0) : Ω = 0 := by
  have hc := hessian_coercive Ω hdiv
  rw [hcurl] at hc
  have hl : 0 < 8 * Real.sin (Real.pi / (2 * N)) ^ 2 := by
    have := lam_pos N
    unfold lam at this
    linarith
  have hs : ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 ≤ 0 := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos hl hneg]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg fun μ _ => sq_nonneg _)).mp (le_antisymm hs
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun μ _ => sq_nonneg _))
  funext a μ
  have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg _)).mp
    (hz a (Finset.mem_univ _)) μ (Finset.mem_univ _)
  simpa using hz2

/-! ### Identification of the colour bundles with the adjoint action of `flatLink` -/

/-- The imaginary quaternion basis. -/
def basis (a : Fin 3) : ℍ[ℝ] :=
  ![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] a

theorem qI_inv : ((qI⁻¹ : Q) : ℍ[ℝ]) = ⟨0, -1, 0, 0⟩ := by
  change star ((qI : Q) : ℍ[ℝ]) = _
  ext <;> simp [qI]

theorem qJ_inv : ((qJ⁻¹ : Q) : ℍ[ℝ]) = ⟨0, 0, -1, 0⟩ := by
  change star ((qJ : Q) : ℍ[ℝ]) = _
  ext <;> simp [qJ]

/-- The adjoint action of the flat field on each colour is exactly the bundle sign. -/
theorem ad_flatLink (a : Fin 3) (x : Vertex N) (μ : Fin 4) :
    ((flatLink x μ : Q) : ℍ[ℝ]) * basis a * ((flatLink x μ)⁻¹ : Q) =
      (eta (bundle a).1 (bundle a).2 x μ : ℝ) • basis a := by
  unfold flatLink
  by_cases h1 : μ = 1 ∧ x 1 = 0
  · have hμ : μ = 1 := h1.1
    subst hμ
    rw [if_pos h1, qI_inv]
    have hs : seam 1 x = -1 := by simp [seam, h1.2]
    fin_cases a <;> simp [eta, bundle, hs, basis, qI] <;> ext <;> simp
  · rw [if_neg h1]
    by_cases h2 : μ = 2 ∧ x 2 = 0
    · have hμ : μ = 2 := h2.1
      subst hμ
      rw [if_pos h2, qJ_inv]
      have hs : seam 2 x = -1 := by simp [seam, h2.2]
      fin_cases a <;> simp [eta, bundle, hs, basis, qJ] <;> ext <;> simp
    · rw [if_neg h2]
      have he : eta (bundle a).1 (bundle a).2 x μ = 1 := by
        unfold eta seam
        by_cases hμ1 : μ = 1
        · subst hμ1
          have hx : x 1 ≠ 0 := fun h => h1 ⟨rfl, h⟩
          simp [hx]
        · by_cases hμ2 : μ = 2
          · subst hμ2
            have hx : x 2 ≠ 0 := fun h => h2 ⟨rfl, h⟩
            simp [hx]
          · simp [hμ1, hμ2]
      rw [he]
      simp

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian
