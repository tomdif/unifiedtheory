/- Unconditional square-root and form-energy bounds for all positive shifted
resolvents of the full time-dependent Hamiltonian H(t), the residual
Hamiltonian S(t), and the growing Hamiltonian G. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalOperatorFormEnergy
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore
import UnifiedTheory.Audit.KFCausalClockFloorGrowingYosida

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventFormBounds
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)
open KFCausalClockFloorUnconditionalOperatorFormEnergy

private theorem resolvent_pairing_eq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a) (f : H) :
    (inner ℂ (T (KFCausalPositiveResolventBounds.point T R a hr f)) (R f)).re+
      a*‖R f‖^2 = (inner ℂ f (R f)).re := by
  have hv := KFCausalPositiveResolventBounds.point_value T R a hr f
  rw [hv,inner_sub_left,inner_smul_left_eq_smul,
    KFCausalShiftedForm.complex_inner_square (R f)]
  simp only [Complex.sub_re,Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_re]
  ring

private theorem resolvent_pairing_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    (inner ℂ (T (KFCausalPositiveResolventBounds.point T R a hr f)) (R f)).re+
      a*‖R f‖^2 ≤ a⁻¹*‖f‖^2 := by
  rw [resolvent_pairing_eq T R a hr f]
  have hi : (inner ℂ f (R f)).re ≤ ‖f‖*‖R f‖ := re_inner_le_norm (𝕜 := ℂ) f (R f)
  have hnorm := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound T R a ha hr hp f
  have hmul : ‖f‖*‖R f‖ ≤ ‖f‖*(a⁻¹*‖f‖) :=
    mul_le_mul_of_nonneg_left hnorm (norm_nonneg f)
  linarith [show ‖f‖*(a⁻¹*‖f‖) = a⁻¹*‖f‖^2 by ring]

private theorem subst_energy_le {e s b c : ℝ} (he : e = s) (hp : e+b ≤ c) : s+b ≤ c := by
  rw [← he]
  exact hp

private theorem drop_middle_nonneg {a b c d : ℝ} (h : a+b+c ≤ d) (hb : 0 ≤ b) : a+c ≤ d := by
  linarith

private theorem first_of_two_le {a b d : ℝ} (h : a+b ≤ d) (hb : 0 ≤ b) : a ≤ d := by
  linarith

private theorem first_of_three_le {a b c d : ℝ} (h : a+b+c ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) : a ≤ d := by
  linarith

private theorem second_of_three_le {a b c d : ℝ} (h : a+b+c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) : b ≤ d := by
  linarith

private theorem third_of_four_le {a b c e d : ℝ}
    (h : a+b+c+e ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) : c ≤ d := by
  linarith

private theorem le_sqrt_inv_mul_of_sq_le (u a b : ℝ)
    (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 ≤ b) (hsq : u^2 ≤ a⁻¹*b^2) :
    u ≤ Real.sqrt (a⁻¹)*b := by
  apply (sq_le_sq₀ hu (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  rw [mul_pow,Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  exact hsq

private theorem exp_mul_le_sqrt_inv_mul_of_sq_le (t u a b : ℝ)
    (hu : 0 ≤ u) (ha : 0 < a) (hb : 0 ≤ b)
    (hsq : Real.exp (2*t)*u^2 ≤ a⁻¹*b^2) :
    Real.exp t*u ≤ Real.sqrt (a⁻¹)*b := by
  apply le_sqrt_inv_mul_of_sq_le (Real.exp t*u) a b
    (mul_nonneg (Real.exp_pos t).le hu) ha hb
  have he : Real.exp t^2 = Real.exp (2*t) := by
    rw [sq,← Real.exp_add,show t+t = 2*t by ring]
  rw [mul_pow,he]
  exact hsq

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k

/-! ### Full Time-Dependent Hamiltonian Resolvent Form Bounds -/

def hamiltonianResolventPoint (t a : ℝ) (ha : 0 < a) (f : Hilbert) : (H t).domain :=
  KFCausalPositiveResolventBounds.point (H t) (RH t a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem hamiltonian_resolvent_mem_staticRoot_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (Tstat).domain :=
  hamiltonian_mem_staticRoot_domain ε hε h hh hb m g k t
    (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_mem_radialRoot_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (Kroot).domain :=
  hamiltonian_mem_radialRoot_domain ε hε h hh hb m g k t
    (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_mem_potentialForm_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (Tpot).domain :=
  hamiltonian_mem_potentialForm_domain ε hε h hh hb m g k t
    (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_mem_growingForm_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (Tgrow).domain :=
  hamiltonian_mem_growingForm_domain ε hε h hh hb m g k t
    (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_mem_residualForm_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (Tres t).domain :=
  hamiltonian_mem_residualForm_domain ε hε h hh hb m g k t
    (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_pairing_eq (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (inner ℂ (H t (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)) (RH t a f)).re+
      a*‖RH t a f‖^2 = (inner ℂ f (RH t a f)).re :=
  resolvent_pairing_eq (H t) (RH t a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem hamiltonian_resolvent_pairing_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (inner ℂ (H t (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)) (RH t a f)).re+
      a*‖RH t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  resolvent_pairing_le (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f

theorem hamiltonian_resolvent_three_channel_energy_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RH t a f,hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      Real.exp (2*t)*‖Kroot ⟨RH t a f,hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      Real.exp (2*t)*‖Tpot ⟨RH t a f,hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      a*‖RH t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  subst_energy_le
    (hamiltonian_form_energy_eq_three_channel ε hε h hh hb m g k t
      (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f))
    (hamiltonian_resolvent_pairing_le ε hε h hh hb m g k t a ha f)

theorem hamiltonian_resolvent_static_radial_energy_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RH t a f,hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      Real.exp (2*t)*‖Kroot ⟨RH t a f,hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      a*‖RH t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  drop_middle_nonneg
    (hamiltonian_resolvent_three_channel_energy_le ε hε h hh hb m g k t a ha f)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

theorem hamiltonian_resolvent_staticRoot_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RH t a f,hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  le_sqrt_inv_mul_of_sq_le _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (first_of_three_le
      (hamiltonian_resolvent_static_radial_energy_le ε hε h hh hb m g k t a ha f)
      (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))
      (mul_nonneg ha.le (sq_nonneg _)))

theorem hamiltonian_resolvent_radialRoot_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp t*‖Kroot ⟨RH t a f,hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  exp_mul_le_sqrt_inv_mul_of_sq_le t _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (second_of_three_le
      (hamiltonian_resolvent_static_radial_energy_le ε hε h hh hb m g k t a ha f)
      (sq_nonneg _)
      (mul_nonneg ha.le (sq_nonneg _)))

theorem hamiltonian_resolvent_potentialForm_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp t*‖Tpot ⟨RH t a f,hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  exp_mul_le_sqrt_inv_mul_of_sq_le t _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (third_of_four_le
      (hamiltonian_resolvent_three_channel_energy_le ε hε h hh hb m g k t a ha f)
      (sq_nonneg _)
      (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))
      (mul_nonneg ha.le (sq_nonneg _)))

/-! ### Residual Hamiltonian Resolvent Form Bounds -/

def residualResolventPoint (t a : ℝ) (ha : 0 < a) (f : Hilbert) : (S t).domain :=
  KFCausalPositiveResolventBounds.point (S t) (RS t a) a
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem residual_resolvent_mem_staticRoot_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (Tstat).domain :=
  residual_mem_staticRoot_domain ε hε h hh hb m g k t
    (residualResolventPoint ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_mem_potentialForm_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (Tpot).domain :=
  residual_mem_potentialForm_domain ε hε h hh hb m g k t
    (residualResolventPoint ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_mem_residualForm_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (Tres t).domain :=
  residual_mem_residualForm_domain ε hε h hh hb m g k t
    (residualResolventPoint ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_pairing_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (inner ℂ (S t (residualResolventPoint ε hε h hh hb m g k t a ha f)) (RS t a f)).re+
      a*‖RS t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  resolvent_pairing_le (S t) (RS t a) a ha
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive
      (KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t)) f

theorem residual_resolvent_two_channel_energy_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS t a f,residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      Real.exp (2*t)*‖Tpot ⟨RS t a f,residual_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      a*‖RS t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  subst_energy_le
    (residual_form_energy_eq_split ε hε h hh hb m g k t
      (residualResolventPoint ε hε h hh hb m g k t a ha f))
    (residual_resolvent_pairing_le ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_static_energy_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS t a f,residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      a*‖RS t a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  drop_middle_nonneg
    (residual_resolvent_two_channel_energy_le ε hε h hh hb m g k t a ha f)
    (mul_nonneg (Real.exp_pos (2*t)).le (sq_nonneg _))

theorem residual_resolvent_staticRoot_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS t a f,residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  le_sqrt_inv_mul_of_sq_le _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (first_of_two_le
      (residual_resolvent_static_energy_le ε hε h hh hb m g k t a ha f)
      (mul_nonneg ha.le (sq_nonneg _)))

theorem residual_resolvent_potentialForm_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp t*‖Tpot ⟨RS t a f,residual_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  exp_mul_le_sqrt_inv_mul_of_sq_le t _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (second_of_three_le
      (residual_resolvent_two_channel_energy_le ε hε h hh hb m g k t a ha f)
      (sq_nonneg _)
      (mul_nonneg ha.le (sq_nonneg _)))

/-! ### Growing Hamiltonian Resolvent Form Bounds -/

def growingResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (G).domain :=
  KFCausalPositiveResolventBounds.point G (RG a) a
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) f

theorem growing_resolvent_mem_radialRoot_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (Kroot).domain :=
  growing_mem_radialRoot_domain ε hε h hh hb m g k
    (growingResolventPoint ε hε h hh hb m g k a ha f)

theorem growing_resolvent_mem_potentialForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (Tpot).domain :=
  growing_mem_potentialForm_domain ε hε h hh hb m g k
    (growingResolventPoint ε hε h hh hb m g k a ha f)

theorem growing_resolvent_mem_growingForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (Tgrow).domain :=
  growing_mem_growingForm_domain ε hε h hh hb m g k
    (growingResolventPoint ε hε h hh hb m g k a ha f)

theorem growing_resolvent_pairing_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (inner ℂ (G (growingResolventPoint ε hε h hh hb m g k a ha f)) (RG a f)).re+
      a*‖RG a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  resolvent_pairing_le G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k) f

theorem growing_resolvent_two_channel_energy_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Kroot ⟨RG a f,growing_resolvent_mem_radialRoot_domain ε hε h hh hb m g k a ha f⟩‖^2+
      ‖Tpot ⟨RG a f,growing_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖^2+
      a*‖RG a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  subst_energy_le
    (growing_form_energy_eq_split ε hε h hh hb m g k
      (growingResolventPoint ε hε h hh hb m g k a ha f))
    (growing_resolvent_pairing_le ε hε h hh hb m g k a ha f)

theorem growing_resolvent_radial_energy_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Kroot ⟨RG a f,growing_resolvent_mem_radialRoot_domain ε hε h hh hb m g k a ha f⟩‖^2+
      a*‖RG a f‖^2 ≤ a⁻¹*‖f‖^2 :=
  drop_middle_nonneg
    (growing_resolvent_two_channel_energy_le ε hε h hh hb m g k a ha f)
    (sq_nonneg _)

theorem growing_resolvent_radialRoot_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Kroot ⟨RG a f,growing_resolvent_mem_radialRoot_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  le_sqrt_inv_mul_of_sq_le _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (first_of_two_le
      (growing_resolvent_radial_energy_le ε hε h hh hb m g k a ha f)
      (mul_nonneg ha.le (sq_nonneg _)))

theorem growing_resolvent_potentialForm_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RG a f,growing_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      Real.sqrt (a⁻¹)*‖f‖ :=
  le_sqrt_inv_mul_of_sq_le _ a ‖f‖ (norm_nonneg _) ha (norm_nonneg _)
    (second_of_three_le
      (growing_resolvent_two_channel_energy_le ε hε h hh hb m g k a ha f)
      (sq_nonneg _)
      (mul_nonneg ha.le (sq_nonneg _)))

#print axioms hamiltonian_resolvent_mem_staticRoot_domain
#print axioms hamiltonian_resolvent_mem_radialRoot_domain
#print axioms hamiltonian_resolvent_mem_potentialForm_domain
#print axioms hamiltonian_resolvent_mem_growingForm_domain
#print axioms hamiltonian_resolvent_mem_residualForm_domain
#print axioms hamiltonian_resolvent_pairing_eq
#print axioms hamiltonian_resolvent_pairing_le
#print axioms hamiltonian_resolvent_three_channel_energy_le
#print axioms hamiltonian_resolvent_static_radial_energy_le
#print axioms hamiltonian_resolvent_staticRoot_norm_le
#print axioms hamiltonian_resolvent_radialRoot_norm_le
#print axioms hamiltonian_resolvent_potentialForm_norm_le
#print axioms residual_resolvent_mem_staticRoot_domain
#print axioms residual_resolvent_mem_potentialForm_domain
#print axioms residual_resolvent_mem_residualForm_domain
#print axioms residual_resolvent_pairing_le
#print axioms residual_resolvent_two_channel_energy_le
#print axioms residual_resolvent_static_energy_le
#print axioms residual_resolvent_staticRoot_norm_le
#print axioms residual_resolvent_potentialForm_norm_le
#print axioms growing_resolvent_mem_radialRoot_domain
#print axioms growing_resolvent_mem_potentialForm_domain
#print axioms growing_resolvent_mem_growingForm_domain
#print axioms growing_resolvent_pairing_le
#print axioms growing_resolvent_two_channel_energy_le
#print axioms growing_resolvent_radial_energy_le
#print axioms growing_resolvent_radialRoot_norm_le
#print axioms growing_resolvent_potentialForm_norm_le
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventFormBounds
