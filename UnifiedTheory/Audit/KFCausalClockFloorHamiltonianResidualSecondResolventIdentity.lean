/- Unconditional exact second resolvent identity and multi-channel form-energy
bounds between the residual Hamiltonian resolvent R_{S(t)}(a) = (S(t) + a)⁻¹
and the full time-dependent Hamiltonian resolvent R_{H(t)}(a) = (H(t) + a)⁻¹
for all real couplings m, g, k ∈ ℝ, physical times t ∈ ℝ, and shifts a > 0:
1. Establishes the shifted residual equation on every Hamiltonian-resolvent state:
   S(t) (R_{H(t)}(a) f) + a • R_{H(t)}(a) f = f - exp(2t) • K (R_{H(t)}(a) f).
2. Deduces the unconditional exact second resolvent identity on all of Hilbert:
   R_{H(t)}(a) f = R_{S(t)}(a) f - exp(2t) • R_{S(t)}(a) (K (R_{H(t)}(a) f)),
   R_{S(t)}(a) f - R_{H(t)}(a) f = exp(2t) • R_{S(t)}(a) (K (R_{H(t)}(a) f)),
   S(t) (R_{S(t)}(a) f) - S(t) (R_{H(t)}(a) f)
     = exp(2t) • K (R_{H(t)}(a) f) - (a * exp(2t)) • R_{S(t)}(a) (K (R_{H(t)}(a) f)).
3. Proves unconditional Hilbert, residual-operator, residual-form (T_res(t)),
   two-channel (T_stat + exp(2t) T_pot), and half-clock norm-square bounds for
   the resolvent difference R_{S(t)}(a) f - R_{H(t)}(a) f. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualResolventRadialRootRegularity
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianComponentResolventBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorUnconditionalOperatorFormEnergy
  (residual_mem_residualForm_domain residual_mem_staticRoot_domain
    residual_mem_potentialForm_domain residual_form_energy_eq_residualOutput
    residual_form_energy_eq_split)
open KFCausalClockFloorHamiltonianResolventFormBounds
  (residualResolventPoint residual_resolvent_mem_staticRoot_domain
    residual_resolvent_mem_potentialForm_domain
    residual_resolvent_mem_residualForm_domain
    residual_resolvent_pairing_le
    residual_resolvent_two_channel_energy_le
    residual_resolvent_staticRoot_norm_le
    residual_resolvent_potentialForm_norm_le)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_root_subset_clockHalf_domain static_root_clockHalf_norm_sq_le)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (residual_resolvent_norm_le)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolventPoint resolvent_mem_hamiltonian_domain resolvent_mem_radial_domain
    resolvent_mem_residual_domain resolvent_equation resolvent_residual_eq_sub
    resolvent_operator_sum resolvent_hamiltonian_norm_sq_add_scaled_sq_le
    resolvent_norm_le resolvent_component_norm_sq_le_sharp)

private theorem accretive_resolvent_energy_split {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x : H)).re) (f : H) :
    ‖T (KFCausalPositiveResolventBounds.point T R a hr f)‖ ^ 2 + a ^ 2 * ‖R f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let x := KFCausalPositiveResolventBounds.point T R a hr f
  have hv := KFCausalPositiveResolventBounds.point_value T R a hr f
  have hsum : T x + (a : ℂ) • R f = f := by
    rw [hv, Complex.coe_smul, sub_add_cancel]
  have hexp : ‖T x + (a : ℂ) • R f‖ ^ 2 =
      ‖T x‖ ^ 2 + 2 * (inner ℂ (T x) ((a : ℂ) • R f)).re + ‖(a : ℂ) • R f‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) (T x) ((a : ℂ) • R f)
  have hi : (inner ℂ (T x) ((a : ℂ) • R f)).re = a * (inner ℂ (T x) (x : H)).re := by
    change (inner ℂ (T x) ((a : ℂ) • (x : H))).re = a * (inner ℂ (T x) (x : H)).re
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hn : ‖(a : ℂ) • R f‖ ^ 2 = a ^ 2 * ‖R f‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  have hpos : 0 ≤ 2 * (a * (inner ℂ (T x) (x : H)).re) :=
    mul_nonneg zero_le_two (mul_nonneg ha.le (hp x))
  rw [hsum, hi, hn] at hexp
  linarith

private theorem subst_energy_le {e s b c : ℝ} (he : e = s) (hp : e + b ≤ c) : s + b ≤ c := by
  rw [← he]
  exact hp

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k t
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k t
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k t

/-! ### 1. Residual Resolvent Operator & Form EnergyPreliminaries -/

theorem residual_resolvent_mem_residual_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f ∈ (S).domain :=
  (residualResolventPoint ε hε h hh hb m g k t a ha f).property

theorem residual_resolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      f - a • RS a f :=
  KFCausalPositiveResolventBounds.point_value S (RS a) a
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem residual_resolvent_left_inverse (a : ℝ) (ha : 0 < a) (x : (S).domain) :
    RS a (S x + a • (x : Hilbert)) = (x : Hilbert) :=
  KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha x

theorem residual_resolvent_operator_norm_sq_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      a ^ 2 * ‖RS a f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  accretive_resolvent_energy_split S (RS a) a ha
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive SD) f

theorem residual_resolvent_operator_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h1 := residual_resolvent_operator_norm_sq_add_scaled_sq_le ε hε h hh hb m g k t a ha f
  have h2 : 0 ≤ a ^ 2 * ‖RS a f‖ ^ 2 := by positivity
  linarith

theorem residual_resolvent_residualForm_energy_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tres ⟨RS a f, residual_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      a * ‖RS a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
  subst_energy_le
    (residual_form_energy_eq_residualOutput ε hε h hh hb m g k t
      (residualResolventPoint ε hε h hh hb m g k t a ha f))
    (residual_resolvent_pairing_le ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_residualForm_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tres ⟨RS a f, residual_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := residual_resolvent_residualForm_energy_add_scaled_sq_le ε hε h hh hb m g k t a ha f
  have h2 : 0 ≤ a * ‖RS a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem residual_resolvent_two_channel_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS a f, residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖Tpot ⟨RS a f, residual_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := residual_resolvent_two_channel_energy_le ε hε h hh hb m g k t a ha f
  have h2 : 0 ≤ a * ‖RS a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

/-! ### 2. Shifted Residual Equation and Exact Second Resolvent Identity -/

theorem hamiltonian_resolvent_shifted_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    H ⟨RH a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ +
      (a : ℂ) • RH a f = f := by
  rw [resolvent_equation ε hε h hh hb m g k t a ha f, Complex.coe_smul, sub_add_cancel]

theorem hamiltonian_resolvent_shifted_residual_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ +
      (a : ℂ) • RH a f =
      f - (Real.exp (2 * t) : ℂ) •
        K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ := by
  rw [resolvent_residual_eq_sub ε hε h hh hb m g k t a ha f,
    resolvent_equation ε hε h hh hb m g k t a ha f, ← Complex.coe_smul]
  abel

theorem hamiltonian_resolvent_shifted_residual_eq_real (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ +
      a • RH a f =
      f - (Real.exp (2 * t) : ℂ) •
        K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ := by
  rw [← Complex.coe_smul]
  exact hamiltonian_resolvent_shifted_residual_eq ε hε h hh hb m g k t a ha f

theorem hamiltonian_resolvent_eq_residual_resolvent_shifted_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH a f = RS a (f - (Real.exp (2 * t) : ℂ) •
      K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) := by
  have hlinv := residual_resolvent_left_inverse ε hε h hh hb m g k t a ha
    ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩
  change RS a (S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ +
    a • RH a f) = RH a f at hlinv
  rw [hamiltonian_resolvent_shifted_residual_eq_real ε hε h hh hb m g k t a ha f] at hlinv
  exact hlinv.symm

theorem hamiltonian_resolvent_second_resolvent_identity (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH a f = RS a f - (Real.exp (2 * t) : ℂ) •
      RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) :=
  (hamiltonian_resolvent_eq_residual_resolvent_shifted_source ε hε h hh hb m g k t a ha f).trans
    ((map_sub (RS a) f _).trans
      (congrArg (fun u : Hilbert => RS a f - u) (map_smul (RS a) (Real.exp (2 * t) : ℂ) _)))

theorem residual_sub_hamiltonian_resolvent_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f = (Real.exp (2 * t) : ℂ) •
      RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) :=
  (congrArg (fun u : Hilbert => RS a f - u)
    (hamiltonian_resolvent_second_resolvent_identity ε hε h hh hb m g k t a ha f)).trans
    (sub_sub_cancel _ _)

theorem residual_sub_hamiltonian_resolvent_mem_residual_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f ∈ (S).domain :=
  (S).domain.sub_mem
    (residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f)
    (resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f)

theorem residual_on_residual_sub_hamiltonian_resolvent_eq_scaled_residual_resolvent
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
      S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      (Real.exp (2 * t) : ℂ) •
        S ⟨RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩),
          residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha _⟩ := by
  let xS : (S).domain := ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩
  let xH : (S).domain := ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩
  let xK : (S).domain :=
    ⟨RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩),
      residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha _⟩
  have hsub : xS - xH = (Real.exp (2 * t) : ℂ) • xK :=
    Subtype.ext (residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f)
  exact ((S).map_sub xS xH).symm.trans ((congrArg S hsub).trans ((S).map_smul _ xK))

theorem residual_on_residual_sub_hamiltonian_resolvent_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
      S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      (Real.exp (2 * t) : ℂ) • K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ -
        (a * Real.exp (2 * t) : ℂ) •
          RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) := by
  rw [residual_on_residual_sub_hamiltonian_resolvent_eq_scaled_residual_resolvent
      ε hε h hh hb m g k t a ha f,
    residual_resolvent_equation ε hε h hh hb m g k t a ha _,
    smul_sub, ← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul,
    mul_comm (Real.exp (2 * t)) a, Complex.ofReal_mul]

theorem residual_on_hamiltonian_resolvent_eq_sub (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
        (Real.exp (2 * t) : ℂ) •
          S ⟨RS a (K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩),
            residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha _⟩ :=
  (sub_sub_cancel
    (S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)
    (S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)).symm.trans
    (congrArg (fun u : Hilbert =>
      S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ - u)
      (residual_on_residual_sub_hamiltonian_resolvent_eq_scaled_residual_resolvent
        ε hε h hh hb m g k t a ha f))

/-! ### 3. Unconditional Norm and Multi-Channel Form-Energy Bounds -/

theorem hamiltonian_resolvent_radial_norm_sq_le_source_sharp (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (4 * t) *
      ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 := by
  have hc := resolvent_component_norm_sq_le_sharp ε hε h hh hb m g k t a ha f
  have hs0 : 0 ≤ ‖S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 :=
    sq_nonneg _
  have hh_sq : ‖H ⟨RH a f, resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      ‖f‖ ^ 2 := by
    have he := resolvent_hamiltonian_norm_sq_add_scaled_sq_le ε hε h hh hb m g k t a ha f
    have ha0 : 0 ≤ a ^ 2 * ‖RH a f‖ ^ 2 := by positivity
    linarith
  have hr_sq : ‖RH a f‖ ^ 2 ≤ (a⁻¹) ^ 2 * ‖f‖ ^ 2 := by
    have hr := resolvent_norm_le ε hε h hh hb m g k t a ha f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hr
    simpa only [mul_pow] using hsq
  have hmul : 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * ‖RH a f‖ ^ 2 ≤
      2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * ((a⁻¹) ^ 2 * ‖f‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hr_sq (by positivity)
  linarith

theorem residual_sub_hamiltonian_resolvent_norm_le_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RS a f - RH a f‖ ≤
      a⁻¹ * Real.exp (2 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ := by
  let kVec := K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩
  have heq : ‖RS a f - RH a f‖ = Real.exp (2 * t) * ‖RS a kVec‖ := by
    refine (congrArg norm (residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f)).trans ?_
    change ‖(Real.exp (2 * t) : ℂ) • RS a kVec‖ = Real.exp (2 * t) * ‖RS a kVec‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have hr := residual_resolvent_norm_le ε hε h hh hb m g k t a ha kVec
  calc
    ‖RS a f - RH a f‖ = Real.exp (2 * t) * ‖RS a kVec‖ := heq
    _ ≤ Real.exp (2 * t) * (a⁻¹ * ‖kVec‖) :=
      mul_le_mul_of_nonneg_left hr (Real.exp_pos (2 * t)).le
    _ = a⁻¹ * Real.exp (2 * t) * ‖kVec‖ := by ring

theorem residual_sub_hamiltonian_resolvent_norm_sq_le_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RS a f - RH a f‖ ^ 2 ≤
      (a⁻¹) ^ 2 * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _)
    (residual_sub_hamiltonian_resolvent_norm_le_radial ε hε h hh hb m g k t a ha f) 2
  have he : Real.exp (2 * t) ^ 2 = Real.exp (4 * t) := by
    rw [sq, ← Real.exp_add, show 2 * t + 2 * t = 4 * t by ring]
  calc
    ‖RS a f - RH a f‖ ^ 2 ≤
        (a⁻¹ * Real.exp (2 * t) *
          ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖) ^ 2 := h1
    _ = (a⁻¹) ^ 2 * Real.exp (2 * t) ^ 2 *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by ring
    _ = (a⁻¹) ^ 2 * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by rw [he]

theorem residual_sub_hamiltonian_resolvent_norm_sq_le_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RS a f - RH a f‖ ^ 2 ≤
      (a⁻¹) ^ 2 * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 := by
  have h1 := residual_sub_hamiltonian_resolvent_norm_sq_le_radial ε hε h hh hb m g k t a ha f
  have h2 := hamiltonian_resolvent_radial_norm_sq_le_source_sharp ε hε h hh hb m g k t a ha f
  have hmul := mul_le_mul_of_nonneg_left h2 (sq_nonneg a⁻¹)
  linarith

theorem residual_action_diff_norm_le_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
      S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.exp (2 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ := by
  let kVec := K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩
  let sK := S ⟨RS a kVec, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha kVec⟩
  have heq : ‖S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
      S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ =
      Real.exp (2 * t) * ‖sK‖ := by
    refine (congrArg norm
      (residual_on_residual_sub_hamiltonian_resolvent_eq_scaled_residual_resolvent
        ε hε h hh hb m g k t a ha f)).trans ?_
    change ‖(Real.exp (2 * t) : ℂ) • sK‖ = Real.exp (2 * t) * ‖sK‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (residual_resolvent_operator_norm_le ε hε h hh hb m g k t a ha kVec)
    (Real.exp_pos (2 * t)).le

theorem residual_action_diff_norm_le_two_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖S ⟨RS a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ -
      S ⟨RH a f, resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      2 * Real.exp (2 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ := by
  have h1 := residual_action_diff_norm_le_radial ε hε h hh hb m g k t a ha f
  have h0 : 0 ≤ Real.exp (2 * t) *
      ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ :=
    mul_nonneg (Real.exp_pos (2 * t)).le (norm_nonneg _)
  linarith

theorem residual_sub_hamiltonian_resolvent_mem_residualForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f ∈ (Tres).domain :=
  residual_mem_residualForm_domain ε hε h hh hb m g k t
    ⟨RS a f - RH a f, residual_sub_hamiltonian_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩

theorem residual_sub_hamiltonian_resolvent_mem_staticRoot_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f ∈ (Tstat).domain :=
  residual_mem_staticRoot_domain ε hε h hh hb m g k t
    ⟨RS a f - RH a f, residual_sub_hamiltonian_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩

theorem residual_sub_hamiltonian_resolvent_mem_potentialForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f ∈ (Tpot).domain :=
  residual_mem_potentialForm_domain ε hε h hh hb m g k t
    ⟨RS a f - RH a f, residual_sub_hamiltonian_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩

theorem residual_sub_hamiltonian_resolvent_mem_clockHalf_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS a f - RH a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RS a f - RH a f)
    (residual_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)

theorem residual_sub_hamiltonian_resolvent_residualForm_norm_sq_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tres ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  let kVec := K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩
  let xDiff : (Tres).domain :=
    ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f⟩
  let xK : (Tres).domain :=
    ⟨RS a kVec, residual_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha kVec⟩
  have hsub : xDiff = (Real.exp (2 * t) : ℂ) • xK :=
    Subtype.ext (residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f)
  have hmap : Tres xDiff = (Real.exp (2 * t) : ℂ) • Tres xK :=
    (congrArg Tres hsub).trans ((Tres).map_smul _ xK)
  have he : Real.exp (2 * t) ^ 2 = Real.exp (4 * t) := by
    rw [sq, ← Real.exp_add, show 2 * t + 2 * t = 4 * t by ring]
  have hnorm : ‖Tres xDiff‖ ^ 2 = Real.exp (4 * t) * ‖Tres xK‖ ^ 2 := by
    rw [hmap, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2 * t)), mul_pow, he]
  have hbK := residual_resolvent_residualForm_norm_sq_le ε hε h hh hb m g k t a ha kVec
  have hmul := mul_le_mul_of_nonneg_left hbK (Real.exp_pos (4 * t)).le
  change ‖Tres xDiff‖ ^ 2 ≤ a⁻¹ * Real.exp (4 * t) * ‖kVec‖ ^ 2
  rw [hnorm]
  linarith

theorem residual_sub_hamiltonian_resolvent_two_channel_norm_sq_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖Tpot ⟨RS a f - RH a f,
          residual_sub_hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 =
      ‖Tres ⟨RS a f - RH a f,
        residual_sub_hamiltonian_resolvent_mem_residualForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  let x : (S).domain :=
    ⟨RS a f - RH a f, residual_sub_hamiltonian_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩
  exact (residual_form_energy_eq_split ε hε h hh hb m g k t x).symm.trans
    (residual_form_energy_eq_residualOutput ε hε h hh hb m g k t x)

theorem residual_sub_hamiltonian_resolvent_two_channel_norm_sq_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖Tpot ⟨RS a f - RH a f,
          residual_sub_hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  rw [residual_sub_hamiltonian_resolvent_two_channel_norm_sq_eq ε hε h hh hb m g k t a ha f]
  exact residual_sub_hamiltonian_resolvent_residualForm_norm_sq_le_radial
    ε hε h hh hb m g k t a ha f

theorem residual_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  have h1 := residual_sub_hamiltonian_resolvent_two_channel_norm_sq_le_radial
    ε hε h hh hb m g k t a ha f
  have h2 : 0 ≤ Real.exp (2 * t) *
      ‖Tpot ⟨RS a f - RH a f,
        residual_sub_hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 :=
    mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _)
  linarith

theorem residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * Real.exp (4 * t) *
        ‖K ⟨RH a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RS a f - RH a f)
    (residual_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)
  have h2 := residual_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_radial
    ε hε h hh hb m g k t a ha f
  linarith

theorem residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_source
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RS a f - RH a f,
      residual_sub_hamiltonian_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 := by
  have h1 := residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_radial
    ε hε h hh hb m g k t a ha f
  have h2 := hamiltonian_resolvent_radial_norm_sq_le_source_sharp ε hε h hh hb m g k t a ha f
  have hmul := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * a⁻¹ by positivity)
  linarith

#print axioms residual_resolvent_mem_residual_domain
#print axioms residual_resolvent_equation
#print axioms residual_resolvent_left_inverse
#print axioms residual_resolvent_operator_norm_sq_add_scaled_sq_le
#print axioms residual_resolvent_operator_norm_le
#print axioms residual_resolvent_residualForm_energy_add_scaled_sq_le
#print axioms residual_resolvent_residualForm_norm_sq_le
#print axioms residual_resolvent_two_channel_norm_sq_le
#print axioms hamiltonian_resolvent_shifted_eq
#print axioms hamiltonian_resolvent_shifted_residual_eq
#print axioms hamiltonian_resolvent_shifted_residual_eq_real
#print axioms hamiltonian_resolvent_eq_residual_resolvent_shifted_source
#print axioms hamiltonian_resolvent_second_resolvent_identity
#print axioms residual_sub_hamiltonian_resolvent_eq
#print axioms residual_sub_hamiltonian_resolvent_mem_residual_domain
#print axioms residual_on_residual_sub_hamiltonian_resolvent_eq_scaled_residual_resolvent
#print axioms residual_on_residual_sub_hamiltonian_resolvent_eq
#print axioms residual_on_hamiltonian_resolvent_eq_sub
#print axioms hamiltonian_resolvent_radial_norm_sq_le_source_sharp
#print axioms residual_sub_hamiltonian_resolvent_norm_le_radial
#print axioms residual_sub_hamiltonian_resolvent_norm_sq_le_radial
#print axioms residual_sub_hamiltonian_resolvent_norm_sq_le_source
#print axioms residual_action_diff_norm_le_radial
#print axioms residual_action_diff_norm_le_two_radial
#print axioms residual_sub_hamiltonian_resolvent_mem_residualForm_domain
#print axioms residual_sub_hamiltonian_resolvent_mem_staticRoot_domain
#print axioms residual_sub_hamiltonian_resolvent_mem_potentialForm_domain
#print axioms residual_sub_hamiltonian_resolvent_mem_clockHalf_domain
#print axioms residual_sub_hamiltonian_resolvent_residualForm_norm_sq_le_radial
#print axioms residual_sub_hamiltonian_resolvent_two_channel_norm_sq_eq
#print axioms residual_sub_hamiltonian_resolvent_two_channel_norm_sq_le_radial
#print axioms residual_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_radial
#print axioms residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_radial
#print axioms residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_source
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
