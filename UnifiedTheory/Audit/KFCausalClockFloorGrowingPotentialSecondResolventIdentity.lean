/- Unconditional exact second resolvent identity and component/form-energy
bounds between the positive potential resolvent R_P(a) = (P + a)⁻¹ and the
growing clock-floor resolvent R_G(a) = (G + a)⁻¹ for all real couplings
m, g, k ∈ ℝ and all shifts a > 0:
1. Establishes the shifted potential equation on every growing-resolvent state:
   P (R_G(a) f) + a • R_G(a) f = f - K (R_G(a) f).
2. Deduces the unconditional exact second resolvent identity on all of Hilbert:
   R_G(a) f = R_P(a) f - R_P(a) (K (R_G(a) f)),
   R_P(a) f - R_G(a) f = R_P(a) (K (R_G(a) f)),
   P (R_P(a) f) - P (R_G(a) f) = K (R_G(a) f) - a • R_P(a) (K (R_G(a) f))
                               = P (R_P(a) (K (R_G(a) f))).
3. Proves unconditional Hilbert, potential-operator, potential-form (T_pot),
   and half-clock norm bounds for the resolvent difference R_P(a) f - R_G(a) f. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingComponentResolventBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSecondResolventIdentity
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le potential_resolvent_residual_norm_le)
open KFCausalClockFloorGrowingComponentResolventBounds
  (resolventPoint resolvent_mem_growing_domain resolvent_mem_radial_domain
    resolvent_mem_potential_domain resolvent_equation resolvent_potential_eq_sub
    resolvent_operator_sum resolvent_radial_norm_le)

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

private theorem resolvent_pairing_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x : H)).re) (f : H) :
    (inner ℂ (T (KFCausalPositiveResolventBounds.point T R a hr f)) (R f)).re +
      a * ‖R f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 := by
  have hv := KFCausalPositiveResolventBounds.point_value T R a hr f
  have heq : (inner ℂ (T (KFCausalPositiveResolventBounds.point T R a hr f)) (R f)).re +
      a * ‖R f‖ ^ 2 = (inner ℂ f (R f)).re := by
    rw [hv, inner_sub_left, inner_smul_left_eq_smul,
      KFCausalShiftedForm.complex_inner_square (R f)]
    simp only [Complex.sub_re, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [heq]
  have hi : (inner ℂ f (R f)).re ≤ ‖f‖ * ‖R f‖ := re_inner_le_norm (𝕜 := ℂ) f (R f)
  have hnorm := KFCausalPositiveResolventBounds.resolvent_apply_norm_bound T R a ha hr hp f
  have hmul : ‖f‖ * ‖R f‖ ≤ ‖f‖ * (a⁻¹ * ‖f‖) :=
    mul_le_mul_of_nonneg_left hnorm (norm_nonneg f)
  linarith [show ‖f‖ * (a⁻¹ * ‖f‖) = a⁻¹ * ‖f‖ ^ 2 by ring]

private theorem subst_energy_le {e s b c : ℝ} (he : e = s) (hp : e + b ≤ c) : s + b ≤ c := by
  rw [← he]
  exact hp

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k

/-! ### 1. Potential Resolvent Equations and Form-Energy Bounds -/

theorem potential_domain_subset_potentialForm_domain (x : (P).domain) :
    (x : Hilbert) ∈ (Tpot).domain := by
  let u := KFCausalClosedGraphForm.formLift PD x
  have hJ : KFCausalClosedGraphForm.embedding PD u = (x : Hilbert) :=
    KFCausalClosedGraphForm.embedding_formLift PD x
  exact hJ ▸ LinearPMap.mem_domain_of_mem_graph u.property

theorem potential_form_energy_eq_potentialOutput (x : (P).domain) :
    (inner ℂ (P x) (x : Hilbert)).re =
      ‖Tpot ⟨(x : Hilbert), potential_domain_subset_potentialForm_domain ε hε h hh hb m g k x⟩‖ ^ 2 := by
  let u := KFCausalClosedGraphForm.formLift PD x
  have hout := form_output_eq_operator PD u (x : Hilbert)
    (KFCausalClosedGraphForm.embedding_formLift PD x)
    (potential_domain_subset_potentialForm_domain ε hε h hh hb m g k x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy PD x).trans
    (congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout)

def potentialResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (P).domain :=
  KFCausalPositiveResolventBounds.point P (RP a) a
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) f

theorem potential_resolvent_mem_potential_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f ∈ (P).domain :=
  (potentialResolventPoint ε hε h hh hb m g k a ha f).property

theorem potential_resolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ =
      f - a • RP a f :=
  KFCausalPositiveResolventBounds.point_value P (RP a) a
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) f

theorem potential_resolvent_left_inverse (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    RP a (P x + a • (x : Hilbert)) = (x : Hilbert) :=
  KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k a ha x

theorem potential_resolvent_mem_potentialForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f ∈ (Tpot).domain :=
  potential_domain_subset_potentialForm_domain ε hε h hh hb m g k
    (potentialResolventPoint ε hε h hh hb m g k a ha f)

theorem potential_resolvent_form_energy_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f, potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      a * ‖RP a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
  subst_energy_le
    (potential_form_energy_eq_potentialOutput ε hε h hh hb m g k
      (potentialResolventPoint ε hε h hh hb m g k a ha f))
    (resolvent_pairing_le P (RP a) a ha
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
      (KFCausalClosedGraphForm.hamiltonian_positive PD) f)

theorem potential_resolvent_potentialForm_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f, potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := potential_resolvent_form_energy_add_scaled_sq_le ε hε h hh hb m g k a ha f
  have h2 : 0 ≤ a * ‖RP a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem potential_resolvent_potentialForm_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f, potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      Real.sqrt (a⁻¹) * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  exact potential_resolvent_potentialForm_norm_sq_le ε hε h hh hb m g k a ha f

theorem potential_resolvent_operator_norm_sq_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      a ^ 2 * ‖RP a f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  accretive_resolvent_energy_split P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) f

theorem potential_resolvent_operator_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h1 := potential_resolvent_operator_norm_sq_add_scaled_sq_le ε hε h hh hb m g k a ha f
  have h2 : 0 ≤ a ^ 2 * ‖RP a f‖ ^ 2 := by positivity
  linarith

/-! ### 2. Shifted Potential Equation and Exact Second Resolvent Identity -/

theorem growing_resolvent_shifted_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    G ⟨RG a f, resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩ +
      (a : ℂ) • RG a f = f := by
  rw [resolvent_equation ε hε h hh hb m g k a ha f, Complex.coe_smul, sub_add_cancel]

theorem growing_resolvent_shifted_potential_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ +
      (a : ℂ) • RG a f =
      f - K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ := by
  rw [resolvent_potential_eq_sub ε hε h hh hb m g k a ha f,
    resolvent_equation ε hε h hh hb m g k a ha f, Complex.coe_smul]
  abel

theorem growing_resolvent_shifted_potential_eq_real (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ +
      a • RG a f =
      f - K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ := by
  rw [← Complex.coe_smul]
  exact growing_resolvent_shifted_potential_eq ε hε h hh hb m g k a ha f

theorem growing_resolvent_eq_potential_resolvent_shifted_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f = RP a (f - K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩) := by
  have hlinv := potential_resolvent_left_inverse ε hε h hh hb m g k a ha
    ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩
  change RP a (P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ +
    a • RG a f) = RG a f at hlinv
  rw [growing_resolvent_shifted_potential_eq_real ε hε h hh hb m g k a ha f] at hlinv
  exact hlinv.symm

theorem growing_resolvent_second_resolvent_identity (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f = RP a f - RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩) :=
  (growing_resolvent_eq_potential_resolvent_shifted_source ε hε h hh hb m g k a ha f).trans
    (map_sub (RP a) f _)

theorem potential_sub_growing_resolvent_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f - RG a f = RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩) :=
  (congrArg (fun u : Hilbert => RP a f - u)
    (growing_resolvent_second_resolvent_identity ε hε h hh hb m g k a ha f)).trans
    (sub_sub_cancel _ _)

theorem potential_sub_growing_resolvent_mem_potential_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f - RG a f ∈ (P).domain :=
  (P).domain.sub_mem
    (potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f)
    (resolvent_mem_potential_domain ε hε h hh hb m g k a ha f)

theorem potential_on_potential_sub_growing_resolvent_eq_potential_resolvent (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ =
      P ⟨RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩),
        potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _⟩ := by
  let xP : (P).domain := ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩
  let xG : (P).domain := ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩
  let xK : (P).domain :=
    ⟨RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩),
      potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _⟩
  have hsub : xP - xG = xK :=
    Subtype.ext (potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f)
  exact ((P).map_sub xP xG).symm.trans (congrArg P hsub)

theorem potential_on_potential_sub_growing_resolvent_eq (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ =
      K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ -
        (a : ℂ) • RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩) := by
  rw [potential_on_potential_sub_growing_resolvent_eq_potential_resolvent ε hε h hh hb m g k a ha f,
    potential_resolvent_equation ε hε h hh hb m g k a ha _, Complex.coe_smul]

theorem potential_on_growing_resolvent_eq_sub (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ =
      P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
        P ⟨RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩),
          potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _⟩ :=
  (sub_sub_cancel
    (P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩)
    (P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩)).symm.trans
    (congrArg (fun u : Hilbert =>
      P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ - u)
      (potential_on_potential_sub_growing_resolvent_eq_potential_resolvent ε hε h hh hb m g k a ha f))

/-! ### 3. Unconditional Hilbert, Potential, Form-Energy, and Half-Clock Bounds -/

theorem potential_sub_growing_resolvent_norm_le_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RP a f - RG a f‖ ≤
      a⁻¹ * ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ :=
  (congrArg norm (potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f)).trans_le
    (potential_resolvent_norm_le ε hε h hb hh m g k a ha _)

theorem potential_sub_growing_resolvent_norm_le_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RP a f - RG a f‖ ≤ a⁻¹ * ‖f‖ :=
  (potential_sub_growing_resolvent_norm_le_radial ε hε h hh hb m g k a ha f).trans
    (mul_le_mul_of_nonneg_left
      (resolvent_radial_norm_le ε hε h hh hb m g k a ha f)
      (inv_nonneg.mpr ha.le))

theorem potential_action_diff_norm_le_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ :=
  (congrArg norm
    (potential_on_potential_sub_growing_resolvent_eq_potential_resolvent ε hε h hh hb m g k a ha f)).trans_le
    (potential_resolvent_operator_norm_le ε hε h hh hb m g k a ha _)

theorem potential_action_diff_norm_le_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ :=
  (potential_action_diff_norm_le_radial ε hε h hh hb m g k a ha f).trans
    (resolvent_radial_norm_le ε hε h hh hb m g k a ha f)

theorem potential_action_diff_norm_le_two_radial (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      2 * ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ := by
  have h1 := potential_action_diff_norm_le_radial ε hε h hh hb m g k a ha f
  have h0 : 0 ≤ ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ :=
    norm_nonneg _
  linarith

theorem potential_action_diff_norm_le_two_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ -
      P ⟨RG a f, resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤ 2 * ‖f‖ :=
  (potential_action_diff_norm_le_two_radial ε hε h hh hb m g k a ha f).trans
    (mul_le_mul_of_nonneg_left
      (resolvent_radial_norm_le ε hε h hh hb m g k a ha f)
      zero_le_two)

theorem potential_sub_growing_resolvent_mem_potentialForm_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f - RG a f ∈ (Tpot).domain :=
  potential_domain_subset_potentialForm_domain ε hε h hh hb m g k
    ⟨RP a f - RG a f, potential_sub_growing_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩

theorem potential_sub_growing_resolvent_potentialForm_norm_sq_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f - RG a f,
      potential_sub_growing_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 := by
  have hsub : (⟨RP a f - RG a f,
      potential_sub_growing_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩ :
      (Tpot).domain) =
    ⟨RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩),
      potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha _⟩ :=
    Subtype.ext (potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f)
  exact (congrArg (fun x : (Tpot).domain => ‖Tpot x‖ ^ 2) hsub).trans_le
    (potential_resolvent_potentialForm_norm_sq_le ε hε h hh hb m g k a ha _)

theorem potential_sub_growing_resolvent_potentialForm_norm_sq_le_source
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f - RG a f,
      potential_sub_growing_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := potential_sub_growing_resolvent_potentialForm_norm_sq_le_radial
    ε hε h hh hb m g k a ha f
  have h2 : ‖K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (resolvent_radial_norm_le ε hε h hh hb m g k a ha f) 2
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ha.le))

theorem potential_sub_growing_resolvent_mem_clockHalf_domain_of_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hK : K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ ∈ (clockHalf ε).domain) :
    RP a f - RG a f ∈ (clockHalf ε).domain :=
  (congrArg (fun u : Hilbert => u ∈ (clockHalf ε).domain)
    (potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f)).mpr
    (KFCausalClockFloorPotentialClockResolvent.resolvent_half_domain
      ε hε h hh hw m g k a ha _ hK)

theorem potential_sub_growing_resolvent_clockHalf_norm_le_of_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hK : K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨RP a f - RG a f,
      potential_sub_growing_resolvent_mem_clockHalf_domain_of_radial ε hε h hh hb m g k a ha f hK⟩‖ ≤
      a⁻¹ * ‖clockHalf ε ⟨K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩, hK⟩‖ := by
  have hsub : (⟨RP a f - RG a f,
      potential_sub_growing_resolvent_mem_clockHalf_domain_of_radial ε hε h hh hb m g k a ha f hK⟩ :
      (clockHalf ε).domain) =
    ⟨RP a (K ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩),
      KFCausalClockFloorPotentialClockResolvent.resolvent_half_domain
        ε hε h hh hw m g k a ha _ hK⟩ :=
    Subtype.ext (potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f)
  exact (congrArg (fun x : (clockHalf ε).domain => ‖clockHalf ε x‖) hsub).trans_le
    (KFCausalClockFloorPotentialClockResolvent.resolvent_half_norm_bound
      ε hε h hh hw m g k a ha _ hK)

#print axioms potential_domain_subset_potentialForm_domain
#print axioms potential_form_energy_eq_potentialOutput
#print axioms potential_resolvent_mem_potential_domain
#print axioms potential_resolvent_equation
#print axioms potential_resolvent_left_inverse
#print axioms potential_resolvent_mem_potentialForm_domain
#print axioms potential_resolvent_form_energy_add_scaled_sq_le
#print axioms potential_resolvent_potentialForm_norm_sq_le
#print axioms potential_resolvent_potentialForm_norm_le
#print axioms potential_resolvent_operator_norm_sq_add_scaled_sq_le
#print axioms potential_resolvent_operator_norm_le
#print axioms growing_resolvent_shifted_eq
#print axioms growing_resolvent_shifted_potential_eq
#print axioms growing_resolvent_shifted_potential_eq_real
#print axioms growing_resolvent_eq_potential_resolvent_shifted_source
#print axioms growing_resolvent_second_resolvent_identity
#print axioms potential_sub_growing_resolvent_eq
#print axioms potential_sub_growing_resolvent_mem_potential_domain
#print axioms potential_on_potential_sub_growing_resolvent_eq_potential_resolvent
#print axioms potential_on_potential_sub_growing_resolvent_eq
#print axioms potential_on_growing_resolvent_eq_sub
#print axioms potential_sub_growing_resolvent_norm_le_radial
#print axioms potential_sub_growing_resolvent_norm_le_source
#print axioms potential_action_diff_norm_le_radial
#print axioms potential_action_diff_norm_le_source
#print axioms potential_action_diff_norm_le_two_radial
#print axioms potential_action_diff_norm_le_two_source
#print axioms potential_sub_growing_resolvent_mem_potentialForm_domain
#print axioms potential_sub_growing_resolvent_potentialForm_norm_sq_le_radial
#print axioms potential_sub_growing_resolvent_potentialForm_norm_sq_le_source
#print axioms potential_sub_growing_resolvent_mem_clockHalf_domain_of_radial
#print axioms potential_sub_growing_resolvent_clockHalf_norm_le_of_radial
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSecondResolventIdentity
