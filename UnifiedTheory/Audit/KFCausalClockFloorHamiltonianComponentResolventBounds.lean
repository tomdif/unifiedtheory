/- Component-level domain membership, operator splitting H(t) = exp(2t) Kr + S(t),
and norm-square bounds for all positive shifted resolvents of the full
time-dependent clock-floor Hamiltonian, together with uniform radial resolvent
regularization bounds and strong convergence on every Hamiltonian-resolvent state. -/
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialCrossEstimate
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianComponentResolventBounds
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain)

private theorem accretive_resolvent_energy_split {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x:H)).re) (f : H) :
    ‖T (KFCausalPositiveResolventBounds.point T R a hr f)‖^2+a^2*‖R f‖^2 ≤ ‖f‖^2 := by
  let x := KFCausalPositiveResolventBounds.point T R a hr f
  have hv := KFCausalPositiveResolventBounds.point_value T R a hr f
  have hsum : T x+(a:ℂ) • R f=f := by
    rw [hv,Complex.coe_smul,sub_add_cancel]
  have hexp : ‖T x+(a:ℂ) • R f‖^2=
      ‖T x‖^2+2*(inner ℂ (T x) ((a:ℂ) • R f)).re+‖(a:ℂ) • R f‖^2 :=
    norm_add_sq (𝕜 := ℂ) (T x) ((a:ℂ) • R f)
  have hi : (inner ℂ (T x) ((a:ℂ) • R f)).re=a*(inner ℂ (T x) (x:H)).re := by
    change (inner ℂ (T x) ((a:ℂ) • (x:H))).re=a*(inner ℂ (T x) (x:H)).re
    rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hn : ‖(a:ℂ) • R f‖^2=a^2*‖R f‖^2 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,mul_pow]
  have hpos : 0 ≤ 2*(a*(inner ℂ (T x) (x:H)).re) :=
    mul_nonneg zero_le_two (mul_nonneg ha.le (hp x))
  rw [hsum,hi,hn] at hexp
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k t

def resolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (H).domain :=
  KFCausalPositiveResolventBounds.point H (RH a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem resolvent_mem_hamiltonian_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH a f ∈ (H).domain :=
  (resolventPoint ε hε h hh hb m g k t a ha f).property

theorem resolvent_mem_radial_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH a f ∈ (K).domain :=
  KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m g k t
    (resolventPoint ε hε h hh hb m g k t a ha f)

theorem resolvent_mem_residual_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH a f ∈ (S).domain :=
  KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb m g k t
    (resolventPoint ε hε h hh hb m g k t a ha f)

theorem resolvent_mem_clockHalf_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    RH a f ∈ (clockHalf ε).domain :=
  KFCausalClockFloorHamiltonianClockCore.resolvent_half_domain ε hε h hh hw m g k t a ha f hf

theorem resolvent_clockHalf_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨RH a f,resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f hf⟩‖ ≤
      a⁻¹*‖clockHalf ε ⟨f,hf⟩‖ :=
  KFCausalClockFloorHamiltonianClockCore.resolvent_half_norm_bound ε hε h hh hw m g k t a ha f hf

theorem resolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ =
      f-a • RH a f :=
  KFCausalPositiveResolventBounds.point_value H (RH a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha) f

theorem resolvent_residual_eq_sub (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ =
      H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩-
        (Real.exp (2*t):ℂ) • K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩ :=
  KFCausalClockFloorHamiltonianRadialSum.residual_output ε hε h hh hb m g k t
    (resolventPoint ε hε h hh hb m g k t a ha f)

theorem resolvent_operator_sum (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩ =
      (Real.exp (2*t):ℂ) • K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩+
        S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩ := by
  rw [resolvent_residual_eq_sub ε hε h hh hb m g k t a ha f]
  abel

theorem resolvent_hamiltonian_norm_sq_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      a^2*‖RH a f‖^2 ≤ ‖f‖^2 :=
  accretive_resolvent_energy_split H (RH a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f

theorem resolvent_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RH a f‖ ≤ a⁻¹*‖f‖ :=
  KFCausalPositiveResolventBounds.resolvent_apply_norm_bound H (RH a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f

theorem resolvent_hamiltonian_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh_sq := resolvent_hamiltonian_norm_sq_add_scaled_sq_le ε hε h hh hb m g k t a ha f
  have ha0 : 0 ≤ a^2*‖RH a f‖^2 := by positivity
  linarith

theorem resolvent_residual_radial_pairing (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    -(h^2/ε^2)*‖RH a f‖^2 ≤
      (inner ℂ
        (S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩)
        (K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩)).re := by
  rw [resolvent_residual_eq_sub ε hε h hh hb m g k t a ha f]
  exact KFCausalClockFloorHamiltonianRadialCrossEstimate.residual_radial_pairing ε hε h hh hb m g k t
    (resolventPoint ε hε h hh hb m g k t a ha f)

theorem resolvent_component_norm_sq_le_sharp (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (4*t)*‖K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      ‖S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖^2 ≤
        ‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖^2+
          2*Real.exp (2*t)*(h^2/ε^2)*‖RH a f‖^2 := by
  rw [resolvent_residual_eq_sub ε hε h hh hb m g k t a ha f]
  exact KFCausalClockFloorHamiltonianRadialCrossEstimate.split_norm_square ε hε h hh hb m g k t
    (resolventPoint ε hε h hh hb m g k t a ha f)

theorem resolvent_component_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (4*t)*‖K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      ‖S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖^2 ≤
        2*‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖^2+
          2*Real.exp (2*t)*(h^2/ε^2)*‖RH a f‖^2 := by
  have hs := resolvent_component_norm_sq_le_sharp ε hε h hh hb m g k t a ha f
  have hh0 : 0 ≤ ‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖^2 :=
    sq_nonneg _
  linarith

theorem resolvent_component_norm_sq_le_source (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Real.exp (4*t)*‖K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖^2+
      ‖S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖^2 ≤
        (2+2*Real.exp (2*t)*(h^2/ε^2)*(a⁻¹)^2)*‖f‖^2 := by
  have hc := resolvent_component_norm_sq_le ε hε h hh hb m g k t a ha f
  have hh_sq : ‖H ⟨RH a f,resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f⟩‖^2 ≤ ‖f‖^2 := by
    have he := resolvent_hamiltonian_norm_sq_add_scaled_sq_le ε hε h hh hb m g k t a ha f
    have ha0 : 0 ≤ a^2*‖RH a f‖^2 := by positivity
    linarith
  have hr_sq : ‖RH a f‖^2 ≤ (a⁻¹)^2*‖f‖^2 := by
    have hr := resolvent_norm_le ε hε h hh hb m g k t a ha f
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hr
    simpa only [mul_pow] using hsq
  have hmul : 2*Real.exp (2*t)*(h^2/ε^2)*‖RH a f‖^2 ≤
      2*Real.exp (2*t)*(h^2/ε^2)*((a⁻¹)^2*‖f‖^2) :=
    mul_le_mul_of_nonneg_left hr_sq (by positivity)
  linarith

theorem resolvent_regularized_radial_norm_le_radial (a : ℝ) (ha : 0 < a)
    (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    ‖K ⟨action ε hε h N hN (RH a f),radial_domain ε hε h N hN (RH a f)⟩‖ ≤
      ‖K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ :=
  KFCausalClockFloorRadialResolventOperator.operator_norm_le ε hε h N hN
    ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩

theorem resolvent_regularized_radial_norm_sq_le (a : ℝ) (ha : 0 < a)
    (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    Real.exp (4*t)*‖K ⟨action ε hε h N hN (RH a f),radial_domain ε hε h N hN (RH a f)⟩‖^2 ≤
      (2+2*Real.exp (2*t)*(h^2/ε^2)*(a⁻¹)^2)*‖f‖^2 := by
  have h1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (resolvent_regularized_radial_norm_le_radial ε hε h hh hb m g k t a ha N hN f)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (4*t)).le
  have h3 := resolvent_component_norm_sq_le_source ε hε h hh hb m g k t a ha f
  have hs0 : 0 ≤ ‖S ⟨RH a f,resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖^2 :=
    sq_nonneg _
  linarith

theorem resolvent_regularized_radial_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      K ⟨action ε hε h ((n:ℝ)+1) (by positivity) (RH a f),
        radial_domain ε hε h ((n:ℝ)+1) (by positivity) (RH a f)⟩)
      atTop (𝓝 (K ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩)) :=
  KFCausalClockFloorRadialResolventOperator.operator_sequence_tendsto ε hε h
    ⟨RH a f,resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩

#print axioms resolvent_mem_hamiltonian_domain
#print axioms resolvent_mem_radial_domain
#print axioms resolvent_mem_residual_domain
#print axioms resolvent_mem_clockHalf_domain
#print axioms resolvent_clockHalf_norm_le
#print axioms resolvent_equation
#print axioms resolvent_residual_eq_sub
#print axioms resolvent_operator_sum
#print axioms resolvent_hamiltonian_norm_sq_add_scaled_sq_le
#print axioms resolvent_norm_le
#print axioms resolvent_hamiltonian_norm_le
#print axioms resolvent_residual_radial_pairing
#print axioms resolvent_component_norm_sq_le_sharp
#print axioms resolvent_component_norm_sq_le
#print axioms resolvent_component_norm_sq_le_source
#print axioms resolvent_regularized_radial_norm_le_radial
#print axioms resolvent_regularized_radial_norm_sq_le
#print axioms resolvent_regularized_radial_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianComponentResolventBounds
