/- Component-level domain membership, positive potential-radial pairing,
and norm-square energy bounds for all positive shifted resolvents of the
actual growing clock-floor Hamiltonian G = Kr + P, together with uniform
contraction and strong convergence of the radial resolvent regularizer on
every growing-resolvent state. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum
import UnifiedTheory.Audit.KFCausalClockFloorGrowingClockResolvent
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingComponentResolventBounds
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
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k

def resolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (G).domain :=
  KFCausalPositiveResolventBounds.point G (RG a) a
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) f

theorem resolvent_mem_growing_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (G).domain :=
  (resolventPoint ε hε h hh hb m g k a ha f).property

theorem resolvent_mem_radial_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (K).domain :=
  KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k
    (resolventPoint ε hε h hh hb m g k a ha f)

theorem resolvent_mem_potential_domain (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (P).domain :=
  KFCausalClockFloorGrowingPotentialSum.potential_domain ε hε h hh hb m g k
    (resolventPoint ε hε h hh hb m g k a ha f)

theorem resolvent_mem_clockHalf_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    RG a f ∈ (clockHalf ε).domain :=
  KFCausalClockFloorGrowingClockResolvent.resolvent_half_domain ε hε h hh hw m g k a ha f hf

theorem resolvent_clockHalf_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨RG a f,resolvent_mem_clockHalf_domain ε hε h hh hb m g k a ha f hf⟩‖ ≤
      a⁻¹*‖clockHalf ε ⟨f,hf⟩‖ :=
  KFCausalClockFloorGrowingClockResolvent.resolvent_half_norm_bound ε hε h hh hw m g k a ha f hf

theorem resolvent_equation (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩ =
      f-a • RG a f :=
  KFCausalPositiveResolventBounds.point_value G (RG a) a
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) f

theorem resolvent_potential_eq_sub (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ =
      G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩-
        K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩ :=
  (P).mem_graph_snd_inj' ((P).mem_graph _)
    (KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb m g k
      (resolventPoint ε hε h hh hb m g k a ha f)) rfl

theorem resolvent_operator_sum (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩ =
      K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩+
        P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩ := by
  rw [resolvent_potential_eq_sub ε hε h hh hb m g k a ha f]
  abel

theorem resolvent_potential_radial_pairing_nonneg (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    0 ≤ (inner ℂ
      (P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩)
      (K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩)).re := by
  rw [resolvent_potential_eq_sub ε hε h hh hb m g k a ha f]
  exact KFCausalClockFloorGrowingRadialCrossEstimate.remainder_pairing ε hε h hh hb m g k
    (resolventPoint ε hε h hh hb m g k a ha f)

theorem resolvent_component_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖^2+
      ‖P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖^2 ≤
        ‖G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩‖^2 :=
  KFCausalClockFloorGrowingPotentialSum.split_norm_square ε hε h hh hb m g k
    (resolventPoint ε hε h hh hb m g k a ha f)

theorem resolvent_growing_norm_sq_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩‖^2+
      a^2*‖RG a f‖^2 ≤ ‖f‖^2 :=
  accretive_resolvent_energy_split G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k) f

theorem resolvent_full_component_energy_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖^2+
      ‖P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖^2+
        a^2*‖RG a f‖^2 ≤ ‖f‖^2 := by
  have hc := resolvent_component_norm_sq_le ε hε h hh hb m g k a ha f
  have hg := resolvent_growing_norm_sq_add_scaled_sq_le ε hε h hh hb m g k a ha f
  linarith

theorem resolvent_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RG a f‖ ≤ a⁻¹*‖f‖ :=
  KFCausalPositiveResolventBounds.resolvent_apply_norm_bound G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k) f

theorem resolvent_growing_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖G ⟨RG a f,resolvent_mem_growing_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hg := resolvent_growing_norm_sq_add_scaled_sq_le ε hε h hh hb m g k a ha f
  have ha0 : 0 ≤ a^2*‖RG a f‖^2 := by positivity
  linarith

theorem resolvent_radial_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hf := resolvent_full_component_energy_le ε hε h hh hb m g k a ha f
  have hp0 : 0 ≤ ‖P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖^2 :=
    sq_nonneg _
  have ha0 : 0 ≤ a^2*‖RG a f‖^2 := by positivity
  linarith

theorem resolvent_potential_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖P ⟨RG a f,resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hf := resolvent_full_component_energy_le ε hε h hh hb m g k a ha f
  have hk0 : 0 ≤ ‖K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖^2 :=
    sq_nonneg _
  have ha0 : 0 ≤ a^2*‖RG a f‖^2 := by positivity
  linarith

theorem resolvent_regularized_radial_norm_le (a : ℝ) (ha : 0 < a)
    (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    ‖K ⟨action ε hε h N hN (RG a f),radial_domain ε hε h N hN (RG a f)⟩‖ ≤ ‖f‖ :=
  (KFCausalClockFloorRadialResolventOperator.operator_norm_le ε hε h N hN
    ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩).trans
    (resolvent_radial_norm_le ε hε h hh hb m g k a ha f)

theorem resolvent_regularized_radial_tendsto (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    Tendsto (fun n : ℕ =>
      K ⟨action ε hε h ((n:ℝ)+1) (by positivity) (RG a f),
        radial_domain ε hε h ((n:ℝ)+1) (by positivity) (RG a f)⟩)
      atTop (𝓝 (K ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩)) :=
  KFCausalClockFloorRadialResolventOperator.operator_sequence_tendsto ε hε h
    ⟨RG a f,resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩

#print axioms resolvent_mem_growing_domain
#print axioms resolvent_mem_radial_domain
#print axioms resolvent_mem_potential_domain
#print axioms resolvent_mem_clockHalf_domain
#print axioms resolvent_clockHalf_norm_le
#print axioms resolvent_equation
#print axioms resolvent_potential_eq_sub
#print axioms resolvent_operator_sum
#print axioms resolvent_potential_radial_pairing_nonneg
#print axioms resolvent_component_norm_sq_le
#print axioms resolvent_growing_norm_sq_add_scaled_sq_le
#print axioms resolvent_full_component_energy_le
#print axioms resolvent_norm_le
#print axioms resolvent_growing_norm_le
#print axioms resolvent_radial_norm_le
#print axioms resolvent_potential_norm_le
#print axioms resolvent_regularized_radial_norm_le
#print axioms resolvent_regularized_radial_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingComponentResolventBounds
