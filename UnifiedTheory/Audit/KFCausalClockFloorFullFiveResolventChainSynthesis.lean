/- Complete Five-Operator Resolvent Chain Synthesis and Exact Static-Growing-
Hamiltonian Second Resolvent Identities for all real couplings m, g, k ∈ ℝ,
physical times t ∈ ℝ, and positive shifts a > 0:
1. Synthesizes the five positive shifted resolvents
   R_T(a) = (T + a)⁻¹, R_P(a) = (P + a)⁻¹, R_G(a) = (G + a)⁻¹,
   R_{S(t)}(a) = (S(t) + a)⁻¹, and R_{H(t)}(a) = (H(t) + a)⁻¹
   on all of Hilbert, establishing unconditional 4-resolvent radial difference
   identities, 5-resolvent telescopes, and collective Hilbert, operator-output,
   and half-clock (clockHalf) norm-square bounds.
2. Establishes the exact operator decompositions on
   Dom(H(t)) ∩ Dom(G) = Dom(H(t)) ∩ Dom(T):
   H(t) x = T x + exp(2t) • G x,
   T x = H(t) x - exp(2t) • G x,
   G x = exp(-2t) • (H(t) x - T x).
3. Deduces the exact Static-Hamiltonian Second Resolvent Identity for every state
   f : Hilbert with R_{H(t)}(a) f ∈ Dom(P) (which implies R_{H(t)}(a) f ∈ Dom(G)
   and R_{H(t)}(a) f ∈ Dom(T)):
   R_T(a) f - R_{H(t)}(a) f = exp(2t) • R_T(a) (G (R_{H(t)}(a) f))
     = exp(2t) • R_T(a) (K (R_{H(t)}(a) f)) + exp(2t) • R_T(a) (P (R_{H(t)}(a) f)),
   together with Hilbert, static-root (T_stat), and half-clock (clockHalf) norm
   bounds, plus the dual Growing-Hamiltonian Second Resolvent Identity and full
   Potential-Growing-Hamiltonian telescope at t = 0. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticResidualSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorStaticGrowingDecomposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFullFiveResolventChainSynthesis
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_root_subset_clockHalf_domain static_root_clockHalf_norm_sq_le)
open KFCausalClockFloorStaticGrowingDecomposition
  (static_graph growing_graph)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (residual_resolvent_norm_le)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_mem_potential_domain potential_resolvent_left_inverse
    potential_resolvent_operator_norm_le
    potential_sub_growing_resolvent_eq
    potential_sub_growing_resolvent_norm_le_radial)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_resolvent_mem_residual_domain residual_resolvent_operator_norm_le
    residual_resolvent_residualForm_norm_sq_le
    residual_sub_hamiltonian_resolvent_eq
    residual_sub_hamiltonian_resolvent_norm_le_radial)
open KFCausalClockFloorHamiltonianResolventFormBounds
  (hamiltonian_resolvent_mem_staticRoot_domain
    hamiltonian_resolvent_staticRoot_norm_le
    residual_resolvent_mem_staticRoot_domain
    residual_resolvent_staticRoot_norm_le)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_mem_static_domain static_resolvent_left_inverse
    static_resolvent_norm_le static_resolvent_operator_norm_le
    static_resolvent_mem_staticRoot_domain
    static_resolvent_staticRoot_norm_sq_le
    static_resolvent_mem_clockHalf_domain
    static_resolvent_clockHalf_norm_sq_le)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h

/-! ### 1. Unconditional Four-Resolvent and Five-Resolvent Chain Synthesis -/

theorem potential_sub_growing_sub_residual_sub_hamiltonian_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (RP a f - RG a f) - (RS t a f - RH t a f) =
      RP a (K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩) -
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a f,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha f⟩) := by
  rw [potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f,
    residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f]

theorem potential_sub_growing_add_residual_sub_hamiltonian_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (RP a f - RG a f) + (RS t a f - RH t a f) =
      RP a (K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩) +
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a f,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha f⟩) := by
  rw [potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f,
    residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f]

theorem potential_sub_hamiltonian_via_growing_residual_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f - RH t a f =
      RP a (K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩) +
        (RG a f - RS t a f) +
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a f,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha f⟩) := by
  have h1 := potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f
  have h2 := residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f
  have htel : RP a f - RH t a f =
      (RP a f - RG a f) + (RG a f - RS t a f) + (RS t a f - RH t a f) := by
    abel
  rw [htel, h1, h2]

theorem five_resolvent_chain_telescope
    (a : ℝ) (f : Hilbert) :
    RP a f - RH t a f =
      (RP a f - RG a f) + (RG a f - RT a f) +
        (RT a f - RS t a f) + (RS t a f - RH t a f) := by
  abel

theorem potential_sub_growing_sub_residual_sub_hamiltonian_norm_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖(RP a f - RG a f) - (RS t a f - RH t a f)‖ ≤
      a⁻¹ * ‖K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩‖ +
        a⁻¹ * Real.exp (2 * t) * ‖K ⟨RH t a f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha f⟩‖ := by
  have htri := norm_sub_le (RP a f - RG a f) (RS t a f - RH t a f)
  have h1 := potential_sub_growing_resolvent_norm_le_radial ε hε h hh hb m g k a ha f
  have h2 := residual_sub_hamiltonian_resolvent_norm_le_radial ε hε h hh hb m g k t a ha f
  linarith

theorem potential_sub_growing_add_residual_sub_hamiltonian_norm_le_radial
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖(RP a f - RG a f) + (RS t a f - RH t a f)‖ ≤
      a⁻¹ * ‖K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩‖ +
        a⁻¹ * Real.exp (2 * t) * ‖K ⟨RH t a f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha f⟩‖ := by
  have htri := norm_add_le (RP a f - RG a f) (RS t a f - RH t a f)
  have h1 := potential_sub_growing_resolvent_norm_le_radial ε hε h hh hb m g k a ha f
  have h2 := residual_sub_hamiltonian_resolvent_norm_le_radial ε hε h hh hb m g k t a ha f
  linarith

theorem five_resolvent_norm_sum_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RT a f‖ + ‖RP a f‖ + ‖RG a f‖ + ‖RS t a f‖ + ‖RH t a f‖ ≤
      5 * a⁻¹ * ‖f‖ := by
  have hT := static_resolvent_norm_le ε hε h hh hb m g k a ha f
  have hP := potential_resolvent_norm_le ε hε h hb hh m g k a ha f
  have hG := KFCausalClockFloorGrowingComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k a ha f
  have hS := residual_resolvent_norm_le ε hε h hh hb m g k t a ha f
  have hH := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha f
  linarith

theorem five_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖RT a f‖ ^ 2 + ‖RP a f‖ ^ 2 + ‖RG a f‖ ^ 2 + ‖RS t a f‖ ^ 2 + ‖RH t a f‖ ^ 2 ≤
      5 * (a⁻¹) ^ 2 * ‖f‖ ^ 2 := by
  have hpos : 0 ≤ a⁻¹ * ‖f‖ := mul_nonneg (inv_nonneg.mpr ha.le) (norm_nonneg f)
  have hT : ‖RT a f‖ ^ 2 ≤ (a⁻¹ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).mpr
      (static_resolvent_norm_le ε hε h hh hb m g k a ha f)
  have hP : ‖RP a f‖ ^ 2 ≤ (a⁻¹ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).mpr
      (potential_resolvent_norm_le ε hε h hb hh m g k a ha f)
  have hG : ‖RG a f‖ ^ 2 ≤ (a⁻¹ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).mpr
      (KFCausalClockFloorGrowingComponentResolventBounds.resolvent_norm_le
        ε hε h hh hb m g k a ha f)
  have hS : ‖RS t a f‖ ^ 2 ≤ (a⁻¹ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).mpr
      (residual_resolvent_norm_le ε hε h hh hb m g k t a ha f)
  have hH : ‖RH t a f‖ ^ 2 ≤ (a⁻¹ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpos).mpr
      (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
        ε hε h hh hb m g k t a ha f)
  linarith [show (a⁻¹ * ‖f‖) ^ 2 = (a⁻¹) ^ 2 * ‖f‖ ^ 2 by ring]

theorem five_operator_output_norm_sum_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩‖ +
      ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ +
      ‖G ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_growing_domain
          ε hε h hh hb m g k a ha f⟩‖ +
      ‖S t ⟨RS t a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ +
      ‖H t ⟨RH t a f,
        KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
          ε hε h hh hb m g k t a ha f⟩‖ ≤
      5 * ‖f‖ := by
  have hT := static_resolvent_operator_norm_le ε hε h hh hb m g k a ha f
  have hP := potential_resolvent_operator_norm_le ε hε h hh hb m g k a ha f
  have hG := KFCausalClockFloorGrowingComponentResolventBounds.resolvent_growing_norm_le
    ε hε h hh hb m g k a ha f
  have hS := residual_resolvent_operator_norm_le ε hε h hh hb m g k t a ha f
  have hH := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_hamiltonian_norm_le
    ε hε h hh hb m g k t a ha f
  linarith

theorem five_operator_output_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      ‖G ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_growing_domain
          ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      ‖S t ⟨RS t a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      ‖H t ⟨RH t a f,
        KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
          ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      5 * ‖f‖ ^ 2 := by
  have hT : ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (static_resolvent_operator_norm_le ε hε h hh hb m g k a ha f)
  have hP : ‖P ⟨RP a f, potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤
      ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (potential_resolvent_operator_norm_le ε hε h hh hb m g k a ha f)
  have hG : ‖G ⟨RG a f,
      KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_growing_domain
        ε hε h hh hb m g k a ha f⟩‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (KFCausalClockFloorGrowingComponentResolventBounds.resolvent_growing_norm_le
        ε hε h hh hb m g k a ha f)
  have hS : ‖S t ⟨RS t a f, residual_resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (residual_resolvent_operator_norm_le ε hε h hh hb m g k t a ha f)
  have hH : ‖H t ⟨RH t a f,
      KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
        ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_hamiltonian_norm_le
        ε hε h hh hb m g k t a ha f)
  linarith

theorem hamiltonian_resolvent_mem_clockHalf_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RH t a f)
    (hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_mem_clockHalf_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RS t a f)
    (residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)

theorem static_residual_hamiltonian_clockHalf_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RT a f, static_resolvent_mem_clockHalf_domain ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
      ‖clockHalf ε ⟨RS t a f,
        residual_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      ‖clockHalf ε ⟨RH t a f,
        hamiltonian_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      6 * a⁻¹ * ‖f‖ ^ 2 := by
  have hT := static_resolvent_clockHalf_norm_sq_le ε hε h hh hb m g k a ha f
  have hS1 := static_root_clockHalf_norm_sq_le ε hε h (RS t a f)
    (residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)
  have hS2 : ‖Tstat ⟨RS t a f,
      residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
    have hle := KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_static_energy_le
      ε hε h hh hb m g k t a ha f
    have ha0 : 0 ≤ a * ‖RS t a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    linarith
  have hH1 := static_root_clockHalf_norm_sq_le ε hε h (RH t a f)
    (hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)
  have hH2 : ‖Tstat ⟨RH t a f,
      hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
    have hle := KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_static_radial_energy_le
      ε hε h hh hb m g k t a ha f
    have hr0 : 0 ≤ Real.exp (2 * t) *
        ‖KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
          ⟨RH t a f,
            KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
              ε hε h hh hb m g k t a ha f⟩‖ ^ 2 :=
      mul_nonneg (Real.exp_pos (2 * t)).le (sq_nonneg _)
    have ha0 : 0 ≤ a * ‖RH t a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    linarith
  linarith

/-! ### 2. Exact Static-Growing-Hamiltonian Operator Decompositions -/

theorem hamiltonian_growing_mem_static_domain (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (hg_dom : x ∈ (G).domain) :
    x ∈ (T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (static_graph ε hε h hh hw m g k t x (H t ⟨x, hh_dom⟩) (G ⟨x, hg_dom⟩)
      ((H t).mem_graph ⟨x, hh_dom⟩) ((G).mem_graph ⟨x, hg_dom⟩))

theorem static_apply_on_hamiltonian_growing (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (hg_dom : x ∈ (G).domain) :
    T ⟨x, hamiltonian_growing_mem_static_domain ε hε h hh hb m g k t x hh_dom hg_dom⟩ =
      H t ⟨x, hh_dom⟩ - (Real.exp (2 * t) : ℂ) • G ⟨x, hg_dom⟩ := by
  rw [Complex.coe_smul]
  exact (T).mem_graph_snd_inj'
    ((T).mem_graph ⟨x, hamiltonian_growing_mem_static_domain ε hε h hh hb m g k t x hh_dom hg_dom⟩)
    (static_graph ε hε h hh hw m g k t x (H t ⟨x, hh_dom⟩) (G ⟨x, hg_dom⟩)
      ((H t).mem_graph ⟨x, hh_dom⟩) ((G).mem_graph ⟨x, hg_dom⟩)) rfl

theorem hamiltonian_eq_static_add_scaled_growing (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (hg_dom : x ∈ (G).domain) :
    H t ⟨x, hh_dom⟩ =
      T ⟨x, hamiltonian_growing_mem_static_domain ε hε h hh hb m g k t x hh_dom hg_dom⟩ +
        (Real.exp (2 * t) : ℂ) • G ⟨x, hg_dom⟩ := by
  rw [static_apply_on_hamiltonian_growing ε hε h hh hb m g k t x hh_dom hg_dom, sub_add_cancel]

theorem hamiltonian_static_mem_growing_domain (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (ht_dom : x ∈ (T).domain) :
    x ∈ (G).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (growing_graph ε hε h hh hw m g k t x (H t ⟨x, hh_dom⟩) (T ⟨x, ht_dom⟩)
      ((H t).mem_graph ⟨x, hh_dom⟩) ((T).mem_graph ⟨x, ht_dom⟩))

theorem growing_apply_on_hamiltonian_static (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (ht_dom : x ∈ (T).domain) :
    G ⟨x, hamiltonian_static_mem_growing_domain ε hε h hh hb m g k t x hh_dom ht_dom⟩ =
      (Real.exp (2 * t))⁻¹ • (H t ⟨x, hh_dom⟩ - T ⟨x, ht_dom⟩) :=
  (G).mem_graph_snd_inj'
    ((G).mem_graph ⟨x, hamiltonian_static_mem_growing_domain ε hε h hh hb m g k t x hh_dom ht_dom⟩)
    (growing_graph ε hε h hh hw m g k t x (H t ⟨x, hh_dom⟩) (T ⟨x, ht_dom⟩)
      ((H t).mem_graph ⟨x, hh_dom⟩) ((T).mem_graph ⟨x, ht_dom⟩)) rfl

theorem static_resolvent_on_shifted_hamiltonian_sub_eq
    (a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hh_dom : x ∈ (H t).domain) (hg_dom : x ∈ (G).domain) :
    RT a (H t ⟨x, hh_dom⟩ + a • x) - x =
      (Real.exp (2 * t) : ℂ) • RT a (G ⟨x, hg_dom⟩) := by
  let ht_dom := hamiltonian_growing_mem_static_domain ε hε h hh hb m g k t x hh_dom hg_dom
  have hsum : H t ⟨x, hh_dom⟩ + a • x =
      (T ⟨x, ht_dom⟩ + a • x) + (Real.exp (2 * t) : ℂ) • G ⟨x, hg_dom⟩ := by
    rw [hamiltonian_eq_static_add_scaled_growing ε hε h hh hb m g k t x hh_dom hg_dom]
    abel
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨x, ht_dom⟩
  change RT a (T ⟨x, ht_dom⟩ + a • x) = x at hlinv
  rw [hsum, map_add, hlinv, map_smul, add_sub_cancel_left]

theorem growing_resolvent_on_shifted_hamiltonian_zero_sub_eq
    (a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hh0 : x ∈ (H 0).domain) (ht0 : x ∈ (T).domain) :
    RG a (H 0 ⟨x, hh0⟩ + a • x) - x =
      RG a (T ⟨x, ht0⟩) := by
  let hg0 := hamiltonian_static_mem_growing_domain ε hε h hh hb m g k 0 x hh0 ht0
  have hg_eq := growing_apply_on_hamiltonian_static ε hε h hh hb m g k 0 x hh0 ht0
  change G ⟨x, hg0⟩ = (Real.exp (2 * (0 : ℝ)))⁻¹ • (H 0 ⟨x, hh0⟩ - T ⟨x, ht0⟩) at hg_eq
  rw [mul_zero, Real.exp_zero, inv_one, one_smul] at hg_eq
  have hsum : H 0 ⟨x, hh0⟩ + a • x = (G ⟨x, hg0⟩ + a • x) + T ⟨x, ht0⟩ := by
    rw [hg_eq]
    abel
  have hlinv := KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k a ha ⟨x, hg0⟩
  change RG a (G ⟨x, hg0⟩ + a • x) = x at hlinv
  rw [hsum, map_add, hlinv, add_sub_cancel_left]

theorem potential_resolvent_on_shifted_growing_sub_eq
    (a : ℝ) (ha : 0 < a) (x : (G).domain) :
    RP a (G x + a • (x : Hilbert)) - (x : Hilbert) =
      RP a (K ⟨(x : Hilbert),
        KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k x⟩) := by
  let hk := KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k x
  let hp := KFCausalClockFloorGrowingPotentialSum.potential_domain ε hε h hh hb m g k x
  have hp_eq : P ⟨(x : Hilbert), hp⟩ = G x - K ⟨(x : Hilbert), hk⟩ :=
    (P).mem_graph_snd_inj' ((P).mem_graph ⟨(x : Hilbert), hp⟩)
      (KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb m g k x) rfl
  have hsum : G x + a • (x : Hilbert) =
      (P ⟨(x : Hilbert), hp⟩ + a • (x : Hilbert)) + K ⟨(x : Hilbert), hk⟩ := by
    rw [hp_eq]
    abel
  have hlinv := potential_resolvent_left_inverse ε hε h hh hb m g k a ha ⟨(x : Hilbert), hp⟩
  change RP a (P ⟨(x : Hilbert), hp⟩ + a • (x : Hilbert)) = (x : Hilbert) at hlinv
  rw [hsum, map_add, hlinv, add_sub_cancel_left]

/-! ### 3. Exact Static-Hamiltonian Second Resolvent Identity & Full Telescopes -/

theorem hamiltonian_resolvent_mem_growing_of_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RH t a f ∈ (G).domain :=
  (KFCausalClockFloorGrowingPotentialSum.domain_iff ε hε h hh hb m g k (RH t a f)).mpr
    ⟨KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
      ε hε h hh hb m g k t a ha f, hp⟩

theorem hamiltonian_resolvent_mem_static_of_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RH t a f ∈ (T).domain :=
  hamiltonian_growing_mem_static_domain ε hε h hh hb m g k t (RH t a f)
    (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
      ε hε h hh hb m g k t a ha f)
    (hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp)

theorem hamiltonian_resolvent_growing_eq_radial_add_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    G ⟨RH t a f, hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩ =
      K ⟨RH t a f,
        KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k t a ha f⟩ +
        P ⟨RH t a f, hp⟩ := by
  let xG : (G).domain :=
    ⟨RH t a f, hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩
  have hp_eq : P ⟨RH t a f, hp⟩ =
      G xG - K ⟨RH t a f,
        KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k t a ha f⟩ :=
    (P).mem_graph_snd_inj' ((P).mem_graph ⟨RH t a f, hp⟩)
      (KFCausalClockFloorGrowingPotentialSum.potential_graph ε hε h hh hb m g k xG) rfl
  rw [hp_eq]
  abel

theorem hamiltonian_resolvent_shifted_static_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    T ⟨RH t a f, hamiltonian_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      (a : ℂ) • RH t a f =
      f - (Real.exp (2 * t) : ℂ) •
        G ⟨RH t a f, hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩ := by
  rw [static_apply_on_hamiltonian_growing ε hε h hh hb m g k t (RH t a f)
      (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
        ε hε h hh hb m g k t a ha f)
      (hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp),
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_equation
      ε hε h hh hb m g k t a ha f,
    ← Complex.coe_smul]
  abel

theorem hamiltonian_resolvent_shifted_static_eq_real
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    T ⟨RH t a f, hamiltonian_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      a • RH t a f =
      f - (Real.exp (2 * t) : ℂ) •
        G ⟨RH t a f, hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩ := by
  rw [← Complex.coe_smul]
  exact hamiltonian_resolvent_shifted_static_eq ε hε h hh hb m g k t a ha f hp

theorem hamiltonian_resolvent_eq_static_resolvent_shifted_source
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RH t a f = RT a (f - (Real.exp (2 * t) : ℂ) •
      G ⟨RH t a f, hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩) := by
  have hlinv := static_resolvent_left_inverse ε hε h hh hb m g k a ha
    ⟨RH t a f, hamiltonian_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩
  change RT a
    (T ⟨RH t a f, hamiltonian_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩ +
      a • RH t a f) = RH t a f at hlinv
  rw [hamiltonian_resolvent_shifted_static_eq_real ε hε h hh hb m g k t a ha f hp] at hlinv
  exact hlinv.symm

theorem hamiltonian_resolvent_static_second_resolvent_identity
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RH t a f = RT a f - (Real.exp (2 * t) : ℂ) •
      RT a (G ⟨RH t a f,
        hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩) :=
  (hamiltonian_resolvent_eq_static_resolvent_shifted_source ε hε h hh hb m g k t a ha f hp).trans
    ((map_sub (RT a) f _).trans
      (congrArg (fun u : Hilbert => RT a f - u)
        (map_smul (RT a) (Real.exp (2 * t) : ℂ) _)))

theorem static_sub_hamiltonian_resolvent_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RT a f - RH t a f = (Real.exp (2 * t) : ℂ) •
      RT a (G ⟨RH t a f,
        hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩) :=
  (congrArg (fun u : Hilbert => RT a f - u)
    (hamiltonian_resolvent_static_second_resolvent_identity ε hε h hh hb m g k t a ha f hp)).trans
    (sub_sub_cancel _ _)

theorem static_sub_hamiltonian_resolvent_eq_radial_add_potential
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    RT a f - RH t a f =
      (Real.exp (2 * t) : ℂ) •
        RT a (K ⟨RH t a f,
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha f⟩) +
      (Real.exp (2 * t) : ℂ) • RT a (P ⟨RH t a f, hp⟩) := by
  rw [static_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f hp,
    hamiltonian_resolvent_growing_eq_radial_add_potential ε hε h hh hb m g k t a ha f hp,
    map_add, smul_add]

theorem static_sub_hamiltonian_resolvent_norm_le_growing
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    ‖RT a f - RH t a f‖ ≤
      a⁻¹ * Real.exp (2 * t) *
        ‖G ⟨RH t a f,
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ := by
  let gVec := G ⟨RH t a f,
    hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩
  have heq : ‖RT a f - RH t a f‖ = Real.exp (2 * t) * ‖RT a gVec‖ := by
    refine (congrArg norm
      (static_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f hp)).trans ?_
    change ‖(Real.exp (2 * t) : ℂ) • RT a gVec‖ = Real.exp (2 * t) * ‖RT a gVec‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have hr := static_resolvent_norm_le ε hε h hh hb m g k a ha gVec
  calc
    ‖RT a f - RH t a f‖ = Real.exp (2 * t) * ‖RT a gVec‖ := heq
    _ ≤ Real.exp (2 * t) * (a⁻¹ * ‖gVec‖) :=
      mul_le_mul_of_nonneg_left hr (Real.exp_pos (2 * t)).le
    _ = a⁻¹ * Real.exp (2 * t) * ‖gVec‖ := by ring

theorem static_sub_hamiltonian_resolvent_mem_staticRoot_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f - RH t a f ∈ (Tstat).domain :=
  (Tstat).domain.sub_mem
    (static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha f)
    (hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)

theorem static_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_growing
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    ‖Tstat ⟨RT a f - RH t a f,
      static_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) *
        ‖G ⟨RH t a f,
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 := by
  let gVec := G ⟨RH t a f,
    hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩
  let xDiff : (Tstat).domain :=
    ⟨RT a f - RH t a f,
      static_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f⟩
  let xG : (Tstat).domain :=
    ⟨RT a gVec, static_resolvent_mem_staticRoot_domain ε hε h hh hb m g k a ha gVec⟩
  have hsub : xDiff = (Real.exp (2 * t) : ℂ) • xG :=
    Subtype.ext (static_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f hp)
  have hmap : Tstat xDiff = (Real.exp (2 * t) : ℂ) • Tstat xG :=
    (congrArg Tstat hsub).trans ((Tstat).map_smul _ xG)
  have he : Real.exp (2 * t) ^ 2 = Real.exp (4 * t) := by
    rw [sq, ← Real.exp_add, show 2 * t + 2 * t = 4 * t by ring]
  have hnorm : ‖Tstat xDiff‖ ^ 2 = Real.exp (4 * t) * ‖Tstat xG‖ ^ 2 := by
    rw [hmap, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (2 * t)), mul_pow, he]
  have hbG := static_resolvent_staticRoot_norm_sq_le ε hε h hh hb m g k a ha gVec
  have hmul := mul_le_mul_of_nonneg_left hbG (Real.exp_pos (4 * t)).le
  change ‖Tstat xDiff‖ ^ 2 ≤ a⁻¹ * Real.exp (4 * t) * ‖gVec‖ ^ 2
  rw [hnorm]
  linarith

theorem static_sub_hamiltonian_resolvent_mem_clockHalf_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RT a f - RH t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RT a f - RH t a f)
    (static_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)

theorem static_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_growing
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hp : RH t a f ∈ (P).domain) :
    ‖clockHalf ε ⟨RT a f - RH t a f,
      static_sub_hamiltonian_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * Real.exp (4 * t) *
        ‖G ⟨RH t a f,
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RT a f - RH t a f)
    (static_sub_hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f)
  have h2 := static_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_growing
    ε hε h hh hb m g k t a ha f hp
  linarith

theorem growing_sub_hamiltonian_zero_resolvent_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (ht : RH 0 a f ∈ (T).domain) :
    RG a f - RH 0 a f = RG a (T ⟨RH 0 a f, ht⟩) := by
  have hh0 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
    ε hε h hh hb m g k 0 a ha f
  have hsub := growing_resolvent_on_shifted_hamiltonian_zero_sub_eq
    ε hε h hh hb m g k a ha (RH 0 a f) hh0 ht
  have hshift : H 0 ⟨RH 0 a f, hh0⟩ + a • RH 0 a f = f := by
    rw [KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_equation
      ε hε h hh hb m g k 0 a ha f, sub_add_cancel]
  rw [hshift] at hsub
  exact hsub

theorem potential_sub_hamiltonian_zero_resolvent_full_telescope
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (ht : RH 0 a f ∈ (T).domain) :
    RP a f - RH 0 a f =
      RP a (K ⟨RG a f,
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha f⟩) +
        RG a (T ⟨RH 0 a f, ht⟩) := by
  have h1 := potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f
  have h2 := growing_sub_hamiltonian_zero_resolvent_eq ε hε h hh hb m g k a ha f ht
  have htel : RP a f - RH 0 a f = (RP a f - RG a f) + (RG a f - RH 0 a f) := by
    abel
  rw [htel, h1, h2]

#print axioms potential_sub_growing_sub_residual_sub_hamiltonian_eq
#print axioms potential_sub_growing_add_residual_sub_hamiltonian_eq
#print axioms potential_sub_hamiltonian_via_growing_residual_eq
#print axioms five_resolvent_chain_telescope
#print axioms potential_sub_growing_sub_residual_sub_hamiltonian_norm_le_radial
#print axioms potential_sub_growing_add_residual_sub_hamiltonian_norm_le_radial
#print axioms five_resolvent_norm_sum_le
#print axioms five_resolvent_norm_sq_sum_le
#print axioms five_operator_output_norm_sum_le
#print axioms five_operator_output_norm_sq_sum_le
#print axioms hamiltonian_resolvent_mem_clockHalf_domain
#print axioms residual_resolvent_mem_clockHalf_domain
#print axioms static_residual_hamiltonian_clockHalf_norm_sq_sum_le
#print axioms hamiltonian_growing_mem_static_domain
#print axioms static_apply_on_hamiltonian_growing
#print axioms hamiltonian_eq_static_add_scaled_growing
#print axioms hamiltonian_static_mem_growing_domain
#print axioms growing_apply_on_hamiltonian_static
#print axioms static_resolvent_on_shifted_hamiltonian_sub_eq
#print axioms growing_resolvent_on_shifted_hamiltonian_zero_sub_eq
#print axioms potential_resolvent_on_shifted_growing_sub_eq
#print axioms hamiltonian_resolvent_mem_growing_of_potential
#print axioms hamiltonian_resolvent_mem_static_of_potential
#print axioms hamiltonian_resolvent_growing_eq_radial_add_potential
#print axioms hamiltonian_resolvent_shifted_static_eq
#print axioms hamiltonian_resolvent_shifted_static_eq_real
#print axioms hamiltonian_resolvent_eq_static_resolvent_shifted_source
#print axioms hamiltonian_resolvent_static_second_resolvent_identity
#print axioms static_sub_hamiltonian_resolvent_eq
#print axioms static_sub_hamiltonian_resolvent_eq_radial_add_potential
#print axioms static_sub_hamiltonian_resolvent_norm_le_growing
#print axioms static_sub_hamiltonian_resolvent_mem_staticRoot_domain
#print axioms static_sub_hamiltonian_resolvent_staticRoot_norm_sq_le_growing
#print axioms static_sub_hamiltonian_resolvent_mem_clockHalf_domain
#print axioms static_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_growing
#print axioms growing_sub_hamiltonian_zero_resolvent_eq
#print axioms potential_sub_hamiltonian_zero_resolvent_full_telescope
end
end UnifiedTheory.Audit.KFCausalClockFloorFullFiveResolventChainSynthesis
