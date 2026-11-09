/- Standard Model Forced Gauge-Dimension and Weinberg-Angle Resolvent Bridge for
the Five-Operator Clock-Floor Hamiltonian Hierarchy:
1. Connects the substrate-derived Standard Model atomic dimensions
   (N_c = 3, N_W = 2, d_eff = 4), the 15-component chiral Weyl fermion generation
   count (12 colored + 3 uncolored), the 16-component SO(10) spinor dimension
   (singleGenDim = 2^4 = 16 = 15 + 1), and the unification-scale Weinberg-angle
   electroweak partition weights sin²θ_W = 3/8 and cos²θ_W = 5/8 (with ratio
   3/5 = k₂/k₁) to the K/F causal clock-floor Hilbert space.
2. Lifts the five positive shifted resolvents
   R_T(a), R_P(a), R_G(a), R_{S(t)}(a), R_{H(t)}(a)
   to 16-component single-generation multi-fermion Hilbert tuples (SMGenState)
   and 15-component chiral Weyl tuples (SMWeylState), proving componentwise and
   collective ℓ²(Fin n; Hilbert) norm-square contraction bounds.
3. Establishes componentwise and Weinberg-angle electroweak-partitioned second
   resolvent identities across the 16-component Standard Model generation space
   and packages the complete structural and analytical bridge into a master
   synthesis theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullFiveResolventChainSynthesis
import UnifiedTheory.LayerA.FermionCountDerived
import UnifiedTheory.LayerA.WeinbergAngle
import UnifiedTheory.LayerC.SMHilbertInstantiation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMForcedGaugeResolventBridge
noncomputable section
open scoped BigOperators Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open UnifiedTheory.LayerB.CrossSectorIdentitySearch
  (atom_N_W atom_N_c atom_d_eff)
open UnifiedTheory.LayerA.FermionCountDerived
  (coloredFermions uncoloredFermions totalFermions)
open UnifiedTheory.LayerA.WeinbergAngle
  (sin2_weinberg sin2_weinberg_eq gutNormalization gutNormalization_eq)
open UnifiedTheory.LayerC.SMHilbertInstantiation
  (singleGenDim singleGenDim_eq_sixteen singleGenDim_eq_spinor)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (residual_resolvent_norm_le)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_sub_growing_resolvent_eq
    potential_sub_growing_resolvent_norm_le_source)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (residual_sub_hamiltonian_resolvent_eq)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_norm_le static_sub_residual_resolvent_eq)
open KFCausalClockFloorFullFiveResolventChainSynthesis
  (static_sub_hamiltonian_resolvent_eq
    hamiltonian_resolvent_mem_growing_of_potential)

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

/-! ### 1. Standard Model Forced Gauge Dimensions & Weinberg-Angle Partition Weights -/

theorem sm_color_dim_eq_three : atom_N_c = 3 := rfl

theorem sm_weak_dim_eq_two : atom_N_W = 2 := rfl

theorem sm_eff_spacetime_dim_eq_four : atom_d_eff = 4 := rfl

theorem sm_colored_fermion_dim_eq_twelve :
    coloredFermions atom_N_c atom_N_W = 12 := rfl

theorem sm_uncolored_fermion_dim_eq_three :
    uncoloredFermions atom_N_W = 3 := rfl

theorem sm_weyl_fermion_dim_eq_fifteen :
    totalFermions atom_N_c atom_N_W = 15 := rfl

theorem sm_singleGenDim_eq_sixteen : singleGenDim = 16 :=
  singleGenDim_eq_sixteen

theorem sm_singleGenDim_eq_weyl_succ :
    singleGenDim = totalFermions atom_N_c atom_N_W + 1 := rfl

theorem sm_singleGenDim_eq_colored_add_uncolored_succ :
    singleGenDim =
      coloredFermions atom_N_c atom_N_W + uncoloredFermions atom_N_W + 1 := rfl

def smWeakWeight : ℝ := (sin2_weinberg : ℝ)

def smHyperWeight : ℝ := 1 - (sin2_weinberg : ℝ)

theorem smWeakWeight_eq : smWeakWeight = 3 / 8 := by
  unfold smWeakWeight
  rw [sin2_weinberg_eq]
  norm_num

theorem smHyperWeight_eq : smHyperWeight = 5 / 8 := by
  unfold smHyperWeight
  rw [sin2_weinberg_eq]
  norm_num

theorem smWeakWeight_pos : 0 < smWeakWeight := by
  rw [smWeakWeight_eq]
  norm_num

theorem smHyperWeight_pos : 0 < smHyperWeight := by
  rw [smHyperWeight_eq]
  norm_num

theorem smWeakWeight_add_smHyperWeight :
    smWeakWeight + smHyperWeight = 1 := by
  unfold smWeakWeight smHyperWeight
  ring

theorem smWeakWeight_div_smHyperWeight :
    smWeakWeight / smHyperWeight = 3 / 5 := by
  rw [smWeakWeight_eq, smHyperWeight_eq]
  norm_num

theorem smWeakWeight_div_smHyperWeight_eq_inv_gutNormalization :
    smWeakWeight / smHyperWeight = ((gutNormalization : ℝ))⁻¹ := by
  rw [smWeakWeight_div_smHyperWeight, gutNormalization_eq]
  norm_num

theorem weinberg_convex_vector_split (x : Hilbert) :
    (smWeakWeight : ℂ) • x + (smHyperWeight : ℂ) • x = x := by
  rw [← add_smul, ← Complex.ofReal_add, smWeakWeight_add_smHyperWeight,
    Complex.ofReal_one, one_smul]

theorem weinberg_convex_resolvent_split
    (R : Hilbert →L[ℂ] Hilbert) (f : Hilbert) :
    (smWeakWeight : ℂ) • R f + (smHyperWeight : ℂ) • R f = R f :=
  weinberg_convex_vector_split (R f)

theorem weinberg_convex_energy_split (E : ℝ) :
    smWeakWeight * E + smHyperWeight * E = E := by
  rw [← add_mul, smWeakWeight_add_smHyperWeight, one_mul]

/-! ### 2. Multi-Fermion Hilbert Tuples and 5-Operator Resolvent Contraction -/

abbrev SMGenState : Type := Fin singleGenDim → Hilbert

abbrev SMWeylState : Type := Fin (totalFermions atom_N_c atom_N_W) → Hilbert

theorem fin_tuple_resolvent_norm_sq_sum_le {n : ℕ}
    (R : Hilbert →L[ℂ] Hilbert) (c : ℝ) (hc : 0 ≤ c)
    (hR : ∀ f : Hilbert, ‖R f‖ ≤ c * ‖f‖) (ψ : Fin n → Hilbert) :
    (∑ i : Fin n, ‖R (ψ i)‖ ^ 2) ≤ c ^ 2 * (∑ i : Fin n, ‖ψ i‖ ^ 2) := by
  calc
    (∑ i : Fin n, ‖R (ψ i)‖ ^ 2) ≤ ∑ i : Fin n, (c * ‖ψ i‖) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr (hR (ψ i))
    _ = ∑ i : Fin n, c ^ 2 * ‖ψ i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => by ring
    _ = c ^ 2 * ∑ i : Fin n, ‖ψ i‖ ^ 2 :=
      (Finset.mul_sum Finset.univ (fun i : Fin n => ‖ψ i‖ ^ 2) (c ^ 2)).symm

theorem smGen_static_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RT a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) :=
  fin_tuple_resolvent_norm_sq_sum_le (RT a) a⁻¹ (inv_nonneg.mpr ha.le)
    (static_resolvent_norm_le ε hε h hh hb m g k a ha) ψ

theorem smGen_potential_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RP a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) :=
  fin_tuple_resolvent_norm_sq_sum_le (RP a) a⁻¹ (inv_nonneg.mpr ha.le)
    (potential_resolvent_norm_le ε hε h hb hh m g k a ha) ψ

theorem smGen_growing_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RG a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) :=
  fin_tuple_resolvent_norm_sq_sum_le (RG a) a⁻¹ (inv_nonneg.mpr ha.le)
    (KFCausalClockFloorGrowingComponentResolventBounds.resolvent_norm_le
      ε hε h hh hb m g k a ha) ψ

theorem smGen_residual_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RS t a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) :=
  fin_tuple_resolvent_norm_sq_sum_le (RS t a) a⁻¹ (inv_nonneg.mpr ha.le)
    (residual_resolvent_norm_le ε hε h hh hb m g k t a ha) ψ

theorem smGen_hamiltonian_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RH t a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) :=
  fin_tuple_resolvent_norm_sq_sum_le (RH t a) a⁻¹ (inv_nonneg.mpr ha.le)
    (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
      ε hε h hh hb m g k t a ha) ψ

theorem smGen_five_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RT a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RP a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RG a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RS t a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RH t a (ψ i)‖ ^ 2) ≤
      5 * (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) := by
  have hT := smGen_static_resolvent_norm_sq_sum_le ε hε h hh hb m g k a ha ψ
  have hP := smGen_potential_resolvent_norm_sq_sum_le ε hε h hh hb m g k a ha ψ
  have hG := smGen_growing_resolvent_norm_sq_sum_le ε hε h hh hb m g k a ha ψ
  have hS := smGen_residual_resolvent_norm_sq_sum_le ε hε h hh hb m g k t a ha ψ
  have hH := smGen_hamiltonian_resolvent_norm_sq_sum_le ε hε h hh hb m g k t a ha ψ
  linarith

theorem smWeyl_five_resolvent_norm_sq_sum_le
    (a : ℝ) (ha : 0 < a) (ψ : SMWeylState) :
    (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖RT a (ψ i)‖ ^ 2) +
      (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖RP a (ψ i)‖ ^ 2) +
      (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖RG a (ψ i)‖ ^ 2) +
      (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖RS t a (ψ i)‖ ^ 2) +
      (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖RH t a (ψ i)‖ ^ 2) ≤
      5 * (a⁻¹) ^ 2 * (∑ i : Fin (totalFermions atom_N_c atom_N_W), ‖ψ i‖ ^ 2) := by
  have hT := fin_tuple_resolvent_norm_sq_sum_le (RT a) a⁻¹ (inv_nonneg.mpr ha.le)
    (static_resolvent_norm_le ε hε h hh hb m g k a ha) ψ
  have hP := fin_tuple_resolvent_norm_sq_sum_le (RP a) a⁻¹ (inv_nonneg.mpr ha.le)
    (potential_resolvent_norm_le ε hε h hb hh m g k a ha) ψ
  have hG := fin_tuple_resolvent_norm_sq_sum_le (RG a) a⁻¹ (inv_nonneg.mpr ha.le)
    (KFCausalClockFloorGrowingComponentResolventBounds.resolvent_norm_le
      ε hε h hh hb m g k a ha) ψ
  have hS := fin_tuple_resolvent_norm_sq_sum_le (RS t a) a⁻¹ (inv_nonneg.mpr ha.le)
    (residual_resolvent_norm_le ε hε h hh hb m g k t a ha) ψ
  have hH := fin_tuple_resolvent_norm_sq_sum_le (RH t a) a⁻¹ (inv_nonneg.mpr ha.le)
    (KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
      ε hε h hh hb m g k t a ha) ψ
  linarith

/-! ### 3. Componentwise Second Resolvent Identities & Master SM-Resolvent Bridge -/

theorem smGen_potential_sub_growing_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim) :
    RP a (ψ i) - RG a (ψ i) =
      RP a (K ⟨RG a (ψ i),
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha (ψ i)⟩) :=
  potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha (ψ i)

theorem smGen_residual_sub_hamiltonian_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim) :
    RS t a (ψ i) - RH t a (ψ i) =
      (Real.exp (2 * t) : ℂ) •
        RS t a (K ⟨RH t a (ψ i),
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha (ψ i)⟩) :=
  residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha (ψ i)

theorem smGen_static_sub_residual_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim)
    (hp : RS t a (ψ i) ∈ (P).domain) :
    RT a (ψ i) - RS t a (ψ i) =
      (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t a (ψ i), hp⟩) :=
  static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha (ψ i) hp

theorem smGen_static_sub_hamiltonian_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim)
    (hp : RH t a (ψ i) ∈ (P).domain) :
    RT a (ψ i) - RH t a (ψ i) =
      (Real.exp (2 * t) : ℂ) •
        RT a (G ⟨RH t a (ψ i),
          hamiltonian_resolvent_mem_growing_of_potential ε hε h hh hb m g k t a ha (ψ i) hp⟩) :=
  static_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha (ψ i) hp

theorem smGen_potential_sub_growing_norm_sq_sum_le_source
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (∑ i : Fin singleGenDim, ‖RP a (ψ i) - RG a (ψ i)‖ ^ 2) ≤
      (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2) := by
  calc
    (∑ i : Fin singleGenDim, ‖RP a (ψ i) - RG a (ψ i)‖ ^ 2) ≤
        ∑ i : Fin singleGenDim, (a⁻¹ * ‖ψ i‖) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (inv_nonneg.mpr ha.le) (norm_nonneg _))).mpr
        (potential_sub_growing_resolvent_norm_le_source ε hε h hh hb m g k a ha (ψ i))
    _ = ∑ i : Fin singleGenDim, (a⁻¹) ^ 2 * ‖ψ i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => by ring
    _ = (a⁻¹) ^ 2 * ∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2 :=
      (Finset.mul_sum Finset.univ (fun i : Fin singleGenDim => ‖ψ i‖ ^ 2) ((a⁻¹) ^ 2)).symm

theorem smWeyl_potential_sub_growing_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMWeylState)
    (i : Fin (totalFermions atom_N_c atom_N_W)) :
    RP a (ψ i) - RG a (ψ i) =
      RP a (K ⟨RG a (ψ i),
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha (ψ i)⟩) :=
  potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha (ψ i)

theorem smWeyl_residual_sub_hamiltonian_resolvent_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMWeylState)
    (i : Fin (totalFermions atom_N_c atom_N_W)) :
    RS t a (ψ i) - RH t a (ψ i) =
      (Real.exp (2 * t) : ℂ) •
        RS t a (K ⟨RH t a (ψ i),
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha (ψ i)⟩) :=
  residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha (ψ i)

theorem smGen_weinberg_weighted_potential_sub_growing_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim) :
    (smWeakWeight : ℂ) • (RP a (ψ i) - RG a (ψ i)) +
      (smHyperWeight : ℂ) • (RP a (ψ i) - RG a (ψ i)) =
      RP a (K ⟨RG a (ψ i),
        KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
          ε hε h hh hb m g k a ha (ψ i)⟩) :=
  (weinberg_convex_vector_split (RP a (ψ i) - RG a (ψ i))).trans
    (smGen_potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha ψ i)

theorem smGen_weinberg_weighted_residual_sub_hamiltonian_eq
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) (i : Fin singleGenDim) :
    (smWeakWeight : ℂ) • (RS t a (ψ i) - RH t a (ψ i)) +
      (smHyperWeight : ℂ) • (RS t a (ψ i) - RH t a (ψ i)) =
      (Real.exp (2 * t) : ℂ) •
        RS t a (K ⟨RH t a (ψ i),
          KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k t a ha (ψ i)⟩) :=
  (weinberg_convex_vector_split (RS t a (ψ i) - RH t a (ψ i))).trans
    (smGen_residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha ψ i)

theorem sm_forced_gauge_five_resolvent_master_bridge
    (a : ℝ) (ha : 0 < a) (ψ : SMGenState) :
    (atom_N_c = 3 ∧ atom_N_W = 2 ∧ atom_d_eff = 4) ∧
    (totalFermions atom_N_c atom_N_W = 15 ∧ singleGenDim = 16) ∧
    (smWeakWeight = 3 / 8 ∧ smHyperWeight = 5 / 8 ∧
      smWeakWeight + smHyperWeight = 1) ∧
    ((∑ i : Fin singleGenDim, ‖RT a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RP a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RG a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RS t a (ψ i)‖ ^ 2) +
      (∑ i : Fin singleGenDim, ‖RH t a (ψ i)‖ ^ 2) ≤
      5 * (a⁻¹) ^ 2 * (∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2)) ∧
    (∀ i : Fin singleGenDim,
      RP a (ψ i) - RG a (ψ i) =
        RP a (K ⟨RG a (ψ i),
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha (ψ i)⟩) ∧
      RS t a (ψ i) - RH t a (ψ i) =
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a (ψ i),
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha (ψ i)⟩)) :=
  ⟨⟨sm_color_dim_eq_three, sm_weak_dim_eq_two, sm_eff_spacetime_dim_eq_four⟩,
   ⟨sm_weyl_fermion_dim_eq_fifteen, sm_singleGenDim_eq_sixteen⟩,
   ⟨smWeakWeight_eq, smHyperWeight_eq, smWeakWeight_add_smHyperWeight⟩,
   smGen_five_resolvent_norm_sq_sum_le ε hε h hh hb m g k t a ha ψ,
   fun i => ⟨smGen_potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha ψ i,
     smGen_residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha ψ i⟩⟩

#print axioms sm_color_dim_eq_three
#print axioms sm_weak_dim_eq_two
#print axioms sm_eff_spacetime_dim_eq_four
#print axioms sm_colored_fermion_dim_eq_twelve
#print axioms sm_uncolored_fermion_dim_eq_three
#print axioms sm_weyl_fermion_dim_eq_fifteen
#print axioms sm_singleGenDim_eq_sixteen
#print axioms sm_singleGenDim_eq_weyl_succ
#print axioms sm_singleGenDim_eq_colored_add_uncolored_succ
#print axioms smWeakWeight_eq
#print axioms smHyperWeight_eq
#print axioms smWeakWeight_pos
#print axioms smHyperWeight_pos
#print axioms smWeakWeight_add_smHyperWeight
#print axioms smWeakWeight_div_smHyperWeight
#print axioms smWeakWeight_div_smHyperWeight_eq_inv_gutNormalization
#print axioms weinberg_convex_vector_split
#print axioms weinberg_convex_resolvent_split
#print axioms weinberg_convex_energy_split
#print axioms fin_tuple_resolvent_norm_sq_sum_le
#print axioms smGen_static_resolvent_norm_sq_sum_le
#print axioms smGen_potential_resolvent_norm_sq_sum_le
#print axioms smGen_growing_resolvent_norm_sq_sum_le
#print axioms smGen_residual_resolvent_norm_sq_sum_le
#print axioms smGen_hamiltonian_resolvent_norm_sq_sum_le
#print axioms smGen_five_resolvent_norm_sq_sum_le
#print axioms smWeyl_five_resolvent_norm_sq_sum_le
#print axioms smGen_potential_sub_growing_resolvent_eq
#print axioms smGen_residual_sub_hamiltonian_resolvent_eq
#print axioms smGen_static_sub_residual_resolvent_eq
#print axioms smGen_static_sub_hamiltonian_resolvent_eq
#print axioms smGen_potential_sub_growing_norm_sq_sum_le_source
#print axioms smWeyl_potential_sub_growing_resolvent_eq
#print axioms smWeyl_residual_sub_hamiltonian_resolvent_eq
#print axioms smGen_weinberg_weighted_potential_sub_growing_eq
#print axioms smGen_weinberg_weighted_residual_sub_hamiltonian_eq
#print axioms sm_forced_gauge_five_resolvent_master_bridge
end
end UnifiedTheory.Audit.KFCausalClockFloorSMForcedGaugeResolventBridge
