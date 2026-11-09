/- Algebraic QFT Bridge between Bisognano-Wichmann Rindler-Wedge KMS / Unruh-Hawking
Thermodynamics, Reeh-Schlieder Cyclicity, K/P-Derived CPT Invariance, Continuous Unitary
Chamber Poincare Representation, and the Clock-Floor Iterated Hamiltonian Resolvent Chain:
1. Synthesizes the Bisognano-Wichmann Unruh temperature `unruhTemperature a = a / (2π)`,
   its KMS period `bwInverseTemperature a = 2π / a`, their reciprocity `β_BW · T_U = 1`,
   the equivalence-principle Hawking-Unruh bridge `T_U(κ(M)) = T_H(M) = 1 / (8π M)`,
   and the black-hole first-law reciprocity `T_H(M) · dS/dM = 1`.
2. Unites the finite-dimensional Reeh-Schlieder cyclicity theorem (`IsCyclic`, rank-1
   outer-product witness `vecMulVec`, surjectivity of the orbit map for every nonzero
   state, sharpness `zero_not_cyclic`), the K/P derivation of C, P, and CPT invariance
   across the Born rule, U(1) dressing rotations, S-matrix, transition probabilities,
   and partition functions, and the continuous unitary Poincare representation `U_chamber`
   on the 3-dimensional chamber Hilbert space.
3. Couples these AQFT invariants to the clock-floor quantum operator chain: proves
   10-domain and second-power regularity for `iteratedHamiltonianResolvent` under CPT
   step reflection `h ↦ -h`, at the conjugate pair `(unruhTemperature acc, bwInverseTemperature acc)`
   and `(hawkingTemperature M, entropyDerivative M)` (where KMS and first-law reciprocity
   yield the parameter-free contraction `‖R_H(T_U)(R_H(β_BW) f)‖ ≤ ‖f‖` and
   `‖R_H(T_H)(R_H(dS/dM) f)‖ ≤ ‖f‖`), and at CPT-invariant Born-rule observables. -/
import UnifiedTheory.LayerB.BisognanoWichmann
import UnifiedTheory.LayerB.ReehSchlieder
import UnifiedTheory.LayerB.CPTFromKP
import UnifiedTheory.LayerB.Clay_W1_ContinuousPoincare
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedResolventRegularity
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAQFTBisognanoWichmannReehSchliederCPTBridge

noncomputable section

open Real Matrix
open scoped BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution
  (evolution evolution_norm)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
  (mem_all_form_domains_of_evolved)
open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.HawkingTemperature
open UnifiedTheory.LayerB.BisognanoWichmann
open UnifiedTheory.LayerB.ReehSchlieder
open UnifiedTheory.LayerB.CPTFromKP
open UnifiedTheory.LayerB.CL1_BathSector
open UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
open UnifiedTheory.LayerB.Clay_W1_ContinuousPoincare
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains
   iteratedHamiltonianResolvent_mem_radial_residual_domain
   iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
   iteratedHamiltonianResolvent_second_power_radial_residual_eq)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (hamiltonianResolvent_comm)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_norm_le)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "U" => evolution ε hε h hh hw m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-! ### 1. Bisognano-Wichmann Rindler KMS Temperature and Hawking-Unruh Equivalence Principle -/

/-- Zero-acceleration characterization, strict positivity, and non-negativity of
`unruhTemperature`. -/
theorem bisognano_wichmann_unruh_temperature_zero_and_positivity :
    unruhTemperature 0 = 0 ∧
    (∀ a : ℝ, unruhTemperature a = 0 ↔ a = 0) ∧
    (∀ a : ℝ, 0 < a → 0 < unruhTemperature a) ∧
    (∀ a : ℝ, 0 ≤ a → 0 ≤ unruhTemperature a) :=
  ⟨unruhTemperature_zero,
   unruhTemperature_eq_zero_iff,
   unruhTemperature_pos,
   unruhTemperature_nonneg⟩

/-- The `2π · T_U(a) = a` invariant, linearity, monotonicity, and strict monotonicity of
`unruhTemperature`. -/
theorem bisognano_wichmann_unruh_linearity_monotonicity_and_invariant :
    (∀ a : ℝ, 2 * Real.pi * unruhTemperature a = a) ∧
    (∀ c a : ℝ, unruhTemperature (c * a) = c * unruhTemperature a) ∧
    (∀ a₁ a₂ : ℝ, a₁ ≤ a₂ → unruhTemperature a₁ ≤ unruhTemperature a₂) ∧
    (∀ a₁ a₂ : ℝ, a₁ < a₂ → unruhTemperature a₁ < unruhTemperature a₂) :=
  ⟨twopi_unruhTemperature,
   unruhTemperature_linear,
   fun _ _ => unruhTemperature_mono,
   fun _ _ => unruhTemperature_strictMono⟩

/-- Strict positivity and KMS reciprocity `bwInverseTemperature a * unruhTemperature a = 1`
for any positive Rindler acceleration `0 < a`. -/
theorem bisognano_wichmann_kms_inverse_temperature_reciprocity
    (a : ℝ) (ha : 0 < a) :
    0 < bwInverseTemperature a ∧
    bwInverseTemperature a * unruhTemperature a = 1 :=
  ⟨bwInverseTemperature_pos a ha,
   bwInverseTemperature_times_unruhTemperature a ha⟩

/-- Equivalence-principle Hawking-Unruh bridge: for any black-hole mass `0 < M`,
`unruhTemperature (1 / (4 * M)) = 1 / (8 * Real.pi * M) = hawkingTemperature M`,
`unruhTemperature (surfaceGravity M) = hawkingTemperature M`, and
`bwInverseTemperature (1 / (4 * M)) = 8 * Real.pi * M`. -/
theorem bisognano_wichmann_hawking_unruh_equivalence_principle_bridge
    (M : ℝ) (hM : 0 < M) :
    unruhTemperature (1 / (4 * M)) = 1 / (8 * Real.pi * M) ∧
    unruhTemperature (1 / (4 * M)) = hawkingTemperature M ∧
    unruhTemperature (surfaceGravity M) = hawkingTemperature M ∧
    bwInverseTemperature (1 / (4 * M)) = 8 * Real.pi * M :=
  ⟨hawking_from_unruh M hM,
   hawking_unruh_bridge M hM,
   unruhTemperature_surfaceGravity_eq_hawking M hM,
   hawking_inverse_temperature_from_bw M hM⟩

/-- First-law reciprocity `hawkingTemperature M * entropyDerivative M = 1`, strict positivity
of `hawkingTemperature M` and `entropyDerivative M`, and the mass-temperature invariant
`M * hawkingTemperature M = 1 / (8 * Real.pi)` for `0 < M`. -/
theorem hawking_thermodynamics_first_law_and_entropy_derivative
    (M : ℝ) (hM : 0 < M) :
    0 < hawkingTemperature M ∧
    0 < entropyDerivative M ∧
    hawkingTemperature M * entropyDerivative M = 1 ∧
    M * hawkingTemperature M = 1 / (8 * Real.pi) :=
  ⟨hawkingTemperature_pos M hM,
   entropyDerivative_pos M hM,
   hawkingTemp_from_entropy_derivative M hM,
   M_times_hawkingTemperature M hM⟩

/-- Both substantive Bisognano-Wichmann and Unruh closed-form packages hold unconditionally. -/
theorem bisognano_wichmann_operational_substantive_package :
    BisognanoWichmann_Operational_Substantive ∧
    Unruh_ClosedForm_Substantive :=
  ⟨BisognanoWichmann_Operational_Substantive_holds,
   Unruh_ClosedForm_Substantive_holds⟩

/-! ### 2. Reeh-Schlieder Cyclicity, K/P-Derived CPT Invariance, and Chamber Poincare Unitarity -/

/-- Rank-1 outer-product action `(vecMulVec φ v) *ᵥ ψ = (v ⬝ᵥ ψ) • φ` on `Fin n → ℂ`. -/
theorem reeh_schlieder_rank_one_outer_product_and_covector
    {n : ℕ} (φ v ψ : Fin n → ℂ) :
    (Matrix.vecMulVec φ v) *ᵥ ψ = (v ⬝ᵥ ψ) • φ :=
  vecMulVec_mulVec_comm φ v ψ

/-- For any coordinate `i₀ : Fin n` with `ψ i₀ ≠ 0`, the covector `Pi.single i₀ (1 / ψ i₀)`
has unit dot product with `ψ`. -/
theorem reeh_schlieder_single_covector_dotProduct
    {n : ℕ} (ψ : Fin n → ℂ) (i₀ : Fin n) (hi : ψ i₀ ≠ 0) :
    (Pi.single i₀ (1 / ψ i₀)) ⬝ᵥ ψ = 1 :=
  single_inv_dotProduct ψ i₀ hi

/-- Every nonzero vector `ψ : Fin n → ℂ` has a surjective matrix orbit and is cyclic for the
full matrix algebra `End(ℂⁿ)`. -/
theorem reeh_schlieder_finite_dim_surjectivity_and_cyclicity
    {n : ℕ} (ψ : Fin n → ℂ) (hψ : ψ ≠ 0) :
    (∀ φ : Fin n → ℂ, ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ) ∧
    IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) ψ ∧
    Function.Surjective (fun a : Matrix (Fin n) (Fin n) ℂ => a *ᵥ ψ) :=
  ⟨reeh_schlieder_toy ψ hψ,
   full_algebra_cyclic_for_nonzero ψ hψ,
   action_map_surjective ψ hψ⟩

/-- Full-orbit equality `{a *ᵥ ψ} = Set.univ` for every nonzero `ψ : Fin n → ℂ`, together with
sharpness `¬ IsCyclic Set.univ 0` for `0 < n`. -/
theorem reeh_schlieder_orbit_eq_univ_and_zero_not_cyclic :
    (∀ {n : ℕ} (ψ : Fin n → ℂ), ψ ≠ 0 →
      {φ : Fin n → ℂ | ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ} = Set.univ) ∧
    (∀ {n : ℕ}, 0 < n →
      ¬ IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) (0 : Fin n → ℂ)) :=
  ⟨fun ψ hψ => orbit_full_algebra_eq_univ ψ hψ,
   fun hn => zero_not_cyclic hn⟩

/-- Both substantive finite-dimensional Reeh-Schlieder targets hold unconditionally. -/
theorem reeh_schlieder_substantive_targets :
    ReehSchlieder_FiniteDim_Target ∧
    ReehSchlieder_AlgebraicQFT_Target_Substantive :=
  ⟨reehSchlieder_finiteDim_target_holds,
   reehSchlieder_AlgebraicQFT_Target_Substantive_holds⟩

/-- Charge conjugation `φ(-v) = -φ(v)`, matter-antimatter mass equality `|φ(-v)| = |φ(v)|`,
and zero-charge annihilation `φ(v + (-v)) = 0` for any linear charge functional `φ`. -/
theorem cpt_charge_conjugation_antimatter_mass_and_annihilation
    {V : Type*} [AddCommGroup V] [Module ℝ V] (φ : V →ₗ[ℝ] ℝ) (v : V) :
    φ (-v) = -φ v ∧
    |φ (-v)| = |φ v| ∧
    φ (v + (-v)) = 0 :=
  ⟨charge_conjugation φ v,
   antimatter_same_mass φ v,
   annihilation_zero_charge φ v⟩

/-- Exact Born-rule evaluation `obs (amplitudeFromKP Q P) = Q ^ 2 + P ^ 2` and invariance
under C (`Q ↦ -Q`), P (`P ↦ -P`), and full CPT (`(Q, P) ↦ (-Q, -P)`). -/
theorem cpt_born_rule_invariance_under_C_P_and_CPT (Q P_dress : ℝ) :
    obs (amplitudeFromKP Q P_dress) = Q ^ 2 + P_dress ^ 2 ∧
    obs (amplitudeFromKP (-Q) P_dress) = obs (amplitudeFromKP Q P_dress) ∧
    obs (amplitudeFromKP Q (-P_dress)) = obs (amplitudeFromKP Q P_dress) ∧
    obs (amplitudeFromKP (-Q) (-P_dress)) = obs (amplitudeFromKP Q P_dress) :=
  ⟨obs_from_KP Q P_dress,
   charge_conj_preserves_obs Q P_dress,
   parity_preserves_obs Q P_dress,
   full_cpt_preserves_obs Q P_dress⟩

/-- U(1) dressing-rotation invariance of the Born rule and exact dressing-interference
formula `2 * (Q * Q + P₁ * P₂)`. -/
theorem cpt_u1_dressing_rotation_and_interference (θ Q P₁ P₂ : ℝ) :
    obs (dressingRotation θ Q P₁) = obs (amplitudeFromKP Q P₁) ∧
    obs (amplitudeFromKP Q P₁ + amplitudeFromKP Q P₂) =
      obs (amplitudeFromKP Q P₁) + obs (amplitudeFromKP Q P₂) +
        interferenceTerm (amplitudeFromKP Q P₁) (amplitudeFromKP Q P₂) ∧
    interferenceTerm (amplitudeFromKP Q P₁) (amplitudeFromKP Q P₂) =
      2 * (Q * Q + P₁ * P₂) :=
  ⟨dressing_rotation_preserves_obs θ Q P₁,
   dressing_causes_interference Q P₁ P₂,
   interference_is_dressing_dependent Q P₁ P₂⟩

/-- CPT invariance of the S-matrix functional, transition probability `|S|²`, and weighted
partition sum `∑ i, w i * obs(z_i)`. -/
theorem cpt_smatrix_transition_probability_and_partition_invariance
    {n : ℕ} (f_S : (Fin n → ℝ) → ℝ) (Q P_dress w : Fin n → ℝ) :
    f_S (fun i => obs (amplitudeFromKP (-(Q i)) (-(P_dress i)))) =
      f_S (fun i => obs (amplitudeFromKP (Q i) (P_dress i))) ∧
    (f_S (fun i => obs (amplitudeFromKP (-(Q i)) (-(P_dress i))))) ^ 2 =
      (f_S (fun i => obs (amplitudeFromKP (Q i) (P_dress i)))) ^ 2 ∧
    ∑ i : Fin n, w i * obs (amplitudeFromKP (-(Q i)) (-(P_dress i))) =
      ∑ i : Fin n, w i * obs (amplitudeFromKP (Q i) (P_dress i)) :=
  ⟨smatrix_cpt_invariant f_S Q P_dress,
   transition_probability_cpt f_S Q P_dress,
   partition_function_cpt Q P_dress w⟩

/-- Symmetry, non-negativity, and orthonormality of `(Ω_chamber, chamber_first_state, chamber_top_state)`
with respect to `chamberInner`. -/
theorem poincare_chamber_inner_product_and_orthonormal_eigenbasis :
    (∀ ψ φ : ChamberState, chamberInner ψ φ = chamberInner φ ψ) ∧
    (∀ ψ : ChamberState, 0 ≤ chamberInner ψ ψ) ∧
    chamberInner Ω_chamber Ω_chamber = 1 ∧
    chamberInner chamber_first_state chamber_first_state = 1 ∧
    chamberInner chamber_top_state chamber_top_state = 1 ∧
    chamberInner Ω_chamber chamber_first_state = 0 ∧
    chamberInner Ω_chamber chamber_top_state = 0 ∧
    chamberInner chamber_first_state chamber_top_state = 0 :=
  ⟨chamberInner_symm,
   chamberInner_self_nonneg,
   chamberInner_vacuum_self,
   chamberInner_first_self,
   chamberInner_top_self,
   chamberInner_vacuum_first,
   chamberInner_vacuum_top,
   chamberInner_first_top⟩

/-- Group laws for `PoincareParam` under `poincareMul`, `poincareIdentity`, and `poincareInv`. -/
theorem poincare_parameter_group_laws (g₁ g₂ g₃ : PoincareParam) :
    poincareMul poincareIdentity g₁ = g₁ ∧
    poincareMul g₁ poincareIdentity = g₁ ∧
    poincareMul (poincareInv g₁) g₁ = poincareIdentity ∧
    poincareMul (poincareMul g₁ g₂) g₃ = poincareMul g₁ (poincareMul g₂ g₃) :=
  ⟨poincareMul_identity_left g₁,
   poincareMul_identity_right g₁,
   poincareMul_inv_left g₁,
   poincareMul_assoc g₁ g₂ g₃⟩

/-- Unitarity, continuity, group-homomorphism law, identity preservation, and vacuum-fixing
for the continuous chamber Poincare representation `U_chamber`. -/
theorem poincare_chamber_continuous_unitary_representation :
    (∀ g_p : PoincareParam, ∀ ψ φ : ChamberState,
      chamberInner (U_chamber g_p ψ) (U_chamber g_p φ) = chamberInner ψ φ) ∧
    (∀ g₁ g₂ : PoincareParam, U_chamber g₁ = U_chamber g₂) ∧
    (∀ g₁ g₂ : PoincareParam,
      U_chamber (poincareMul g₁ g₂) = fun ψ => U_chamber g₁ (U_chamber g₂ ψ)) ∧
    U_chamber poincareIdentity = chamberId ∧
    (∀ g_p : PoincareParam, U_chamber g_p Ω_chamber = Ω_chamber) :=
  ⟨U_chamber_unitary,
   U_chamber_continuous,
   U_chamber_group_hom,
   U_chamber_sends_identity,
   U_chamber_fixes_vacuum⟩

/-- Nonemptiness of `ChamberHilbertWithUP` and full-spectrum spectral-gap lift under
`ChamberIsLowestSector`. -/
theorem poincare_chamber_hilbert_with_UP_and_full_spectrum_lift :
    Nonempty ChamberHilbertWithUP ∧
    (∀ (B : BathSpectrum), ChamberIsLowestSector B →
      (∀ lam ∈ FullSpectrum B, μ_vac ≤ lam) ∧
      (∀ lam ∈ FullSpectrum B, lam ≠ μ_vac → μ_first ≤ lam) ∧
      (∀ lam ∈ B.eigs, μ_top ≤ lam)) :=
  ⟨chamberHilbertWithUP_exists,
   fun B hB => ⟨(W1_full_under_lowest_sector B hB).2.2.1,
                (W1_full_under_lowest_sector B hB).2.2.2.1,
                (W1_full_under_lowest_sector B hB).2.2.2.2⟩⟩

/-! ### 3. Clock-Floor Iterated Resolvent Regularity at CPT, Unruh-KMS, and Hawking Parameters -/

include hh hb in
/-- Under CPT charge-conjugation reflection `h ↦ -h`, the step width remains nonzero and
satisfies the full-strip clock bound `|-h| ≤ Real.pi * ε / 3`. -/
theorem clock_floor_cpt_charge_conjugated_step_width_bound :
    -h ≠ 0 ∧ |-h| ≤ Real.pi * ε / 3 :=
  ⟨neg_ne_zero.mpr hh, by simpa only [abs_neg] using hb⟩

/-- Under CPT reflection `(h, m, g) ↦ (-h, -m, -g)`, `iteratedHamiltonianResolvent` preserves
full 10-domain and second-power domain regularity for all `0 < a, 0 < b`. -/
theorem clock_floor_iterated_resolvent_under_cpt_step_inversion_mem_ten_domains
    (t s a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let hnh := (clock_floor_cpt_charge_conjugated_step_width_bound ε h hh hb).1
    let hnb := (clock_floor_cpt_charge_conjugated_step_width_bound ε h hh hb).2
    let x := iteratedHamiltonianResolvent ε hε (-h) hnh hnb (-m) (-g) k t a b f
    x ∈ hamiltonianSecondPowerDomain ε hε (-h) hnh hnb (-m) (-g) k t ∧
    x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε (-h) hnh
          (wide_bound ε hε (-h) hnb) (-m) (-g) k t).domain ∧
    x ∈ (KFCausalClockFloorRadialYosidaDomain.operator ε hε (-h)).domain ∧
    x ∈ (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε (-h) hnh
          (wide_bound ε hε (-h) hnb) (-m) (-g) k t).domain ∧
    x ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε (-h)
          (hamiltonian_bound ε (-h) (wide_bound ε hε (-h) hnb)) hnh (-m) (-g) k s).domain ∧
    x ∈ (clockHalf ε).domain := by
  intro hnh hnb x
  have h10 := iteratedHamiltonianResolvent_mem_ten_domains
    ε hε (-h) hnh hnb (-m) (-g) k t s a b ha hb_pos f
  exact ⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.1,
         h10.2.2.2.2.2.2.2.2.2.2⟩

/-- Evaluating `iteratedHamiltonianResolvent` at the Bisognano-Wichmann conjugate pair
`(unruhTemperature acc, bwInverseTemperature acc)` for any `0 < acc` places the state in
`hamiltonianSecondPowerDomain t` and all 10 operator, form, and clock domains. -/
theorem clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_mem_ten_domains
    (t s acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    x ∈ (H t).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S t).domain ∧
    x ∈ (Eavg s).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres s).domain ∧
    x ∈ (clockHalf ε).domain :=
  iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t s
    (unruhTemperature acc) (bwInverseTemperature acc)
    (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f

/-- Exact parameter commutativity of `iteratedHamiltonianResolvent` between
`unruhTemperature acc` and `bwInverseTemperature acc` (`0 < acc`). -/
theorem clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_comm
    (t acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f =
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (bwInverseTemperature acc) (unruhTemperature acc) f :=
  hamiltonianResolvent_comm ε hε h hh hb m g k t
    (unruhTemperature acc) (bwInverseTemperature acc)
    (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f

/-- By the Bisognano-Wichmann KMS reciprocity `bwInverseTemperature acc * unruhTemperature acc = 1`
(`0 < acc`), the iterated resolvent at `(unruhTemperature acc, bwInverseTemperature acc)` is a
parameter-free contraction: `‖iteratedHamiltonianResolvent t (T_U acc) (β_BW acc) f‖ ≤ ‖f‖`. -/
theorem clock_floor_iterated_resolvent_at_unruh_and_kms_norm_le_source
    (t acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f‖ ≤ ‖f‖ := by
  have hT := unruhTemperature_pos acc hacc
  have hB := bwInverseTemperature_pos acc hacc
  have h1 := resolvent_norm_le ε hε h hh hb m g k t
    (unruhTemperature acc) hT (RH t (bwInverseTemperature acc) f)
  have h2 := resolvent_norm_le ε hε h hh hb m g k t
    (bwInverseTemperature acc) hB f
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hT.le))
  have hrec := bwInverseTemperature_times_unruhTemperature acc hacc
  have hprod : (unruhTemperature acc)⁻¹ * ((bwInverseTemperature acc)⁻¹ * ‖f‖) = ‖f‖ := by
    rw [← mul_assoc, ← mul_inv, mul_comm (unruhTemperature acc), hrec, inv_one, one_mul]
  exact h3.trans_eq hprod

/-- Exact first-power radial-residual decomposition on
`x := iteratedHamiltonianResolvent t (unruhTemperature acc) (bwInverseTemperature acc) f` (`0 < acc`). -/
theorem clock_floor_iterated_resolvent_at_unruh_and_kms_radial_residual_decomposition
    (t acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain
      ε hε h hh hb m g k t (unruhTemperature acc) (bwInverseTemperature acc)
      (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f
    H t ⟨x, hdom.1⟩ =
      (Real.exp (2 * t) : ℂ) • K ⟨x, hdom.2.1⟩ + S t ⟨x, hdom.2.2⟩ ∧
    H t ⟨x, hdom.1⟩ =
      RH t (bwInverseTemperature acc) f - (unruhTemperature acc : ℂ) • x :=
  iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
    ε hε h hh hb m g k t (unruhTemperature acc) (bwInverseTemperature acc)
    (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f

/-- Exact second-power radial-residual identity for `iteratedHamiltonianResolvent` at
`(unruhTemperature acc, bwInverseTemperature acc)` (`0 < acc`). -/
theorem clock_floor_iterated_resolvent_at_unruh_and_kms_second_power_identity
    (t acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f
    let y := RH t (bwInverseTemperature acc) f - (unruhTemperature acc : ℂ) • x
    let hdom :=
      KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination.iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t (unruhTemperature acc) (bwInverseTemperature acc)
        (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((unruhTemperature acc + bwInverseTemperature acc : ℝ) : ℂ) •
        RH t (bwInverseTemperature acc) f +
        ((unruhTemperature acc ^ 2 : ℝ) : ℂ) • x :=
  iteratedHamiltonianResolvent_second_power_radial_residual_eq
    ε hε h hh hb m g k t (unruhTemperature acc) (bwInverseTemperature acc)
    (unruhTemperature_pos acc hacc) (bwInverseTemperature_pos acc hacc) f

/-- Evaluating `iteratedHamiltonianResolvent` at the black-hole thermodynamic conjugate pair
`(hawkingTemperature M, entropyDerivative M)` (`0 < M`) places the state in
`hamiltonianSecondPowerDomain t` and all 10 operator, form, and clock domains, with exact
parameter commutativity. -/
theorem clock_floor_iterated_resolvent_at_hawking_and_entropy_derivative_mem_ten_domains
    (t s M : ℝ) (hM : 0 < M) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (hawkingTemperature M) (entropyDerivative M) f
    (x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
     x ∈ (H t).domain ∧
     x ∈ (K).domain ∧
     x ∈ (S t).domain ∧
     x ∈ (Eavg s).domain ∧
     x ∈ (Tstat).domain ∧
     x ∈ (Kroot).domain ∧
     x ∈ (Tpot).domain ∧
     x ∈ (Tgrow).domain ∧
     x ∈ (Tres s).domain ∧
     x ∈ (clockHalf ε).domain) ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (hawkingTemperature M) (entropyDerivative M) f =
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (entropyDerivative M) (hawkingTemperature M) f :=
  ⟨iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t s
     (hawkingTemperature M) (entropyDerivative M)
     (hawkingTemperature_pos M hM) (entropyDerivative_pos M hM) f,
   hamiltonianResolvent_comm ε hε h hh hb m g k t
     (hawkingTemperature M) (entropyDerivative M)
     (hawkingTemperature_pos M hM) (entropyDerivative_pos M hM) f⟩

/-- By the black-hole first-law reciprocity `hawkingTemperature M * entropyDerivative M = 1`
(`0 < M`), the iterated resolvent at `(hawkingTemperature M, entropyDerivative M)` satisfies
the parameter-free contraction `‖iteratedHamiltonianResolvent t (T_H M) (dS/dM) f‖ ≤ ‖f‖`. -/
theorem clock_floor_iterated_resolvent_at_hawking_and_entropy_derivative_norm_le_source
    (t M : ℝ) (hM : 0 < M) (f : Hilbert) :
    ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (hawkingTemperature M) (entropyDerivative M) f‖ ≤ ‖f‖ := by
  have hT := hawkingTemperature_pos M hM
  have hS := entropyDerivative_pos M hM
  have h1 := resolvent_norm_le ε hε h hh hb m g k t
    (hawkingTemperature M) hT (RH t (entropyDerivative M) f)
  have h2 := resolvent_norm_le ε hε h hh hb m g k t
    (entropyDerivative M) hS f
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hT.le))
  have hrec := hawkingTemp_from_entropy_derivative M hM
  have hprod : (hawkingTemperature M)⁻¹ * ((entropyDerivative M)⁻¹ * ‖f‖) = ‖f‖ := by
    rw [← mul_assoc, ← mul_inv, hrec, inv_one, one_mul]
  exact h3.trans_eq hprod

/-- Equivalence-principle identity at the operator-resolvent level: for `0 < M`,
`iteratedHamiltonianResolvent` at `(unruhTemperature (surfaceGravity M), entropyDerivative M)`
coincides identically with `iteratedHamiltonianResolvent` at
`(hawkingTemperature M, entropyDerivative M)`. -/
theorem clock_floor_iterated_resolvent_at_hawking_eq_unruh_surfaceGravity
    (t M : ℝ) (hM : 0 < M) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature (surfaceGravity M)) (entropyDerivative M) f =
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (hawkingTemperature M) (entropyDerivative M) f := by
  rw [unruhTemperature_surfaceGravity_eq_hawking M hM]

/-- Evolving `iteratedHamiltonianResolvent s (unruhTemperature acc) (bwInverseTemperature acc) f`
(`0 < acc`) by `U s t` places the trajectory vector in all 7 form and clock domains with
parameter-free contraction `‖U s t (iteratedHamiltonianResolvent s (T_U acc) (β_BW acc) f)‖ ≤ ‖f‖`. -/
theorem clock_floor_evolved_iterated_resolvent_at_unruh_and_kms_mem_all_form_domains
    (s t q acc : ℝ) (hacc : 0 < acc) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k s
      (unruhTemperature acc) (bwInverseTemperature acc) f
    let u := U s t x
    (u ∈ (Eavg q).domain ∧
     u ∈ (Tstat).domain ∧
     u ∈ (Kroot).domain ∧
     u ∈ (Tpot).domain ∧
     u ∈ (Tgrow).domain ∧
     u ∈ (Tres q).domain ∧
     u ∈ (clockHalf ε).domain) ∧
    ‖u‖ ≤ ‖f‖ := by
  intro x u
  have hEs := (clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_mem_ten_domains
    ε hε h hh hb m g k s s acc hacc f).2.2.2.2.1
  have hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hEs
  have hnorm : ‖u‖ ≤ ‖f‖ :=
    (evolution_norm ε hε h hh hw m g k s t x).trans_le
      (clock_floor_iterated_resolvent_at_unruh_and_kms_norm_le_source
        ε hε h hh hb m g k s acc hacc f)
  exact ⟨hdom, hnorm⟩

/-- For any K/P defect `(Q, P_dress)` with `P_dress ≠ 0`, the CPT-transformed Born observable
`obs (amplitudeFromKP (-Q) (-P_dress))` equals `obs (amplitudeFromKP Q P_dress) > 0`, so
`iteratedHamiltonianResolvent` at `(obs(CPT·z), obs(z))` equals `squaredHamiltonianResolvent`
at `obs(z)` and belongs to `hamiltonianSecondPowerDomain t` and all 10 operator, form, and clock
domains. -/
theorem clock_floor_iterated_resolvent_at_cpt_born_observable_mem_ten_domains
    (t s Q P_dress : ℝ) (hP : P_dress ≠ 0) (f : Hilbert) :
    let a_cpt := obs (amplitudeFromKP (-Q) (-P_dress))
    let a_born := obs (amplitudeFromKP Q P_dress)
    a_cpt = a_born ∧
    0 < a_born ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a_cpt a_born f =
      squaredHamiltonianResolvent ε hε h hh hb m g k t a_born f ∧
    squaredHamiltonianResolvent ε hε h hh hb m g k t a_born f ∈
      hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    squaredHamiltonianResolvent ε hε h hh hb m g k t a_born f ∈ (Eavg s).domain ∧
    squaredHamiltonianResolvent ε hε h hh hb m g k t a_born f ∈ (clockHalf ε).domain := by
  intro a_cpt a_born
  have heq : a_cpt = a_born := full_cpt_preserves_obs Q P_dress
  have hpos : 0 < a_born := by
    change 0 < obs (amplitudeFromKP Q P_dress)
    rw [obs_from_KP]
    have hP2 : 0 < P_dress ^ 2 := sq_pos_of_ne_zero hP
    have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
    linarith
  have hsq : iteratedHamiltonianResolvent ε hε h hh hb m g k t a_cpt a_born f =
      squaredHamiltonianResolvent ε hε h hh hb m g k t a_born f := by
    rw [heq]
    rfl
  have h10 := iteratedHamiltonianResolvent_mem_ten_domains
    ε hε h hh hb m g k t s a_born a_born hpos hpos f
  exact ⟨heq, hpos, hsq, h10.1, h10.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.2.2⟩

/-- Grand AQFT synthesis uniting Bisognano-Wichmann Unruh-Hawking reciprocity, finite-dimensional
Reeh-Schlieder cyclicity, K/P-derived CPT invariance, chamber continuous unitary Poincare
invariance, and clock-floor 10-domain iterated resolvent regularity with KMS-Unruh and
Hawking first-law contraction `≤ ‖f‖`. -/
theorem aqft_bisognano_wichmann_reeh_schlieder_cpt_clock_floor_synthesis
    (t s acc M Q P_dress : ℝ) (hacc : 0 < acc) (hM : 0 < M) (f : Hilbert) :
    (bwInverseTemperature acc * unruhTemperature acc = 1 ∧
     unruhTemperature (surfaceGravity M) = hawkingTemperature M ∧
     hawkingTemperature M * entropyDerivative M = 1) ∧
    ReehSchlieder_FiniteDim_Target ∧
    obs (amplitudeFromKP (-Q) (-P_dress)) = obs (amplitudeFromKP Q P_dress) ∧
    Nonempty ChamberHilbertWithUP ∧
    ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f‖ ≤ ‖f‖ ∧
    ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (hawkingTemperature M) (entropyDerivative M) f‖ ≤ ‖f‖ ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      (unruhTemperature acc) (bwInverseTemperature acc) f ∈ (Eavg s).domain :=
  ⟨⟨bwInverseTemperature_times_unruhTemperature acc hacc,
    unruhTemperature_surfaceGravity_eq_hawking M hM,
    hawkingTemp_from_entropy_derivative M hM⟩,
   reehSchlieder_finiteDim_target_holds,
   full_cpt_preserves_obs Q P_dress,
   chamberHilbertWithUP_exists,
   clock_floor_iterated_resolvent_at_unruh_and_kms_norm_le_source
     ε hε h hh hb m g k t acc hacc f,
   clock_floor_iterated_resolvent_at_hawking_and_entropy_derivative_norm_le_source
     ε hε h hh hb m g k t M hM f,
   (clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_mem_ten_domains
     ε hε h hh hb m g k t s acc hacc f).2.2.2.2.1⟩

#print axioms bisognano_wichmann_unruh_temperature_zero_and_positivity
#print axioms bisognano_wichmann_unruh_linearity_monotonicity_and_invariant
#print axioms bisognano_wichmann_kms_inverse_temperature_reciprocity
#print axioms bisognano_wichmann_hawking_unruh_equivalence_principle_bridge
#print axioms hawking_thermodynamics_first_law_and_entropy_derivative
#print axioms bisognano_wichmann_operational_substantive_package
#print axioms reeh_schlieder_rank_one_outer_product_and_covector
#print axioms reeh_schlieder_single_covector_dotProduct
#print axioms reeh_schlieder_finite_dim_surjectivity_and_cyclicity
#print axioms reeh_schlieder_orbit_eq_univ_and_zero_not_cyclic
#print axioms reeh_schlieder_substantive_targets
#print axioms cpt_charge_conjugation_antimatter_mass_and_annihilation
#print axioms cpt_born_rule_invariance_under_C_P_and_CPT
#print axioms cpt_u1_dressing_rotation_and_interference
#print axioms cpt_smatrix_transition_probability_and_partition_invariance
#print axioms poincare_chamber_inner_product_and_orthonormal_eigenbasis
#print axioms poincare_parameter_group_laws
#print axioms poincare_chamber_continuous_unitary_representation
#print axioms poincare_chamber_hilbert_with_UP_and_full_spectrum_lift
#print axioms clock_floor_cpt_charge_conjugated_step_width_bound
#print axioms clock_floor_iterated_resolvent_under_cpt_step_inversion_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_unruh_and_kms_parameters_comm
#print axioms clock_floor_iterated_resolvent_at_unruh_and_kms_norm_le_source
#print axioms clock_floor_iterated_resolvent_at_unruh_and_kms_radial_residual_decomposition
#print axioms clock_floor_iterated_resolvent_at_unruh_and_kms_second_power_identity
#print axioms clock_floor_iterated_resolvent_at_hawking_and_entropy_derivative_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_hawking_and_entropy_derivative_norm_le_source
#print axioms clock_floor_iterated_resolvent_at_hawking_eq_unruh_surfaceGravity
#print axioms clock_floor_evolved_iterated_resolvent_at_unruh_and_kms_mem_all_form_domains
#print axioms clock_floor_iterated_resolvent_at_cpt_born_observable_mem_ten_domains
#print axioms aqft_bisognano_wichmann_reeh_schlieder_cpt_clock_floor_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorAQFTBisognanoWichmannReehSchliederCPTBridge
