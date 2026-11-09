/- Bridge between the Explicit Wilson-Loop Action, Abstract Wilson Hamiltonian,
Explicit 6-Mode Volterra-Basis Feshbach Projection, Physical Wilson Expectation,
Volterra Block-Diagonal Derivation, SO(10) Haar Trace Identity, Physical Partition
Function Scaling, and the Clock-Floor Iterated Hamiltonian Resolvent Chain:
1. Synthesizes the 4-event causal-diamond Wilson action (`wilsonAction`), plaquette
   amplitude bounds, sample gauge configurations (`idGaugeField`, `halfGaugeField`,
   `mostNegativeGaugeField`), and compatibility with `WilsonExpectation`.
2. Connects the abstract `wilsonHamiltonian` carrier and chamber matrix to the
   explicit 6x6 Volterra-basis Wilson Hamiltonian `H_W`, its Feshbach blocks
   (`H_PP`, `H_PQ`, `H_QP`, `H_QQ`), bath resolvent `bathResolvent`, vanishing
   self-energy `selfEnergy`, effective Hamiltonian `H_eff(λ) = J₄`, characteristic
   polynomial factorization, and the `WilsonBlockHypothesis` derivation from
   `ChamberBathCommutes`, Volterra singular ratios, and color dressing.
3. Combines the structural `physicalWilsonExpectation`, the closed-form mass-gap
   candidate `yangMillsMassGap = √7 / 15 > 0`, the SO(10) Haar trace identity
   `∫ reTrace dHaar = 0`, and the physical partition-function scaling `PhysicalZ → exp(-β)`
   with unconditional 10-domain clock-floor iterated Hamiltonian resolvent regularity
   at `(yangMillsMassGap, lambda_star_real)` and `(μ_bath, exp(-β))`. -/
import UnifiedTheory.LayerB.Build5_WilsonYMSynthesis
import UnifiedTheory.LayerB.Clay_HaarTraceIdentity
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorWilsonActionFeshbachVolterraHaarBridge

noncomputable section

open Real Filter Topology MeasureTheory MeasureTheory.Measure
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.YangMillsCausalAttack
open UnifiedTheory.LayerB.CL1_ChamberLowestSector
open UnifiedTheory.LayerB.Clay1_GeneralPoissonLift
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure
open UnifiedTheory.LayerB.Clay3_PhysicalZ
open UnifiedTheory.LayerB.Clay3_StructureInputsDerivation
open UnifiedTheory.LayerB.Clay_HaarTraceIdentity
open UnifiedTheory.LayerB.Build1_ExplicitWilsonAction
open UnifiedTheory.LayerB.Build2_HamiltonianFromAction
open UnifiedTheory.LayerB.Build3_ExplicitFeshbach
open UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation
open UnifiedTheory.LayerB.Build5_WilsonYMSynthesis
open UnifiedTheory.LayerB.Build6_VolterraBlockDiagonalDerivation
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains
   iteratedHamiltonianResolvent_mem_radial_residual_domain
   iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
   iteratedHamiltonianResolvent_second_power_radial_residual_eq
   iteratedHamiltonianResolvent_component_norm_sq_le_source)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (hamiltonianResolvent_comm)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
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

/-! ### 1. Causal-Diamond Wilson Action and Abstract Wilson Hamiltonian Carrier -/

/-- The 4-event causal diamond has 4 covering links (`e1`, `e2`, `e3`, `e4`) and a unique
fundamental plaquette (`Plaquette.square`). -/
theorem wilson_diamond_links_and_plaquette_structure :
    diamondLinkCount = 4 ∧
    diamondPlaquetteCount = 1 ∧
    (∀ e : DiamondLink,
      e = DiamondLink.e1 ∨ e = DiamondLink.e2 ∨
      e = DiamondLink.e3 ∨ e = DiamondLink.e4) ∧
    (∀ p : Plaquette, p = Plaquette.square) :=
  ⟨diamondLinkCount_eq_four, diamondPlaquetteCount_eq_one,
   DiamondLink_exhaustive, Plaquette_unique⟩

/-- Exact plaquette amplitudes on `idGaugeField`, `halfGaugeField`, and `mostNegativeGaugeField`,
together with the two-sided bound `-1 ≤ plaquetteAmp g Plaquette.square ≤ 1`. -/
theorem wilson_plaquette_amplitude_bounds_and_id :
    plaquetteAmp idGaugeField Plaquette.square = 1 ∧
    plaquetteAmp halfGaugeField Plaquette.square = 1 / 2 ∧
    plaquetteAmp mostNegativeGaugeField Plaquette.square = -1 ∧
    (∀ g_cfg : GaugeField,
      -1 ≤ plaquetteAmp g_cfg Plaquette.square ∧
      plaquetteAmp g_cfg Plaquette.square ≤ 1) :=
  ⟨plaquetteAmp_id Plaquette.square,
   plaquetteAmp_half Plaquette.square,
   plaquetteAmp_mostNeg Plaquette.square,
   fun g_cfg => ⟨plaquetteAmp_ge_mone g_cfg Plaquette.square,
                 plaquetteAmp_le_one g_cfg Plaquette.square⟩⟩

/-- Exact evaluations of `wilsonAction S` on `idGaugeField` (`0`), `halfGaugeField` (`S / 2`),
and `mostNegativeGaugeField` (`2 * S`). -/
theorem wilson_action_sample_values (S_cpl : ℝ) :
    wilsonAction S_cpl idGaugeField = 0 ∧
    wilsonAction S_cpl halfGaugeField = S_cpl / 2 ∧
    wilsonAction S_cpl mostNegativeGaugeField = 2 * S_cpl :=
  ⟨wilsonAction_id S_cpl, wilsonAction_half S_cpl, wilsonAction_mostNeg S_cpl⟩

/-- For non-negative coupling `0 ≤ S_cpl`, `wilsonAction S_cpl` is non-negative, bounded above
by `2 * S_cpl`, and reverses link-amplitude order (`g₂.amp ≤ g₁.amp → wilsonAction S_cpl g₁ ≤ wilsonAction S_cpl g₂`). -/
theorem wilson_action_nonneg_upper_bound_and_monotone
    (S_cpl : ℝ) (hS : 0 ≤ S_cpl) :
    (∀ g_cfg : GaugeField,
      0 ≤ wilsonAction S_cpl g_cfg ∧ wilsonAction S_cpl g_cfg ≤ 2 * S_cpl) ∧
    (∀ g₁ g₂ : GaugeField,
      (∀ e : DiamondLink, g₂.amp e ≤ g₁.amp e) →
      wilsonAction S_cpl g₁ ≤ wilsonAction S_cpl g₂) :=
  ⟨fun g_cfg => ⟨wilsonAction_nonneg S_cpl hS g_cfg,
                 wilsonAction_le_two_S S_cpl hS g_cfg⟩,
   wilsonAction_monotone S_cpl hS⟩

/-- Plaquette-sum decomposition, `defaultWilsonAction` agreement, and compatibility of
`gaugeObservable` with `WilsonExpectation`. -/
theorem wilson_action_plaquette_sum_and_expectation_bridge
    (ρ β S_cpl : ℝ) (g_cfg : GaugeField) :
    wilsonAction S_cpl g_cfg = plaquetteContribution S_cpl g_cfg Plaquette.square ∧
    defaultWilsonAction.action S_cpl g_cfg = wilsonAction S_cpl g_cfg ∧
    WilsonExpectation ρ β (gaugeObservable S_cpl g_cfg) = wilsonAction S_cpl g_cfg :=
  ⟨wilsonAction_eq_sum_plaquettes S_cpl g_cfg,
   defaultWilsonAction_eq S_cpl g_cfg,
   wilsonAction_compatible_with_WilsonExpectation ρ β S_cpl g_cfg⟩

/-- Exact rational invariants of the canonical `wilsonHamiltonian` carrier:
`chamberDim = 3`, `topEigenvalue = 3 / 5`, `interiorDiscriminant = 7`,
`interiorTrace = 1 / 3`, and `interiorProduct = 1 / 50`. -/
theorem wilson_hamiltonian_carrier_invariants :
    wilsonHamiltonian.chamberDim = 3 ∧
    wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    wilsonHamiltonian.interiorDiscriminant = 7 ∧
    wilsonHamiltonian.interiorTrace = 1 / 3 ∧
    wilsonHamiltonian.interiorProduct = 1 / 50 :=
  ⟨wilsonHamiltonian_chamberDim,
   wilsonHamiltonian_topEigenvalue,
   wilsonHamiltonian_discriminant,
   wilsonHamiltonian_trace,
   wilsonHamiltonian_product⟩

/-- The abstract chamber matrix `wilsonHamiltonian_chamberMatrix` coincides entrywise with
`H_chamber_entry`, is Hermitian, and has trace `14 / 15 = 3 / 5 + 1 / 3`. -/
theorem wilson_hamiltonian_chamber_matrix_hermitian_and_trace :
    (∀ i j : Fin 3, wilsonHamiltonian_chamberMatrix i j = H_chamber_entry i j) ∧
    (∀ i j : Fin 3, wilsonHamiltonian_chamberMatrix i j = wilsonHamiltonian_chamberMatrix j i) ∧
    wilsonHamiltonian_chamberMatrix ⟨0, by decide⟩ ⟨0, by decide⟩ +
      wilsonHamiltonian_chamberMatrix ⟨1, by decide⟩ ⟨1, by decide⟩ +
      wilsonHamiltonian_chamberMatrix ⟨2, by decide⟩ ⟨2, by decide⟩ = 14 / 15 ∧
    (14 : ℚ) / 15 = 3 / 5 + 1 / 3 :=
  ⟨fun _ _ => rfl,
   wilsonHamiltonian_chamberMatrix_hermitian,
   wilsonHamiltonian_chamberMatrix_trace,
   chamber_trace_decomposes⟩

/-- For any `s > 0` with `s ^ 2 = 7`, the three chamber eigenvalues `3 / 5`, `(5 + s) / 30`,
and `(5 - s) / 30` of `wilsonHamiltonian` satisfy their characteristic equations and are
strictly positive. -/
theorem wilson_hamiltonian_spectrum_and_positivity
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    (H_charPoly wilsonHamiltonian.topEigenvalue = 0 ∧
     150 * ((5 + s) / 30) ^ 2 - 50 * ((5 + s) / 30) + 3 = 0 ∧
     150 * ((5 - s) / 30) ^ 2 - 50 * ((5 - s) / 30) + 3 = 0) ∧
    ((0 : ℝ) < wilsonHamiltonian.topEigenvalue ∧
     (0 : ℝ) < (5 + s) / 30 ∧
     (0 : ℝ) < (5 - s) / 30) :=
  ⟨wilsonHamiltonian_eigenvalues_match_chamber s hs,
   wilsonHamiltonian_eigenvalues_positive s hs hs_pos⟩

/-! ### 2. Explicit 6-Mode Feshbach Projection and Volterra Block-Diagonal Derivation -/

/-- Exhaustive chamber/bath dichotomy on `Fin 6` and image properties of `chamberIdx` and `bathIdx`. -/
theorem volterra_chamber_bath_dichotomy_and_embeddings :
    (∀ i : Fin 6, isChamber i ∨ isBath i) ∧
    (∀ i : Fin 3, isChamber (chamberIdx i)) ∧
    (∀ i : Fin 3, isBath (bathIdx i)) :=
  ⟨chamber_or_bath, chamberIdx_isChamber, bathIdx_isBath⟩

/-- Symmetry of the explicit 6×6 Wilson Hamiltonian `H_W` and exact rational values of its
structural parameters `α₁, α₂, α₃, β₁sq, β₂sq, μ_bath`. -/
theorem explicit_wilson_hamiltonian_symmetric_and_parameter_values :
    (∀ i j : Fin 6, H_W i j = H_W j i) ∧
    α₁ = 1 / 3 ∧ α₂ = 2 / 5 ∧ α₃ = 1 / 5 ∧
    β₁sq = 1 / 25 ∧ β₂sq = 1 / 50 ∧ μ_bath = 3 :=
  ⟨H_W_symmetric, α₁_val, α₂_val, α₃_val, β₁sq_val, β₂sq_val, μ_bath_val⟩

/-- Exact identification of the four 3×3 Feshbach blocks of `H_W`:
`H_PP = J₄`, `H_PQ = 0`, `H_QP = 0`, and `H_QQ = μ_bath · I₃`. -/
theorem explicit_wilson_hamiltonian_feshbach_blocks :
    (∀ i j : Fin 3, H_PP i j = J₄ i j) ∧
    (∀ i j : Fin 3, H_PQ i j = 0) ∧
    (∀ i j : Fin 3, H_QP i j = 0) ∧
    (∀ i j : Fin 3, H_QQ i j = if i = j then μ_bath else 0) :=
  ⟨H_PP_eq_J₄, H_PQ_zero, H_QP_zero, H_QQ_diag⟩

/-- For every spectral parameter `lam : ℝ` and all `i, j : Fin 3`, the Feshbach self-energy
`selfEnergy lam i j` vanishes and `H_eff lam i j = H_PP i j = J₄ i j = H_chamber_entry i j`. -/
theorem explicit_feshbach_self_energy_zero_and_effective_hamiltonian_eq_J4
    (lam : ℝ) (i j : Fin 3) :
    selfEnergy lam i j = 0 ∧
    H_eff lam i j = H_PP i j ∧
    H_eff lam i j = J₄ i j ∧
    H_eff lam i j = (H_chamber_entry i j : ℝ) :=
  ⟨selfEnergy_zero lam i j,
   H_eff_eq_H_PP lam i j,
   H_eff_eq_J₄ lam i j,
   H_eff_eq_H_chamber_entry lam i j⟩

/-- At the chamber spectral fixed point `lambda_star_real = 3 / 5`, `lambda_star_real ≠ μ_bath`,
the bath resolvent diagonal equals `-5 / 12`, and `H_eff lambda_star_real` matches `J₄` and
`H_chamber_entry` entry-by-entry. -/
theorem explicit_feshbach_at_lambda_star_and_bath_resolvent :
    lambda_star_real = 3 / 5 ∧
    lambda_star_real ≠ μ_bath ∧
    (∀ i : Fin 3, bathResolvent lambda_star_real i i = -5 / 12) ∧
    (∀ i j : Fin 3,
      H_eff lambda_star_real i j = J₄ i j ∧
      H_eff lambda_star_real i j = (H_chamber_entry i j : ℝ)) :=
  ⟨rfl,
   lambda_star_ne_mu_bath,
   bathResolvent_at_lambda_star_diag,
   fun i j => ⟨H_eff_at_lambda_star_eq_J₄ i j,
               H_eff_at_lambda_star_eq_H_chamber_entry i j⟩⟩

/-- Complete 9-entry table of the Feshbach effective Hamiltonian `H_eff lam` for any `lam : ℝ`. -/
theorem explicit_feshbach_nine_entries (lam : ℝ) :
    H_eff lam ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / 3 ∧
    H_eff lam ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 / 5 ∧
    H_eff lam ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 / 5 ∧
    H_eff lam ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 / 25 ∧
    H_eff lam ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 / 25 ∧
    H_eff lam ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 / 50 ∧
    H_eff lam ⟨2, by decide⟩ ⟨1, by decide⟩ = 1 / 50 ∧
    H_eff lam ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 ∧
    H_eff lam ⟨2, by decide⟩ ⟨0, by decide⟩ = 0 :=
  ⟨H_eff_00 lam, H_eff_11 lam, H_eff_22 lam,
   H_eff_01 lam, H_eff_10 lam, H_eff_12 lam,
   H_eff_21 lam, H_eff_02 lam, H_eff_20 lam⟩

/-- Exact factorization `750 * H_eff_charPoly x = (5 * x - 3) * (150 * x ^ 2 - 50 * x + 3)` and
roots `3 / 5`, `(5 + s) / 30`, `(5 - s) / 30` (for `s ^ 2 = 7`) of `H_eff_charPoly`. -/
theorem explicit_feshbach_charPoly_factorization_and_roots :
    (∀ x : ℝ, 750 * H_eff_charPoly x = (5 * x - 3) * (150 * x ^ 2 - 50 * x + 3)) ∧
    H_eff_charPoly (3 / 5) = 0 ∧
    (∀ s : ℝ, s ^ 2 = 7 →
      H_eff_charPoly ((5 + s) / 30) = 0 ∧
      H_eff_charPoly ((5 - s) / 30) = 0) :=
  ⟨H_eff_charPoly_factors,
   H_eff_charPoly_at_lambda_star,
   fun s hs => ⟨H_eff_charPoly_at_eig2 s hs, H_eff_charPoly_at_eig3 s hs⟩⟩

/-- The explicit 6×6 Wilson Hamiltonian `H_W` satisfies both `ChamberBathCommutes H_W` and the
three-part `WilsonBlockHypothesis H_W`. -/
theorem volterra_chamber_bath_commutes_and_block_hypothesis :
    ChamberBathCommutes H_W ∧ WilsonBlockHypothesis H_W :=
  ⟨H_W_chamberBath_commutes, H_W_satisfies_block_hypothesis⟩

/-- Derivation of the bath block of `H_W` from the color-dressed Volterra ratio
`bath_dressed_ratio (bathMode i) = 3 = N_c`. -/
theorem volterra_bath_block_derived_from_color_dressing (i j : Fin 3) :
    H_W (bathIdx i) (bathIdx i) = 3 ∧
    H_W (bathIdx i) (bathIdx i) = bath_dressed_ratio (bathMode i) ∧
    H_W (bathIdx i) (bathIdx j) = if i = j then (N_c : ℝ) else 0 :=
  ⟨bath_diag_eq_three i,
   bath_diag_eq_color_dressed i,
   bath_block_eq_Nc_identity i j⟩

/-- Derivation of the chamber diagonal entries `(1/3, 2/5, 1/5)` from `volterra_ratio 2` and
`volterra_ratio 3`, and off-diagonal entries `(1/25, 1/50)` from the Feshbach self-energy fixed point. -/
theorem volterra_chamber_entries_derived_from_volterra_ratios_and_selfenergy :
    H_W (chamberIdx ⟨0, by decide⟩) (chamberIdx ⟨0, by decide⟩) = volterra_ratio 2 ∧
    H_W (chamberIdx ⟨1, by decide⟩) (chamberIdx ⟨1, by decide⟩) = 2 * volterra_ratio 3 ∧
    H_W (chamberIdx ⟨2, by decide⟩) (chamberIdx ⟨2, by decide⟩) = volterra_ratio 3 ∧
    H_W (chamberIdx ⟨0, by decide⟩) (chamberIdx ⟨1, by decide⟩) = 1 / 25 ∧
    H_W (chamberIdx ⟨1, by decide⟩) (chamberIdx ⟨2, by decide⟩) = 1 / 50 :=
  ⟨chamber_diag_00_from_volterra,
   chamber_diag_11_from_volterra,
   chamber_diag_22_from_volterra,
   chamber_offdiag_01_from_selfenergy,
   chamber_offdiag_12_from_selfenergy⟩

/-- Complete Volterra block-diagonal decomposition for `H_W`:
`block_PP H_W = J₄`, `block_QQ H_W = N_c · I₃`, `block_PQ H_W = 0`, and `block_QP H_W = 0`. -/
theorem volterra_block_diagonal_structure_for_H_W :
    (∀ i j : Fin 3, block_PP H_W i j = J₄ i j) ∧
    (∀ i j : Fin 3, block_QQ H_W i j = if i = j then (N_c : ℝ) else 0) ∧
    (∀ i j : Fin 3, block_PQ H_W i j = 0) ∧
    (∀ i j : Fin 3, block_QP H_W i j = 0) :=
  H_W_volterra_block_diagonal

/-! ### 3. Physical Wilson Expectation, SO(10) Haar Trace Identity, and Partition Function Scaling -/

/-- Normalization, positivity, linearity, and monotonicity of `physicalWilsonExpectation`. -/
theorem physical_wilson_expectation_structural_properties (ρ β : ℝ) :
    physicalWilsonExpectation ρ β 1 = 1 ∧
    (∀ W : ℝ, 0 ≤ W → 0 ≤ physicalWilsonExpectation ρ β W) ∧
    (∀ W₁ W₂ c : ℝ,
      physicalWilsonExpectation ρ β (c * W₁ + W₂) =
        c * physicalWilsonExpectation ρ β W₁ +
        physicalWilsonExpectation ρ β W₂) ∧
    (∀ W₁ W₂ : ℝ, W₁ ≤ W₂ →
      physicalWilsonExpectation ρ β W₁ ≤ physicalWilsonExpectation ρ β W₂) :=
  ⟨physicalWilsonExpectation_one ρ β,
   physicalWilsonExpectation_nonneg_for_nonneg_observable ρ β,
   physicalWilsonExpectation_linear ρ β,
   physicalWilsonExpectation_monotone ρ β⟩

/-- Two-sided `[0, 1]` Haar bound, absolute-value bound, and bridge identity between
`physicalWilsonExpectation` and `WilsonExpectation`. -/
theorem physical_wilson_expectation_haar_bounds_and_bridge (ρ β W : ℝ) :
    (0 ≤ W → W ≤ 1 →
      0 ≤ physicalWilsonExpectation ρ β W ∧
      physicalWilsonExpectation ρ β W ≤ 1) ∧
    |physicalWilsonExpectation ρ β W| ≤ |W| ∧
    physicalWilsonExpectation ρ β W = WilsonExpectation ρ β W :=
  ⟨physicalWilsonExpectation_le_for_le_one ρ β W,
   physicalWilsonExpectation_abs_le ρ β W,
   physicalWilsonExpectation_bridge ρ β W⟩

/-- Closed-form identity `yangMillsMassGap = √7 / 15` and strict positivity `0 < yangMillsMassGap`. -/
theorem yang_mills_mass_gap_closed_form_and_positivity :
    yangMillsMassGap = Real.sqrt 7 / 15 ∧ 0 < yangMillsMassGap :=
  ⟨yangMillsMassGap_eq, yangMillsMassGap_pos⟩

/-- For any `SO10HaarTraceWitness W` and `0 < N`, the Haar trace integral vanishes
(`∫ x, W.reTrace x ∂W.μ_SO10 = 0`) and the per-plaquette mean action density limit equals
`haarActionDensityLimit_SO10 = 1`. -/
theorem haar_trace_identity_abstract_and_SO10
    (W : SO10HaarTraceWitness) (N : ℝ) (hN : 0 < N) :
    (∫ x, W.reTrace x ∂W.μ_SO10) = 0 ∧
    1 - (∫ x, W.reTrace x ∂W.μ_SO10) / N = haarActionDensityLimit_SO10 ∧
    haarActionDensityLimit_SO10 = 1 :=
  ⟨SO10_haar_trace_identity_proved W,
   haarActionDensityLimit_SO10_value_derived W N hN,
   haarActionDensityLimit_SO10_eq_one⟩

/-- Uniform squeeze bounds `exp(-(β * M.S_max)) ≤ PhysicalZ M ρ β ≤ 1`, strict positivity, and
continuum convergence `PhysicalZ M ρ β → exp(-(β * M.S_inf))` as `ρ → ∞`. -/
theorem physical_partition_function_bounds_and_convergence
    (M : MeanActionScaling) (β : ℝ) (hβ : 0 ≤ β) :
    (∀ ρ : ℝ, 0 ≤ ρ →
      Real.exp (-(β * M.S_max)) ≤ PhysicalZ M ρ β ∧
      PhysicalZ M ρ β ≤ 1 ∧
      0 < PhysicalZ M ρ β) ∧
    Tendsto (fun ρ : ℝ => PhysicalZ M ρ β) atTop
      (𝓝 (Real.exp (-(β * M.S_inf)))) :=
  ⟨fun ρ hρ => ⟨(PhysicalZ_uniform_bounds M β hβ ρ hρ).1,
                (PhysicalZ_uniform_bounds M β hβ ρ hρ).2,
                PhysicalZ_pos M ρ β⟩,
   PhysicalZ_tendsto M β⟩

/-- Closed SO(10) partition-function scaling backed by the Haar trace identity:
`Z_SO10 ρ β → exp(-β) ∈ (0, 1]` as `ρ → ∞` with `∫ x, W.reTrace x ∂W.μ_SO10 = 0`. -/
theorem so10_partition_function_scaling_closed_with_haar
    (W : SO10HaarTraceWitness) (N : ℝ) (hN : 0 < N) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Z_inf : ℝ, 0 < Z_inf ∧ Z_inf ≤ 1 ∧
      Z_inf = Real.exp (-β) ∧
      Tendsto (fun ρ : ℝ => Z_SO10 ρ β) atTop (𝓝 Z_inf) ∧
      (∫ x, W.reTrace x ∂W.μ_SO10) = 0 :=
  physical_partition_function_scaling_SO10_closed W N hN β hβ

/-! ### 4. Clock-Floor Iterated Hamiltonian Resolvent Regularity at Wilson-Feshbach Spectral Parameters -/

private theorem lambda_star_real_pos : 0 < lambda_star_real := by
  unfold lambda_star_real
  norm_num

private theorem mu_bath_pos : 0 < μ_bath := by
  rw [μ_bath_val]
  norm_num

/-- Evaluating `iteratedHamiltonianResolvent` at the closed-form mass-gap candidate
`yangMillsMassGap = √7 / 15 > 0` and the Feshbach spectral fixed point `lambda_star_real = 3 / 5 > 0`
places the resulting state in `hamiltonianSecondPowerDomain t` and all 10 operator, form, and clock
domains for every `f : Hilbert` and all `m, g, k, t, s ∈ ℝ`. -/
theorem clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_mem_ten_domains
    (t s : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f
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
    yangMillsMassGap lambda_star_real yangMillsMassGap_pos lambda_star_real_pos f

/-- Exact parameter commutativity of `iteratedHamiltonianResolvent` at
`(yangMillsMassGap, lambda_star_real)`. -/
theorem clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_comm
    (t : ℝ) (f : Hilbert) :
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f =
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      lambda_star_real yangMillsMassGap f :=
  hamiltonianResolvent_comm ε hε h hh hb m g k t
    yangMillsMassGap lambda_star_real
    yangMillsMassGap_pos lambda_star_real_pos f

/-- Exact first-power radial-residual decomposition on
`x := iteratedHamiltonianResolvent t yangMillsMassGap lambda_star_real f`:
`H t x = exp(2t) • K x + S t x = RH t lambda_star_real f - (yangMillsMassGap : ℂ) • x`. -/
theorem clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_radial_residual_decomposition
    (t : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain
      ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
      yangMillsMassGap_pos lambda_star_real_pos f
    H t ⟨x, hdom.1⟩ =
      (Real.exp (2 * t) : ℂ) • K ⟨x, hdom.2.1⟩ + S t ⟨x, hdom.2.2⟩ ∧
    H t ⟨x, hdom.1⟩ =
      RH t lambda_star_real f - (yangMillsMassGap : ℂ) • x :=
  iteratedHamiltonianResolvent_hamiltonian_eq_radial_add_residual
    ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
    yangMillsMassGap_pos lambda_star_real_pos f

/-- Exact second-power radial-residual identity for `iteratedHamiltonianResolvent` at
`(yangMillsMassGap, lambda_star_real)`. -/
theorem clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_second_power_identity
    (t : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f
    let y := RH t lambda_star_real f - (yangMillsMassGap : ℂ) • x
    let hdom :=
      KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination.iteratedHamiltonianResolvent_first_power_mem_radial_residual_domain
        ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
        yangMillsMassGap_pos lambda_star_real_pos f
    (Real.exp (2 * t) : ℂ) • K ⟨y, hdom.2.1⟩ + S t ⟨y, hdom.2.2⟩ =
      f - ((yangMillsMassGap + lambda_star_real : ℝ) : ℂ) • RH t lambda_star_real f +
        ((yangMillsMassGap ^ 2 : ℝ) : ℂ) • x :=
  iteratedHamiltonianResolvent_second_power_radial_residual_eq
    ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
    yangMillsMassGap_pos lambda_star_real_pos f

/-- Unconditional combined radial and residual norm-square bound on
`x := iteratedHamiltonianResolvent t yangMillsMassGap lambda_star_real f`. -/
theorem clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_component_norm_sq_bound
    (t : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f
    let hdom := iteratedHamiltonianResolvent_mem_radial_residual_domain
      ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
      yangMillsMassGap_pos lambda_star_real_pos f
    Real.exp (4 * t) * ‖K ⟨x, hdom.2.1⟩‖ ^ 2 + ‖S t ⟨x, hdom.2.2⟩‖ ^ 2 ≤
      (2 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (yangMillsMassGap⁻¹) ^ 2) *
        (lambda_star_real⁻¹) ^ 2 * ‖f‖ ^ 2 :=
  iteratedHamiltonianResolvent_component_norm_sq_le_source
    ε hε h hh hb m g k t yangMillsMassGap lambda_star_real
    yangMillsMassGap_pos lambda_star_real_pos f

/-- Evaluating `iteratedHamiltonianResolvent` at the color-dressed bath eigenvalue
`μ_bath = 3 > 0` and the SO(10) continuum partition limit `exp(-β) > 0` places the state in
`hamiltonianSecondPowerDomain t` and all 10 operator, form, and clock domains, with exact
parameter commutativity. -/
theorem clock_floor_iterated_resolvent_at_bath_eigenvalue_and_partition_limit_mem_ten_domains
    (t s β : ℝ) (f : Hilbert) :
    let x := iteratedHamiltonianResolvent ε hε h hh hb m g k t
      μ_bath (Real.exp (-β)) f
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
    iteratedHamiltonianResolvent ε hε h hh hb m g k t μ_bath (Real.exp (-β)) f =
      iteratedHamiltonianResolvent ε hε h hh hb m g k t (Real.exp (-β)) μ_bath f :=
  ⟨iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t s
     μ_bath (Real.exp (-β)) mu_bath_pos (Real.exp_pos (-β)) f,
   hamiltonianResolvent_comm ε hε h hh hb m g k t
     μ_bath (Real.exp (-β)) mu_bath_pos (Real.exp_pos (-β)) f⟩

/-- Grand synthesis bridging the causal-diamond Wilson action, explicit 6-mode Feshbach
projection `H_eff(λ*) = J₄`, Volterra block-diagonal derivation, SO(10) Haar trace identity,
and 10-domain clock-floor iterated Hamiltonian resolvent regularity at
`(yangMillsMassGap, lambda_star_real)`. -/
theorem wilson_feshbach_volterra_haar_clock_floor_synthesis
    (W : SO10HaarTraceWitness) (t s : ℝ) (f : Hilbert) :
    (∀ S_cpl : ℝ, 0 ≤ S_cpl → ∀ g_cfg : GaugeField,
      0 ≤ wilsonAction S_cpl g_cfg ∧ wilsonAction S_cpl g_cfg ≤ 2 * S_cpl) ∧
    (∀ i j : Fin 3,
      H_eff lambda_star_real i j = J₄ i j ∧
      block_PP H_W i j = J₄ i j ∧
      block_PQ H_W i j = 0 ∧
      block_QP H_W i j = 0) ∧
    (∫ x, W.reTrace x ∂W.μ_SO10) = 0 ∧
    0 < yangMillsMassGap ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f ∈
      hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    iteratedHamiltonianResolvent ε hε h hh hb m g k t
      yangMillsMassGap lambda_star_real f ∈ (Eavg s).domain :=
  ⟨fun S_cpl hS g_cfg => ⟨wilsonAction_nonneg S_cpl hS g_cfg,
                          wilsonAction_le_two_S S_cpl hS g_cfg⟩,
   fun i j => ⟨H_eff_at_lambda_star_eq_J₄ i j,
               H_W_volterra_block_diagonal.1 i j,
               H_W_volterra_block_diagonal.2.2.1 i j,
               H_W_volterra_block_diagonal.2.2.2 i j⟩,
   SO10_haar_trace_identity_proved W,
   yangMillsMassGap_pos,
   (clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_mem_ten_domains
     ε hε h hh hb m g k t s f).1,
   (clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_mem_ten_domains
     ε hε h hh hb m g k t s f).2.2.2.2.1⟩

#print axioms wilson_diamond_links_and_plaquette_structure
#print axioms wilson_plaquette_amplitude_bounds_and_id
#print axioms wilson_action_sample_values
#print axioms wilson_action_nonneg_upper_bound_and_monotone
#print axioms wilson_action_plaquette_sum_and_expectation_bridge
#print axioms wilson_hamiltonian_carrier_invariants
#print axioms wilson_hamiltonian_chamber_matrix_hermitian_and_trace
#print axioms wilson_hamiltonian_spectrum_and_positivity
#print axioms volterra_chamber_bath_dichotomy_and_embeddings
#print axioms explicit_wilson_hamiltonian_symmetric_and_parameter_values
#print axioms explicit_wilson_hamiltonian_feshbach_blocks
#print axioms explicit_feshbach_self_energy_zero_and_effective_hamiltonian_eq_J4
#print axioms explicit_feshbach_at_lambda_star_and_bath_resolvent
#print axioms explicit_feshbach_nine_entries
#print axioms explicit_feshbach_charPoly_factorization_and_roots
#print axioms volterra_chamber_bath_commutes_and_block_hypothesis
#print axioms volterra_bath_block_derived_from_color_dressing
#print axioms volterra_chamber_entries_derived_from_volterra_ratios_and_selfenergy
#print axioms volterra_block_diagonal_structure_for_H_W
#print axioms physical_wilson_expectation_structural_properties
#print axioms physical_wilson_expectation_haar_bounds_and_bridge
#print axioms yang_mills_mass_gap_closed_form_and_positivity
#print axioms haar_trace_identity_abstract_and_SO10
#print axioms physical_partition_function_bounds_and_convergence
#print axioms so10_partition_function_scaling_closed_with_haar
#print axioms clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_mem_ten_domains
#print axioms clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_comm
#print axioms clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_radial_residual_decomposition
#print axioms clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_second_power_identity
#print axioms clock_floor_iterated_resolvent_at_mass_gap_and_lambda_star_component_norm_sq_bound
#print axioms clock_floor_iterated_resolvent_at_bath_eigenvalue_and_partition_limit_mem_ten_domains
#print axioms wilson_feshbach_volterra_haar_clock_floor_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorWilsonActionFeshbachVolterraHaarBridge
