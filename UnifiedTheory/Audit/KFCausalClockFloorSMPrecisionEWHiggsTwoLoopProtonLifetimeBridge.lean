/- Standard Model Precision Electroweak Running, Two-Loop Higgs Feshbach Residue,
Dimension-6 Proton Lifetime, Muon g - 2 Pre-Registration, and Clock-Floor Higher-Power
Yosida Bridge:
1. Connects the Standard Model one-loop beta coefficients and precision electroweak
   running (`b₁ = 41/10`, `b₂ = -19/6`, `b₃ = -7`, `b₁ - b₂ = 109/15`,
   `sin2_at_unification`, `sin2_decreases_under_running`, `mW_sq_exp_in_window`,
   `mW_sq_close_to_experiment`, `couplings_equal_at_MP`, `splitting_ratio`,
   `precision_ew_summary`) to W-boson-mass-weighted Hilbert energies and 16-component
   nonautonomous unitary evolution and higher-power Yosida contractions.
2. Connects the two-virtual-line Feshbach amplitude and structural two-loop Higgs mass
   correction (`twoVirtualLineResidue`, `twoVirtualLineResidue_J4_value = 9/16`,
   `higgsMassCorrSq`, `oneloop_delta = -13/1000`, `corrected_mass_pos_at_published_delta`,
   `corrected_mass_lt_tree_at_published_delta`, `higgs_two_loop_master`) to
   two-loop-corrected Higgs Hilbert energies and `iteratedIdentityPower` contractions.
3. Connects the dimension-6 Planck-scale proton lifetime (`protonLifetime`,
   `lifetime_ratio`, `protonLifetime_pos`) and the pre-registered muon anomalous
   magnetic moment (`aMu_framework_pred_units = 116592000`,
   `g_minus_two_master_prediction`, `g_minus_two_short_verdict`) to 16-component and
   126-component clock-floor unitary evolution and higher-power Yosida convergence. -/
import UnifiedTheory.LayerA.PrecisionEW
import UnifiedTheory.LayerA.HiggsTwoLoop
import UnifiedTheory.LayerA.ProtonLifetime
import UnifiedTheory.LayerB.MuonG2Prediction
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMPrecisionEWHiggsTwoLoopProtonLifetimeBridge

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open Finset
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution (evolution_norm)
open KFCausalClockFloorSMElectroweakHiggsPotentialBridge (evolutionFamily)
open KFCausalClockFloorSMHilbertBridgeMasterSynthesis
  (singleGen_evolutionFamily_norm_sq_sum seesaw_evolutionFamily_norm_sq_sum)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower
   hamiltonian_iteratedIdentityPower_contraction_and_rate
   hamiltonian_iteratedIdentityPower_tendsto
   hamiltonian_iteratedIdentityPower_succ_mem_ten_domains)
open UnifiedTheory.LayerA.FeshbachJ4 (a₁ a₂ b₁_sq lambda_star C_int)
open UnifiedTheory.LayerA.PrecisionEW
  (b₁ b₂ b₃ b₁_minus_b₂ b₁_minus_b₂_pos su3_more_asymptotically_free
   invAlpha sin2_weinberg_running sin2_at_unification sin2_decreases_under_running
   mZ_sq mW_sq_exp mW_sq mW_sq_at_quarter mW_sq_at_fifth
   mW_sq_lower_bound mW_sq_upper_bound mW_sq_exp_in_window
   mW_sq_close_to_experiment mW_sq_close_to_experiment_upper
   invAlphaFS couplings_equal_at_MP splitting_12 splitting_23
   splitting_ratio precision_ew_summary)
open UnifiedTheory.LayerB.VirtualParticles (virtualLineAmplitude)
open UnifiedTheory.LayerA.HiggsTwoLoop
  (oneloop_delta oneloop_delta_eq oneloop_delta_in_regime
   twoVirtualLineResidue twoVirtualLineResidue_eq
   twoVirtualLineResidue_from_oneLine twoVirtualLineResidue_is_neg_deriv
   twoVirtualLineResidue_J4_value twoVirtualLineResidue_J4_real
   twoLine_gt_singleLine_J4 bath_insertion_ratio_J4
   higgsMassCorrSq higgsMassCorrSq_pos higgsMassCorrSq_decreases_when_neg
   corrected_mass_pos_at_published_delta corrected_mass_lt_tree_at_published_delta
   candidate_A_value candidate_B_value candidate_C_value
   higgs_two_loop_master)
open UnifiedTheory.LayerA.ProtonLifetime
  (protonLifetime lifetime_ratio protonLifetime_pos)
open UnifiedTheory.LayerB.MuonGMinusTwo
  (aMu_exp_units aMu_SM_units aMu_discrepancy_units)
open UnifiedTheory.LayerB.MuonG2Prediction
  (NWp Ncp NWsqp Ntp discp
   aMu_LO_units_pred aMu_2loop_units_pred aMu_3loop_units_pred
   aMu_4loop_units_pred aMu_5loop_units_pred aMu_QED_total_units_pred
   aMu_QED_total_value aMu_EW_total_units_pred aMu_HVP_LO_BMW_units_pred
   aMu_hadronic_total_units_pred aMu_hadronic_total_value
   aMu_framework_pred_units aMu_exp_minus_pred_units
   aMu_confirmation_window_units aMu_5sigma_threshold_units
   currently_in_confirmation_window dispersion_pull_below_5sigma
   EW_eq_disc_times_22 EW_NOT_disc_NWsq_Nt aMu_HVP_BMW_LO_dwarfs_EW
   two_loop_dominates_three_loop three_loop_dominates_four_loop
   four_loop_dominates_five_loop g_minus_two_master_prediction
   g_minus_two_short_verdict)
open UnifiedTheory.LayerC.SMHilbertInstantiation (singleGenDim)
open UnifiedTheory.LayerC.SMSeeSawSubspace (seesawDim)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-! ### 1. Precision Electroweak Running, Weinberg Angle, and W-Boson Mass Evolution -/

/-- Exact Standard Model one-loop beta coefficients (`b₁ = 41/10`, `b₂ = -19/6`, `b₃ = -7`)
and their running hierarchy (`b₁ - b₂ = 109/15 > 0`, `b₃ < b₂`). -/
theorem sm_one_loop_beta_coefficients_and_running :
    b₁ = 41 / 10 ∧
    b₂ = -(19 / 6) ∧
    b₃ = -7 ∧
    b₁ - b₂ = 109 / 15 ∧
    b₁ - b₂ > 0 ∧
    b₃ < b₂ :=
  ⟨rfl, rfl, rfl, b₁_minus_b₂, b₁_minus_b₂_pos, su3_more_asymptotically_free⟩

/-- Weinberg angle unification (`sin²θ_W = 3/8` at `I₁ = I₂`) and downward RG running
(`sin²θ_W(M_Z) < 3/8` for `A > 0, L > 0`). -/
theorem weinberg_angle_unification_and_running_decrease :
    (∀ I : ℚ, I ≠ 0 → sin2_weinberg_running I I = 3 / 8) ∧
    (∀ A L : ℚ, 0 < A → 0 < L →
      sin2_weinberg_running (invAlpha A b₁ L) (invAlpha A b₂ L) < 3 / 8) :=
  ⟨sin2_at_unification, sin2_decreases_under_running⟩

/-- Custodial Weinberg angle complement at unification: `1 - sin²θ_W = 5/8` and
`sin²θ_W + (1 - sin²θ_W) = 1`. -/
theorem weinberg_angle_complement_at_unification (I : ℚ) (hI : I ≠ 0) :
    1 - sin2_weinberg_running I I = 5 / 8 ∧
    sin2_weinberg_running I I + (1 - sin2_weinberg_running I I) = 1 := by
  rw [sin2_at_unification I hI]
  constructor <;> norm_num

/-- Tree-level W-boson squared mass window (`[3/4 · m_Z², 4/5 · m_Z²]`) and precision
agreement at `sin²θ_W = 231/1000`. -/
theorem w_boson_mass_window_and_experiment_match :
    mW_sq (1 / 4) = 3 / 4 * mZ_sq ∧
    mW_sq (1 / 5) = 4 / 5 * mZ_sq ∧
    (3 / 4 * mZ_sq < mW_sq_exp ∧ mW_sq_exp < 4 / 5 * mZ_sq) ∧
    mW_sq (231 / 1000) > 97 / 100 * mW_sq_exp ∧
    mW_sq (231 / 1000) < 101 / 100 * mW_sq_exp :=
  ⟨mW_sq_at_quarter,
   mW_sq_at_fifth,
   mW_sq_exp_in_window,
   mW_sq_close_to_experiment,
   mW_sq_close_to_experiment_upper⟩

/-- Gauge coupling unification at `M_P` (`T_rg = 0`) and scale-independent splitting ratio
`Δ₁₂ / Δ₂₃ = 218 / 115`. -/
theorem gauge_coupling_convergence_and_splitting_ratio :
    (∀ I₀ : ℚ, invAlphaFS I₀ b₁ 0 = invAlphaFS I₀ b₂ 0 ∧
               invAlphaFS I₀ b₂ 0 = invAlphaFS I₀ b₃ 0) ∧
    (∀ I₀ T_rg : ℚ, invAlphaFS I₀ b₁ T_rg - invAlphaFS I₀ b₂ T_rg = (109 / 15) * T_rg) ∧
    (∀ I₀ T_rg : ℚ, invAlphaFS I₀ b₂ T_rg - invAlphaFS I₀ b₃ T_rg = (23 / 6) * T_rg) ∧
    ((109 : ℚ) / 15 / (23 / 6) = 218 / 115) :=
  ⟨couplings_equal_at_MP, splitting_12, splitting_23, splitting_ratio⟩

/-- W-boson squared-mass weighted Hilbert energy `(mW_sq s2w : ℝ) * ‖x‖ ^ 2`. -/
def ewMassWeightedHilbertEnergy (s2w : ℚ) (x : Hilbert) : ℝ :=
  (mW_sq s2w : ℝ) * ‖x‖ ^ 2

/-- Window bounds on `ewMassWeightedHilbertEnergy s2w x` for `s2w ∈ [1/5, 1/4]`. -/
theorem ewMassWeightedHilbertEnergy_window_bounds
    (s2w : ℚ) (hlo : 1 / 5 ≤ s2w) (hhi : s2w ≤ 1 / 4) (x : Hilbert) :
    ((3 / 4 * mZ_sq : ℚ) : ℝ) * ‖x‖ ^ 2 ≤ ewMassWeightedHilbertEnergy s2w x ∧
    ewMassWeightedHilbertEnergy s2w x ≤ ((4 / 5 * mZ_sq : ℚ) : ℝ) * ‖x‖ ^ 2 := by
  unfold ewMassWeightedHilbertEnergy
  have h1 : ((3 / 4 * mZ_sq : ℚ) : ℝ) ≤ (mW_sq s2w : ℝ) := by
    exact_mod_cast mW_sq_lower_bound s2w hlo hhi
  have h2 : (mW_sq s2w : ℝ) ≤ ((4 / 5 * mZ_sq : ℚ) : ℝ) := by
    exact_mod_cast mW_sq_upper_bound s2w hlo hhi
  exact ⟨mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖x‖)⟩

/-- Exact conservation of `ewMassWeightedHilbertEnergy` under `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_ewMassWeightedHilbertEnergy
    (s t : ℝ) (s2w : ℚ) (x : Hilbert) :
    ewMassWeightedHilbertEnergy s2w (evolutionFamily ε hε h hh hb m g k s t x) =
      ewMassWeightedHilbertEnergy s2w x := by
  unfold ewMassWeightedHilbertEnergy
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Exact conservation of the 16-component single-generation `ewMassWeightedHilbertEnergy`
sum under `evolutionFamily s t`. -/
theorem singleGen_ewMassWeightedHilbertEnergy_sum_conservation
    (s t : ℝ) (s2w : ℚ) (ψ : Fin singleGenDim → Hilbert) :
    ∑ i : Fin singleGenDim,
        ewMassWeightedHilbertEnergy s2w (evolutionFamily ε hε h hh hb m g k s t (ψ i)) =
      (mW_sq s2w : ℝ) * ∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2 := by
  unfold ewMassWeightedHilbertEnergy
  rw [← Finset.mul_sum, singleGen_evolutionFamily_norm_sq_sum]

/-- Contraction of `ewMassWeightedHilbertEnergy` across the 16-component single-generation
multiplet under the `r`-th order Hamiltonian Yosida approximant `iteratedIdentityPower (RH t a) a r`. -/
theorem singleGen_iteratedIdentityPower_ewMassWeightedHilbertEnergy_contraction
    (t a : ℝ) (ha : 0 < a) (r : ℕ) (s2w : ℚ) (hmW : 0 ≤ mW_sq s2w)
    (ψ : Fin singleGenDim → Hilbert) (xH : (H t).domain) :
    ∑ i : Fin singleGenDim,
        ewMassWeightedHilbertEnergy s2w (iteratedIdentityPower (RH t a) a r (ψ i)) ≤
      ∑ i : Fin singleGenDim, ewMassWeightedHilbertEnergy s2w (ψ i) := by
  apply Finset.sum_le_sum
  intro i _
  unfold ewMassWeightedHilbertEnergy
  have hnorm : ‖iteratedIdentityPower (RH t a) a r (ψ i)‖ ≤ ‖ψ i‖ :=
    (hamiltonian_iteratedIdentityPower_contraction_and_rate
      ε hε h hh hb m g k t a ha r (ψ i) xH).2.1
  have hsq : ‖iteratedIdentityPower (RH t a) a r (ψ i)‖ ^ 2 ≤ ‖ψ i‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hmW_real : (0 : ℝ) ≤ (mW_sq s2w : ℝ) := by exact_mod_cast hmW
  exact mul_le_mul_of_nonneg_left hsq hmW_real

/-! ### 2. Two-Loop Higgs Feshbach Residue, Corrected Mass Squared, and Clock-Floor Evolution -/

/-- Closed-form algebraic identities for the two-virtual-line Feshbach residue
`twoVirtualLineResidue b a_Q lam = b ^ 2 / (lam - a_Q) ^ 2`. -/
theorem two_virtual_line_residue_identities :
    (∀ b a_Q lam : ℝ, lam - a_Q ≠ 0 →
      twoVirtualLineResidue b a_Q lam = b ^ 2 / (lam - a_Q) ^ 2) ∧
    (∀ b a_Q lam : ℝ, lam - a_Q ≠ 0 →
      twoVirtualLineResidue b a_Q lam * (lam - a_Q) = virtualLineAmplitude b a_Q lam) ∧
    (∀ b a_Q lam : ℝ, lam - a_Q ≠ 0 →
      twoVirtualLineResidue b a_Q lam * (lam - a_Q) ^ 2 = b ^ 2) :=
  ⟨twoVirtualLineResidue_eq,
   twoVirtualLineResidue_from_oneLine,
   twoVirtualLineResidue_is_neg_deriv⟩

/-- Exact evaluation of the two-virtual-line residue at the `J₄` chamber data
(`b₁² / (λ* - a₁)² = 9 / 16 > C_int = 3 / 20`, `a₁ / (λ* - a₁) = 5 / 4`). -/
theorem two_virtual_line_residue_J4_package :
    b₁_sq / (lambda_star - a₁) ^ 2 = (9 : ℚ) / 16 ∧
    twoVirtualLineResidue (Real.sqrt (1 / 25)) (1 / 3) (3 / 5) = 9 / 16 ∧
    C_int < b₁_sq / (lambda_star - a₁) ^ 2 ∧
    a₁ / (lambda_star - a₁) = (5 : ℚ) / 4 :=
  ⟨twoVirtualLineResidue_J4_value,
   twoVirtualLineResidue_J4_real,
   twoLine_gt_singleLine_J4,
   bath_insertion_ratio_J4⟩

/-- Structural properties of the two-loop-corrected Higgs mass squared `higgsMassCorrSq`
at `oneloop_delta = -13 / 1000`. -/
theorem higgs_two_loop_corrected_mass_package :
    oneloop_delta = -13 / 1000 ∧
    (-1 < oneloop_delta ∧ oneloop_delta < 0) ∧
    (∀ v : ℝ, v ≠ 0 → 0 < higgsMassCorrSq oneloop_delta v) ∧
    (∀ v : ℝ, v ≠ 0 → higgsMassCorrSq oneloop_delta v < higgsMassCorrSq 0 v) :=
  ⟨oneloop_delta_eq,
   oneloop_delta_in_regime,
   corrected_mass_pos_at_published_delta,
   corrected_mass_lt_tree_at_published_delta⟩

/-- Two-loop-corrected Higgs Hilbert energy `higgsMassCorrSq δ v * ‖x‖ ^ 2`. -/
def twoLoopHiggsDressedHilbertEnergy (δ v : ℝ) (x : Hilbert) : ℝ :=
  higgsMassCorrSq δ v * ‖x‖ ^ 2

/-- Strict positivity of `twoLoopHiggsDressedHilbertEnergy δ v x` for `-1 < δ`, `v ≠ 0`,
and `x ≠ 0`. -/
theorem twoLoopHiggsDressedHilbertEnergy_pos (δ v : ℝ) (hδ : -1 < δ) (hv : v ≠ 0)
    {x : Hilbert} (hx : x ≠ 0) :
    0 < twoLoopHiggsDressedHilbertEnergy δ v x :=
  mul_pos (higgsMassCorrSq_pos δ v hδ hv) (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- Strict reduction of `twoLoopHiggsDressedHilbertEnergy δ v x` relative to tree level
(`δ = 0`) whenever `-1 < δ < 0`, `v ≠ 0`, and `x ≠ 0`. -/
theorem twoLoopHiggsDressedHilbertEnergy_decreases_when_neg
    (δ v : ℝ) (hδ_neg : δ < 0) (hδ_lb : -1 < δ) (hv : v ≠ 0)
    {x : Hilbert} (hx : x ≠ 0) :
    twoLoopHiggsDressedHilbertEnergy δ v x < twoLoopHiggsDressedHilbertEnergy 0 v x :=
  mul_lt_mul_of_pos_right
    (higgsMassCorrSq_decreases_when_neg δ v hδ_neg hδ_lb hv)
    (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- At `oneloop_delta = -13 / 1000`, `twoLoopHiggsDressedHilbertEnergy` is strictly
smaller than the tree-level Higgs Hilbert energy for every `v ≠ 0` and `x ≠ 0`. -/
theorem twoLoopHiggsDressedHilbertEnergy_published_delta_lt_tree
    (v : ℝ) (hv : v ≠ 0) {x : Hilbert} (hx : x ≠ 0) :
    twoLoopHiggsDressedHilbertEnergy oneloop_delta v x <
      twoLoopHiggsDressedHilbertEnergy 0 v x :=
  mul_lt_mul_of_pos_right
    (corrected_mass_lt_tree_at_published_delta v hv)
    (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- Exact conservation of `twoLoopHiggsDressedHilbertEnergy δ v` along `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_twoLoopHiggsDressedHilbertEnergy
    (s t δ v : ℝ) (x : Hilbert) :
    twoLoopHiggsDressedHilbertEnergy δ v (evolutionFamily ε hε h hh hb m g k s t x) =
      twoLoopHiggsDressedHilbertEnergy δ v x := by
  unfold twoLoopHiggsDressedHilbertEnergy
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Contraction of `twoLoopHiggsDressedHilbertEnergy δ v` under the `r`-th order Hamiltonian
Yosida approximant `iteratedIdentityPower (RH t a) a r` whenever `-1 < δ` and `v ≠ 0`. -/
theorem iteratedIdentityPower_twoLoopHiggsDressedHilbertEnergy_contraction
    (t a δ v : ℝ) (ha : 0 < a) (hδ : -1 < δ) (hv : v ≠ 0) (r : ℕ)
    (x : Hilbert) (xH : (H t).domain) :
    twoLoopHiggsDressedHilbertEnergy δ v (iteratedIdentityPower (RH t a) a r x) ≤
      twoLoopHiggsDressedHilbertEnergy δ v x := by
  unfold twoLoopHiggsDressedHilbertEnergy
  have hnorm : ‖iteratedIdentityPower (RH t a) a r x‖ ≤ ‖x‖ :=
    (hamiltonian_iteratedIdentityPower_contraction_and_rate
      ε hε h hh hb m g k t a ha r x xH).2.1
  have hsq : ‖iteratedIdentityPower (RH t a) a r x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact mul_le_mul_of_nonneg_left hsq (higgsMassCorrSq_pos δ v hδ hv).le

/-- Honest numerical values of the three natural `J₄` two-loop coupling candidates
(`1/40`, `1/27`, `1/9`), each exceeding `13/1000`. -/
theorem higgs_two_loop_honest_candidate_values :
    C_int ^ 2 * a₂ / lambda_star ^ 2 = (1 : ℚ) / 40 ∧
    b₁_sq * a₁ / lambda_star ^ 2 = (1 : ℚ) / 27 ∧
    b₁_sq / lambda_star ^ 2 = (1 : ℚ) / 9 :=
  ⟨candidate_A_value, candidate_B_value, candidate_C_value⟩

/-! ### 3. Dimension-6 Proton Lifetime, Muon `g - 2` Pre-Registration, and Yosida Synthesis -/

/-- Dimension-6 proton lifetime quartic scaling law and positivity. -/
theorem protonLifetime_quartic_scaling_and_positivity :
    (∀ MX alpha mp : ℝ, 0 < MX → 0 < alpha → 0 < mp → 0 < protonLifetime MX alpha mp) ∧
    (∀ M1 M2 alpha1 alpha2 mp : ℝ,
      M2 ≠ 0 → alpha1 ≠ 0 → alpha2 ≠ 0 → mp ≠ 0 →
      protonLifetime M1 alpha1 mp / protonLifetime M2 alpha2 mp =
        (M1 / M2) ^ 4 * (alpha2 / alpha1) ^ 2) :=
  ⟨protonLifetime_pos, lifetime_ratio⟩

/-- Monotone increasing dependence of `protonLifetime MX alpha mp` on the heavy unification
scale `MX` (`0 < M1 ≤ M2`). -/
theorem protonLifetime_monotone_increasing_in_MX
    (M1 M2 alpha mp : ℝ) (hM1 : 0 < M1) (hle : M1 ≤ M2) (ha : 0 < alpha) (hmp : 0 < mp) :
    protonLifetime M1 alpha mp ≤ protonLifetime M2 alpha mp := by
  unfold protonLifetime
  have hpow : M1 ^ 4 ≤ M2 ^ 4 := pow_le_pow_left₀ hM1.le hle 4
  have hden : 0 ≤ alpha ^ 2 * mp ^ 5 := by positivity
  exact div_le_div_of_nonneg_right hpow hden

/-- Strict increasing dependence of `protonLifetime MX alpha mp` on the heavy unification
scale `MX` (`0 < M1 < M2`). -/
theorem protonLifetime_strict_increasing_in_MX
    (M1 M2 alpha mp : ℝ) (hM1 : 0 < M1) (hlt : M1 < M2) (ha : 0 < alpha) (hmp : 0 < mp) :
    protonLifetime M1 alpha mp < protonLifetime M2 alpha mp := by
  unfold protonLifetime
  have hpow : M1 ^ 4 < M2 ^ 4 := pow_lt_pow_left₀ hlt hM1.le (by norm_num)
  have hden : 0 < alpha ^ 2 * mp ^ 5 := by positivity
  exact div_lt_div_of_pos_right hpow hden

/-- Proton-lifetime-weighted Hilbert norm-square `protonLifetime MX alpha mp * ‖x‖ ^ 2`. -/
def protonLifetimeWeightedHilbertNormSq (MX alpha mp : ℝ) (x : Hilbert) : ℝ :=
  protonLifetime MX alpha mp * ‖x‖ ^ 2

/-- Strict positivity of `protonLifetimeWeightedHilbertNormSq` for positive scales and `x ≠ 0`. -/
theorem protonLifetimeWeightedHilbertNormSq_pos
    (MX alpha mp : ℝ) (hMX : 0 < MX) (ha : 0 < alpha) (hmp : 0 < mp)
    {x : Hilbert} (hx : x ≠ 0) :
    0 < protonLifetimeWeightedHilbertNormSq MX alpha mp x :=
  mul_pos (protonLifetime_pos MX alpha mp hMX ha hmp)
    (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- Exact conservation of `protonLifetimeWeightedHilbertNormSq` under `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_protonLifetimeWeightedHilbertNormSq
    (s t MX alpha mp : ℝ) (x : Hilbert) :
    protonLifetimeWeightedHilbertNormSq MX alpha mp
        (evolutionFamily ε hε h hh hb m g k s t x) =
      protonLifetimeWeightedHilbertNormSq MX alpha mp x := by
  unfold protonLifetimeWeightedHilbertNormSq
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Quartic scale-ratio invariance of `protonLifetimeWeightedHilbertNormSq` along
`evolutionFamily s t` for any nonzero state `x ≠ 0`. -/
theorem evolutionFamily_protonLifetime_ratio_invariant
    (s t M1 M2 alpha1 alpha2 mp : ℝ)
    (hM2 : M2 ≠ 0) (ha1 : alpha1 ≠ 0) (ha2 : alpha2 ≠ 0) (hmp : mp ≠ 0)
    {x : Hilbert} (hx : x ≠ 0) :
    protonLifetimeWeightedHilbertNormSq M1 alpha1 mp
        (evolutionFamily ε hε h hh hb m g k s t x) /
      protonLifetimeWeightedHilbertNormSq M2 alpha2 mp
        (evolutionFamily ε hε h hh hb m g k s t x) =
      (M1 / M2) ^ 4 * (alpha2 / alpha1) ^ 2 := by
  rw [evolutionFamily_preserves_protonLifetimeWeightedHilbertNormSq,
    evolutionFamily_preserves_protonLifetimeWeightedHilbertNormSq]
  unfold protonLifetimeWeightedHilbertNormSq
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [mul_div_mul_right _ _ hx2]
  exact lifetime_ratio M1 M2 alpha1 alpha2 mp hM2 ha1 ha2 hmp

/-- Exact conservation of the 126-component see-saw `protonLifetimeWeightedHilbertNormSq`
sum under `evolutionFamily s t`. -/
theorem seesaw_tuple_protonLifetimeWeightedHilbertNormSq_sum_conservation
    (s t MX alpha mp : ℝ) (Φ : Fin seesawDim → Hilbert) :
    ∑ i : Fin seesawDim,
        protonLifetimeWeightedHilbertNormSq MX alpha mp
          (evolutionFamily ε hε h hh hb m g k s t (Φ i)) =
      protonLifetime MX alpha mp * ∑ i : Fin seesawDim, ‖Φ i‖ ^ 2 := by
  unfold protonLifetimeWeightedHilbertNormSq
  rw [← Finset.mul_sum, seesaw_evolutionFamily_norm_sq_sum]

/-- Pre-registered muon `g - 2` prediction package: `aMu_framework_pred_units = 116592000`,
QED 5-loop and hadronic totals, `exp - pred = 61 < 100` confirmation window, and
dispersion pull `< 295` (`5σ` threshold). -/
theorem muon_g2_preregistered_prediction_package :
    aMu_framework_pred_units = 116592000 ∧
    aMu_QED_total_units_pred = 116584844 ∧
    aMu_hadronic_total_units_pred = 70745 ∧
    aMu_exp_units - aMu_framework_pred_units = 61 ∧
    aMu_exp_minus_pred_units < aMu_confirmation_window_units ∧
    aMu_discrepancy_units < aMu_5sigma_threshold_units :=
  ⟨rfl,
   aMu_QED_total_value,
   aMu_hadronic_total_value,
   g_minus_two_short_verdict.2.1,
   currently_in_confirmation_window,
   dispersion_pull_below_5sigma⟩

/-- Muon `g - 2` multi-loop QED convergence hierarchy and honest EW atomic decomposition test. -/
theorem muon_g2_loop_hierarchy_and_ew_atomic_test :
    aMu_2loop_units_pred > 10 * aMu_3loop_units_pred ∧
    aMu_3loop_units_pred > 70 * aMu_4loop_units_pred ∧
    aMu_4loop_units_pred > 70 * aMu_5loop_units_pred ∧
    aMu_EW_total_units_pred = discp * 22 ∧
    aMu_EW_total_units_pred ≠ discp * NWsqp * Ntp ∧
    aMu_HVP_LO_BMW_units_pred > 400 * aMu_EW_total_units_pred :=
  ⟨two_loop_dominates_three_loop,
   three_loop_dominates_four_loop,
   four_loop_dominates_five_loop,
   EW_eq_disc_times_22,
   EW_NOT_disc_NWsq_Nt,
   aMu_HVP_BMW_LO_dwarfs_EW⟩

/-- Exact conservation of the muon-`g - 2`-weighted 16-component single-generation spinor
norm-square sum under `evolutionFamily s t`. -/
theorem muon_g2_weighted_singleGen_evolution_conservation
    (s t : ℝ) (ψ : Fin singleGenDim → Hilbert) :
    ∑ i : Fin singleGenDim,
        (aMu_framework_pred_units : ℝ) *
          ‖evolutionFamily ε hε h hh hb m g k s t (ψ i)‖ ^ 2 =
      (116592000 : ℝ) * ∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2 := by
  rw [← Finset.mul_sum, singleGen_evolutionFamily_norm_sq_sum]
  rfl

/-- Uniform norm-square sum contraction across both the 16-component single-generation
multiplet and the 126-component see-saw multiplet under `iteratedIdentityPower (RH t a) a r`. -/
theorem singleGen_and_seesaw_iteratedIdentityPower_contraction
    (t a : ℝ) (ha : 0 < a) (r : ℕ)
    (ψ : Fin singleGenDim → Hilbert) (Φ : Fin seesawDim → Hilbert) (xH : (H t).domain) :
    ∑ i : Fin singleGenDim, ‖iteratedIdentityPower (RH t a) a r (ψ i)‖ ^ 2 ≤
      ∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2 ∧
    ∑ i : Fin seesawDim, ‖iteratedIdentityPower (RH t a) a r (Φ i)‖ ^ 2 ≤
      ∑ i : Fin seesawDim, ‖Φ i‖ ^ 2 := by
  constructor
  · apply Finset.sum_le_sum
    intro i _
    have hnorm : ‖iteratedIdentityPower (RH t a) a r (ψ i)‖ ≤ ‖ψ i‖ :=
      (hamiltonian_iteratedIdentityPower_contraction_and_rate
        ε hε h hh hb m g k t a ha r (ψ i) xH).2.1
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  · apply Finset.sum_le_sum
    intro i _
    have hnorm : ‖iteratedIdentityPower (RH t a) a r (Φ i)‖ ≤ ‖Φ i‖ :=
      (hamiltonian_iteratedIdentityPower_contraction_and_rate
        ε hε h hh hb m g k t a ha r (Φ i) xH).2.1
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Contraction of total `protonLifetimeWeightedHilbertNormSq` across a 126-component
see-saw multiplet under `iteratedIdentityPower (RH t a) a r`. -/
theorem seesaw_iteratedIdentityPower_protonLifetimeWeightedHilbertNormSq_contraction
    (t a MX alpha mp : ℝ) (ha : 0 < a) (hMX : 0 < MX) (halpha : 0 < alpha) (hmp : 0 < mp)
    (r : ℕ) (Φ : Fin seesawDim → Hilbert) (xH : (H t).domain) :
    ∑ i : Fin seesawDim,
        protonLifetimeWeightedHilbertNormSq MX alpha mp
          (iteratedIdentityPower (RH t a) a r (Φ i)) ≤
      ∑ i : Fin seesawDim,
        protonLifetimeWeightedHilbertNormSq MX alpha mp (Φ i) := by
  unfold protonLifetimeWeightedHilbertNormSq
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hpos : 0 ≤ protonLifetime MX alpha mp :=
    le_of_lt (protonLifetime_pos MX alpha mp hMX halpha hmp)
  apply mul_le_mul_of_nonneg_left _ hpos
  apply Finset.sum_le_sum
  intro i _
  have hnorm : ‖iteratedIdentityPower (RH t a) a r (Φ i)‖ ≤ ‖Φ i‖ :=
    (hamiltonian_iteratedIdentityPower_contraction_and_rate
      ε hε h hh hb m g k t a ha r (Φ i) xH).2.1
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Grand Master Bridge for Standard Model Precision Electroweak Running, Two-Loop Higgs
Feshbach Residue, Dimension-6 Proton Lifetime, Muon `g - 2` Pre-Registration, and
Clock-Floor Higher-Power Yosida Contraction and Convergence. -/
theorem sm_precision_ew_higgs_two_loop_proton_lifetime_clock_floor_master_bridge
    (s t a MX alpha mp : ℝ) (ha : 0 < a) (hMX : 0 < MX) (halpha : 0 < alpha) (hmp : 0 < mp)
    (r : ℕ) (ψ : Fin singleGenDim → Hilbert) (Φ : Fin seesawDim → Hilbert)
    (x : Hilbert) (xH : (H t).domain) :
    (b₁ - b₂ = 109 / 15 ∧
     (3 / 4 * mZ_sq < mW_sq_exp ∧ mW_sq_exp < 4 / 5 * mZ_sq) ∧
     mW_sq (231 / 1000) > 97 / 100 * mW_sq_exp) ∧
    (b₁_sq / (lambda_star - a₁) ^ 2 = (9 : ℚ) / 16 ∧
     oneloop_delta = -13 / 1000 ∧
     (∀ v : ℝ, v ≠ 0 → higgsMassCorrSq oneloop_delta v < higgsMassCorrSq 0 v)) ∧
    (0 < protonLifetime MX alpha mp ∧
     aMu_framework_pred_units = 116592000 ∧
     aMu_exp_units - aMu_framework_pred_units = 61 ∧
     aMu_discrepancy_units < 295) ∧
    (∑ i : Fin singleGenDim, ‖evolutionFamily ε hε h hh hb m g k s t (ψ i)‖ ^ 2 =
       ∑ i : Fin singleGenDim, ‖ψ i‖ ^ 2 ∧
     ∑ i : Fin seesawDim,
       protonLifetimeWeightedHilbertNormSq MX alpha mp
         (evolutionFamily ε hε h hh hb m g k s t (Φ i)) =
       protonLifetime MX alpha mp * ∑ i : Fin seesawDim, ‖Φ i‖ ^ 2) ∧
    (iteratedIdentityPower (RH t a) a (r + 1) x ∈
       hamiltonianPowerDomain ε hε h hh hb m g k t (r + 1) ∧
     ‖iteratedIdentityPower (RH t a) a (r + 1) x‖ ≤ ‖x‖ ∧
     Tendsto
       (fun n : ℕ => iteratedIdentityPower (RH t ((n : ℝ) + 1)) ((n : ℝ) + 1) r (xH : Hilbert))
       atTop (𝓝 (xH : Hilbert))) := by
  have hY := hamiltonian_iteratedIdentityPower_succ_mem_ten_domains
    ε hε h hh hb m g k t s a ha r x
  exact ⟨⟨b₁_minus_b₂, mW_sq_exp_in_window, mW_sq_close_to_experiment⟩,
    ⟨twoVirtualLineResidue_J4_value, oneloop_delta_eq, corrected_mass_lt_tree_at_published_delta⟩,
    ⟨protonLifetime_pos MX alpha mp hMX halpha hmp,
     rfl, g_minus_two_short_verdict.2.1, g_minus_two_short_verdict.2.2.2.1⟩,
    ⟨singleGen_evolutionFamily_norm_sq_sum ε hε h hh hb m g k s t ψ,
     seesaw_tuple_protonLifetimeWeightedHilbertNormSq_sum_conservation
       ε hε h hh hb m g k s t MX alpha mp Φ⟩,
    ⟨hY.1, hY.2.2, (hamiltonian_iteratedIdentityPower_tendsto ε hε h hh hb m g k t r xH).2⟩⟩

#print axioms sm_one_loop_beta_coefficients_and_running
#print axioms weinberg_angle_unification_and_running_decrease
#print axioms weinberg_angle_complement_at_unification
#print axioms w_boson_mass_window_and_experiment_match
#print axioms gauge_coupling_convergence_and_splitting_ratio
#print axioms ewMassWeightedHilbertEnergy_window_bounds
#print axioms evolutionFamily_preserves_ewMassWeightedHilbertEnergy
#print axioms singleGen_ewMassWeightedHilbertEnergy_sum_conservation
#print axioms singleGen_iteratedIdentityPower_ewMassWeightedHilbertEnergy_contraction
#print axioms two_virtual_line_residue_identities
#print axioms two_virtual_line_residue_J4_package
#print axioms higgs_two_loop_corrected_mass_package
#print axioms twoLoopHiggsDressedHilbertEnergy_pos
#print axioms twoLoopHiggsDressedHilbertEnergy_decreases_when_neg
#print axioms twoLoopHiggsDressedHilbertEnergy_published_delta_lt_tree
#print axioms evolutionFamily_preserves_twoLoopHiggsDressedHilbertEnergy
#print axioms iteratedIdentityPower_twoLoopHiggsDressedHilbertEnergy_contraction
#print axioms higgs_two_loop_honest_candidate_values
#print axioms protonLifetime_quartic_scaling_and_positivity
#print axioms protonLifetime_monotone_increasing_in_MX
#print axioms protonLifetime_strict_increasing_in_MX
#print axioms protonLifetimeWeightedHilbertNormSq_pos
#print axioms evolutionFamily_preserves_protonLifetimeWeightedHilbertNormSq
#print axioms evolutionFamily_protonLifetime_ratio_invariant
#print axioms seesaw_tuple_protonLifetimeWeightedHilbertNormSq_sum_conservation
#print axioms muon_g2_preregistered_prediction_package
#print axioms muon_g2_loop_hierarchy_and_ew_atomic_test
#print axioms muon_g2_weighted_singleGen_evolution_conservation
#print axioms singleGen_and_seesaw_iteratedIdentityPower_contraction
#print axioms seesaw_iteratedIdentityPower_protonLifetimeWeightedHilbertNormSq_contraction
#print axioms sm_precision_ew_higgs_two_loop_proton_lifetime_clock_floor_master_bridge

end

end UnifiedTheory.Audit.KFCausalClockFloorSMPrecisionEWHiggsTwoLoopProtonLifetimeBridge
