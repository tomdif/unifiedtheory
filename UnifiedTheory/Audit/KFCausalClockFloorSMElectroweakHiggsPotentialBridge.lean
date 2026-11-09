/- Standard Model Electroweak-Higgs Potential and Clock-Floor Evolution Bridge:
1. Connects the Standard Model Higgs potential renormalizability uniqueness
   (HiggsPotential, physicalHiggs, renorm_iff_d4, allowedMonomials_card,
   nonConstantMonomials_card, higgs_two_parameter_family, higher_order_nonrenorm)
   and spectral-gap Higgs mass derivation (higgs_quartic_predicted,
   higgs_quartic_value, higgs_mass_tree, higgs_mass_positive, d4_in_window,
   d3_too_heavy, d5_too_light, only_ew_scale_works) to the clock-floor form
   energy functional and nonautonomous unitary evolution.
2. Defines the spectral-gap physical Higgs potential
   spectralGapHiggs mu_sq := physicalHiggs mu_sq higgs_quartic_predicted
   and the Higgs-dressed clock-floor form energy
   higgsDressedFormEnergy ... V_H r x := formNormSqTD ... t x + V_H.eval r * ‖x‖ ^ 2,
   proving exact reduction at r = 0, positivity of the quartic contribution for
   r ≠ 0 and x ≠ 0, exact conservation of V_H.eval r * ‖x‖ ^ 2 along the
   nonautonomous unitary evolution evolutionFamily, and two-sided exponential
   bounds on the evolved form-norm component.
3. Connects the electroweak symmetry-breaking generator split
   (ewGroupDim = 4, emGroupDim = 1, brokenGeneratorCount = 3,
   brokenGeneratorCount + emGroupDim = ewGroupDim) and the Gell-Mann-Nishijima
   relation Q = T₃ + Y (with unbroken_direction_unique) to charge-dressed
   nonautonomous evolution channels and iterated-resolvent second-power domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedResolventSecondPowerCore
import UnifiedTheory.LayerA.HiggsPotentialForm
import UnifiedTheory.LayerA.HiggsMassDerived
import UnifiedTheory.LayerC.SMGaugeDynamics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSMElectroweakHiggsPotentialBridge

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedFormTransport
  (FormSpace embedding energyOutput form_norm_identity)
open KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
  (twoTimeFormEvolution twoTimeFormEvolution_embedding
   twoTimeFormEvolution_two_sided_norm_sq_bounds)
open KFCausalClockFloorEvolvedFormCoreInvariance
  (formEvolution form_embedding_in_averaged_domain form_embedding_mem_averaged_domain)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain hamiltonian_iterated_resolvent_secondPower
   hamiltonian_iterated_resolvent_mem_ten_domains)
open UnifiedTheory.LayerA.HiggsPotentialForm
  (isRenormalizable renorm_iff_d4 allowedMonomials allowedMonomials_card
   nonConstantMonomials nonConstantMonomials_card HiggsPotential
   physicalHiggs physicalHiggs_zero physicalHiggs_eval
   higgs_two_parameter_family higher_order_nonrenorm)
open UnifiedTheory.LayerA.HiggsMassDerived
  (higgs_quartic_predicted higgs_quartic_value higgs_mass_tree higgs_mass_positive
   predicted_mass d4_in_window d3_too_heavy d5_too_light only_ew_scale_works)
open UnifiedTheory.LayerC.SMGaugeDynamics
  (ewGroupDim emGroupDim brokenGeneratorCount MassiveVectorBoson MasslessGaugeBoson
   higgs_pattern_counting electricCharge gellMannNishijima
   higgsHypercharge higgsUpperT3 higgsLowerT3 higgs_upper_charge higgs_vev_neutral
   unbroken_direction_unique up_quark_charge down_quark_charge
   neutrino_charge electron_charge)

/-! ### 1. Spectral-Gap Higgs Potential and Dimensional Renormalizability -/

/-- The physical Higgs potential with quartic coupling fixed by the `d = 4` chamber
spectral gap `higgs_quartic_predicted = (log (5 / 3)) ^ 2 / 2`. -/
def spectralGapHiggs (mu_sq : ℝ) : HiggsPotential :=
  physicalHiggs mu_sq higgs_quartic_predicted

/-- The spectral-gap Higgs potential vanishes at `r = 0`. -/
theorem spectralGapHiggs_zero (mu_sq : ℝ) :
    (spectralGapHiggs mu_sq).eval 0 = 0 :=
  physicalHiggs_zero mu_sq higgs_quartic_predicted

/-- Explicit evaluation formula `(spectralGapHiggs mu_sq).eval r = mu_sq * r + higgs_quartic_predicted * r * r`. -/
theorem spectralGapHiggs_eval (mu_sq r : ℝ) :
    (spectralGapHiggs mu_sq).eval r =
      mu_sq * r + higgs_quartic_predicted * r * r :=
  physicalHiggs_eval mu_sq higgs_quartic_predicted r

/-- The quartic coefficient `(spectralGapHiggs mu_sq).a₂` is strictly positive and `< 1 / 2`. -/
theorem spectralGapHiggs_quartic_bounds (mu_sq : ℝ) :
    0 < (spectralGapHiggs mu_sq).a₂ ∧ (spectralGapHiggs mu_sq).a₂ < 1 / 2 :=
  higgs_quartic_value

/-- Two-parameter uniqueness specialized to `spectralGapHiggs`: any physical Higgs potential
agreeing pointwise with `spectralGapHiggs mu₁` has `mu₂ = mu₁` and `lam₂ = higgs_quartic_predicted`. -/
theorem spectralGapHiggs_two_parameter_uniqueness (mu₁ mu₂ lam₂ : ℝ)
    (h : ∀ r : ℝ, (spectralGapHiggs mu₁).eval r = (physicalHiggs mu₂ lam₂).eval r) :
    mu₁ = mu₂ ∧ lam₂ = higgs_quartic_predicted := by
  have hpair := higgs_two_parameter_family mu₁ higgs_quartic_predicted mu₂ lam₂ h
  exact ⟨hpair.1, hpair.2.symm⟩

/-- Complete `d = 4` renormalizable monomial classification: `isRenormalizable 4 k ↔ k ≤ 2`,
3 allowed monomials, 2 non-constant monomials, and non-renormalizability for all `k ≥ 3`. -/
theorem renorm_d4_monomial_classification :
    (∀ k : ℕ, isRenormalizable 4 k ↔ k ≤ 2) ∧
    allowedMonomials.card = 3 ∧
    nonConstantMonomials.card = 2 ∧
    (∀ k : ℕ, 3 ≤ k → ¬isRenormalizable 4 k) :=
  ⟨renorm_iff_d4, allowedMonomials_card, nonConstantMonomials_card, higher_order_nonrenorm⟩

/-- Non-negativity of the spectral-gap Higgs quartic Hilbert energy
`higgs_quartic_predicted * r * r * ‖x‖ ^ 2` for all `r : ℝ` and `x : Hilbert`. -/
theorem spectralGapHiggs_quartic_energy_nonneg (r : ℝ) (x : Hilbert) :
    0 ≤ higgs_quartic_predicted * r * r * ‖x‖ ^ 2 := by
  have hq : 0 ≤ higgs_quartic_predicted := higgs_quartic_value.1.le
  have hr : 0 ≤ r * r := mul_self_nonneg r
  have hqr : 0 ≤ higgs_quartic_predicted * (r * r) := mul_nonneg hq hr
  rw [mul_assoc higgs_quartic_predicted r r]
  exact mul_nonneg hqr (sq_nonneg ‖x‖)

/-- Strict positivity of the spectral-gap Higgs quartic Hilbert energy
`higgs_quartic_predicted * r * r * ‖x‖ ^ 2` whenever `r ≠ 0` and `x ≠ 0`. -/
theorem spectralGapHiggs_quartic_energy_pos {r : ℝ} (hr : r ≠ 0) {x : Hilbert} (hx : x ≠ 0) :
    0 < higgs_quartic_predicted * r * r * ‖x‖ ^ 2 := by
  have hq : 0 < higgs_quartic_predicted := higgs_quartic_value.1
  have hr2 : 0 < r * r := mul_self_pos.mpr hr
  have hx2 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  rw [mul_assoc higgs_quartic_predicted r r]
  exact mul_pos (mul_pos hq hr2) hx2

/-- Perturbative upper bound `higgs_quartic_predicted * r * r * ‖x‖ ^ 2 ≤ (1 / 2) * r * r * ‖x‖ ^ 2`. -/
theorem spectralGapHiggs_quartic_energy_upper_bound (r : ℝ) (x : Hilbert) :
    higgs_quartic_predicted * r * r * ‖x‖ ^ 2 ≤ (1 / 2) * r * r * ‖x‖ ^ 2 := by
  have hle : higgs_quartic_predicted ≤ 1 / 2 := higgs_quartic_value.2.le
  have hr2 : 0 ≤ r * r * ‖x‖ ^ 2 := mul_nonneg (mul_self_nonneg r) (sq_nonneg ‖x‖)
  calc
    higgs_quartic_predicted * r * r * ‖x‖ ^ 2 =
        higgs_quartic_predicted * (r * r * ‖x‖ ^ 2) := by ring
    _ ≤ (1 / 2) * (r * r * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_right hle hr2
    _ = (1 / 2) * r * r * ‖x‖ ^ 2 := by ring

/-- Spectral-gap Higgs mass window and dimensional exclusion (`d = 3` too heavy, `d = 5` too light)
for every electroweak VEV `v ∈ (240, 250)`. -/
theorem higgs_mass_spectral_gap_window (v : ℝ) (hv1 : 240 < v) (hv2 : v < 250) :
    0 < higgs_mass_tree v ∧
    (120 < predicted_mass 4 v ∧ predicted_mass 4 v < 130) ∧
    150 < predicted_mass 3 v ∧
    predicted_mass 5 v < 125 :=
  ⟨higgs_mass_positive v (by linarith),
   d4_in_window v hv1 hv2,
   d3_too_heavy v (by linarith),
   d5_too_light v (by linarith) hv2⟩

/-- Electroweak scale isolation: any energy scale `E` placing the `d = 4` spectral-gap mass
in `(120, 130)` must lie in `(230, 260)`. -/
theorem higgs_ew_scale_isolation (E : ℝ)
    (hE : 120 < predicted_mass 4 E ∧ predicted_mass 4 E < 130) :
    230 < E ∧ E < 260 :=
  only_ew_scale_works E hE

/-! ### 2. Higgs-Dressed Clock-Floor Form Energy and Unitary Conservation -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "VT" => FormSpace ε hε h hh hw m g k
local notation "AJ" => embedding ε hε h hh hw m g k
local notation "AT" => energyOutput ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- The nonautonomous two-time unitary evolution family on `Hilbert`. -/
abbrev evolutionFamily (s t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  evolution ε hε h hh hw m g k s t

/-- Time-dependent squared form norm on `Hilbert`: equals `‖x‖ ^ 2 + ‖Eavg t ⟨x, hx⟩‖ ^ 2`
when `x ∈ (Eavg t).domain`, and `‖x‖ ^ 2` otherwise. -/
def formNormSqTD (t : ℝ) (x : Hilbert) : ℝ := by
  classical
  exact if hx : x ∈ (Eavg t).domain then ‖x‖ ^ 2 + ‖Eavg t ⟨x, hx⟩‖ ^ 2 else ‖x‖ ^ 2

/-- Higgs-dressed clock-floor form energy functional on `Hilbert`:
`formNormSqTD t x + V_H.eval r * ‖x‖ ^ 2`. -/
def higgsDressedFormEnergy (t : ℝ) (V_H : HiggsPotential) (r : ℝ) (x : Hilbert) : ℝ :=
  formNormSqTD ε hε h hh hb m g k t x + V_H.eval r * ‖x‖ ^ 2

/-- On `(Eavg t).domain`, `formNormSqTD t x = ‖x‖ ^ 2 + ‖Eavg t ⟨x, hx⟩‖ ^ 2`. -/
theorem formNormSqTD_of_mem_domain (t : ℝ) {x : Hilbert} (hx : x ∈ (Eavg t).domain) :
    formNormSqTD ε hε h hh hb m g k t x = ‖x‖ ^ 2 + ‖Eavg t ⟨x, hx⟩‖ ^ 2 := by
  unfold formNormSqTD
  exact dif_pos hx

/-- Unconditional non-negativity and Hilbert-norm lower bound for `formNormSqTD`. -/
theorem formNormSqTD_nonneg_and_lower (t : ℝ) (x : Hilbert) :
    0 ≤ formNormSqTD ε hε h hh hb m g k t x ∧
    ‖x‖ ^ 2 ≤ formNormSqTD ε hε h hh hb m g k t x := by
  unfold formNormSqTD
  split_ifs with hx
  · exact ⟨add_nonneg (sq_nonneg _) (sq_nonneg _),
      le_add_of_nonneg_right (sq_nonneg _)⟩
  · exact ⟨sq_nonneg _, le_rfl⟩

/-- For any form vector `w : VT t`, `formNormSqTD t (AJ t w)` coincides with the squared
completed form norm `‖w‖ ^ 2`. -/
theorem formNormSqTD_embedding_eq (t : ℝ) (w : VT t) :
    formNormSqTD ε hε h hh hb m g k t (AJ t w) = ‖w‖ ^ 2 := by
  have hEw : AJ t w ∈ (Eavg t).domain :=
    form_embedding_in_averaged_domain ε hε h hh hb m g k t w
  rw [formNormSqTD_of_mem_domain ε hε h hh hb m g k t hEw]
  have hE_eq : ‖Eavg t ⟨AJ t w, hEw⟩‖ ^ 2 = ‖AT t w‖ ^ 2 :=
    (form_embedding_mem_averaged_domain ε hε h hh hb m g k t w).2.1
  rw [hE_eq]
  exact (form_norm_identity ε hε h hh hw m g k t w).symm

/-- At `r = 0`, the Higgs-dressed form energy for `spectralGapHiggs mu_sq` reduces
exactly to `formNormSqTD t x`. -/
theorem higgsDressedFormEnergy_at_zero (t mu_sq : ℝ) (x : Hilbert) :
    higgsDressedFormEnergy ε hε h hh hb m g k t (spectralGapHiggs mu_sq) 0 x =
      formNormSqTD ε hε h hh hb m g k t x := by
  unfold higgsDressedFormEnergy
  rw [spectralGapHiggs_zero mu_sq, zero_mul, add_zero]

/-- Explicit expansion of `higgsDressedFormEnergy` for `spectralGapHiggs mu_sq`. -/
theorem higgsDressedFormEnergy_spectralGap_eval (t mu_sq r : ℝ) (x : Hilbert) :
    higgsDressedFormEnergy ε hε h hh hb m g k t (spectralGapHiggs mu_sq) r x =
      formNormSqTD ε hε h hh hb m g k t x +
        (mu_sq * r + higgs_quartic_predicted * r * r) * ‖x‖ ^ 2 := by
  unfold higgsDressedFormEnergy
  rw [spectralGapHiggs_eval mu_sq r]

/-- At `mu_sq = 0`, the spectral-gap Higgs-dressed form energy dominates `formNormSqTD t x`
for every `r : ℝ` and `x : Hilbert`. -/
theorem higgsDressedFormEnergy_zero_mass_ge_formNormSqTD (t r : ℝ) (x : Hilbert) :
    formNormSqTD ε hε h hh hb m g k t x ≤
      higgsDressedFormEnergy ε hε h hh hb m g k t (spectralGapHiggs 0) r x := by
  rw [higgsDressedFormEnergy_spectralGap_eval, zero_mul, zero_add]
  exact le_add_of_nonneg_right (spectralGapHiggs_quartic_energy_nonneg r x)

/-- At `mu_sq = 0`, the spectral-gap Higgs-dressed form energy is strictly greater than
`formNormSqTD t x` whenever `r ≠ 0` and `x ≠ 0`. -/
theorem higgsDressedFormEnergy_zero_mass_strict_gt (t : ℝ) {r : ℝ} (hr : r ≠ 0)
    {x : Hilbert} (hx : x ≠ 0) :
    formNormSqTD ε hε h hh hb m g k t x <
      higgsDressedFormEnergy ε hε h hh hb m g k t (spectralGapHiggs 0) r x := by
  rw [higgsDressedFormEnergy_spectralGap_eval, zero_mul, zero_add]
  exact lt_add_of_pos_right _ (spectralGapHiggs_quartic_energy_pos hr hx)

/-- Exact conservation of the Higgs potential Hilbert energy `V_H.eval r * ‖x‖ ^ 2`
along the nonautonomous unitary evolution `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_higgs_potential_energy
    (s t : ℝ) (V_H : HiggsPotential) (r : ℝ) (x : Hilbert) :
    V_H.eval r * ‖evolutionFamily ε hε h hh hb m g k s t x‖ ^ 2 =
      V_H.eval r * ‖x‖ ^ 2 := by
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Exact conservation of the spectral-gap quartic contribution
`higgs_quartic_predicted * r * r * ‖x‖ ^ 2` under `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_quartic_energy (s t r : ℝ) (x : Hilbert) :
    higgs_quartic_predicted * r * r * ‖evolutionFamily ε hε h hh hb m g k s t x‖ ^ 2 =
      higgs_quartic_predicted * r * r * ‖x‖ ^ 2 := by
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Exact conservation of the tree-level Higgs mass energy `(higgs_mass_tree v) ^ 2 * ‖x‖ ^ 2`
under `evolutionFamily s t`. -/
theorem evolutionFamily_preserves_tree_mass_energy (s t v : ℝ) (x : Hilbert) :
    (higgs_mass_tree v) ^ 2 * ‖evolutionFamily ε hε h hh hb m g k s t x‖ ^ 2 =
      (higgs_mass_tree v) ^ 2 * ‖x‖ ^ 2 := by
  rw [evolution_norm ε hε h hh hw m g k s t x]

/-- Two-sided exponential bounds on `formNormSqTD` along `evolutionFamily s t (AJ s w)`
for every `w : VT s`. -/
theorem evolved_formNormSqTD_two_sided_bounds (s t : ℝ) (w : VT s) :
    Real.exp (-2 * |t - s|) * formNormSqTD ε hε h hh hb m g k s (AJ s w) ≤
      formNormSqTD ε hε h hh hb m g k t (evolutionFamily ε hε h hh hb m g k s t (AJ s w)) ∧
    formNormSqTD ε hε h hh hb m g k t (evolutionFamily ε hε h hh hb m g k s t (AJ s w)) ≤
      Real.exp (2 * |t - s|) * formNormSqTD ε hε h hh hb m g k s (AJ s w) := by
  let v : VT t := twoTimeFormEvolution ε hε h hh hb m g k s t w
  have hJ : evolutionFamily ε hε h hh hb m g k s t (AJ s w) = AJ t v :=
    (twoTimeFormEvolution_embedding ε hε h hh hb m g k s t w).symm
  have ht : formNormSqTD ε hε h hh hb m g k t (evolutionFamily ε hε h hh hb m g k s t (AJ s w)) =
      ‖v‖ ^ 2 :=
    (congrArg (formNormSqTD ε hε h hh hb m g k t) hJ).trans
      (formNormSqTD_embedding_eq ε hε h hh hb m g k t v)
  have hs : formNormSqTD ε hε h hh hb m g k s (AJ s w) = ‖w‖ ^ 2 :=
    formNormSqTD_embedding_eq ε hε h hh hb m g k s w
  have hb_vt := twoTimeFormEvolution_two_sided_norm_sq_bounds ε hε h hh hb m g k s t w
  exact ⟨(congrArg (Real.exp (-2 * |t - s|) * ·) hs).trans_le (hb_vt.1.trans_eq ht.symm),
    ht.trans_le (hb_vt.2.trans_eq (congrArg (Real.exp (2 * |t - s|) * ·) hs.symm))⟩

/-! ### 3. Electroweak Symmetry Breaking and Gell-Mann–Nishijima Charge Evolution Channels -/

/-- Complete electroweak symmetry-breaking generator split: `ewGroupDim = 4`, `emGroupDim = 1`,
`brokenGeneratorCount = 3`, `brokenGeneratorCount + emGroupDim = ewGroupDim`, 3 massive vector
bosons, and 1 massless photon. -/
theorem electroweak_generator_split :
    ewGroupDim = 4 ∧
    emGroupDim = 1 ∧
    brokenGeneratorCount = 3 ∧
    brokenGeneratorCount + emGroupDim = ewGroupDim ∧
    Fintype.card MassiveVectorBoson = brokenGeneratorCount ∧
    Fintype.card MasslessGaugeBoson = emGroupDim :=
  ⟨rfl, rfl, rfl, rfl, higgs_pattern_counting.2.1, higgs_pattern_counting.2.2⟩

/-- Gell-Mann–Nishijima charge-dressed evolution channel decomposition:
`((electricCharge T3 Y : ℝ) : ℂ) • evolutionFamily s t x` splits as the sum of the
weak-isospin `T3` evolution channel and the hypercharge `Y` evolution channel. -/
theorem gellMannNishijima_evolution_channel_split
    (s t : ℝ) (T3 Y : ℚ) (x : Hilbert) :
    ((electricCharge T3 Y : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x =
      ((T3 : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x +
        ((Y : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x := by
  rw [gellMannNishijima T3 Y, Rat.cast_add, Complex.ofReal_add, add_smul]

/-- Intertwining of Gell-Mann–Nishijima charge dressing with `evolutionFamily s t`. -/
theorem gellMannNishijima_evolution_intertwine
    (s t : ℝ) (T3 Y : ℚ) (x : Hilbert) :
    evolutionFamily ε hε h hh hb m g k s t (((electricCharge T3 Y : ℝ) : ℂ) • x) =
      ((T3 : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x +
        ((Y : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x := by
  rw [map_smul, gellMannNishijima_evolution_channel_split]

/-- Norm conservation of Gell-Mann–Nishijima charge-dressed states under `evolutionFamily s t`. -/
theorem gellMannNishijima_evolution_norm
    (s t : ℝ) (T3 Y : ℚ) (x : Hilbert) :
    ‖((electricCharge T3 Y : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x‖ =
      |(T3 : ℝ) + (Y : ℝ)| * ‖x‖ := by
  rw [norm_smul, gellMannNishijima T3 Y, Rat.cast_add, Complex.norm_real,
    Real.norm_eq_abs, evolution_norm ε hε h hh hw m g k s t x]

/-- The lower (vacuum expectation value) Higgs component (`T₃ = -1/2, Y = 1/2`) has
identically zero electric-charge evolution channel for every `x : Hilbert`. -/
theorem higgs_vev_evolution_channel_neutral (s t : ℝ) (x : Hilbert) :
    ((electricCharge higgsLowerT3 higgsHypercharge : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x = 0 := by
  rw [higgs_vev_neutral, Rat.cast_zero, Complex.ofReal_zero, zero_smul]

/-- The upper charged Higgs component (`T₃ = +1/2, Y = 1/2`) has unit electric-charge
evolution channel for every `x : Hilbert`. -/
theorem higgs_upper_evolution_channel_unit (s t : ℝ) (x : Hilbert) :
    ((electricCharge higgsUpperT3 higgsHypercharge : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x =
      evolutionFamily ε hε h hh hb m g k s t x := by
  rw [higgs_upper_charge, Rat.cast_one, Complex.ofReal_one, one_smul]

/-- Unbroken `U(1)_em` direction uniqueness on evolved states: any linear combination
`a_q * T₃ + b_q * Y` that annihilates the Higgs VEV channel and normalizes the upper
Higgs channel coincides on all evolved states with `electricCharge T₃ Y`. -/
theorem unbroken_direction_evolution_uniqueness (s t : ℝ) (a_q b_q T3 Y : ℚ)
    (hvev : a_q * higgsLowerT3 + b_q * higgsHypercharge = 0)
    (hnorm : a_q * higgsUpperT3 + b_q * higgsHypercharge = 1) (x : Hilbert) :
    (((a_q * T3 + b_q * Y : ℚ) : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x =
      ((electricCharge T3 Y : ℝ) : ℂ) • evolutionFamily ε hε h hh hb m g k s t x := by
  rcases unbroken_direction_unique a_q b_q hvev hnorm with ⟨rfl, rfl⟩
  rw [one_mul, one_mul, gellMannNishijima]

/-- Standard Model single-generation fermion charge evolution norms:
up-quark (`2/3`), down-quark (`1/3`), neutrino (`0`), and electron (`1`). -/
theorem sm_fermion_charge_evolution_norms (s t : ℝ) (x : Hilbert) :
    ‖((electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x‖ = (2 / 3 : ℝ) * ‖x‖ ∧
    ‖((electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x‖ = (1 / 3 : ℝ) * ‖x‖ ∧
    ((electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x = 0 ∧
    ‖((electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x‖ = ‖x‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [up_quark_charge, norm_smul, evolution_norm ε hε h hh hw m g k s t x]
    norm_num
  · rw [down_quark_charge, norm_smul, evolution_norm ε hε h hh hw m g k s t x]
    norm_num
  · rw [neutrino_charge, Rat.cast_zero, Complex.ofReal_zero, zero_smul]
  · rw [electron_charge, norm_smul, evolution_norm ε hε h hh hw m g k s t x]
    norm_num

/-- Iterated Hamiltonian resolvent bound on non-negative Higgs potential energy:
when `0 ≤ V_H.eval r` and `0 < a, 0 < b`,
`V_H.eval r * ‖RH t a (RH t b x)‖ ^ 2 ≤ V_H.eval r * (a⁻¹ * (b⁻¹ * ‖x‖)) ^ 2`. -/
theorem iterated_resolvent_higgs_potential_energy_bound
    (t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (V_H : HiggsPotential) (r : ℝ) (hV : 0 ≤ V_H.eval r) (x : Hilbert) :
    V_H.eval r * ‖RH t a (RH t b x)‖ ^ 2 ≤
      V_H.eval r * (a⁻¹ * (b⁻¹ * ‖x‖)) ^ 2 := by
  have hnorm : ‖RH t a (RH t b x)‖ ≤ a⁻¹ * (b⁻¹ * ‖x‖) :=
    (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos x).2.2.2.2.1
  have hsq : ‖RH t a (RH t b x)‖ ^ 2 ≤ (a⁻¹ * (b⁻¹ * ‖x‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact mul_le_mul_of_nonneg_left hsq hV

/-- Master Standard Model Electroweak-Higgs and Clock-Floor Evolution Bridge theorem. -/
theorem sm_electroweak_higgs_clock_floor_bridge
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (mu_sq r : ℝ) (x : Hilbert) :
    (allowedMonomials.card = 3 ∧ nonConstantMonomials.card = 2) ∧
    (0 < higgs_quartic_predicted ∧ higgs_quartic_predicted < 1 / 2) ∧
    (120 < predicted_mass 4 246 ∧ predicted_mass 4 246 < 130) ∧
    (higgsDressedFormEnergy ε hε h hh hb m g k t (spectralGapHiggs mu_sq) 0 x =
      formNormSqTD ε hε h hh hb m g k t x) ∧
    (spectralGapHiggs mu_sq).eval r * ‖evolutionFamily ε hε h hh hb m g k s t x‖ ^ 2 =
      (spectralGapHiggs mu_sq).eval r * ‖x‖ ^ 2 ∧
    (brokenGeneratorCount = 3 ∧ emGroupDim = 1 ∧ brokenGeneratorCount + emGroupDim = ewGroupDim) ∧
    (((electricCharge higgsLowerT3 higgsHypercharge : ℝ) : ℂ) •
      evolutionFamily ε hε h hh hb m g k s t x = 0) ∧
    RH t a (RH t b x) ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t :=
  ⟨⟨allowedMonomials_card, nonConstantMonomials_card⟩,
   higgs_quartic_value,
   d4_in_window 246 (by norm_num) (by norm_num),
   higgsDressedFormEnergy_at_zero ε hε h hh hb m g k t mu_sq x,
   evolutionFamily_preserves_higgs_potential_energy ε hε h hh hb m g k s t
     (spectralGapHiggs mu_sq) r x,
   ⟨rfl, rfl, rfl⟩,
   higgs_vev_evolution_channel_neutral ε hε h hh hb m g k s t x,
   (hamiltonian_iterated_resolvent_secondPower ε hε h hh hb m g k t a b ha hb_pos x).1⟩

#print axioms spectralGapHiggs_zero
#print axioms spectralGapHiggs_eval
#print axioms spectralGapHiggs_quartic_bounds
#print axioms spectralGapHiggs_two_parameter_uniqueness
#print axioms renorm_d4_monomial_classification
#print axioms spectralGapHiggs_quartic_energy_nonneg
#print axioms spectralGapHiggs_quartic_energy_pos
#print axioms spectralGapHiggs_quartic_energy_upper_bound
#print axioms higgs_mass_spectral_gap_window
#print axioms higgs_ew_scale_isolation
#print axioms formNormSqTD_of_mem_domain
#print axioms formNormSqTD_nonneg_and_lower
#print axioms formNormSqTD_embedding_eq
#print axioms higgsDressedFormEnergy_at_zero
#print axioms higgsDressedFormEnergy_spectralGap_eval
#print axioms higgsDressedFormEnergy_zero_mass_ge_formNormSqTD
#print axioms higgsDressedFormEnergy_zero_mass_strict_gt
#print axioms evolutionFamily_preserves_higgs_potential_energy
#print axioms evolutionFamily_preserves_quartic_energy
#print axioms evolutionFamily_preserves_tree_mass_energy
#print axioms evolved_formNormSqTD_two_sided_bounds
#print axioms electroweak_generator_split
#print axioms gellMannNishijima_evolution_channel_split
#print axioms gellMannNishijima_evolution_intertwine
#print axioms gellMannNishijima_evolution_norm
#print axioms higgs_vev_evolution_channel_neutral
#print axioms higgs_upper_evolution_channel_unit
#print axioms unbroken_direction_evolution_uniqueness
#print axioms sm_fermion_charge_evolution_norms
#print axioms iterated_resolvent_higgs_potential_energy_bound
#print axioms sm_electroweak_higgs_clock_floor_bridge

end

end UnifiedTheory.Audit.KFCausalClockFloorSMElectroweakHiggsPotentialBridge
