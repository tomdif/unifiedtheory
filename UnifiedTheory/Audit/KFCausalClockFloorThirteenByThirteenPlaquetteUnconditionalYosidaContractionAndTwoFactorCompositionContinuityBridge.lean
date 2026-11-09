/- Bridge of the Thirteen-by-Thirteen `(s₁..s₁₃) × (t₁..t₁₃)` (`12 × 12 = 144` Elementary Plaquettes)
Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, 2D Stokes Boundary Cancellation,
**Unconditional Residual-Yosida (`YS(t, a) = I - a RS(t, a) = S(t) RS(t, a)`) & Full-Hamiltonian-Yosida
(`YH(t, a) = I - a RH(t, a) = H(t) RH(t, a)`) Pythagorean Energy-Split & Contraction Bounds**:
- `‖YS(t, a) f‖^2 + a^2 ‖RS(t, a) f‖^2 ≤ ‖f‖^2`, `‖YS(t, a) f‖ ≤ ‖f‖`, `‖YS(t, a)‖ ≤ 1`,
- `‖YH(t, a) f‖^2 + a^2 ‖RH(t, a) f‖^2 ≤ ‖f‖^2`, `‖YH(t, a) f‖ ≤ ‖f‖`, `‖YH(t, a)‖ ≤ 1`,
and **Unconditional Uniform-in-`(a, b)` Two-Time Two-Factor Yosida Contraction Composition
Strong Hilbert-Norm & Operator-Norm Lipschitz Continuity and Convergence**:
- `‖YS(s, a)(YS(s, b) f) - YS(t, a)(YS(t, b) f)‖ ≤ 2 |e^{2t} - e^{2s}| (e^{-(t+s)} ‖f‖)`,
- `‖YS(s, a) ∘ YS(s, b) - YS(t, a) ∘ YS(t, b)‖ ≤ 2 |e^{2t} - e^{2s}| e^{-(t+s)}`,
- `‖YH(s, a)(YH(s, b) f) - YH(t, a)(YH(t, b) f)‖ ≤ 4 |e^{2t} - e^{2s}| (e^{-(t+s)} ‖f‖)`,
- `‖YH(s, a) ∘ YH(s, b) - YH(t, a) ∘ YH(t, b)‖ ≤ 4 |e^{2t} - e^{2s}| e^{-(t+s)}`
(Independent of `a, b > 0`),
Together with Positive-Vacuum (`k > 0`) Time-Independent Operator-Intersection Domains and the LayerB
Wilson-Action, Feshbach, Volterra Block-Diagonal, Bath/Chamber Sector, Wightman, Causal-Set
Continuum, and Clay Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorTwelveByTwelvePlaquetteUnconditionalUniformTwoTimeYosidaGeneratorLipschitzContinuityBridge
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
import UnifiedTheory.LayerB.AlphaSAudit
import UnifiedTheory.LayerB.AndoGeometricMean
import UnifiedTheory.LayerB.AnomalyAudit
import UnifiedTheory.LayerB.BTauReaudit
import UnifiedTheory.LayerB.Build1_ExplicitWilsonAction
import UnifiedTheory.LayerB.Build2_HamiltonianFromAction
import UnifiedTheory.LayerB.Build3_ExplicitFeshbach
import UnifiedTheory.LayerB.Build6_VolterraBlockDiagonalDerivation
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import UnifiedTheory.LayerB.CKMCompleteAudit
import UnifiedTheory.LayerB.CKMPreRegistration
import UnifiedTheory.LayerB.CKMSchur7
import UnifiedTheory.LayerB.CL1_BathSector
import UnifiedTheory.LayerB.CL1_ChamberLowestSector
import UnifiedTheory.LayerB.CL2_WightmanAxioms
import UnifiedTheory.LayerB.CL3_CausalSetContinuum
import UnifiedTheory.LayerB.Clay3_PhysicalZ

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorThirteenByThirteenPlaquetteUnconditionalYosidaContractionAndTwoFactorCompositionContinuityBridge
noncomputable section

open Filter
open scoped Topology InnerProduct ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (positive_vacuum_common_domain_eq_three_operator
   positive_vacuum_hamiltonian_inter_growing_domain_eq
   positive_vacuum_three_operator_hamiltonian_eval)
open KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
  (positive_vacuum_two_time_hamiltonian_continuous)
open KFCausalClockFloorTwelveByTwelvePlaquetteUnconditionalUniformTwoTimeYosidaGeneratorLipschitzContinuityBridge
  (residualYosida
   hamiltonianYosida
   unconditional_uniform_twoTime_residual_and_hamiltonian_yosida_generator_lipschitz_and_convergence_synthesis)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (twelveByTwelveResolventPlaquetteGridSum
   twelveByTwelveIdentityPlaquetteGridSum
   twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_thirteen_initial_and_final_tridecagon_cocycles
   twelveByTwelveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   twelveByTwelveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

private theorem general_yosida_pythagorean_and_contraction
    (A : Hilbert →ₗ.[ℂ] Hilbert) (R : Hilbert →L[ℂ] Hilbert) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves A R a) (ht : IsSelfAdjoint A)
    (hp : ∀ x : A.domain, 0 ≤ (inner ℂ (A x) (x : Hilbert)).re) :
    let Y : Hilbert →L[ℂ] Hilbert := ContinuousLinearMap.id ℂ Hilbert - a • R
    (∀ f : Hilbert, ‖Y f‖ ^ 2 + a ^ 2 * ‖R f‖ ^ 2 ≤ ‖f‖ ^ 2) ∧
    (∀ f : Hilbert, ‖Y f‖ ≤ ‖f‖) ∧
    ‖Y‖ ≤ 1 := by
  intro Y
  have hpyth : ∀ f : Hilbert, ‖Y f‖ ^ 2 + a ^ 2 * ‖R f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    intro f
    have hexp : inner ℂ (Y f) (Y f) =
        inner ℂ f f - a • inner ℂ f (R f) -
          (a • inner ℂ f (R f) - a • (a • inner ℂ (R f) (R f))) := by
      change inner ℂ (f - a • R f) (f - a • R f) = _
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        inner_smul_left_eq_smul, inner_smul_right_eq_smul,
        inner_smul_left_eq_smul, inner_smul_right_eq_smul,
        KFCausalPositiveResolventBounds.resolvent_inner_symm A R a hr ht f f]
    have hre := congrArg Complex.re hexp
    rw [KFCausalShiftedForm.complex_inner_square (Y f),
      KFCausalShiftedForm.complex_inner_square f,
      KFCausalShiftedForm.complex_inner_square (R f)] at hre
    simp only [Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] at hre
    have hlow := KFCausalPositiveResolventBounds.resolvent_inner_lower A R a hr hp f
    have hmul : a * (a * ‖R f‖ ^ 2) ≤ a * (inner ℂ f (R f)).re :=
      mul_le_mul_of_nonneg_left hlow ha.le
    have hring : a ^ 2 * ‖R f‖ ^ 2 = a * (a * ‖R f‖ ^ 2) := by ring
    linarith
  have hcontr : ∀ f : Hilbert, ‖Y f‖ ≤ ‖f‖ := by
    intro f
    have hp_f := hpyth f
    have hnonneg : 0 ≤ a ^ 2 * ‖R f‖ ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg ‖R f‖)
    have hsq : ‖Y f‖ ^ 2 ≤ ‖f‖ ^ 2 := by linarith
    exact (abs_le_of_sq_le_sq' hsq (norm_nonneg f)).2
  have hop : ‖Y‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by simpa only [one_mul] using hcontr f)
  exact ⟨hpyth, hcontr, hop⟩

private theorem residualYosida_pythagorean_and_contraction
    (t a : ℝ) (ha : 0 < a) :
    let YS := residualYosida ε hε h hh hb m g k
    (∀ f : Hilbert, ‖YS t a f‖ ^ 2 + a ^ 2 * ‖RS t a f‖ ^ 2 ≤ ‖f‖ ^ 2) ∧
    (∀ f : Hilbert, ‖YS t a f‖ ≤ ‖f‖) ∧
    ‖YS t a‖ ≤ 1 :=
  general_yosida_pythagorean_and_contraction (S t) (RS t a) a ha
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_selfAdjoint (SD t))
    (KFCausalClosedGraphForm.hamiltonian_positive (SD t))

private theorem hamiltonianYosida_pythagorean_and_contraction
    (t a : ℝ) (ha : 0 < a) :
    let YH := hamiltonianYosida ε hε h hh hb m g k
    (∀ f : Hilbert, ‖YH t a f‖ ^ 2 + a ^ 2 * ‖RH t a f‖ ^ 2 ≤ ‖f‖ ^ 2) ∧
    (∀ f : Hilbert, ‖YH t a f‖ ≤ ‖f‖) ∧
    ‖YH t a‖ ≤ 1 :=
  general_yosida_pythagorean_and_contraction (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k t)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)

private theorem twoFactor_yosida_comp_strong_and_opNorm_diff_bound
    (Y_s_a Y_t_a Y_s_b Y_t_b : Hilbert →L[ℂ] Hilbert) (C : ℝ) (hC : 0 ≤ C)
    (hcontr_s_a : ∀ w : Hilbert, ‖Y_s_a w‖ ≤ ‖w‖)
    (hcontr_t_b : ∀ f : Hilbert, ‖Y_t_b f‖ ≤ ‖f‖)
    (hdiff_a : ∀ w : Hilbert, ‖Y_s_a w - Y_t_a w‖ ≤ C * ‖w‖)
    (hdiff_b : ∀ f : Hilbert, ‖Y_s_b f - Y_t_b f‖ ≤ C * ‖f‖) :
    (∀ f : Hilbert, ‖Y_s_a (Y_s_b f) - Y_t_a (Y_t_b f)‖ ≤ 2 * C * ‖f‖) ∧
    ‖Y_s_a.comp Y_s_b - Y_t_a.comp Y_t_b‖ ≤ 2 * C := by
  have hstr : ∀ f : Hilbert, ‖Y_s_a (Y_s_b f) - Y_t_a (Y_t_b f)‖ ≤ 2 * C * ‖f‖ := by
    intro f
    have hsplit :
        Y_s_a (Y_s_b f) - Y_t_a (Y_t_b f) =
          Y_s_a (Y_s_b f - Y_t_b f) + (Y_s_a (Y_t_b f) - Y_t_a (Y_t_b f)) := by
      rw [map_sub]
      abel
    have h1 : ‖Y_s_a (Y_s_b f - Y_t_b f)‖ ≤ C * ‖f‖ :=
      (hcontr_s_a (Y_s_b f - Y_t_b f)).trans (hdiff_b f)
    have h2 : ‖Y_s_a (Y_t_b f) - Y_t_a (Y_t_b f)‖ ≤ C * ‖f‖ :=
      (hdiff_a (Y_t_b f)).trans (mul_le_mul_of_nonneg_left (hcontr_t_b f) hC)
    calc
      ‖Y_s_a (Y_s_b f) - Y_t_a (Y_t_b f)‖
        ≤ ‖Y_s_a (Y_s_b f - Y_t_b f)‖ + ‖Y_s_a (Y_t_b f) - Y_t_a (Y_t_b f)‖ := by
          rw [hsplit]
          exact norm_add_le _ _
      _ ≤ C * ‖f‖ + C * ‖f‖ := add_le_add h1 h2
      _ = 2 * C * ‖f‖ := by ring
  have hop : ‖Y_s_a.comp Y_s_b - Y_t_a.comp Y_t_b‖ ≤ 2 * C := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun f => ?_)
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply] using hstr f
  exact ⟨hstr, hop⟩

private theorem yosida_single_strong_diff_bounds_of_pos_vacuum
    (hk : 0 < k) {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain)
    (s t c : ℝ) (hc : 0 < c) (w : Hilbert) :
    let YS := residualYosida ε hε h hh hb m g k
    let YH := hamiltonianYosida ε hε h hh hb m g k
    ‖YS s c w - YS t c w‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (Real.exp (-(t + s)) * ‖w‖) ∧
    ‖YH s c w - YH t c w‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (2 * Real.exp (-(t + s)) * ‖w‖) := by
  have h26 := KFCausalClockFloorTwelveByTwelvePlaquetteUnconditionalUniformTwoTimeYosidaGeneratorLipschitzContinuityBridge.twelveByTwelve_plaquetteGrid_unconditionalUniformTwoTimeYosidaGeneratorLipschitz_bridge_master
    ε hε h hh hb m g k hk s s s s s s s s s s s s t t t t t t t t t t t t 0
    c c c c c c c c c c c c c c c c c c c c c c c c
    c c c c c c c c c c c c c c c c c c c c c c c c
    c c c c c c c c c c c c c c c c c c c c c c c c
    c c c c c c c c c c c c c c c c c c c c c c c c
    c c c c c c c c c c c c c c c c c c c c c c c c
    c c c c c c c c c c c c c c c c c c c c c c c c
    hc hc hc hc 0 w w w w w w w w w w w w hxT hxK hxP
  exact ⟨h26.1.2.2.1, h26.1.2.2.2.2.2.2.1⟩

/-- **Unconditional Yosida Contraction, Pythagorean Energy-Split, and Uniform-in-`(a, b)` Two-Time
Two-Factor Yosida Composition Lipschitz Continuity & Convergence**:
1. Unconditional Pythagorean energy-split and contraction bounds (`0 < a`, no `k > 0` required):
   - `‖YS(t, a) f‖^2 + a^2 ‖RS(t, a) f‖^2 ≤ ‖f‖^2`, `‖YS(t, a) f‖ ≤ ‖f‖`, `‖YS(t, a)‖ ≤ 1`,
   - `‖YH(t, a) f‖^2 + a^2 ‖RH(t, a) f‖^2 ≤ ‖f‖^2`, `‖YH(t, a) f‖ ≤ ‖f‖`, `‖YH(t, a)‖ ≤ 1`;
2. Parameter-independent (`(a, b)`-uniform) two-time two-factor Yosida composition Lipschitz bounds:
   - `‖YS(s, a)(YS(s, b) f) - YS(t, a)(YS(t, b) f)‖ ≤ 2 |e^{2t} - e^{2s}| (e^{-(t+s)} ‖f‖)`,
   - `‖YS(s, a) ∘ YS(s, b) - YS(t, a) ∘ YS(t, b)‖ ≤ 2 |e^{2t} - e^{2s}| e^{-(t+s)}`,
   - `‖YH(s, a)(YH(s, b) f) - YH(t, a)(YH(t, b) f)‖ ≤ 4 |e^{2t} - e^{2s}| (e^{-(t+s)} ‖f‖)`,
   - `‖YH(s, a) ∘ YH(s, b) - YH(t, a) ∘ YH(t, b)‖ ≤ 4 |e^{2t} - e^{2s}| e^{-(t+s)}`;
3. Strong Hilbert-norm and operator-norm convergence of both single-factor and two-factor Yosida
   compositions as `s → t`. -/
theorem unconditional_yosida_contraction_pythagorean_and_twoFactor_composition_lipschitz_synthesis
    (hk : 0 < k) (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (k_vol : ℕ) (hk_vol : 1 ≤ k_vol)
    (f f₁ f₂ : Hilbert)
    (hE_t : f ∈ (Eavg t).domain)
    (hG_res : RH s a f ∈ (G).domain)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let YS := residualYosida ε hε h hh hb m g k
    let YH := hamiltonianYosida ε hε h hh hb m g k
    (‖YS t a f‖ ^ 2 + a ^ 2 * ‖RS t a f‖ ^ 2 ≤ ‖f‖ ^ 2 ∧
      ‖YS t a f‖ ≤ ‖f‖ ∧
      ‖YS t a‖ ≤ 1 ∧
      ‖YH t a f‖ ^ 2 + a ^ 2 * ‖RH t a f‖ ^ 2 ≤ ‖f‖ ^ 2 ∧
      ‖YH t a f‖ ≤ ‖f‖ ∧
      ‖YH t a‖ ≤ 1 ∧
      ‖YS s a (YS s b f) - YS t a (YS t b f)‖ ≤
        2 * |Real.exp (2 * t) - Real.exp (2 * s)| * (Real.exp (-(t + s)) * ‖f‖) ∧
      ‖(YS s a).comp (YS s b) - (YS t a).comp (YS t b)‖ ≤
        2 * |Real.exp (2 * t) - Real.exp (2 * s)| * Real.exp (-(t + s)) ∧
      Tendsto (fun s' : ℝ => YS s' a (YS s' b f)) (𝓝 t) (𝓝 (YS t a (YS t b f))) ∧
      Tendsto (fun s' : ℝ => (YS s' a).comp (YS s' b)) (𝓝 t) (𝓝 ((YS t a).comp (YS t b))) ∧
      ‖YH s a (YH s b f) - YH t a (YH t b f)‖ ≤
        4 * |Real.exp (2 * t) - Real.exp (2 * s)| * (Real.exp (-(t + s)) * ‖f‖) ∧
      ‖(YH s a).comp (YH s b) - (YH t a).comp (YH t b)‖ ≤
        4 * |Real.exp (2 * t) - Real.exp (2 * s)| * Real.exp (-(t + s)) ∧
      Tendsto (fun s' : ℝ => YH s' a (YH s' b f)) (𝓝 t) (𝓝 (YH t a (YH t b f))) ∧
      Tendsto (fun s' : ℝ => (YH s' a).comp (YH s' b)) (𝓝 t) (𝓝 ((YH t a).comp (YH t b))) ∧
      ‖YS s a f - YS t a f‖ ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| * (Real.exp (-(t + s)) * ‖f‖) ∧
      ‖YH s a f - YH t a f‖ ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| * (2 * Real.exp (-(t + s)) * ‖f‖)) ∧
    (commonOperatorDomain ε hε h hh hb m g k = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      (H t).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain) ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  intro YS YH
  have h26 := unconditional_uniform_twoTime_residual_and_hamiltonian_yosida_generator_lipschitz_and_convergence_synthesis
    ε hε h hh hb m g k hk s t a ha k_vol hk_vol f f₁ f₂ hE_t hG_res hxT hxK hxP
  have hYS_pyth := residualYosida_pythagorean_and_contraction ε hε h hh hb m g k t a ha
  have hYH_pyth := hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k t a ha
  have hYS_two : ∀ s' : ℝ,
      (∀ w : Hilbert, ‖YS s' a (YS s' b w) - YS t a (YS t b w)‖ ≤
        2 * |Real.exp (2 * t) - Real.exp (2 * s')| * (Real.exp (-(t + s')) * ‖w‖)) ∧
      ‖(YS s' a).comp (YS s' b) - (YS t a).comp (YS t b)‖ ≤
        2 * |Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s')) := by
    intro s'
    have hc := twoFactor_yosida_comp_strong_and_opNorm_diff_bound
      (YS s' a) (YS t a) (YS s' b) (YS t b)
      (|Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s')))
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (residualYosida_pythagorean_and_contraction ε hε h hh hb m g k s' a ha).2.1
      (residualYosida_pythagorean_and_contraction ε hε h hh hb m g k t b hb_pos).2.1
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t a ha w).1)
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t b hb_pos w).1)
    exact ⟨fun w => by simpa only [mul_assoc] using hc.1 w,
      by simpa only [mul_assoc] using hc.2⟩
  have hYH_two : ∀ s' : ℝ,
      (∀ w : Hilbert, ‖YH s' a (YH s' b w) - YH t a (YH t b w)‖ ≤
        4 * |Real.exp (2 * t) - Real.exp (2 * s')| * (Real.exp (-(t + s')) * ‖w‖)) ∧
      ‖(YH s' a).comp (YH s' b) - (YH t a).comp (YH t b)‖ ≤
        4 * |Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s')) := by
    intro s'
    have hc := twoFactor_yosida_comp_strong_and_opNorm_diff_bound
      (YH s' a) (YH t a) (YH s' b) (YH t b)
      (|Real.exp (2 * t) - Real.exp (2 * s')| * (2 * Real.exp (-(t + s'))))
      (mul_nonneg (abs_nonneg _) (mul_nonneg zero_le_two (Real.exp_pos _).le))
      (hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k s' a ha).2.1
      (hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k t b hb_pos).2.1
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t a ha w).2)
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t b hb_pos w).2)
    refine ⟨fun w => ?_, ?_⟩
    · calc
        ‖YH s' a (YH s' b w) - YH t a (YH t b w)‖
          ≤ 2 * (|Real.exp (2 * t) - Real.exp (2 * s')| * (2 * Real.exp (-(t + s')))) * ‖w‖ := hc.1 w
        _ = 4 * |Real.exp (2 * t) - Real.exp (2 * s')| * (Real.exp (-(t + s')) * ‖w‖) := by ring
    · calc
        ‖(YH s' a).comp (YH s' b) - (YH t a).comp (YH t b)‖
          ≤ 2 * (|Real.exp (2 * t) - Real.exp (2 * s')| * (2 * Real.exp (-(t + s')))) := hc.2
        _ = 4 * |Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s')) := by ring
  have hYS_two_lim_f :
      Tendsto (fun s' : ℝ => YS s' a (YS s' b f)) (𝓝 t) (𝓝 (YS t a (YS t b f))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      2 * |Real.exp (2 * t) - Real.exp (2 * s')| * (Real.exp (-(t + s')) * ‖f‖)
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYS_two s').1 f)
  have hYS_two_lim_op :
      Tendsto (fun s' : ℝ => (YS s' a).comp (YS s' b)) (𝓝 t) (𝓝 ((YS t a).comp (YS t b))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      2 * |Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s'))
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYS_two s').2)
  have hYH_two_lim_f :
      Tendsto (fun s' : ℝ => YH s' a (YH s' b f)) (𝓝 t) (𝓝 (YH t a (YH t b f))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      4 * |Real.exp (2 * t) - Real.exp (2 * s')| * (Real.exp (-(t + s')) * ‖f‖)
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYH_two s').1 f)
  have hYH_two_lim_op :
      Tendsto (fun s' : ℝ => (YH s' a).comp (YH s' b)) (𝓝 t) (𝓝 ((YH t a).comp (YH t b))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      4 * |Real.exp (2 * t) - Real.exp (2 * s')| * Real.exp (-(t + s'))
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYH_two s').2)
  exact ⟨⟨hYS_pyth.1 f, hYS_pyth.2.1 f, hYS_pyth.2.2,
      hYH_pyth.1 f, hYH_pyth.2.1 f, hYH_pyth.2.2,
      (hYS_two s).1 f, (hYS_two s).2, hYS_two_lim_f, hYS_two_lim_op,
      (hYH_two s).1 f, (hYH_two s).2, hYH_two_lim_f, hYH_two_lim_op,
      h26.1.2.2.1, h26.1.2.2.2.2.2.2.1⟩,
    h26.2.1, h26.2.2.1, h26.2.2.2.1, h26.2.2.2.2.1, h26.2.2.2.2.2⟩

/-- `13 × 13` (`12 × 12 = 144` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem thirteenByThirteen_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
     d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ d₁ d₁₃ r f₁ f₁₃ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `13 × 13` (`12 × 12 = 144` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem thirteenByThirteen_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
     d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (i_idx : Fin 3) :
    twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ d₁ d₁₃ r f₁ f₁₃ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twelveByTwelveResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_thirteenByThirteenResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
     d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hd₁ : 0 < d₁) (hd₁₃ : 0 < d₁₃)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    ha₁ ha₁₃ hd₁ hd₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twelveByTwelveIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_thirteenByThirteenIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
     d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hd₁ : 0 < d₁) (hd₁₃ : 0 < d₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    ha₁ ha₁₃ hd₁ hd₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `13 × 13` (`12 × 12 = 144` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional residual-Yosida (`YS(t, a)`) and
Hamiltonian-Yosida (`YH(t, a)`) Pythagorean energy-split & contraction bounds, uniform-in-`(a, b)`
two-time two-factor Yosida composition Lipschitz continuity and convergence, positive-vacuum (`k > 0`)
time-independent operator domains, and the Wilson / Feshbach / Volterra / Wightman / Clay continuum
modules. -/
theorem thirteenByThirteen_plaquetteGrid_unconditionalYosidaContractionAndTwoFactorCompositionContinuity_bridge_master
    (hk : 0 < k)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
     d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hd₁ : 0 < d₁) (hd₁₃ : 0 < d₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let YS := residualYosida ε hε h hh hb m g k
    let YH := hamiltonianYosida ε hε h hh hb m g k
    let hxt_H := (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t₁ hxT hxK hxP).choose
    (‖YS t₁ a₁ f₁₃‖ ^ 2 + a₁ ^ 2 * ‖RS t₁ a₁ f₁₃‖ ^ 2 ≤ ‖f₁₃‖ ^ 2 ∧
      ‖YS t₁ a₁ f₁₃‖ ≤ ‖f₁₃‖ ∧
      ‖YS t₁ a₁‖ ≤ 1 ∧
      ‖YH t₁ a₁ f₁₃‖ ^ 2 + a₁ ^ 2 * ‖RH t₁ a₁ f₁₃‖ ^ 2 ≤ ‖f₁₃‖ ^ 2 ∧
      ‖YH t₁ a₁ f₁₃‖ ≤ ‖f₁₃‖ ∧
      ‖YH t₁ a₁‖ ≤ 1 ∧
      ‖YS s₁ a₁ (YS s₁ d₁ f₁₃) - YS t₁ a₁ (YS t₁ d₁ f₁₃)‖ ≤
        2 * |Real.exp (2 * t₁) - Real.exp (2 * s₁)| * (Real.exp (-(t₁ + s₁)) * ‖f₁₃‖) ∧
      ‖(YS s₁ a₁).comp (YS s₁ d₁) - (YS t₁ a₁).comp (YS t₁ d₁)‖ ≤
        2 * |Real.exp (2 * t₁) - Real.exp (2 * s₁)| * Real.exp (-(t₁ + s₁)) ∧
      Tendsto (fun s' : ℝ => YS s' a₁ (YS s' d₁ f₁₃)) (𝓝 t₁) (𝓝 (YS t₁ a₁ (YS t₁ d₁ f₁₃))) ∧
      Tendsto (fun s' : ℝ => (YS s' a₁).comp (YS s' d₁)) (𝓝 t₁) (𝓝 ((YS t₁ a₁).comp (YS t₁ d₁))) ∧
      ‖YH s₁ a₁ (YH s₁ d₁ f₁₃) - YH t₁ a₁ (YH t₁ d₁ f₁₃)‖ ≤
        4 * |Real.exp (2 * t₁) - Real.exp (2 * s₁)| * (Real.exp (-(t₁ + s₁)) * ‖f₁₃‖) ∧
      ‖(YH s₁ a₁).comp (YH s₁ d₁) - (YH t₁ a₁).comp (YH t₁ d₁)‖ ≤
        4 * |Real.exp (2 * t₁) - Real.exp (2 * s₁)| * Real.exp (-(t₁ + s₁)) ∧
      Tendsto (fun s' : ℝ => YH s' a₁ (YH s' d₁ f₁₃)) (𝓝 t₁) (𝓝 (YH t₁ a₁ (YH t₁ d₁ f₁₃))) ∧
      Tendsto (fun s' : ℝ => (YH s' a₁).comp (YH s' d₁)) (𝓝 t₁) (𝓝 ((YH t₁ a₁).comp (YH t₁ d₁))) ∧
      (H t₁).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      Tendsto (fun s' : ℝ =>
        H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩)
        (𝓝 t₁) (𝓝 (H t₁ ⟨x, hxt_H⟩))) ∧
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ d₁ d₁₃ r f₁ f₁₃ ∧
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  intro YS YH hxt_H
  have h26 := KFCausalClockFloorTwelveByTwelvePlaquetteUnconditionalUniformTwoTimeYosidaGeneratorLipschitzContinuityBridge.twelveByTwelve_plaquetteGrid_unconditionalUniformTwoTimeYosidaGeneratorLipschitz_bridge_master
    ε hε h hh hb m g k hk s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁
    ha₁ ha₁ hd₁ hd₁ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₃ hxT hxK hxP
  have hYS_pyth := residualYosida_pythagorean_and_contraction ε hε h hh hb m g k t₁ a₁ ha₁
  have hYH_pyth := hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k t₁ a₁ ha₁
  have hYS_two : ∀ s' : ℝ,
      (∀ w : Hilbert, ‖YS s' a₁ (YS s' d₁ w) - YS t₁ a₁ (YS t₁ d₁ w)‖ ≤
        2 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * (Real.exp (-(t₁ + s')) * ‖w‖)) ∧
      ‖(YS s' a₁).comp (YS s' d₁) - (YS t₁ a₁).comp (YS t₁ d₁)‖ ≤
        2 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s')) := by
    intro s'
    have hc := twoFactor_yosida_comp_strong_and_opNorm_diff_bound
      (YS s' a₁) (YS t₁ a₁) (YS s' d₁) (YS t₁ d₁)
      (|Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s')))
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (residualYosida_pythagorean_and_contraction ε hε h hh hb m g k s' a₁ ha₁).2.1
      (residualYosida_pythagorean_and_contraction ε hε h hh hb m g k t₁ d₁ hd₁).2.1
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t₁ a₁ ha₁ w).1)
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t₁ d₁ hd₁ w).1)
    exact ⟨fun w => by simpa only [mul_assoc] using hc.1 w,
      by simpa only [mul_assoc] using hc.2⟩
  have hYH_two : ∀ s' : ℝ,
      (∀ w : Hilbert, ‖YH s' a₁ (YH s' d₁ w) - YH t₁ a₁ (YH t₁ d₁ w)‖ ≤
        4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * (Real.exp (-(t₁ + s')) * ‖w‖)) ∧
      ‖(YH s' a₁).comp (YH s' d₁) - (YH t₁ a₁).comp (YH t₁ d₁)‖ ≤
        4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s')) := by
    intro s'
    have hc := twoFactor_yosida_comp_strong_and_opNorm_diff_bound
      (YH s' a₁) (YH t₁ a₁) (YH s' d₁) (YH t₁ d₁)
      (|Real.exp (2 * t₁) - Real.exp (2 * s')| * (2 * Real.exp (-(t₁ + s'))))
      (mul_nonneg (abs_nonneg _) (mul_nonneg zero_le_two (Real.exp_pos _).le))
      (hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k s' a₁ ha₁).2.1
      (hamiltonianYosida_pythagorean_and_contraction ε hε h hh hb m g k t₁ d₁ hd₁).2.1
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t₁ a₁ ha₁ w).2)
      (fun w => by
        simpa only [mul_assoc] using
          (yosida_single_strong_diff_bounds_of_pos_vacuum ε hε h hh hb m g k hk hxT hxK hxP s' t₁ d₁ hd₁ w).2)
    refine ⟨fun w => ?_, ?_⟩
    · calc
        ‖YH s' a₁ (YH s' d₁ w) - YH t₁ a₁ (YH t₁ d₁ w)‖
          ≤ 2 * (|Real.exp (2 * t₁) - Real.exp (2 * s')| * (2 * Real.exp (-(t₁ + s')))) * ‖w‖ := hc.1 w
        _ = 4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * (Real.exp (-(t₁ + s')) * ‖w‖) := by ring
    · calc
        ‖(YH s' a₁).comp (YH s' d₁) - (YH t₁ a₁).comp (YH t₁ d₁)‖
          ≤ 2 * (|Real.exp (2 * t₁) - Real.exp (2 * s')| * (2 * Real.exp (-(t₁ + s')))) := hc.2
        _ = 4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s')) := by ring
  have hYS_two_lim_f :
      Tendsto (fun s' : ℝ => YS s' a₁ (YS s' d₁ f₁₃)) (𝓝 t₁) (𝓝 (YS t₁ a₁ (YS t₁ d₁ f₁₃))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      2 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * (Real.exp (-(t₁ + s')) * ‖f₁₃‖)
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t₁ = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t₁) (𝓝 0) := hB0 ▸ hB_cont.tendsto t₁
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYS_two s').1 f₁₃)
  have hYS_two_lim_op :
      Tendsto (fun s' : ℝ => (YS s' a₁).comp (YS s' d₁)) (𝓝 t₁) (𝓝 ((YS t₁ a₁).comp (YS t₁ d₁))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      2 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s'))
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t₁ = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t₁) (𝓝 0) := hB0 ▸ hB_cont.tendsto t₁
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYS_two s').2)
  have hYH_two_lim_f :
      Tendsto (fun s' : ℝ => YH s' a₁ (YH s' d₁ f₁₃)) (𝓝 t₁) (𝓝 (YH t₁ a₁ (YH t₁ d₁ f₁₃))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * (Real.exp (-(t₁ + s')) * ‖f₁₃‖)
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t₁ = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t₁) (𝓝 0) := hB0 ▸ hB_cont.tendsto t₁
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYH_two s').1 f₁₃)
  have hYH_two_lim_op :
      Tendsto (fun s' : ℝ => (YH s' a₁).comp (YH s' d₁)) (𝓝 t₁) (𝓝 ((YH t₁ a₁).comp (YH t₁ d₁))) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    let B : ℝ → ℝ := fun s' =>
      4 * |Real.exp (2 * t₁) - Real.exp (2 * s')| * Real.exp (-(t₁ + s'))
    have hB_cont : Continuous B := by fun_prop
    have hB0 : B t₁ = 0 := by simp [B]
    have hB_lim : Tendsto B (𝓝 t₁) (𝓝 0) := hB0 ▸ hB_cont.tendsto t₁
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
      (fun _ => norm_nonneg _) (fun s' => (hYH_two s').2)
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hweq := twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    ha₁ ha₁₃ hd₁ hd₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨⟨hYS_pyth.1 f₁₃, hYS_pyth.2.1 f₁₃, hYS_pyth.2.2,
      hYH_pyth.1 f₁₃, hYH_pyth.2.1 f₁₃, hYH_pyth.2.2,
      (hYS_two s₁).1 f₁₃, (hYS_two s₁).2, hYS_two_lim_f, hYS_two_lim_op,
      (hYH_two s₁).1 f₁₃, (hYH_two s₁).2, hYH_two_lim_f, hYH_two_lim_op,
      h26.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h26.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
    hstokes.1,
    hweq.1,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_yosida_contraction_pythagorean_and_twoFactor_composition_lipschitz_synthesis
#print axioms thirteenByThirteen_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms thirteenByThirteen_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_thirteenByThirteenResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_thirteenByThirteenIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms thirteenByThirteen_plaquetteGrid_unconditionalYosidaContractionAndTwoFactorCompositionContinuity_bridge_master

end
end KFCausalClockFloorThirteenByThirteenPlaquetteUnconditionalYosidaContractionAndTwoFactorCompositionContinuityBridge
end Audit
end UnifiedTheory
