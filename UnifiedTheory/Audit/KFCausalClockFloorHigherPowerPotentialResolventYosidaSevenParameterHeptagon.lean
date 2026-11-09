/- Seven-Parameter `(a, b, c, d, e, f_param, g_param)` Cyclic Heptagon Cocycle, Mixed Six-Hop
Decomposition, Direct Fixed-`N` Four-Domain (`Dom(K) ∩ Dom(K^{1/2}) ∩ Dom(T_pot) ∩ Dom(T_grow)`)
Invariance and Two-Sided Potential-Pairing Domination `0 ≤ Re⟨P x, J_N x⟩ ≤ Re⟨P x, x⟩` on `Dom(P)`
Without `R_P(a)`, and Fourteen-Parameter Cauchy Rate Bounds for Arbitrary-Order Potential-Resolvent
Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSixParameterHexagon
import UnifiedTheory.Audit.KFCausalClockFloorGrowingFormReconstruction

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSevenParameterHeptagon

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm sequence_tendsto)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_le_of_le
   iteratedResolventPower potentialPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_sub iteratedIdentityPower_norm_le)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (iteratedOperatorPower kthPowerGraphNormSq)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence
  (arbitraryOrderPotentialResolventYosidaTierState
   arbitraryOrderPotentialIdentityYosidaTierState
   clockFloorPotentialResolventYosidaTierState
   clockFloorPotentialIdentityYosidaTierState)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate
  (arbitraryOrderPotentialResolventYosidaTierSub
   arbitraryOrderPotentialIdentityYosidaTierSub
   arbitraryOrderPotentialIdentityYosidaCutoffSub
   arbitraryOrderPotentialYosidaTierSub_zero_and_cocycle
   arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_norm_bounds
   arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
   clockFloorPotentialResolventYosidaTierSub
   clockFloorPotentialIdentityYosidaTierSub)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle
  (arbitraryOrderPotentialYosidaTierSub_three_parameter_cyclic_cocycle
   arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaTierSub_three_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle
  (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
   arbitraryOrderPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
   arbitraryOrderPotentialYosidaTierSub_four_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_four_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_four_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_eight_parameter_bound_of_le)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFiveParameterPentagon
  (arbitraryOrderPotentialYosidaTierSub_five_parameter_pentagon_cocycle
   arbitraryOrderPotentialYosidaTierSub_five_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_five_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_three_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_five_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_ten_parameter_bound_of_le)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSixParameterHexagon
  (arbitraryOrderPotentialYosidaTierSub_six_parameter_hexagon_cocycle
   arbitraryOrderPotentialYosidaTierSub_six_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_six_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_four_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_six_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_twelve_parameter_bound_of_le
   direct_fixedN_potentialForm_and_radialDomain_invariance_on_potentialDomain)

section AbstractSevenParameterHeptagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact seven-parameter `(a, b, c, d, e, f_param, g_param)` cyclic heptagon cocycle vanishing and
six-hop chain decomposition for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_seven_parameter_heptagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H) (a b c d e f_param g_param : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R a) J g_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R g_param) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R g_param) J a g_param r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all seven heptagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
and `(a, g_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_seven_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R g_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R g_param) J a g_param r j x ∈
      operatorPowerDomain P r := by
  have habcdef := arbitraryOrderPotentialYosidaTierSub_six_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param ha hb hc hd he hf_p hres hlinv r j x
  have hafg := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a f_param g_param ha hf_p hg_p hres hlinv r j x
  exact ⟨habcdef.1, habcdef.2.1, habcdef.2.2.1, habcdef.2.2.2.1, habcdef.2.2.2.2.1,
    hafg.2.1, hafg.2.2.1, hafg.2.2.2⟩

/-- Seven-parameter `(a, b, c, d, e, f_param, g_param)` six-hop geometric norm bound and uniform
Yosida stability for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_seven_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R g_param) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + (g_param⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ ≤
      12 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdef := arbitraryOrderPotentialYosidaTierSub_six_parameter_norm_bounds
    P R J a b c d e f_param ha hb hc hd he hf_p hres hpos r j x
  have hafg := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a f_param g_param ha hf_p hg_p hres hpos r j x
  have hfg := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J f_param g_param hf_p hg_p hres hpos r j x
  exact ⟨by linarith [habcdef.1, hafg.1], by linarith [habcdef.2.1, hfg.1], by linarith [habcdef.2.2, hfg.2]⟩

/-- Five-parameter `(a, b, c, d, e)` pentagon cocycle for the mixed parameter-regularizer double
difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_five_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R a) J₁ J₂ e a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ ≤
      8 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R a) J₁ J₂ e a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcd := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_four_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d ha hb hc hd hres hpos r j x).2
  have hde := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ d e hd he hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Seven-parameter `(a, b, c, d, e, f_param, g_param)` mediated six-hop Cauchy rate bound for
`arbitraryOrderPotentialIdentityYosidaTierSub` on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_seven_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m)
    {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ ≤
      12 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ + 2 * f_param⁻¹ + g_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdef := arbitraryOrderPotentialIdentityYosidaTierSub_six_parameter_cauchy_rate_of_le
    P R J a b c d e f_param ha hb hc hd he hf_p hres hpos hlinv m j r hjm hx
  have hfg := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J f_param g_param hf_p hg_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint fourteen-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇))` mediated six-hop
Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_fourteen_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ : H →L[ℂ] H)
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m)
    {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R c) J₃ c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R c) J₃ c r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R d) J₄ d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R d) J₄ d r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R e) J₅ e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R e) J₅ e r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R f_param) J₆ f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R f_param) J₆ f_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R g_param) J₇ g_param r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ + 2 * f_param⁻¹ + g_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdef := arbitraryOrderPotentialIdentityYosida_joint_twelve_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ a b c d e f_param ha hb hc hd he hf_p hres hpos hlinv m j r hjm hx
  have hfg := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₆ J₇ f_param g_param hf_p hg_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractSevenParameterHeptagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m_mass g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Direct fixed-`N` four-domain (`Dom(K) ∩ Dom(K^{1/2}) ∩ Dom(T_pot) ∩ Dom(T_grow)`) invariance
and two-sided potential-pairing domination `0 ≤ Re⟨P x, J_N x⟩ ≤ Re⟨P x, x⟩` on `Dom(P)` without
passing through `R_P(a)`: for every `x : (P).domain`, `0 < k`, and `0 < N`,
`action ε hε h N hN (x : Hilbert)` belongs simultaneously to `(K).domain`, `(Kroot).domain`,
`(Tpot).domain`, and `(Tgrow).domain`, and satisfies the exact potential-pairing split
`Re⟨P x, J_N x⟩ + N⁻¹ * Re⟨P x, M_N x⟩ = Re⟨P x, x⟩` together with
`0 ≤ Re⟨P x, J_N x⟩ ≤ Re⟨P x, x⟩`. -/
theorem direct_fixedN_fourDomain_growingForm_invariance_and_potentialPairing_domination_on_potentialDomain
    (_hk : 0 < k) (N : ℝ) (hN : 0 < N) (x : (P).domain) :
    (x : Hilbert) ∈ (Tpot).domain ∧
    action ε hε h N hN (x : Hilbert) ∈ (K).domain ∧
    action ε hε h N hN (x : Hilbert) ∈ (Kroot).domain ∧
    action ε hε h N hN (x : Hilbert) ∈ (Tpot).domain ∧
    action ε hε h N hN (x : Hilbert) ∈ (Tgrow).domain ∧
    (inner ℂ (P x) (action ε hε h N hN (x : Hilbert))).re +
        N⁻¹ * (inner ℂ (P x) (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re =
      (inner ℂ (P x) (x : Hilbert)).re ∧
    0 ≤ (inner ℂ (P x) (action ε hε h N hN (x : Hilbert))).re ∧
    (inner ℂ (P x) (action ε hε h N hN (x : Hilbert))).re ≤
      (inner ℂ (P x) (x : Hilbert)).re := by
  have hinv := direct_fixedN_potentialForm_and_radialDomain_invariance_on_potentialDomain
    ε hε h hh hb m_mass g k N hN x
  have hroot : action ε hε h N hN (x : Hilbert) ∈ (Kroot).domain :=
    KFCausalClockFloorRadialResolventGrowingDomain.radial_domain_le_root_domain
      ε hε h (action ε hε h N hN (x : Hilbert)) hinv.2.1
  have hgrow : action ε hε h N hN (x : Hilbert) ∈ (Tgrow).domain :=
    (KFCausalClockFloorGrowingFormReconstruction.potential_domain_regularized_in_growing
      ε hε h hh hb m_mass g k N hN (x : Hilbert) hinv.1).2
  have hyos_acc : 0 ≤ (inner ℂ (P x)
      (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re :=
    KFCausalClockFloorPotentialRadialYosidaAccretivity.potential_yosida_accretive
      ε hε h N hN hb hh m_mass g k x
  have hsub : (x : Hilbert) - action ε hε h N hN (x : Hilbert) =
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert) := by
    change (x : Hilbert) - ((x : Hilbert) -
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)) = _
    exact sub_sub_cancel (x : Hilbert)
      ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))
  have hre_diff :
      (inner ℂ (P x) (x : Hilbert)).re -
        (inner ℂ (P x) (action ε hε h N hN (x : Hilbert))).re =
      N⁻¹ * (inner ℂ (P x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
    calc
      (inner ℂ (P x) (x : Hilbert)).re -
          (inner ℂ (P x) (action ε hε h N hN (x : Hilbert))).re
        = (inner ℂ (P x) ((x : Hilbert) - action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_sub_right, Complex.sub_re]
      _ = (inner ℂ (P x)
            ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [hsub]
      _ = N⁻¹ * (inner ℂ (P x)
            (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_smul_right, Complex.mul_re]
            simp
  have hnonneg_term :
      0 ≤ N⁻¹ * (inner ℂ (P x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re :=
    mul_nonneg (inv_nonneg.mpr hN.le) hyos_acc
  exact ⟨hinv.1, hinv.2.1, hroot, hinv.2.2.1, hgrow,
    by linarith [hre_diff], hinv.2.2.2, by linarith [hre_diff, hnonneg_term]⟩

/-- Concrete seven-parameter `(a, b, c, d, e, f_param, g_param)` cyclic heptagon cocycle vanishing
and `potentialPowerDomain (r + 2)` regularity across all seven heptagon legs. -/
theorem clockFloorPotentialYosidaTierSub_seven_parameter_heptagon_cocycle_and_regularity
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a g_param n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + (g_param⁻¹) ^ r) * ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hhept := arbitraryOrderPotentialYosidaTierSub_seven_parameter_heptagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_seven_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_seven_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p hres hpos r j x
  exact ⟨hhept.1, hhept.2.1, hmem.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier seven-parameter `(a, b, c, d, e, f_param, g_param)` and
fourteen-parameter `((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_seven_and_fourteen_parameter_cauchy_rates
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ ≤
      12 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ + 2 * f_param⁻¹ + g_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k e n₅ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k e n₅ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k f_param n₆ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k f_param n₆ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k g_param n₇ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ + 2 * f_param⁻¹ + g_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_seven_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_fourteen_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇)
      a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p hres hpos hlinv m j r hjm hx⟩

/-- Master Seven-Parameter `(a, b, c, d, e, f_param, g_param)` Heptagon Cocycle, Direct Fixed-`N`
Four-Domain Invariance & Potential-Pairing Domination, and Fourteen-Parameter Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_sevenParameter_heptagon_master_synthesis
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a g_param n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + (g_param⁻¹) ^ r) * ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ ≤
      12 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ + 2 * f_param⁻¹ + g_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_seven_parameter_heptagon_cocycle_and_regularity
    ε hε h hh hb m_mass g k a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p n₁ r j x
  have hrates := clockFloorPotentialYosida_seven_and_fourteen_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c d e f_param g_param ha hb_pos hc hd he hf_p hg_p
    n₁ n₂ n₃ n₄ n₅ n₆ n₇ m j r hjm hx
  exact ⟨⟨hcoc.1, hcoc.2.1⟩, ⟨hcoc.2.2.1, hcoc.2.2.2⟩, hrates.1⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_seven_parameter_heptagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_seven_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_seven_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_five_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_seven_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_fourteen_parameter_bound_of_le
#print axioms direct_fixedN_fourDomain_growingForm_invariance_and_potentialPairing_domination_on_potentialDomain
#print axioms clockFloorPotentialYosidaTierSub_seven_parameter_heptagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_seven_and_fourteen_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_sevenParameter_heptagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSevenParameterHeptagon
