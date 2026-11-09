/- Nine-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` Cyclic Nonagon Cocycle,
Mixed Eight-Hop Decomposition, Direct Fixed-`N` Full-Hamiltonian `Dom(H(t))` and Residual `Dom(S(t))`
Radial-Yosida Quadratic Lower Bound, Explicit `M_N` Norm Bound, Regularized Pairing Inequality, and
`O(N⁻¹)` Regularizer Rate Without `R_{H(t)}(a)` or `R_{S(t)}(a)`, and Eighteen-Parameter Cauchy
Rate Bounds for Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaEightParameterOctagon

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaNineParameterNonagon

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
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaEightParameterOctagon
  (arbitraryOrderPotentialYosidaTierSub_eight_parameter_octagon_cocycle
   arbitraryOrderPotentialYosidaTierSub_eight_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_eight_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_six_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_eight_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_sixteen_parameter_bound_of_le)

section AbstractNineParameterNonagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` cyclic nonagon
cocycle vanishing and eight-hop chain decomposition for `arbitraryOrderPotentialResolventYosidaTierSub`
and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_nine_parameter_nonagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R i_param) (R a) J i_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R i_param) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R i_param) J a i_param r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all nine nonagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
`(g_param, h_param)`, `(h_param, i_param)`, and `(a, i_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_nine_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R i_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R i_param) J a i_param r j x ∈
      operatorPowerDomain P r := by
  have habcdefgh := arbitraryOrderPotentialYosidaTierSub_eight_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param g_param h_param ha hb hc hd he hf_p hg_p hh_p hres hlinv r j x
  have hahi := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a h_param i_param ha hh_p hi_p hres hlinv r j x
  exact ⟨habcdefgh.1, habcdefgh.2.1, habcdefgh.2.2.1, habcdefgh.2.2.2.1,
    habcdefgh.2.2.2.2.1, habcdefgh.2.2.2.2.2.1, habcdefgh.2.2.2.2.2.2.1,
    hahi.2.1, hahi.2.2.1, hahi.2.2.2⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` eight-hop geometric norm
bound and uniform Yosida stability for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_nine_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R i_param) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r + (i_param⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x‖ ≤
      16 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdefgh := arbitraryOrderPotentialYosidaTierSub_eight_parameter_norm_bounds
    P R J a b c d e f_param g_param h_param ha hb hc hd he hf_p hg_p hh_p hres hpos r j x
  have hahi := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a h_param i_param ha hh_p hi_p hres hpos r j x
  have hhi := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J h_param i_param hh_p hi_p hres hpos r j x
  exact ⟨by linarith [habcdefgh.1, hahi.1], by linarith [habcdefgh.2.1, hhi.1], by linarith [habcdefgh.2.2, hhi.2]⟩

/-- Seven-parameter `(a, b, c, d, e, f_param, g_param)` heptagon cocycle for the mixed
parameter-regularizer double difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_seven_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e f_param g_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R a) J₁ J₂ g_param a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x‖ ≤
      12 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R a) J₁ J₂ g_param a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcdef := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_six_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d e f_param ha hb hc hd he hf_p hres hpos r j x).2
  have hfg := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ f_param g_param hf_p hg_p hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` mediated eight-hop Cauchy
rate bound for `arbitraryOrderPotentialIdentityYosidaTierSub` on `operatorPowerDomain P (m + 1)`
for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_nine_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
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
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x‖ ≤
      16 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + i_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefgh := arbitraryOrderPotentialIdentityYosidaTierSub_eight_parameter_cauchy_rate_of_le
    P R J a b c d e f_param g_param h_param ha hb hc hd he hf_p hg_p hh_p hres hpos hlinv m j r hjm hx
  have hhi := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J h_param i_param hh_p hi_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint eighteen-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇), (h_param, J₈), (i_param, J₉))`
mediated eight-hop Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_eighteen_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R g_param) J₇ g_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R g_param) J₇ g_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R h_param) J₈ h_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R h_param) J₈ h_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R i_param) J₉ i_param r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₉ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + i_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefgh := arbitraryOrderPotentialIdentityYosida_joint_sixteen_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ a b c d e f_param g_param h_param ha hb hc hd he hf_p hg_p hh_p hres hpos hlinv m j r hjm hx
  have hhi := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₈ J₉ h_param i_param hh_p hi_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractNineParameterNonagon

private theorem quadratic_bound (u v z e : ℝ) (hv : 0 ≤ v)
    (hz : 0 ≤ z) (he : 0 < e) (hq : e ^ 2 * u ^ 2 ≤ v * u + z ^ 2) :
    u ≤ v / e ^ 2 + z / e := by
  have hmul : (v / e) * (e * u) = v * u := by rw [← mul_assoc, div_mul_cancel₀ _ he.ne']
  have hs : (e * u) ^ 2 ≤ (v / e) * (e * u) + z ^ 2 := by rw [hmul]; nlinarith only [hq]
  have hn : e * u ≤ v / e + z := by
    have ha : 0 ≤ v / e := div_nonneg hv he.le
    by_contra hbad
    have hb := lt_of_not_ge hbad
    have hc : z < e * u := by linarith
    nlinarith [mul_nonneg ha (show 0 ≤ e * u - z by linarith)]
  have hd : u ≤ (v / e + z) / e := (le_div_iff₀ he).mpr (by simpa only [mul_comm u e] using hn)
  have heq : (v / e + z) / e = v / e ^ 2 + z / e := by ring
  exact hd.trans_eq heq

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Direct fixed-`N` full-Hamiltonian `(H t).domain` and residual `(S t).domain` radial-Yosida
quadratic lower bound, explicit `M_N` norm bound, regularized pairing inequality, and `O(N⁻¹)`
regularizer rate `‖x - J_N x‖ ≤ N⁻¹ * (‖H t x‖ / exp(2t) + (|h|/ε * ‖x‖) / exp t)` directly on
`(H t).domain` and `(S t).domain` without passing through `R_{H(t)}(a)` or `R_{S(t)}(a)`. -/
theorem direct_fixedN_hamiltonian_and_residual_radialYosida_lowerBound_norm_and_rate_on_domains
    (t N : ℝ) (hN : 0 < N) (x : (H t).domain) (y : (S t).domain) :
    (x : Hilbert) ∈ (K).domain ∧
    (x : Hilbert) ∈ (S t).domain ∧
    Real.exp (2 * t) *
        ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 -
      (h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (H t x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ∧
    -(h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (H t x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ∧
    ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ≤
      ‖H t x‖ / Real.exp (2 * t) + (|h| / ε * ‖(x : Hilbert)‖) / Real.exp t ∧
    (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re +
        N⁻¹ * (Real.exp (2 * t) *
          ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2) ≤
      (inner ℂ (H t x) (x : Hilbert)).re +
        N⁻¹ * ((h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2) ∧
    ‖(x : Hilbert) - action ε hε h N hN (x : Hilbert)‖ ≤
      N⁻¹ * (‖H t x‖ / Real.exp (2 * t) + (|h| / ε * ‖(x : Hilbert)‖) / Real.exp t) ∧
    (-(h ^ 2 / ε ^ 2) * ‖(y : Hilbert)‖ ^ 2 ≤
        (inner ℂ (S t y)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert))).re ∧
      (inner ℂ (S t y) (action ε hε h N hN (y : Hilbert))).re ≤
        (inner ℂ (S t y) (y : Hilbert)).re +
          N⁻¹ * ((h ^ 2 / ε ^ 2) * ‖(y : Hilbert)‖ ^ 2)) := by
  have hk_dom : (x : Hilbert) ∈ (K).domain :=
    KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m_mass g k t x
  have hs_dom : (x : Hilbert) ∈ (S t).domain :=
    KFCausalClockFloorHamiltonianRadialSum.residual_domain ε hε h hh hb m_mass g k t x
  have hH_low :=
    KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_operator_yosida_pairing_lower
      ε hε h hh hb m_mass g k N hN t x
  have hH_weak :=
    KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_operator_yosida_pairing_lower_weak
      ε hε h hh hb m_mass g k N hN t x
  have hcs :
      (inner ℂ (H t x)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ≤
        ‖H t x‖ * ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ :=
    le_trans (Complex.re_le_norm _)
      (norm_inner_le_norm (H t x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)))
  have he : (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    rw [sq, ← Real.exp_add, show t + t = 2 * t by ring]
  have hd : (|h| / ε * ‖(x : Hilbert)‖) ^ 2 = (h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_abs]
  have hM_bd :
      ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ≤
        ‖H t x‖ / Real.exp (2 * t) + (|h| / ε * ‖(x : Hilbert)‖) / Real.exp t := by
    have hq := quadratic_bound
      ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖
      ‖H t x‖
      (|h| / ε * ‖(x : Hilbert)‖)
      (Real.exp t)
      (norm_nonneg _)
      (by positivity)
      (Real.exp_pos t)
      (by rw [he, hd]; linarith)
    simpa only [he] using hq
  have hsub_x : (x : Hilbert) - action ε hε h N hN (x : Hilbert) =
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert) := by
    change (x : Hilbert) - ((x : Hilbert) -
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)) = _
    exact sub_sub_cancel (x : Hilbert)
      ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))
  have hre_diff_x :
      (inner ℂ (H t x) (x : Hilbert)).re -
        (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re =
      N⁻¹ * (inner ℂ (H t x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
    calc
      (inner ℂ (H t x) (x : Hilbert)).re -
          (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re
        = (inner ℂ (H t x) ((x : Hilbert) - action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_sub_right, Complex.sub_re]
      _ = (inner ℂ (H t x)
            ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [hsub_x]
      _ = N⁻¹ * (inner ℂ (H t x)
            (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_smul_right, Complex.mul_re]
            simp
  have hNinv_nn : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hJ_pair_x :
      (inner ℂ (H t x) (action ε hε h N hN (x : Hilbert))).re +
        N⁻¹ * (Real.exp (2 * t) *
          ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2) ≤
      (inner ℂ (H t x) (x : Hilbert)).re +
        N⁻¹ * ((h ^ 2 / ε ^ 2) * ‖(x : Hilbert)‖ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hH_low hNinv_nn
    linarith [hre_diff_x, hmul]
  have hrate_x :
      ‖(x : Hilbert) - action ε hε h N hN (x : Hilbert)‖ ≤
        N⁻¹ * (‖H t x‖ / Real.exp (2 * t) + (|h| / ε * ‖(x : Hilbert)‖) / Real.exp t) := by
    rw [hsub_x, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
    exact mul_le_mul_of_nonneg_left hM_bd hNinv_nn
  have hS_low :=
    KFCausalClockFloorResidualResolventRadialRootRegularity.residual_operator_yosida_pairing_lower
      ε hε h hh hb m_mass g k N hN t y
  have hsub_y : (y : Hilbert) - action ε hε h N hN (y : Hilbert) =
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert) := by
    change (y : Hilbert) - ((y : Hilbert) -
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert)) = _
    exact sub_sub_cancel (y : Hilbert)
      ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert))
  have hre_diff_y :
      (inner ℂ (S t y) (y : Hilbert)).re -
        (inner ℂ (S t y) (action ε hε h N hN (y : Hilbert))).re =
      N⁻¹ * (inner ℂ (S t y)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert))).re := by
    calc
      (inner ℂ (S t y) (y : Hilbert)).re -
          (inner ℂ (S t y) (action ε hε h N hN (y : Hilbert))).re
        = (inner ℂ (S t y) ((y : Hilbert) - action ε hε h N hN (y : Hilbert))).re := by
            rw [inner_sub_right, Complex.sub_re]
      _ = (inner ℂ (S t y)
            ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert))).re := by
            rw [hsub_y]
      _ = N⁻¹ * (inner ℂ (S t y)
            (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (y : Hilbert))).re := by
            rw [inner_smul_right, Complex.mul_re]
            simp
  have hJ_pair_y :
      (inner ℂ (S t y) (action ε hε h N hN (y : Hilbert))).re ≤
        (inner ℂ (S t y) (y : Hilbert)).re +
          N⁻¹ * ((h ^ 2 / ε ^ 2) * ‖(y : Hilbert)‖ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hS_low hNinv_nn
    linarith [hre_diff_y, hmul]
  exact ⟨hk_dom, hs_dom, hH_low, hH_weak, hM_bd, hJ_pair_x, hrate_x, ⟨hS_low, hJ_pair_y⟩⟩

/-- Concrete nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` cyclic nonagon
cocycle vanishing and `potentialPowerDomain (r + 2)` regularity across all nine nonagon legs. -/
theorem clockFloorPotentialYosidaTierSub_nine_parameter_nonagon_cocycle_and_regularity
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a i_param n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r + (i_param⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hnon := arbitraryOrderPotentialYosidaTierSub_nine_parameter_nonagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param h_param i_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_nine_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_nine_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hres hpos r j x
  exact ⟨hnon.1, hnon.2.1, hmem.2.2.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier nine-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)`
and eighteen-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇), (h_param, n₈), (i_param, n₉))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_nine_and_eighteen_parameter_cauchy_rates
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ ≤
      16 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + i_param⁻¹) *
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
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k g_param n₇ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k g_param n₇ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k h_param n₈ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k h_param n₈ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k i_param n₉ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₉ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + i_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_nine_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_eighteen_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇) (Jcut n₈) (Jcut n₉)
      a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hres hpos hlinv m j r hjm hx⟩

/-- Master Nine-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param)` Nonagon Cocycle,
Direct Fixed-`N` Full-Hamiltonian and Residual Radial-Yosida Lower Bound & Rate, and
Eighteen-Parameter Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_nineParameter_nonagon_master_synthesis
    (a b c d e f_param g_param h_param i_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a i_param n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r + (i_param⁻¹) ^ r) *
         ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ ≤
      16 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + i_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_nine_parameter_nonagon_cocycle_and_regularity
    ε hε h hh hb m_mass g k a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p n₁ r j x
  have hrates := clockFloorPotentialYosida_nine_and_eighteen_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c d e f_param g_param h_param i_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p
    n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ m j r hjm hx
  exact ⟨⟨hcoc.1, hcoc.2.1⟩, ⟨hcoc.2.2.1, hcoc.2.2.2⟩, hrates.1⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_nine_parameter_nonagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_nine_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_nine_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_seven_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_nine_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_eighteen_parameter_bound_of_le
#print axioms direct_fixedN_hamiltonian_and_residual_radialYosida_lowerBound_norm_and_rate_on_domains
#print axioms clockFloorPotentialYosidaTierSub_nine_parameter_nonagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_nine_and_eighteen_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_nineParameter_nonagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaNineParameterNonagon
