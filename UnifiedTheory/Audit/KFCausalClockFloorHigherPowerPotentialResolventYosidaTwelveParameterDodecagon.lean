/- Twelve-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
Cyclic Dodecagon Cocycle, Mixed Eleven-Hop Decomposition, Wide-Strip (`|h| ≤ π ε / 3`) Forward
Half-Shift `(h/2, 0)` Orbit-Factor Transport & Variational Potential-Domain Regularization Without
`R_P(a)` or Quarter-Strip Restriction, Seven-Operator Wide-Strip Evaluation, and Twenty-Four-Parameter
Cauchy Rate Bounds for Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaElevenParameterHendecagon

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwelveParameterDodecagon

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound)
open KFCausalClockFloorRadialResolventRegularizer (action sequence_tendsto)
open KFCausalClockFloorRadialResolventShifted (shifted_sequence_tendsto)
open KFCausalClockFloorRadialResolventSections (outputActionLp)
open KFCausalClockFloorRadialResolventShiftedPairing
  (zero_shift_bound half_shift_bound shiftedResolvent_half_pairing)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport (shiftedResolvent)
open KFCausalClockFloorRadialResolventPotential (formAction formAction_embedding)
open KFCausalClockFloorRadialResolventPotentialDomain
  (outputActionLp_pairing potentialForm_output_shifted_pairing domainFormLift
   domainFormLift_embedding domainFormLift_represents)
open KFCausalClockFloorRadialResolventGrowingDomain
  (growingHamiltonian_domain_iff growingHamiltonian_resolvent_domain_iff_potential
   growingHamiltonian_resolvent_graph_of_potential)
open KFCausalClockFloorRadialResolventMultiOperatorSynthesis
  (unconditionalCore unconditionalCore_eq_three_operator_domain
   unconditionalCore_eq_static_inter_growing
   resolvent_mem_commonOperatorDomain_of_potential_graph
   resolvent_seven_operator_eval_on_common_of_potential_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain potentialPowerDomain)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (iteratedOperatorPower)
open KFCausalClockFloorHigherPowerPotentialResolventYosidaArbitraryOrderConvergence
  (arbitraryOrderPotentialIdentityYosidaTierState
   clockFloorPotentialIdentityYosidaTierState)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate
  (arbitraryOrderPotentialResolventYosidaTierSub
   arbitraryOrderPotentialIdentityYosidaTierSub
   arbitraryOrderPotentialYosidaTierSub_norm_bounds
   arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
   clockFloorPotentialResolventYosidaTierSub
   clockFloorPotentialIdentityYosidaTierSub)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle
  (arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle
  (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le)
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaElevenParameterHendecagon
  (arbitraryOrderPotentialYosidaTierSub_eleven_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_eleven_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_nine_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_eleven_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_twenty_two_parameter_bound_of_le)

section AbstractTwelveParameterDodecagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact twelve-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
cyclic dodecagon cocycle vanishing and eleven-hop chain decomposition for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R j_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R j_param) (R k_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R i_param) (R j_param) J i_param j_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R j_param) (R k_param) J j_param k_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R a) J l_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R l_param) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R j_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R j_param) (R k_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R l_param) J a l_param r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R i_param) (R j_param) J i_param j_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R j_param) (R k_param) J j_param k_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all twelve dodecagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
`(g_param, h_param)`, `(h_param, i_param)`, `(i_param, j_param)`, `(j_param, k_param)`, `(k_param, l_param)`,
and `(a, l_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_twelve_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R j_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R j_param) (R k_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R l_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R l_param) J a l_param r j x ∈
      operatorPowerDomain P r := by
  have habcdefghijk := arbitraryOrderPotentialYosidaTierSub_eleven_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param g_param h_param i_param j_param k_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hres hlinv r j x
  have hakl := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a k_param l_param ha hk_p hl_p hres hlinv r j x
  exact ⟨habcdefghijk.1, habcdefghijk.2.1, habcdefghijk.2.2.1, habcdefghijk.2.2.2.1,
    habcdefghijk.2.2.2.2.1, habcdefghijk.2.2.2.2.2.1, habcdefghijk.2.2.2.2.2.2.1,
    habcdefghijk.2.2.2.2.2.2.2.1, habcdefghijk.2.2.2.2.2.2.2.2.1,
    habcdefghijk.2.2.2.2.2.2.2.2.2.1, hakl.2.1, hakl.2.2.1, hakl.2.2.2⟩

/-- Twelve-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
eleven-hop geometric norm bound and uniform Yosida stability for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_twelve_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R l_param) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R j_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R j_param) (R k_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R i_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R i_param) (R j_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R j_param) (R k_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        (l_param⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R i_param) (R j_param) J i_param j_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R j_param) (R k_param) J j_param k_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x‖ ≤
      22 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdefghijk := arbitraryOrderPotentialYosidaTierSub_eleven_parameter_norm_bounds
    P R J a b c d e f_param g_param h_param i_param j_param k_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hres hpos r j x
  have hakl := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a k_param l_param ha hk_p hl_p hres hpos r j x
  have hkl := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J k_param l_param hk_p hl_p hres hpos r j x
  exact ⟨by linarith [habcdefghijk.1, hakl.1], by linarith [habcdefghijk.2.1, hkl.1], by linarith [habcdefghijk.2.2, hkl.2]⟩

/-- Ten-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param)` decagon cocycle for the mixed
parameter-regularizer double difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_ten_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param) (hj_p : 0 < j_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R h_param) J₁ J₂ g_param h_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R h_param) (R i_param) J₁ J₂ h_param i_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R i_param) (R j_param) J₁ J₂ i_param j_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R a) J₁ J₂ j_param a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R h_param) J₁ J₂ g_param h_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R h_param) (R i_param) J₁ J₂ h_param i_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R i_param) (R j_param) J₁ J₂ i_param j_param r j x‖ ≤
      18 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R h_param) J₁ J₂ g_param h_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R h_param) (R i_param) J₁ J₂ h_param i_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R i_param) (R j_param) J₁ J₂ i_param j_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R a) J₁ J₂ j_param a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcdefghi := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_nine_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d e f_param g_param h_param i_param ha hb hc hd he hf_p hg_p hh_p hi_p hres hpos r j x).2
  have hij := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ i_param j_param hi_p hj_p hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Twelve-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
mediated eleven-hop Cauchy rate bound for `arbitraryOrderPotentialIdentityYosidaTierSub` on
`operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
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
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R i_param) J h_param i_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R i_param) (R j_param) J i_param j_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R j_param) (R k_param) J j_param k_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x‖ ≤
      22 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + l_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijk := arbitraryOrderPotentialIdentityYosidaTierSub_eleven_parameter_cauchy_rate_of_le
    P R J a b c d e f_param g_param h_param i_param j_param k_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hres hpos hlinv m j r hjm hx
  have hkl := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J k_param l_param hk_p hl_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint twenty-four-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇), (h_param, J₈), (i_param, J₉), (j_param, J₁₀), (k_param, J₁₁), (l_param, J₁₂))`
mediated eleven-hop Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_twenty_four_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R i_param) J₉ i_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R i_param) J₉ i_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R j_param) J₁₀ j_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R j_param) J₁₀ j_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R k_param) J₁₁ k_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R k_param) J₁₁ k_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R l_param) J₁₂ l_param r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₉ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₁₀ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₁₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₁₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + l_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijk := arbitraryOrderPotentialIdentityYosida_joint_twenty_two_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ a b c d e f_param g_param h_param i_param j_param k_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hres hpos hlinv m j r hjm hx
  have hkl := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₁₁ J₁₂ k_param l_param hk_p hl_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractTwelveParameterDodecagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m_mass g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

private theorem outputActionLp_zero_pairing (N : ℝ) (hN : 0 < N)
    (z₁ z₂ : EnergyOutputSpace) :
    inner ℂ (outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) z₁) z₂ =
      inner ℂ z₁ (outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) z₂) := by
  have hp := outputActionLp_pairing ε hε h N hN 0 (zero_shift_bound ε hε) z₁ z₂
  simpa only [neg_zero] using hp

/-- **Wide-Strip (`|h| ≤ π ε / 3`) Forward Half-Shift `(h/2, 0)` Orbit-Factor Transport, Symmetric
Half-Shift Variational Pairing, Wide-Strip Variational `Dom(P)` & `Dom(G)` Regularizer Criterion,
Wide-Strip Half-Shift Commutator Convergence, and Seven-Operator Wide-Strip Evaluation**:
1. On the **entire wide strip** `hb : |h| ≤ π ε / 3` (without any quarter-strip `|h| ≤ π ε / 6` restriction):
   - Forward half-shift `(y₀, y₁) = (h / 2, 0)` orbit-factor graph transport holds for `(Tpot).graph`
     across all `i : Fin 8` because both `|h / 2| ≤ π ε / 6` (`half_shift_bound`) and `|0| ≤ π ε / 6`
     (`zero_shift_bound`) hold on `|h| ≤ π ε / 3`;
   - Under `hshiftHalf` for the wide-strip `(h / 2, 0)` pair, for every `x : (P).domain` and `v : PV`,
     `⟪outputActionLp 0 (PB (domainFormLift x)), PB v⟫ = ⟪shiftedResolvent (-h / 2) (P x), PJ v⟫`;
   - For every `x : (P).domain` and `z : Hilbert` on the full wide strip `|h| ≤ π ε / 3`,
     `(∀ v : PV, ⟪PB (domainFormLift x), outputActionLp (h / 2) (PB v)⟫ = ⟪z, PJ v⟫) →
       (action N x, z) ∈ (P).graph ∧ action N x ∈ (P).domain ∧ action N x ∈ (G).domain`;
   - On the full wide strip `|h| ≤ π ε / 3`, the half-shifted regularizer commutator converges strongly:
     `shiftedResolvent ((n : ℝ) + 1) (-h / 2) f - action ((n : ℝ) + 1) f → 0` as `n → ∞`;
   - Whenever `(action N f, w) ∈ (P).graph` for `f ∈ commonOperatorDomain`, `action N f ∈ commonOperatorDomain`
     and `K`, `P`, `G`, `S(t)`, `H(t)`, and `clockHalf ε` evaluate explicitly on `action N f` across the
     full wide strip `|h| ≤ π ε / 3`. -/
theorem wide_strip_two_step_half_shift_potential_and_seven_operator_regularization
    (t N : ℝ) (hN : 0 < N)
    (hshiftHalf : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN (h / 2) (half_shift_bound ε h hb) (PJ v) ∧
      PB w = outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) (PB v))
    (x : (P).domain) (v : PV)
    (z_var : Hilbert)
    (hvar : ∀ v' : PV,
      inner ℂ (PB (domainFormLift ε hε h hb hh m_mass g k x))
        (outputActionLp ε hε h N hN (h / 2) (half_shift_bound ε h hb) (PB v')) =
        inner ℂ z_var (PJ v'))
    (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m_mass g k)
    (w_out : Hilbert) (hpw : (action ε hε h N hN f, w_out) ∈ (P).graph) :
    let hJcom := resolvent_mem_commonOperatorDomain_of_potential_graph
      ε hε h N hN hb hh m_mass g k hf.1.1.1 hf.2 hpw
    inner ℂ
      (outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε)
        (PB (domainFormLift ε hε h hb hh m_mass g k x)))
      (PB v) =
      inner ℂ (shiftedResolvent ε hε h N hN (-h / 2) (shift_bound ε h hb) (P x)) (PJ v) ∧
    ((action ε hε h N hN (x : Hilbert), z_var) ∈ (P).graph ∧
      action ε hε h N hN (x : Hilbert) ∈ (P).domain ∧
      action ε hε h N hN (x : Hilbert) ∈ (G).domain) ∧
    Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) f -
        action ε hε h ((n : ℝ) + 1) (by positivity) f) atTop (𝓝 0) ∧
    (action ε hε h N hN f ∈ commonOperatorDomain ε hε h hh hb m_mass g k ∧
      K ⟨action ε hε h N hN f, hJcom.1.1.2⟩ = action ε hε h N hN (K ⟨f, hf.1.1.2⟩) ∧
      P ⟨action ε hε h N hN f, hJcom.1.2⟩ = w_out ∧
      G ⟨action ε hε h N hN f,
          KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_growing
            ε hε h hh hb m_mass g k hJcom⟩ =
        action ε hε h N hN (K ⟨f, hf.1.1.2⟩) + w_out ∧
      S t ⟨action ε hε h N hN f,
          KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_residual
            ε hε h hh hb m_mass g k t hJcom⟩ =
        T ⟨action ε hε h N hN f, hJcom.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • w_out ∧
      H t ⟨action ε hε h N hN f,
          KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
            ε hε h hh hb m_mass g k t hJcom⟩ =
        T ⟨action ε hε h N hN f, hJcom.1.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (action ε hε h N hN (K ⟨f, hf.1.1.2⟩) + w_out)) := by
  let u := domainFormLift ε hε h hb hh m_mass g k x
  let w := Classical.choose (hshiftHalf v)
  have hws : PJ w = shiftedResolvent ε hε h N hN (h / 2) (half_shift_bound ε h hb) (PJ v) ∧
      PB w = outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) (PB v) :=
    Classical.choose_spec (hshiftHalf v)
  have hpair1 :
      inner ℂ (outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) (PB u)) (PB v) =
        inner ℂ (PB u) (PB w) :=
    (outputActionLp_zero_pairing ε hε h N hN (PB u) (PB v)).trans
      (congrArg (inner ℂ (PB u)) hws.2.symm)
  have hpair2 :
      inner ℂ (PB u) (PB w) =
        inner ℂ (P x) (shiftedResolvent ε hε h N hN (h / 2) (half_shift_bound ε h hb) (PJ v)) :=
    (domainFormLift_represents ε hε h hb hh m_mass g k x w).trans
      (congrArg (inner ℂ (P x)) hws.1)
  have hpair :
      inner ℂ (outputActionLp ε hε h N hN 0 (zero_shift_bound ε hε) (PB u)) (PB v) =
        inner ℂ (shiftedResolvent ε hε h N hN (-h / 2) (shift_bound ε h hb) (P x)) (PJ v) :=
    (hpair1.trans hpair2).trans
      (shiftedResolvent_half_pairing ε hε h N hN hb (P x) (PJ v)).symm
  have hchar_in : ∀ v' : PV,
      inner ℂ (PB (formAction ε hε h N hN hb hh m_mass g k u)) (PB v') =
        inner ℂ z_var (PJ v') := fun v' =>
    (potentialForm_output_shifted_pairing ε hε h N hN hb hh m_mass g k u v').trans (hvar v')
  obtain ⟨hd, he⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization PD
    (formAction ε hε h N hN hb hh m_mass g k u) z_var).mpr hchar_in
  have hg_form : (PJ (formAction ε hε h N hN hb hh m_mass g k u), z_var) ∈ (P).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨_, hd⟩, rfl, he⟩
  have hPJ_eq : PJ (formAction ε hε h N hN hb hh m_mass g k u) = action ε hε h N hN (x : Hilbert) :=
    (formAction_embedding ε hε h N hN hb hh m_mass g k u).trans
      (congrArg (action ε hε h N hN) (domainFormLift_embedding ε hε h hb hh m_mass g k x))
  have hg_P : (action ε hε h N hN (x : Hilbert), z_var) ∈ (P).graph :=
    (congrArg (fun q : Hilbert => (q, z_var) ∈ (P).graph) hPJ_eq).mp hg_form
  have hd_P : action ε hε h N hN (x : Hilbert) ∈ (P).domain :=
    LinearPMap.mem_domain_of_mem_graph hg_P
  have hd_G : action ε hε h N hN (x : Hilbert) ∈ (G).domain :=
    (growingHamiltonian_resolvent_domain_iff_potential
      ε hε h N hN hb hh m_mass g k (x : Hilbert)).mpr hd_P
  have hcomm : Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) f -
        action ε hε h ((n : ℝ) + 1) (by positivity) f) atTop (𝓝 0) := by
    have h1 := shifted_sequence_tendsto ε hε h (-h / 2) (shift_bound ε h hb) f
    have h2 := sequence_tendsto ε hε h f
    simpa only [sub_self] using h1.sub h2
  have hev7 := resolvent_seven_operator_eval_on_common_of_potential_graph
    ε hε h N hN hb hh m_mass g k t hf hpw
  exact ⟨hpair, ⟨hg_P, hd_P, hd_G⟩, hcomm,
    ⟨hev7.1, hev7.2.2.1, hev7.2.2.2.1, hev7.2.2.2.2.1, hev7.2.2.2.2.2.1, hev7.2.2.2.2.2.2.1⟩⟩

/-- Concrete twelve-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
cyclic dodecagon cocycle vanishing and `potentialPowerDomain (r + 2)` regularity across all twelve
dodecagon legs. -/
theorem clockFloorPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle_and_regularity
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a l_param n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        (l_param⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hdod := arbitraryOrderPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_twelve_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_twelve_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos r j x
  exact ⟨hdod.1, hdod.2.1, hmem.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier twelve-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
and twenty-four-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇), (h_param, n₈), (i_param, n₉), (j_param, n₁₀), (k_param, n₁₁), (l_param, n₁₂))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_twelve_and_twenty_four_parameter_cauchy_rates
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ n₁₂ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ ≤
      22 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + l_param⁻¹) *
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
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k i_param n₉ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k i_param n₉ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k j_param n₁₀ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k j_param n₁₀ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k k_param n₁₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k k_param n₁₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k l_param n₁₂ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₉ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₁₀ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₁₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₁₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + l_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have h1 := arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
    P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos hlinv m j r hjm hx
  have h2 := arbitraryOrderPotentialIdentityYosida_joint_twenty_four_parameter_bound_of_le
    P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇) (Jcut n₈) (Jcut n₉) (Jcut n₁₀) (Jcut n₁₁) (Jcut n₁₂)
    a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos hlinv m j r hjm hx
  exact ⟨h1, h2⟩

/-- Master Twelve-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param)`
Dodecagon Cocycle, Unconditional Growing-Hamiltonian Decomposition `Dom(G) = Dom(K) ∩ Dom(P)`,
Wide-Strip Half-Shift Commutator Convergence, and Twenty-Four-Parameter Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_twelveParameter_dodecagon_master_synthesis
    (a b c d e f_param g_param h_param i_param j_param k_param l_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (n₁ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (∀ z : Hilbert, z ∈ (G).domain ↔ z ∈ (K).domain ∧ z ∈ (P).domain) ∧
    unconditionalCore ε hε h hb hh m_mass g k = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
    unconditionalCore ε hε h hb hh m_mass g k = (T).domain ⊓ (G).domain ∧
    Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) x -
        action ε hε h ((n : ℝ) + 1) (by positivity) x) atTop (𝓝 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param a n₁ r j x = 0 ∧
     clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a l_param n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
         2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
         (l_param⁻¹) ^ r) *
         ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param i_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k i_param j_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k j_param k_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ ≤
      22 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + l_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hcomm : Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) x -
        action ε hε h ((n : ℝ) + 1) (by positivity) x) atTop (𝓝 0) := by
    have h1 := shifted_sequence_tendsto ε hε h (-h / 2) (shift_bound ε h hb) x
    have h2 := sequence_tendsto ε hε h x
    simpa only [sub_self] using h1.sub h2
  exact ⟨growingHamiltonian_domain_iff ε hε h hb hh m_mass g k,
    unconditionalCore_eq_three_operator_domain ε hε h hb hh m_mass g k,
    unconditionalCore_eq_static_inter_growing ε hε h hb hh m_mass g k,
    hcomm,
    clockFloorPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle_and_regularity
      ε hε h hh hb m_mass g k a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p n₁ r j x,
    arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos hlinv m j r hjm hx⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_twelve_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_twelve_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_ten_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_twenty_four_parameter_bound_of_le
#print axioms wide_strip_two_step_half_shift_potential_and_seven_operator_regularization
#print axioms clockFloorPotentialYosidaTierSub_twelve_parameter_dodecagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_twelve_and_twenty_four_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_twelveParameter_dodecagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwelveParameterDodecagon
