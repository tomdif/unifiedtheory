/- Thirteen-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
Cyclic Tridecagon Cocycle, Mixed Twelve-Hop Decomposition, Unconditional Wide-Strip (`|h| ≤ π ε / 3`)
Potential-Form Output Graph & Domain Regularization (`(J_N x, L_N^{-h/2}(PB(formLift x))) ∈ Graph(T_pot)`,
`J_N x ∈ Dom(K) ∩ Dom(T_pot)`), Unconditional Wide-Strip Output-Shift Commutator & Variational Form
Pairing Convergence (`⟪PB(formAction J_n(formLift x)), PB v⟫ → ⟪P x, PJ v⟫` with Zero `hshift` or
Quarter-Strip Hypotheses), and Twenty-Six-Parameter Cauchy Rate Bounds for Arbitrary-Order
Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwelveParameterDodecagon

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThirteenParameterTridecagon

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound)
open KFCausalClockFloorRadialResolventRegularizer (action sequence_tendsto radial_domain)
open KFCausalClockFloorRadialResolventShifted (shifted_sequence_tendsto)
open KFCausalClockFloorRadialResolventSections (outputActionLp output_section_tendsto)
open KFCausalClockFloorRadialResolventShiftedPairing
  (zero_shift_bound half_shift_bound)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport (shiftedResolvent)
open KFCausalClockFloorRadialResolventPotential
  (formAction formAction_embedding formAction_output graph_action domain_action)
open KFCausalClockFloorRadialResolventPotentialForm (form_sequence_tendsto)
open KFCausalClockFloorRadialResolventPotentialDomain
  (domainFormLift domainFormLift_embedding domainFormLift_represents)
open KFCausalClockFloorRadialResolventGrowingDomain (growingHamiltonian_domain_iff)
open KFCausalClockFloorRadialResolventMultiOperatorSynthesis
  (unconditionalCore unconditionalCore_eq_three_operator_domain
   unconditionalCore_eq_static_inter_growing)
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
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwelveParameterDodecagon
  (arbitraryOrderPotentialYosidaTierSub_twelve_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_twelve_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_ten_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_twenty_four_parameter_bound_of_le)

section AbstractThirteenParameterTridecagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
cyclic tridecagon cocycle vanishing and twelve-hop chain decomposition for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ) (r j : ℕ) (x : H) :
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
      arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R a) J r j x = 0 ∧
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
      arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R m_param) (R a) J m_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R m_param) J r j x =
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
        arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R m_param) J a m_param r j x =
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
        arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all thirteen tridecagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
`(g_param, h_param)`, `(h_param, i_param)`, `(i_param, j_param)`, `(j_param, k_param)`, `(k_param, l_param)`,
`(l_param, m_param)`, and `(a, m_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R m_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R m_param) J a m_param r j x ∈
      operatorPowerDomain P r := by
  have habcdefghijkl := arbitraryOrderPotentialYosidaTierSub_twelve_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hlinv r j x
  have halm := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a l_param m_param ha hl_p hm_p hres hlinv r j x
  exact ⟨habcdefghijkl.1, habcdefghijkl.2.1, habcdefghijkl.2.2.1, habcdefghijkl.2.2.2.1,
    habcdefghijkl.2.2.2.2.1, habcdefghijkl.2.2.2.2.2.1, habcdefghijkl.2.2.2.2.2.2.1,
    habcdefghijkl.2.2.2.2.2.2.2.1, habcdefghijkl.2.2.2.2.2.2.2.2.1,
    habcdefghijkl.2.2.2.2.2.2.2.2.2.1, habcdefghijkl.2.2.2.2.2.2.2.2.2.2.1,
    halm.2.1, halm.2.2.1, halm.2.2.2⟩

/-- Thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
twelve-hop geometric norm bound and uniform Yosida stability for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R m_param) J r j x‖ ≤
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
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x‖ ∧
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
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R k_param) (R l_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        2 * (l_param⁻¹) ^ r + (m_param⁻¹) ^ r) *
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
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x‖ ≤
      24 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdefghijkl := arbitraryOrderPotentialYosidaTierSub_twelve_parameter_norm_bounds
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos r j x
  have halm := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a l_param m_param ha hl_p hm_p hres hpos r j x
  have hlm := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J l_param m_param hl_p hm_p hres hpos r j x
  exact ⟨by linarith [habcdefghijkl.1, halm.1], by linarith [habcdefghijkl.2.1, hlm.1], by linarith [habcdefghijkl.2.2, hlm.2]⟩

/-- Eleven-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param)` hendecagon cocycle for the mixed
parameter-regularizer double difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_eleven_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (hj_p : 0 < j_param) (hk_p : 0 < k_param)
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
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R k_param) J₁ J₂ j_param k_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R k_param) (R a) J₁ J₂ k_param a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R h_param) J₁ J₂ g_param h_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R h_param) (R i_param) J₁ J₂ h_param i_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R i_param) (R j_param) J₁ J₂ i_param j_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R k_param) J₁ J₂ j_param k_param r j x‖ ≤
      20 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
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
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R k_param) J₁ J₂ j_param k_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R k_param) (R a) J₁ J₂ k_param a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcdefghij := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_ten_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d e f_param g_param h_param i_param j_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hres hpos r j x).2
  have hjk := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ j_param k_param hj_p hk_p hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
mediated twelve-hop Cauchy rate bound for `arbitraryOrderPotentialIdentityYosidaTierSub` on
`operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_thirteen_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
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
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R k_param) (R l_param) J k_param l_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x‖ ≤
      24 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + m_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijkl := arbitraryOrderPotentialIdentityYosidaTierSub_twelve_parameter_cauchy_rate_of_le
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos hlinv m j r hjm hx
  have hlm := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J l_param m_param hl_p hm_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint twenty-six-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇), (h_param, J₈), (i_param, J₉), (j_param, J₁₀), (k_param, J₁₁), (l_param, J₁₂), (m_param, J₁₃))`
mediated twelve-hop Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_twenty_six_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ J₁₃ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R l_param) J₁₂ l_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R l_param) J₁₂ l_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R m_param) J₁₃ m_param r j x‖ ≤
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
        2 * ‖J₁₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₁₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + m_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijkl := arbitraryOrderPotentialIdentityYosida_joint_twenty_four_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos hlinv m j r hjm hx
  have hlm := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₁₂ J₁₃ l_param m_param hl_p hm_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractThirteenParameterTridecagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m_mass g k
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

private theorem closedGraphForm_mem_graph {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (D : KFCausalClosedGraphForm.Data X Y) (u : KFCausalClosedGraphForm.FormSpace D) :
    (KFCausalClosedGraphForm.embedding D u, KFCausalClosedGraphForm.energyOutput D u) ∈
      D.operator.graph :=
  u.property

private theorem clm_tendsto_comp {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : X →L[ℂ] Y) (seq : ℕ → X) (u : X)
    (hseq : Tendsto seq atTop (𝓝 u)) :
    Tendsto (fun n : ℕ => L (seq n)) atTop (𝓝 (L u)) :=
  (L.continuous.tendsto u).comp hseq

private theorem inner_tendsto_of_tendsto_left {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (seq : ℕ → Y) (y₀ w : Y) (target : ℂ)
    (hseq : Tendsto seq atTop (𝓝 y₀))
    (hrep : inner ℂ y₀ w = target) :
    Tendsto (fun n : ℕ => inner ℂ (seq n) w) atTop (𝓝 target) := by
  rw [← hrep]
  exact Filter.Tendsto.inner hseq tendsto_const_nhds

/-- **Unconditional Wide-Strip (`|h| ≤ π ε / 3`) Potential-Form Output Graph & Domain Regularization,
Output-Shift Commutator Convergence, and Variational Form Pairing Convergence (`⟪PB(formAction J_n(formLift x)), PB v⟫ → ⟪P x, PJ v⟫`
With Zero `hshift`, `hshiftHalf`, or Quarter-Strip Hypotheses)**:
On the full wide strip `hb : |h| ≤ π ε / 3`, for every `x : (P).domain`, `v : PV`, and `z : EnergyOutputSpace`:
1. `((x : Hilbert), PB (domainFormLift x)) ∈ (Tpot).graph` and
   `(action N (x : Hilbert), outputActionLp N (-h / 2) (PB (domainFormLift x))) ∈ (Tpot).graph`;
2. `action N (x : Hilbert) ∈ (K).domain ∧ action N (x : Hilbert) ∈ (Tpot).domain`;
3. `outputActionLp ((n : ℝ) + 1) (-h / 2) z - outputActionLp ((n : ℝ) + 1) 0 z → 0` and
   `outputActionLp ((n : ℝ) + 1) (h / 2) z - outputActionLp ((n : ℝ) + 1) (-h / 2) z → 0` in `EnergyOutputSpace`;
4. `PB (formAction ((n : ℝ) + 1) (domainFormLift x)) → PB (domainFormLift x)` in `EnergyOutputSpace`;
5. `inner ℂ (PB (formAction ((n : ℝ) + 1) (domainFormLift x))) (PB v) → inner ℂ (P x) (PJ v)` as `n → ∞`. -/
theorem unconditional_wide_strip_potential_form_output_and_variational_pairing_convergence
    (N : ℝ) (hN : 0 < N) (x : (P).domain) (v : PV) (z : EnergyOutputSpace) :
    let u := domainFormLift ε hε h hb hh m_mass g k x
    ((x : Hilbert), PB u) ∈ (Tpot).graph ∧
    (action ε hε h N hN (x : Hilbert),
      outputActionLp ε hε h N hN (-h / 2) (shift_bound ε h hb) (PB u)) ∈ (Tpot).graph ∧
    (action ε hε h N hN (x : Hilbert) ∈ (K).domain ∧
      action ε hε h N hN (x : Hilbert) ∈ (Tpot).domain) ∧
    Tendsto (fun n : ℕ =>
      outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) z -
        outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) 0 (zero_shift_bound ε hε) z)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (h / 2) (half_shift_bound ε h hb) z -
        outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) z)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      PB (formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u))
      atTop (𝓝 (PB u)) ∧
    Tendsto (fun n : ℕ =>
      inner ℂ (PB (formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u)) (PB v))
      atTop (𝓝 (inner ℂ (P x) (PJ v))) := by
  intro u
  have hu_graph : (PJ u, PB u) ∈ (Tpot).graph := closedGraphForm_mem_graph PD u
  have hx_graph : ((x : Hilbert), PB u) ∈ (Tpot).graph :=
    (congrArg (fun q : Hilbert => (q, PB u) ∈ (Tpot).graph)
      (domainFormLift_embedding ε hε h hb hh m_mass g k x)).mp hu_graph
  have hact_graph :
      (action ε hε h N hN (x : Hilbert),
        outputActionLp ε hε h N hN (-h / 2) (shift_bound ε h hb) (PB u)) ∈ (Tpot).graph :=
    graph_action ε hε h N hN hb hh m_mass g k (x : Hilbert) (PB u) hx_graph
  have hx_dom : (x : Hilbert) ∈ (Tpot).domain :=
    LinearPMap.mem_domain_of_mem_graph hx_graph
  have hact_dom :
      action ε hε h N hN (x : Hilbert) ∈ (K).domain ∧
      action ε hε h N hN (x : Hilbert) ∈ (Tpot).domain :=
    ⟨radial_domain ε hε h N hN (x : Hilbert),
     domain_action ε hε h N hN hb hh m_mass g k (x : Hilbert) hx_dom⟩
  have h_neghalf := output_section_tendsto ε hε h (-h / 2) (shift_bound ε h hb) z
  have h_zero := output_section_tendsto ε hε h 0 (zero_shift_bound ε hε) z
  have h_poshalf := output_section_tendsto ε hε h (h / 2) (half_shift_bound ε h hb) z
  have hcomm1 : Tendsto (fun n : ℕ =>
      outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) z -
        outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) 0 (zero_shift_bound ε hε) z)
      atTop (𝓝 0) := by
    simpa only [sub_self] using h_neghalf.sub h_zero
  have hcomm2 : Tendsto (fun n : ℕ =>
      outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (h / 2) (half_shift_bound ε h hb) z -
        outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) z)
      atTop (𝓝 0) := by
    simpa only [sub_self] using h_poshalf.sub h_neghalf
  have hform_out : Tendsto (fun n : ℕ =>
      PB (formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u))
      atTop (𝓝 (PB u)) :=
    clm_tendsto_comp PB
      (fun n : ℕ => formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u)
      u (form_sequence_tendsto ε hε h hb hh m_mass g k u)
  have hinner_tendsto : Tendsto (fun n : ℕ =>
      inner ℂ (PB (formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u)) (PB v))
      atTop (𝓝 (inner ℂ (P x) (PJ v))) :=
    inner_tendsto_of_tendsto_left
      (fun n : ℕ => PB (formAction ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k u))
      (PB u) (PB v) (inner ℂ (P x) (PJ v))
      hform_out (domainFormLift_represents ε hε h hb hh m_mass g k x v)
  exact ⟨hx_graph, hact_graph, hact_dom, hcomm1, hcomm2, hform_out, hinner_tendsto⟩

/-- Concrete thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
cyclic tridecagon cocycle vanishing and `potentialPowerDomain (r + 2)` regularity across all thirteen
tridecagon legs. -/
theorem clockFloorPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle_and_regularity
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
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
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param a n r j x = 0 ∧
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
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a m_param n (r + 1) j x ∈
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
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        2 * (l_param⁻¹) ^ r + (m_param⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have htri := arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hres hpos r j x
  exact ⟨htri.1, htri.2.1, hmem.2.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
and twenty-six-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇), (h_param, n₈), (i_param, n₉), (j_param, n₁₀), (k_param, n₁₁), (l_param, n₁₂), (m_param, n₁₃))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_thirteen_and_twenty_six_parameter_cauchy_rates
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ n₁₂ n₁₃ m j r : ℕ) (hjm : j ≤ m)
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
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ ≤
      24 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + m_param⁻¹) *
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
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k l_param n₁₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k l_param n₁₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k m_param n₁₃ r j x‖ ≤
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
        2 * ‖Jcut n₁₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₁₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + m_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have h1 := arbitraryOrderPotentialIdentityYosidaTierSub_thirteen_parameter_cauchy_rate_of_le
    P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hres hpos hlinv m j r hjm hx
  have h2 := arbitraryOrderPotentialIdentityYosida_joint_twenty_six_parameter_bound_of_le
    P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇) (Jcut n₈) (Jcut n₉) (Jcut n₁₀) (Jcut n₁₁) (Jcut n₁₂) (Jcut n₁₃)
    a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hres hpos hlinv m j r hjm hx
  exact ⟨h1, h2⟩

/-- Master Thirteen-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`
Tridecagon Cocycle, Unconditional Growing-Hamiltonian Decomposition `Dom(G) = Dom(K) ∩ Dom(P)`,
Wide-Strip Half-Shift Commutator Convergence, and Twenty-Six-Parameter Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_thirteenParameter_tridecagon_master_synthesis
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param)
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
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param a n₁ r j x = 0 ∧
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
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param a n₁ r j x = 0 ∧
     clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a m_param n₁ (r + 1) j x ∈
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
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
         2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
         2 * (l_param⁻¹) ^ r + (m_param⁻¹) ^ r) *
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
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k k_param l_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ ≤
      24 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + m_param⁻¹) *
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
    clockFloorPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle_and_regularity
      ε hε h hh hb m_mass g k a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n₁ r j x,
    arbitraryOrderPotentialIdentityYosidaTierSub_thirteen_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hres hpos hlinv m j r hjm hx⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_thirteen_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_eleven_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_thirteen_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_twenty_six_parameter_bound_of_le
#print axioms unconditional_wide_strip_potential_form_output_and_variational_pairing_convergence
#print axioms clockFloorPotentialYosidaTierSub_thirteen_parameter_tridecagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_thirteen_and_twenty_six_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_thirteenParameter_tridecagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThirteenParameterTridecagon
