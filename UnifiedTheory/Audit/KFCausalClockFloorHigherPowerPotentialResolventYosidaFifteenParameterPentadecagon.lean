/- Fifteen-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
Cyclic Pentadecagon Cocycle, Mixed Fourteen-Hop Decomposition, Unconditional Wide-Strip (`|h| ≤ π ε / 3`)
Time-Dependent Residual-Form (`SV t`), Residual-Hamiltonian (`S(t)`), and Full-Hamiltonian (`H(t)`)
Output Graph Regularization, Exact Residual-to-Static and Residual-to-Potential Form Lift Coherence
(`staticLift t (formLift (SD t) ⟨f, hfS⟩) = staticDomainFormLift ⟨f, hfT⟩` and
`potentialLift t (formLift (SD t) ⟨f, hfS⟩) = potentialDomainFormLift ⟨f, hfP⟩`),
Unconditional Wide-Strip Residual-Form Variational Pairing Convergence
(`⟪SB t (residualFormAction J_n (formLift (SD t) x_res)), SB t v_res⟫ → ⟪S(t) x_res, SJ t v_res⟫`),
and Unconditional Wide-Strip Operator Output Convergence for Both `S(t)` and `H(t)`
(`T ⟨J_n f, ...⟩ + e^{2t} L_n^{-h/2}(P f) → S(t) f`, `J_n(T f) + e^{2t} J_n(P f) → S(t) f`,
`T ⟨J_n f, ...⟩ + e^{2t}(K ⟨J_n f, ...⟩ + L_n^{-h/2}(P f)) → H(t) f`, and
`J_n(T f) + e^{2t}(J_n(K f) + J_n(P f)) → H(t) f` with Zero Quarter-Strip `hbn` or `hshift` Hypotheses),
and Thirty-Parameter Cauchy Rate Bounds for Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourteenParameterTetradecagon

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFifteenParameterPentadecagon

noncomputable section

open Filter
open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaOrderedTransport (shift_bound)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventOperator (operator_sequence_tendsto)
open KFCausalClockFloorRadialResolventShifted (shifted_sequence_tendsto)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport (shiftedResolvent)
open KFCausalClockFloorResidualFormSplit
  (staticLift potentialLift staticLift_embedding potentialLift_embedding)
open KFCausalClockFloorRadialResolventStaticRadialCore
  (static_resolvent_domain static_resolvent_tendsto)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_residual common_domain_subset_hamiltonian)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph unconditional_three_operator_hamiltonian_graph)
open KFCausalClockFloorRadialResolventMultiOperatorSynthesis
  (commonOperatorDomain_eq_unconditionalCore_inf_residualForm)
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
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourteenParameterTetradecagon
  (arbitraryOrderPotentialYosidaTierSub_fourteen_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_fourteen_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_twelve_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_fourteen_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_twenty_eight_parameter_bound_of_le)

section AbstractFifteenParameterPentadecagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact fifteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
cyclic pentadecagon cocycle vanishing and fourteen-hop chain decomposition for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ) (r j : ℕ) (x : H) :
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
      arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R n_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R n_param) (R o_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R o_param) (R a) J r j x = 0 ∧
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
      arbitraryOrderPotentialIdentityYosidaTierSub P (R m_param) (R n_param) J m_param n_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R n_param) (R o_param) J n_param o_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R o_param) (R a) J o_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R o_param) J r j x =
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
        arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R n_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R n_param) (R o_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R o_param) J a o_param r j x =
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
        arbitraryOrderPotentialIdentityYosidaTierSub P (R m_param) (R n_param) J m_param n_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R n_param) (R o_param) J n_param o_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all fifteen pentadecagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
`(g_param, h_param)`, `(h_param, i_param)`, `(i_param, j_param)`, `(j_param, k_param)`, `(k_param, l_param)`,
`(l_param, m_param)`, `(m_param, n_param)`, `(n_param, o_param)`, and `(a, o_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R n_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R n_param) (R o_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R o_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R o_param) J a o_param r j x ∈
      operatorPowerDomain P r := by
  have habcdefghijklmn := arbitraryOrderPotentialYosidaTierSub_fourteen_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p hres hlinv r j x
  have hano := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a n_param o_param ha hn_p ho_p hres hlinv r j x
  exact ⟨habcdefghijklmn.1, habcdefghijklmn.2.1, habcdefghijklmn.2.2.1, habcdefghijklmn.2.2.2.1,
    habcdefghijklmn.2.2.2.2.1, habcdefghijklmn.2.2.2.2.2.1, habcdefghijklmn.2.2.2.2.2.2.1,
    habcdefghijklmn.2.2.2.2.2.2.2.1, habcdefghijklmn.2.2.2.2.2.2.2.2.1,
    habcdefghijklmn.2.2.2.2.2.2.2.2.2.1, habcdefghijklmn.2.2.2.2.2.2.2.2.2.2.1,
    habcdefghijklmn.2.2.2.2.2.2.2.2.2.2.2.1, habcdefghijklmn.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hano.2.1, hano.2.2.1, hano.2.2.2⟩

/-- Fifteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
fourteen-hop geometric norm bound and uniform Yosida stability for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R o_param) J r j x‖ ≤
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
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R n_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R n_param) (R o_param) J r j x‖ ∧
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
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R l_param) (R m_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R m_param) (R n_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R n_param) (R o_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        2 * (l_param⁻¹) ^ r + 2 * (m_param⁻¹) ^ r + 2 * (n_param⁻¹) ^ r + (o_param⁻¹) ^ r) *
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
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R m_param) (R n_param) J m_param n_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R n_param) (R o_param) J n_param o_param r j x‖ ≤
      28 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdefghijklmn := arbitraryOrderPotentialYosidaTierSub_fourteen_parameter_norm_bounds
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p hres hpos r j x
  have hano := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a n_param o_param ha hn_p ho_p hres hpos r j x
  have hno := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J n_param o_param hn_p ho_p hres hpos r j x
  exact ⟨by linarith [habcdefghijklmn.1, hano.1], by linarith [habcdefghijklmn.2.1, hno.1], by linarith [habcdefghijklmn.2.2, hno.2]⟩

/-- Thirteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)` tridecagon cocycle for the mixed
parameter-regularizer double difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_thirteen_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param) (hi_p : 0 < i_param)
    (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
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
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R k_param) (R l_param) J₁ J₂ k_param l_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R l_param) (R m_param) J₁ J₂ l_param m_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R m_param) (R a) J₁ J₂ m_param a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R g_param) J₁ J₂ f_param g_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R g_param) (R h_param) J₁ J₂ g_param h_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R h_param) (R i_param) J₁ J₂ h_param i_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R i_param) (R j_param) J₁ J₂ i_param j_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R j_param) (R k_param) J₁ J₂ j_param k_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R k_param) (R l_param) J₁ J₂ k_param l_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R l_param) (R m_param) J₁ J₂ l_param m_param r j x‖ ≤
      24 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
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
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R k_param) (R l_param) J₁ J₂ k_param l_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R l_param) (R m_param) J₁ J₂ l_param m_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R m_param) (R a) J₁ J₂ m_param a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcdefghijkl := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_twelve_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d e f_param g_param h_param i_param j_param k_param l_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hres hpos r j x).2
  have hlm := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ l_param m_param hl_p hm_p hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Fifteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
mediated fourteen-hop Cauchy rate bound for `arbitraryOrderPotentialIdentityYosidaTierSub` on
`operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_fifteen_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
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
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R l_param) (R m_param) J l_param m_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R m_param) (R n_param) J m_param n_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R n_param) (R o_param) J n_param o_param r j x‖ ≤
      28 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + 2 * m_param⁻¹ +
          2 * n_param⁻¹ + o_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijklmn := arbitraryOrderPotentialIdentityYosidaTierSub_fourteen_parameter_cauchy_rate_of_le
    P R J a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p hres hpos hlinv m j r hjm hx
  have hno := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J n_param o_param hn_p ho_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint thirty-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇), (h_param, J₈), (i_param, J₉), (j_param, J₁₀), (k_param, J₁₁), (l_param, J₁₂), (m_param, J₁₃), (n_param, J₁₄), (o_param, J₁₅))`
mediated fourteen-hop Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_thirty_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ J₁₃ J₁₄ J₁₅ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R m_param) J₁₃ m_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R m_param) J₁₃ m_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R n_param) J₁₄ n_param r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R n_param) J₁₄ n_param r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R o_param) J₁₅ o_param r j x‖ ≤
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
        2 * ‖J₁₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₁₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₁₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + 2 * m_param⁻¹ +
          2 * n_param⁻¹ + o_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefghijklmn := arbitraryOrderPotentialIdentityYosida_joint_twenty_eight_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ J₁₀ J₁₁ J₁₂ J₁₃ J₁₄ a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param ha hb hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p hres hpos hlinv m j r hjm hx
  have hno := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₁₄ J₁₅ n_param o_param hn_p ho_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractFifteenParameterPentadecagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m_mass g k 0
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m_mass g k
local notation "SJ" => fun t : ℝ => KFCausalClosedGraphForm.embedding (SD t)
local notation "SB" => fun t : ℝ => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m_mass g k
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

private theorem tendsto_of_tendsto_of_eq {X : Type*} [TopologicalSpace X]
    (seq : ℕ → X) (a b : X) (hseq : Tendsto seq atTop (𝓝 a)) (heq : a = b) :
    Tendsto seq atTop (𝓝 b) := by
  rw [← heq]
  exact hseq

/-- **Unconditional Wide-Strip (`|h| ≤ π ε / 3`) Time-Dependent Residual-Form (`SV t`),
Residual-Hamiltonian (`S(t)`), and Full-Hamiltonian (`H(t)`) Output Graph Regularization,
Exact Residual-to-Static and Residual-to-Potential Form Lift Coherence, Unconditional Wide-Strip
Residual-Form Variational Pairing Convergence (`⟪SB t (residualFormAction J_n (formLift (SD t) x_res)), SB t v_res⟫ → ⟪S(t) x_res, SJ t v_res⟫`),
and Unconditional Wide-Strip Operator Output Convergence for Both `S(t)` and `H(t)`
With Zero Quarter-Strip `hbn` or `hshift` Hypotheses**:
On the full wide strip `hb : |h| ≤ π ε / 3`, for every `t : ℝ`, `x_res : (S t).domain`, `v_res : SV t`,
and `f ∈ commonOperatorDomain`:
1. `((x_res : Hilbert), SB t (formLift (SD t) x_res)) ∈ (Tres t).graph` and
   `(action N (x_res : Hilbert), SB t (residualFormAction N (formLift (SD t) x_res))) ∈ (Tres t).graph`;
2. `inner ℂ (SB t (residualFormAction ((n : ℝ) + 1) (formLift (SD t) x_res))) (SB t v_res) → inner ℂ (S t x_res) (SJ t v_res)` as `n → ∞`;
3. `staticLift t (formLift (SD t) ⟨f, hfS⟩) = staticDomainFormLift ⟨f, hfT⟩` and
   `potentialLift t (formLift (SD t) ⟨f, hfS⟩) = potentialDomainFormLift ⟨f, hfP⟩`;
4. `T ⟨action ((n : ℝ) + 1) f, ...⟩ + e^{2t} • shiftedResolvent ((n : ℝ) + 1) (-h / 2) (P ⟨f, hfP⟩) → S t ⟨f, hfS⟩` and
   `action ((n : ℝ) + 1) (T ⟨f, hfT⟩) + e^{2t} • action ((n : ℝ) + 1) (P ⟨f, hfP⟩) → S t ⟨f, hfS⟩`;
5. `T ⟨action ((n : ℝ) + 1) f, ...⟩ + e^{2t} • (K ⟨action ((n : ℝ) + 1) f, ...⟩ + shiftedResolvent ((n : ℝ) + 1) (-h / 2) (P ⟨f, hfP⟩)) → H t ⟨f, hfH⟩` and
   `action ((n : ℝ) + 1) (T ⟨f, hfT⟩) + e^{2t} • (action ((n : ℝ) + 1) (K ⟨f, hfK⟩) + action ((n : ℝ) + 1) (P ⟨f, hfP⟩)) → H t ⟨f, hfH⟩`. -/
theorem unconditional_wide_strip_residual_and_full_hamiltonian_convergence
    (t N : ℝ) (hN : 0 < N) (x_res : (S t).domain) (v_res : SV t)
    {f : Hilbert} (hf : f ∈ commonOperatorDomain ε hε h hh hb m_mass g k) :
    let u_res := KFCausalClosedGraphForm.formLift (SD t) x_res
    let hfT : f ∈ (T).domain := hf.1.1.1
    let hfK : f ∈ (K).domain := hf.1.1.2
    let hfP : f ∈ (P).domain := hf.1.2
    let hfS : f ∈ (S t).domain := common_domain_subset_residual ε hε h hh hb m_mass g k t hf
    let hfH : f ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m_mass g k t hf
    let ufS := KFCausalClosedGraphForm.formLift (SD t) ⟨f, hfS⟩
    ((x_res : Hilbert), SB t u_res) ∈ (Tres t).graph ∧
    (action ε hε h N hN (x_res : Hilbert),
      SB t (KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m_mass g k t u_res)) ∈ (Tres t).graph ∧
    Tendsto (fun n : ℕ =>
      inner ℂ (SB t (KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k t u_res)) (SB t v_res))
      atTop (𝓝 (inner ℂ (S t x_res) (SJ t v_res))) ∧
    staticLift ε hε h hh hw m_mass g k t ufS =
      KFCausalClockFloorRadialResolventStaticDomain.domainFormLift ε hε h hb hh m_mass g k ⟨f, hfT⟩ ∧
    potentialLift ε hε h hh hw m_mass g k t ufS =
      KFCausalClockFloorRadialResolventPotentialDomain.domainFormLift ε hε h hb hh m_mass g k ⟨f, hfP⟩ ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩ +
        (Real.exp (2 * t) : ℂ) •
          shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb)
            (P ⟨f, hfP⟩))
      atTop (𝓝 (S t ⟨f, hfS⟩)) ∧
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (T ⟨f, hfT⟩) +
        (Real.exp (2 * t) : ℂ) •
          action ε hε h ((n : ℝ) + 1) (by positivity) (P ⟨f, hfP⟩))
      atTop (𝓝 (S t ⟨f, hfS⟩)) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩ +
        (Real.exp (2 * t) : ℂ) •
          (K ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
            radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩ +
            shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb)
              (P ⟨f, hfP⟩)))
      atTop (𝓝 (H t ⟨f, hfH⟩)) ∧
    Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (T ⟨f, hfT⟩) +
        (Real.exp (2 * t) : ℂ) •
          (action ε hε h ((n : ℝ) + 1) (by positivity) (K ⟨f, hfK⟩) +
            action ε hε h ((n : ℝ) + 1) (by positivity) (P ⟨f, hfP⟩)))
      atTop (𝓝 (H t ⟨f, hfH⟩)) := by
  intro u_res hfT hfK hfP hfS hfH ufS
  have huJ : SJ t u_res = (x_res : Hilbert) :=
    KFCausalClosedGraphForm.embedding_formLift (SD t) x_res
  have hu_graph : (SJ t u_res, SB t u_res) ∈ (Tres t).graph :=
    closedGraphForm_mem_graph (SD t) u_res
  have hx_graph : ((x_res : Hilbert), SB t u_res) ∈ (Tres t).graph :=
    (congrArg (fun q : Hilbert => (q, SB t u_res) ∈ (Tres t).graph) huJ).mp hu_graph
  let uN := KFCausalClockFloorRadialResolventResidual.formAction ε hε h N hN hb hh m_mass g k t u_res
  have huN_graph : (SJ t uN, SB t uN) ∈ (Tres t).graph :=
    closedGraphForm_mem_graph (SD t) uN
  have huN_emb : SJ t uN = action ε hε h N hN (x_res : Hilbert) :=
    (KFCausalClockFloorRadialResolventResidual.formAction_embedding ε hε h N hN hb hh m_mass g k t u_res).trans
      (congrArg (action ε hε h N hN) huJ)
  have hact_graph :
      (action ε hε h N hN (x_res : Hilbert), SB t uN) ∈ (Tres t).graph :=
    (congrArg (fun q : Hilbert => (q, SB t uN) ∈ (Tres t).graph) huN_emb).mp huN_graph
  have hform_out : Tendsto (fun n : ℕ =>
      SB t (KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k t u_res))
      atTop (𝓝 (SB t u_res)) :=
    clm_tendsto_comp (SB t)
      (fun n : ℕ => KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k t u_res)
      u_res (KFCausalClockFloorRadialResolventResidual.form_sequence_tendsto ε hε h hb hh m_mass g k t u_res)
  have hinner_tendsto : Tendsto (fun n : ℕ =>
      inner ℂ (SB t (KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k t u_res)) (SB t v_res))
      atTop (𝓝 (inner ℂ (S t x_res) (SJ t v_res))) :=
    inner_tendsto_of_tendsto_left
      (fun n : ℕ => SB t (KFCausalClockFloorRadialResolventResidual.formAction
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m_mass g k t u_res))
      (SB t u_res) (SB t v_res) (inner ℂ (S t x_res) (SJ t v_res))
      hform_out (KFCausalClosedGraphForm.hamiltonian_represents_form (SD t) x_res v_res)
  have hufJ : SJ t ufS = f :=
    KFCausalClosedGraphForm.embedding_formLift (SD t) ⟨f, hfS⟩
  have hstat_lift :
      staticLift ε hε h hh hw m_mass g k t ufS =
        KFCausalClockFloorRadialResolventStaticDomain.domainFormLift ε hε h hb hh m_mass g k ⟨f, hfT⟩ := by
    apply KFCausalClosedGraphForm.embedding_injective TD
    exact (staticLift_embedding ε hε h hh hw m_mass g k t ufS).trans
      (hufJ.trans
        (KFCausalClockFloorRadialResolventStaticDomain.domainFormLift_embedding ε hε h hb hh m_mass g k ⟨f, hfT⟩).symm)
  have hpot_lift :
      potentialLift ε hε h hh hw m_mass g k t ufS =
        KFCausalClockFloorRadialResolventPotentialDomain.domainFormLift ε hε h hb hh m_mass g k ⟨f, hfP⟩ := by
    apply KFCausalClosedGraphForm.embedding_injective PD
    exact (potentialLift_embedding ε hε h hh hw m_mass g k t ufS).trans
      (hufJ.trans
        (KFCausalClockFloorRadialResolventPotentialDomain.domainFormLift_embedding ε hε h hb hh m_mass g k ⟨f, hfP⟩).symm)
  have hS_graph := unconditional_three_operator_residual_graph
    ε hε h hh hb m_mass g k t f (T ⟨f, hfT⟩) (P ⟨f, hfP⟩)
    ((T).mem_graph ⟨f, hfT⟩) ((P).mem_graph ⟨f, hfP⟩) hf.2
  have hS_eq : T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨f, hfP⟩ = S t ⟨f, hfS⟩ :=
    ((S t).mem_graph_snd_inj' ((S t).mem_graph ⟨f, hfS⟩) hS_graph rfl).symm
  have hH_graph := unconditional_three_operator_hamiltonian_graph
    ε hε h hh hb m_mass g k t f (T ⟨f, hfT⟩) (K ⟨f, hfK⟩) (P ⟨f, hfP⟩)
    ((T).mem_graph ⟨f, hfT⟩) ((K).mem_graph ⟨f, hfK⟩) ((P).mem_graph ⟨f, hfP⟩) hf.2
  have hH_eq :
      T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨f, hfK⟩ + P ⟨f, hfP⟩) = H t ⟨f, hfH⟩ :=
    ((H t).mem_graph_snd_inj' ((H t).mem_graph ⟨f, hfH⟩) hH_graph rfl).symm
  have hT_dom := static_resolvent_tendsto ε hε h hb hh ⟨f, hfT⟩
  have hT_act := sequence_tendsto ε hε h (T ⟨f, hfT⟩)
  have hK_dom := operator_sequence_tendsto ε hε h ⟨f, hfK⟩
  have hK_act := sequence_tendsto ε hε h (K ⟨f, hfK⟩)
  have hP_shift := shifted_sequence_tendsto ε hε h (-h / 2) (shift_bound ε h hb) (P ⟨f, hfP⟩)
  have hP_act := sequence_tendsto ε hε h (P ⟨f, hfP⟩)
  have hS_out1 : Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩ +
        (Real.exp (2 * t) : ℂ) •
          shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb)
            (P ⟨f, hfP⟩))
      atTop (𝓝 (S t ⟨f, hfS⟩)) :=
    tendsto_of_tendsto_of_eq
      _ (T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨f, hfP⟩) (S t ⟨f, hfS⟩)
      (hT_dom.add (hP_shift.const_smul (Real.exp (2 * t) : ℂ))) hS_eq
  have hS_out2 : Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (T ⟨f, hfT⟩) +
        (Real.exp (2 * t) : ℂ) •
          action ε hε h ((n : ℝ) + 1) (by positivity) (P ⟨f, hfP⟩))
      atTop (𝓝 (S t ⟨f, hfS⟩)) :=
    tendsto_of_tendsto_of_eq
      _ (T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨f, hfP⟩) (S t ⟨f, hfS⟩)
      (hT_act.add (hP_act.const_smul (Real.exp (2 * t) : ℂ))) hS_eq
  have hH_out1 : Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩ +
        (Real.exp (2 * t) : ℂ) •
          (K ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
            radial_domain ε hε h ((n : ℝ) + 1) (by positivity) f⟩ +
            shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb)
              (P ⟨f, hfP⟩)))
      atTop (𝓝 (H t ⟨f, hfH⟩)) :=
    tendsto_of_tendsto_of_eq
      _ (T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨f, hfK⟩ + P ⟨f, hfP⟩)) (H t ⟨f, hfH⟩)
      (hT_dom.add ((hK_dom.add hP_shift).const_smul (Real.exp (2 * t) : ℂ))) hH_eq
  have hH_out2 : Tendsto (fun n : ℕ =>
      action ε hε h ((n : ℝ) + 1) (by positivity) (T ⟨f, hfT⟩) +
        (Real.exp (2 * t) : ℂ) •
          (action ε hε h ((n : ℝ) + 1) (by positivity) (K ⟨f, hfK⟩) +
            action ε hε h ((n : ℝ) + 1) (by positivity) (P ⟨f, hfP⟩)))
      atTop (𝓝 (H t ⟨f, hfH⟩)) :=
    tendsto_of_tendsto_of_eq
      _ (T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨f, hfK⟩ + P ⟨f, hfP⟩)) (H t ⟨f, hfH⟩)
      (hT_act.add ((hK_act.add hP_act).const_smul (Real.exp (2 * t) : ℂ))) hH_eq
  exact ⟨hx_graph, hact_graph, hinner_tendsto, hstat_lift, hpot_lift,
    hS_out1, hS_out2, hH_out1, hH_out2⟩

/-- Concrete fifteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
cyclic pentadecagon cocycle vanishing and `potentialPowerDomain (r + 2)` regularity across all fifteen
pentadecagon legs. -/
theorem clockFloorPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle_and_regularity
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
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
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k o_param a n r j x = 0 ∧
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
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k o_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a o_param n (r + 1) j x ∈
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
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
        2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
        2 * (l_param⁻¹) ^ r + 2 * (m_param⁻¹) ^ r + 2 * (n_param⁻¹) ^ r + (o_param⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hpent := arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p hres hpos r j x
  exact ⟨hpent.1, hpent.2.1, hmem.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier fifteen-parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
and thirty-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇), (h_param, n₈), (i_param, n₉), (j_param, n₁₀), (k_param, n₁₁), (l_param, n₁₂), (m_param, n₁₃), (n_param, n₁₄), (o_param, n₁₅))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_fifteen_and_thirty_parameter_cauchy_rates
    (a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ n₁₁ n₁₂ n₁₃ n₁₄ n₁₅ m j r : ℕ) (hjm : j ≤ m)
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
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n₁ r j x‖ ≤
      28 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + 2 * m_param⁻¹ +
          2 * n_param⁻¹ + o_param⁻¹) *
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
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k m_param n₁₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k m_param n₁₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k n_param n₁₄ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k n_param n₁₄ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k o_param n₁₅ r j x‖ ≤
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
        2 * ‖Jcut n₁₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₁₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₁₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + 2 * m_param⁻¹ +
          2 * n_param⁻¹ + o_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have h1 := arbitraryOrderPotentialIdentityYosidaTierSub_fifteen_parameter_cauchy_rate_of_le
    P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p hres hpos hlinv m j r hjm hx
  have h2 := arbitraryOrderPotentialIdentityYosida_joint_thirty_parameter_bound_of_le
    P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇) (Jcut n₈) (Jcut n₉) (Jcut n₁₀) (Jcut n₁₁) (Jcut n₁₂) (Jcut n₁₃) (Jcut n₁₄) (Jcut n₁₅)
    a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p hres hpos hlinv m j r hjm hx
  exact ⟨h1, h2⟩

/-- Master Fifteen-Parameter `(a, b, c, d, e, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param, n_param, o_param)`
Pentadecagon Cocycle, Unconditional Common-Domain Identities (`Dom(S(t)) ∩ Dom(G)`, `Dom(H(t)) ∩ Dom(P)`, `Dom(H(t)) ∩ Dom(G)`, `Dom(H(t)) ∩ Dom(T)`),
Wide-Strip Half-Shift Commutator Convergence, and Thirty-Parameter Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_fifteenParameter_pentadecagon_master_synthesis
    (t a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param)
    (hm_p : 0 < m_param) (hn_p : 0 < n_param) (ho_p : 0 < o_param)
    (n₁ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    let G := KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m_mass g k
    let uCore := KFCausalClockFloorRadialResolventMultiOperatorSynthesis.unconditionalCore ε hε h hb hh m_mass g k
    commonOperatorDomain ε hε h hh hb m_mass g k = uCore ⊓ (Tres 0).domain ∧
    (S t).domain ⊓ (G).domain = ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain ∧
    (H t).domain ⊓ (G).domain = ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (Tres 0).domain ∧
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
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k o_param a n₁ r j x = 0 ∧
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
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k o_param a n₁ r j x = 0 ∧
     clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a o_param n₁ (r + 1) j x ∈
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
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n₁ r j x‖ +
         ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + 2 * (h_param⁻¹) ^ r +
         2 * (i_param⁻¹) ^ r + 2 * (j_param⁻¹) ^ r + 2 * (k_param⁻¹) ^ r +
         2 * (l_param⁻¹) ^ r + 2 * (m_param⁻¹) ^ r + 2 * (n_param⁻¹) ^ r + (o_param⁻¹) ^ r) *
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
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k l_param m_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k m_param n_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k n_param o_param n₁ r j x‖ ≤
      28 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + 2 * h_param⁻¹ + 2 * i_param⁻¹ +
          2 * j_param⁻¹ + 2 * k_param⁻¹ + 2 * l_param⁻¹ + 2 * m_param⁻¹ +
          2 * n_param⁻¹ + o_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  intro G uCore
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hcomm : Tendsto (fun n : ℕ =>
      shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h / 2) (shift_bound ε h hb) x -
        action ε hε h ((n : ℝ) + 1) (by positivity) x) atTop (𝓝 0) := by
    have h1 := shifted_sequence_tendsto ε hε h (-h / 2) (shift_bound ε h hb) x
    have h2 := sequence_tendsto ε hε h x
    simpa only [sub_self] using h1.sub h2
  exact ⟨commonOperatorDomain_eq_unconditionalCore_inf_residualForm ε hε h hb hh m_mass g k,
    KFCausalClockFloorUnconditionalThreeOperatorDecomposition.residual_growing_common_domain_eq
      ε hε h hh hb m_mass g k t,
    KFCausalClockFloorUnconditionalThreeOperatorDecomposition.hamiltonian_growing_common_domain_eq
      ε hε h hh hb m_mass g k t,
    hcomm,
    clockFloorPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle_and_regularity
      ε hε h hh hb m_mass g k a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p n₁ r j x,
    arbitraryOrderPotentialIdentityYosidaTierSub_fifteen_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param h_param i_param j_param k_param l_param m_param n_param o_param ha hb_pos hc hd he hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hn_p ho_p hres hpos hlinv m j r hjm hx⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_fifteen_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_thirteen_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_fifteen_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_thirty_parameter_bound_of_le
#print axioms unconditional_wide_strip_residual_and_full_hamiltonian_convergence
#print axioms clockFloorPotentialYosidaTierSub_fifteen_parameter_pentadecagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_fifteen_and_thirty_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_fifteenParameter_pentadecagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFifteenParameterPentadecagon
