/- Eight-Parameter `(a, b, c, d, e, f_param, g_param, h_param)` Cyclic Octagon Cocycle, Mixed
Seven-Hop Decomposition, Direct Fixed-`N` Growing-Domain Radial-Yosida Lower Bound, Contraction,
and `O(N⁻¹)` Regularizer Rate on `Dom(G)` Without `R_G(a)` or `R_P(a)`, and Sixteen-Parameter
Cauchy Rate Bounds for Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSevenParameterHeptagon
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaEightParameterOctagon

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
open UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaSevenParameterHeptagon
  (arbitraryOrderPotentialYosidaTierSub_seven_parameter_heptagon_cocycle
   arbitraryOrderPotentialYosidaTierSub_seven_parameter_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_seven_parameter_norm_bounds
   arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_five_parameter_cocycle_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_seven_parameter_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_fourteen_parameter_bound_of_le)

section AbstractEightParameterOctagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact eight-parameter `(a, b, c, d, e, f_param, g_param, h_param)` cyclic octagon cocycle
vanishing and seven-hop chain decomposition for `arbitraryOrderPotentialResolventYosidaTierSub`
and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_eight_parameter_octagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R h_param) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R h_param) (R a) J h_param a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R h_param) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R h_param) J a h_param r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all eight octagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, `(e, f_param)`, `(f_param, g_param)`,
`(g_param, h_param)`, and `(a, h_param)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_eight_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R h_param) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R h_param) J a h_param r j x ∈
      operatorPowerDomain P r := by
  have habcdefg := arbitraryOrderPotentialYosidaTierSub_seven_parameter_mem_operatorPowerDomain
    P R J a b c d e f_param g_param ha hb hc hd he hf_p hg_p hres hlinv r j x
  have hagh := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a g_param h_param ha hg_p hh_p hres hlinv r j x
  exact ⟨habcdefg.1, habcdefg.2.1, habcdefg.2.2.1, habcdefg.2.2.2.1,
    habcdefg.2.2.2.2.1, habcdefg.2.2.2.2.2.1, hagh.2.1, hagh.2.2.1, hagh.2.2.2⟩

/-- Eight-parameter `(a, b, c, d, e, f_param, g_param, h_param)` seven-hop geometric norm bound
and uniform Yosida stability for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_eight_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R h_param) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R f_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R f_param) (R g_param) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R g_param) (R h_param) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + (h_param⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R f_param) J e f_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R f_param) (R g_param) J f_param g_param r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x‖ ≤
      14 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcdefg := arbitraryOrderPotentialYosidaTierSub_seven_parameter_norm_bounds
    P R J a b c d e f_param g_param ha hb hc hd he hf_p hg_p hres hpos r j x
  have hagh := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a g_param h_param ha hg_p hh_p hres hpos r j x
  have hgh := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J g_param h_param hg_p hh_p hres hpos r j x
  exact ⟨by linarith [habcdefg.1, hagh.1], by linarith [habcdefg.2.1, hgh.1], by linarith [habcdefg.2.2, hgh.2]⟩

/-- Six-parameter `(a, b, c, d, e, f_param)` hexagon cocycle for the mixed parameter-regularizer
double difference `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_six_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c d e f_param : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf_p : 0 < f_param)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R a) J₁ J₂ f_param a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x‖ ≤
      10 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R d) J₁ J₂ c d r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R d) (R e) J₁ J₂ d e r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R e) (R f_param) J₁ J₂ e f_param r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R f_param) (R a) J₁ J₂ f_param a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have habcde := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_five_parameter_cocycle_and_norm_le
    P R J₁ J₂ a b c d e ha hb hc hd he hres hpos r j x).2
  have hef := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ e f_param he hf_p hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Eight-parameter `(a, b, c, d, e, f_param, g_param, h_param)` mediated seven-hop Cauchy rate
bound for `arbitraryOrderPotentialIdentityYosidaTierSub` on `operatorPowerDomain P (m + 1)` for
`j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_eight_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
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
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R g_param) (R h_param) J g_param h_param r j x‖ ≤
      14 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + h_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefg := arbitraryOrderPotentialIdentityYosidaTierSub_seven_parameter_cauchy_rate_of_le
    P R J a b c d e f_param g_param ha hb hc hd he hf_p hg_p hres hpos hlinv m j r hjm hx
  have hgh := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J g_param h_param hg_p hh_p hres hpos hlinv m j r hjm hx
  linarith

/-- Joint sixteen-parameter
`((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅), (f_param, J₆), (g_param, J₇), (h_param, J₈))`
mediated seven-hop Cauchy rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_sixteen_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ : H →L[ℂ] H)
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R h_param) J₈ h_param r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + h_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcdefg := arbitraryOrderPotentialIdentityYosida_joint_fourteen_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ J₅ J₆ J₇ a b c d e f_param g_param ha hb hc hd he hf_p hg_p hres hpos hlinv m j r hjm hx
  have hgh := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₇ J₈ g_param h_param hg_p hh_p hres hpos hlinv m j r hjm hx
  linarith

end AbstractEightParameterOctagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Direct fixed-`N` growing-domain radial-Yosida lower bound
`‖M_N x‖ ^ 2 ≤ (inner ℂ (G x) (M_N x)).re`, uniform radial-Yosida contraction `‖M_N x‖ ≤ ‖G x‖`,
regularized pairing lower bound `(inner ℂ (G x) (J_N x)).re + N⁻¹ * ‖M_N x‖ ^ 2 ≤ (inner ℂ (G x) x).re`,
explicit `O(N⁻¹)` regularizer rate `‖x - J_N x‖ ≤ N⁻¹ * ‖G x‖`, and domain equivalence
`J_N x ∈ (G).domain ↔ J_N x ∈ (P).domain` on `(G).domain` without passing through `R_G(a)` or `R_P(a)`. -/
theorem direct_fixedN_growingDomain_radialYosida_lowerBound_contraction_and_rate_on_growingDomain
    (N : ℝ) (hN : 0 < N) (x : (G).domain) :
    (x : Hilbert) ∈ (K).domain ∧
    (x : Hilbert) ∈ (P).domain ∧
    ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (G x) (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ∧
    0 ≤ (inner ℂ (G x) (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ∧
    ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ≤ ‖G x‖ ∧
    (inner ℂ (G x) (action ε hε h N hN (x : Hilbert))).re +
        N⁻¹ * ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (G x) (x : Hilbert)).re ∧
    ‖(x : Hilbert) - action ε hε h N hN (x : Hilbert)‖ ≤ N⁻¹ * ‖G x‖ ∧
    (action ε hε h N hN (x : Hilbert) ∈ (G).domain ↔
      action ε hε h N hN (x : Hilbert) ∈ (P).domain) := by
  have hk_dom : (x : Hilbert) ∈ (K).domain :=
    KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m_mass g k x
  have hp_dom : (x : Hilbert) ∈ (P).domain :=
    KFCausalClockFloorRadialResolventGrowingDomain.growingHamiltonian_in_potentialHamiltonian_domain
      ε hε h hb hh m_mass g k (x : Hilbert) x.property
  have hsplit :=
    KFCausalClockFloorRadialResolventGrowingDomain.growingHamiltonian_eq_radial_add_potential
      ε hε h hb hh m_mass g k x
  have hK_low :=
    KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.radial_operator_yosida_pairing_lower
      ε hε h N hN ⟨(x : Hilbert), hk_dom⟩
  have hP_acc :=
    KFCausalClockFloorPotentialRadialYosidaAccretivity.potential_yosida_accretive
      ε hε h N hN hb hh m_mass g k ⟨(x : Hilbert), hp_dom⟩
  have hadd_re :
      (inner ℂ (G x)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re =
        (inner ℂ (K ⟨(x : Hilbert), hk_dom⟩)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re +
        (inner ℂ (P ⟨(x : Hilbert), hp_dom⟩)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
    rw [hsplit, inner_add_left, Complex.add_re]
  have hG_low :
      ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
        (inner ℂ (G x)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
    linarith [hadd_re, hK_low, hP_acc]
  have hG_acc :
      0 ≤ (inner ℂ (G x)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re :=
    le_trans (sq_nonneg _) hG_low
  have hcs :
      (inner ℂ (G x)
          (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re ≤
        ‖G x‖ * ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ :=
    le_trans (Complex.re_le_norm _)
      (norm_inner_le_norm (G x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)))
  have hsq_le :
      ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
        ‖G x‖ * ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ :=
    le_trans hG_low hcs
  have hM_le_G :
      ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ≤ ‖G x‖ := by
    by_cases hM0 : ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ = 0
    · rw [hM0]
      exact norm_nonneg (G x)
    · have hM_pos : 0 < ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hM0)
      nlinarith [hsq_le, hM_pos]
  have hsub : (x : Hilbert) - action ε hε h N hN (x : Hilbert) =
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert) := by
    change (x : Hilbert) - ((x : Hilbert) -
      (N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)) = _
    exact sub_sub_cancel (x : Hilbert)
      ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))
  have hre_diff :
      (inner ℂ (G x) (x : Hilbert)).re -
        (inner ℂ (G x) (action ε hε h N hN (x : Hilbert))).re =
      N⁻¹ * (inner ℂ (G x)
        (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
    calc
      (inner ℂ (G x) (x : Hilbert)).re -
          (inner ℂ (G x) (action ε hε h N hN (x : Hilbert))).re
        = (inner ℂ (G x) ((x : Hilbert) - action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_sub_right, Complex.sub_re]
      _ = (inner ℂ (G x)
            ((N⁻¹ : ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [hsub]
      _ = N⁻¹ * (inner ℂ (G x)
            (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert))).re := by
            rw [inner_smul_right, Complex.mul_re]
            simp
  have hNinv_nn : 0 ≤ N⁻¹ := inv_nonneg.mpr hN.le
  have hJ_pair :
      (inner ℂ (G x) (action ε hε h N hN (x : Hilbert))).re +
          N⁻¹ * ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN (x : Hilbert)‖ ^ 2 ≤
        (inner ℂ (G x) (x : Hilbert)).re := by
    have hmul := mul_le_mul_of_nonneg_left hG_low hNinv_nn
    linarith [hre_diff, hmul]
  have hrate : ‖(x : Hilbert) - action ε hε h N hN (x : Hilbert)‖ ≤ N⁻¹ * ‖G x‖ := by
    rw [hsub, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN.le]
    exact mul_le_mul_of_nonneg_left hM_le_G hNinv_nn
  have hiff :=
    KFCausalClockFloorRadialResolventGrowingDomain.growingHamiltonian_resolvent_domain_iff_potential
      ε hε h N hN hb hh m_mass g k (x : Hilbert)
  exact ⟨hk_dom, hp_dom, hG_low, hG_acc, hM_le_G, hJ_pair, hrate, hiff⟩

/-- Concrete eight-parameter `(a, b, c, d, e, f_param, g_param, h_param)` cyclic octagon cocycle
vanishing and `potentialPowerDomain (r + 2)` regularity across all eight octagon legs. -/
theorem clockFloorPotentialYosidaTierSub_eight_parameter_octagon_cocycle_and_regularity
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param a n r j x = 0 ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a h_param n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
        2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + (h_param⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hoct := arbitraryOrderPotentialYosidaTierSub_eight_parameter_octagon_cocycle
    P RP (Jcut n) a b c d e f_param g_param h_param r j x
  have hmem := arbitraryOrderPotentialYosidaTierSub_eight_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_eight_parameter_norm_bounds
    P RP (Jcut n) a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p hres hpos r j x
  exact ⟨hoct.1, hoct.2.1, hmem.2.2.2.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier eight-parameter `(a, b, c, d, e, f_param, g_param, h_param)` and
sixteen-parameter `((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅), (f_param, n₆), (g_param, n₇), (h_param, n₈))`
Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_eight_and_sixteen_parameter_cauchy_rates
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ ≤
      14 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + h_param⁻¹) *
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
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k h_param n₈ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₆ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₇ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₈ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + h_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_eight_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_sixteen_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) (Jcut n₆) (Jcut n₇) (Jcut n₈)
      a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p hres hpos hlinv m j r hjm hx⟩

/-- Master Eight-Parameter `(a, b, c, d, e, f_param, g_param, h_param)` Octagon Cocycle, Direct
Fixed-`N` Growing-Domain Radial-Yosida Lower Bound, Contraction & Rate, and Sixteen-Parameter
Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_eightParameter_octagon_master_synthesis
    (a b c d e f_param g_param h_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k h_param a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k h_param a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a h_param n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + 2 * (e⁻¹) ^ r +
         2 * (f_param⁻¹) ^ r + 2 * (g_param⁻¹) ^ r + (h_param⁻¹) ^ r) *
         ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e f_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k f_param g_param n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k g_param h_param n₁ r j x‖ ≤
      14 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + 2 * e⁻¹ +
          2 * f_param⁻¹ + 2 * g_param⁻¹ + h_param⁻¹) *
          ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_eight_parameter_octagon_cocycle_and_regularity
    ε hε h hh hb m_mass g k a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p n₁ r j x
  have hrates := clockFloorPotentialYosida_eight_and_sixteen_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c d e f_param g_param h_param ha hb_pos hc hd he hf_p hg_p hh_p
    n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ m j r hjm hx
  exact ⟨⟨hcoc.1, hcoc.2.1⟩, ⟨hcoc.2.2.1, hcoc.2.2.2⟩, hrates.1⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_eight_parameter_octagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_eight_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_eight_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_six_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_eight_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_sixteen_parameter_bound_of_le
#print axioms direct_fixedN_growingDomain_radialYosida_lowerBound_contraction_and_rate_on_growingDomain
#print axioms clockFloorPotentialYosidaTierSub_eight_parameter_octagon_cocycle_and_regularity
#print axioms clockFloorPotentialYosida_eight_and_sixteen_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_eightParameter_octagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaEightParameterOctagon
