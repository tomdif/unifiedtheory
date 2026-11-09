/- Five-Parameter `(a, b, c, d, e)` Cyclic Pentagon Cocycle, Mixed Four-Hop Decomposition,
and Ten-Parameter `((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅))` Cauchy Rate Bounds for
Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFiveParameterPentagon

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

section AbstractFiveParameterPentagon

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact five-parameter `(a, b, c, d, e)` cyclic pentagon cocycle vanishing and four-hop chain
decomposition for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_five_parameter_pentagon_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H) (a b c d e : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R e) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R e) (R a) J e a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R e) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R e) J a e r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all five pentagon legs `(a, b)`, `(b, c)`, `(c, d)`, `(d, e)`, and `(a, e)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_five_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
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
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R e) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R e) J a e r j x ∈
      operatorPowerDomain P r := by
  have habcd := arbitraryOrderPotentialYosidaTierSub_four_parameter_mem_operatorPowerDomain
    P R J a b c d ha hb hc hd hres hlinv r j x
  have hade := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a d e ha hd he hres hlinv r j x
  exact ⟨habcd.1, habcd.2.1, habcd.2.2.1, hade.2.1, hade.2.2.1, hade.2.2.2⟩

/-- Five-parameter `(a, b, c, d, e)` four-hop geometric norm bound and uniform Yosida stability
for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_five_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R e) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R e) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + (e⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ ≤
      8 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habcd := arbitraryOrderPotentialYosidaTierSub_four_parameter_norm_bounds
    P R J a b c d ha hb hc hd hres hpos r j x
  have hade := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a d e ha hd he hres hpos r j x
  have hde := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J d e hd he hres hpos r j x
  exact ⟨by linarith [habcd.1, hade.1], by linarith [habcd.2.1, hde.1], by linarith [habcd.2.2, hde.2]⟩

/-- Three-parameter `(a, b, c)` cyclic cocycle for the mixed parameter-regularizer double difference
`arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_three_parameter_cocycle_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R a) J₁ J₂ c a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x‖ ≤
      4 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R b) (R c) J₁ J₂ b c r j x +
        arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R c) (R a) J₁ J₂ c a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have hab := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ a b ha hb hres hpos r j x).2.2.2
  have hbc := (arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    P R J₁ J₂ b c hb hc hres hpos r j x).2.2.2
  exact ⟨hcoc, by linarith⟩

/-- Five-parameter `(a, b, c, d, e)` mediated four-hop Cauchy rate bound for
`arbitraryOrderPotentialIdentityYosidaTierSub` on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_five_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m)
    {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R e) J d e r j x‖ ≤
      8 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcd := arbitraryOrderPotentialIdentityYosidaTierSub_four_parameter_cauchy_rate_of_le
    P R J a b c d ha hb hc hd hres hpos hlinv m j r hjm hx
  have hde := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J d e hd he hres hpos hlinv m j r hjm hx
  linarith

/-- Joint ten-parameter `((a, J₁), (b, J₂), (c, J₃), (d, J₄), (e, J₅))` mediated four-hop Cauchy
rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_ten_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ J₅ : H →L[ℂ] H)
    (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R e) J₅ e r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habcd := arbitraryOrderPotentialIdentityYosida_joint_eight_parameter_bound_of_le
    P R J₁ J₂ J₃ J₄ a b c d ha hb hc hd hres hpos hlinv m j r hjm hx
  have hde := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₄ J₅ d e hd he hres hpos hlinv m j r hjm hx
  linarith

end AbstractFiveParameterPentagon

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Concrete five-parameter `(a, b, c, d, e)` cyclic pentagon cocycle vanishing for the
clock-floor potential-resolvent and Yosida-scaled identity tier differences. -/
theorem clockFloorPotentialYosidaTierSub_five_parameter_pentagon_cocycle
    (a b c d e : ℝ) (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e a n r j x = 0 := by
  have hpent := arbitraryOrderPotentialYosidaTierSub_five_parameter_pentagon_cocycle
    P RP (Jcut n) a b c d e r j x
  exact ⟨hpent.1, hpent.2.1⟩

/-- Simultaneous `potentialPowerDomain (r + 2)` regularity across all five pentagon legs and
four-hop geometric norm bound for `clockFloorPotentialResolventYosidaTierSub`. -/
theorem clockFloorPotentialYosidaTierSub_five_parameter_regularity_and_bounds
    (a b c d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a e n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + (e⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hmem := arbitraryOrderPotentialYosidaTierSub_five_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d e ha hb_pos hc hd he hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_five_parameter_norm_bounds
    P RP (Jcut n) a b c d e ha hb_pos hc hd he hres hpos r j x
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2.1, hmem.2.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier five-parameter `(a, b, c, d, e)` and ten-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅))` Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_five_and_ten_parameter_cauchy_rates
    (a b c d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (n₁ n₂ n₃ n₄ n₅ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ ≤
      8 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k e n₅ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_five_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d e ha hb_pos hc hd he hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_ten_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) (Jcut n₅) a b c d e ha hb_pos hc hd he hres hpos hlinv m j r hjm hx⟩

/-- Master Five-Parameter `(a, b, c, d, e)` and Ten-Parameter `((a, n₁), (b, n₂), (c, n₃), (d, n₄), (e, n₅))`
Potential-Resolvent Radial-Yosida Pentagon Cocycle and Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_fiveParameter_pentagon_master_synthesis
    (a b c d e : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (n₁ n₂ n₃ n₄ n₅ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k e a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k e a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a e n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + 2 * (d⁻¹) ^ r + (e⁻¹) ^ r) *
         ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d e n₁ r j x‖ ≤
      8 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k e n₅ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₅ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + 2 * d⁻¹ + e⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_five_parameter_pentagon_cocycle
    ε hε h hh hb m_mass g k a b c d e n₁ r j x
  have hreg := clockFloorPotentialYosidaTierSub_five_parameter_regularity_and_bounds
    ε hε h hh hb m_mass g k a b c d e ha hb_pos hc hd he n₁ r j x
  have hrates := clockFloorPotentialYosida_five_and_ten_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c d e ha hb_pos hc hd he n₁ n₂ n₃ n₄ n₅ m j r hjm hx
  exact ⟨hcoc, ⟨hreg.2.2.2.2.1, hreg.2.2.2.2.2⟩, hrates.1, hrates.2⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_five_parameter_pentagon_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_five_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_five_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_three_parameter_cocycle_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_five_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_ten_parameter_bound_of_le
#print axioms clockFloorPotentialYosidaTierSub_five_parameter_pentagon_cocycle
#print axioms clockFloorPotentialYosidaTierSub_five_parameter_regularity_and_bounds
#print axioms clockFloorPotentialYosida_five_and_ten_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_fiveParameter_pentagon_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFiveParameterPentagon
