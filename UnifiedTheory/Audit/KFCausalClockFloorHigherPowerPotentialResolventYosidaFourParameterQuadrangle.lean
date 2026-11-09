/- Four-Parameter `(a, b, c, d)` Cyclic Quadrangle Cocycle, Mixed Parameter-Regularizer
Double-Difference Commutator, and Eight-Parameter `((a, J₁), (b, J₂), (c, J₃), (d, J₄))`
Cauchy Rate Bounds for Arbitrary-Order Potential-Resolvent Radial-Yosida Tier States. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle

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
   arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le
   clockFloorPotentialYosidaTierSub_three_parameter_cyclic_cocycle
   clockFloorPotentialYosidaTierSub_three_parameter_regularity_and_bounds
   clockFloorPotentialYosida_three_and_six_parameter_cauchy_rates)

section AbstractFourParameterQuadrangle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Mixed parameter-and-regularizer double difference
`((a R_a)^r J₁(P^j x) - (b R_b)^r J₁(P^j x)) - ((a R_a)^r J₂(P^j x) - (b R_b)^r J₂(P^j x))`. -/
def arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
    (P : H →ₗ.[ℂ] H) (Ra Rb J₁ J₂ : H →L[ℂ] H) (a b : ℝ) (r j : ℕ) (x : H) : H :=
  arbitraryOrderPotentialIdentityYosidaTierSub P Ra Rb J₁ a b r j x -
  arbitraryOrderPotentialIdentityYosidaTierSub P Ra Rb J₂ a b r j x

/-- Exact four-parameter `(a, b, c, d)` cyclic quadrangle cocycle vanishing and three-hop chain
decomposition for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H) (a b c d : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R d) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R d) (R a) J d a r j x = 0 ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R d) J r j x =
      arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
        arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R d) J a d r j x =
      arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
        arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all four quadrangle legs `(a, b)`, `(b, c)`, `(c, d)`, and `(a, d)`. -/
theorem arbitraryOrderPotentialYosidaTierSub_four_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R d) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R d) J a d r j x ∈
      operatorPowerDomain P r := by
  have habc := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a b c ha hb hc hres hlinv r j x
  have hacd := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P R J a c d ha hc hd hres hlinv r j x
  exact ⟨habc.1, habc.2.1, hacd.2.1, hacd.2.2.1, hacd.2.2.2⟩

/-- Four-parameter `(a, b, c, d)` three-hop geometric norm bound and uniform Yosida stability
for `arbitraryOrderPotentialResolventYosidaTierSub` and
`arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_four_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R d) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R d) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ ≤
      6 * ‖J (iteratedOperatorPower P j x)‖ := by
  have habc := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a b c ha hb hc hres hpos r j x
  have hacd := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P R J a c d ha hc hd hres hpos r j x
  have hcd := arbitraryOrderPotentialYosidaTierSub_norm_bounds
    P R J c d hc hd hres hpos r j x
  have hring :
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ +
        ((c⁻¹) ^ r + (d⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ =
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) *
        ‖J (iteratedOperatorPower P j x)‖ := by ring
  exact ⟨by linarith [habc.1, hacd.1], by linarith [habc.2.1, hcd.1], by linarith [habc.2.2, hcd.2]⟩

/-- Exact parameter-regularizer commutator symmetry, diagonal vanishing, and uniform
`2 * ‖J₁(P^j x) - J₂(P^j x)‖` Yosida bound for `arbitraryOrderPotentialIdentityYosidaMixedDoubleSub`. -/
theorem arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ : H →L[ℂ] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R a) J₁ J₂ a a r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₁ a b r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x =
      (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₂ a r j x) -
      (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₁ b r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x) ∧
    ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ ≤
      2 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
  have hd1 :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R a) J₁ J₂ a a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have hd2 :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₁ a b r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
    abel
  have hcomm :
      arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x =
        (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
          arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₂ a r j x) -
        (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₁ b r j x -
          arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x) := by
    unfold arbitraryOrderPotentialIdentityYosidaMixedDoubleSub
      arbitraryOrderPotentialIdentityYosidaTierSub
    abel
  have hnorm :
      ‖arbitraryOrderPotentialIdentityYosidaMixedDoubleSub P (R a) (R b) J₁ J₂ a b r j x‖ ≤
        2 * ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ := by
    rw [hcomm]
    have ha_cut := (arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
      P (R a) J₁ J₂ a ha (hres a ha) hpos r j x).2
    have hb_cut := (arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
      P (R b) J₁ J₂ b hb (hres b hb) hpos r j x).2
    unfold arbitraryOrderPotentialIdentityYosidaCutoffSub at ha_cut hb_cut
    have htri := norm_sub_le
      (arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₂ a r j x)
      (arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₁ b r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x)
    linarith
  exact ⟨hd1, hd2, hcomm, hnorm⟩

/-- Four-parameter `(a, b, c, d)` mediated three-hop Cauchy rate bound for
`arbitraryOrderPotentialIdentityYosidaTierSub` on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_four_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hres : ∀ s, 0 < s → Resolves P (R s) s)
    (hpos : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hlinv : ∀ s, 0 < s → ∀ z : P.domain, R s (P z + s • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m)
    {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R d) J c d r j x‖ ≤
      6 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habc := arbitraryOrderPotentialIdentityYosidaTierSub_three_parameter_cauchy_rate_of_le
    P R J a b c ha hb hc hres hpos hlinv m j r hjm hx
  have hcd := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J c d hc hd hres hpos hlinv m j r hjm hx
  have hring :
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ +
        (r : ℝ) * (c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ =
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by ring
  linarith

/-- Joint eight-parameter `((a, J₁), (b, J₂), (c, J₃), (d, J₄))` mediated three-hop Cauchy
rate bound on `operatorPowerDomain P (m + 1)` for `j ≤ m`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_eight_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ J₄ : H →L[ℂ] H)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
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
        arbitraryOrderPotentialIdentityYosidaTierState P (R d) J₄ d r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have habc := arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le
    P R J₁ J₂ J₃ a b c ha hb hc hres hpos hlinv m j r hjm hx
  have hcd := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₃ J₄ c d hc hd hres hpos hlinv m j r hjm hx
  have hring :
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ +
        (r : ℝ) * (c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ =
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by ring
  linarith

end AbstractFourParameterQuadrangle

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Concrete four-parameter `(a, b, c, d)` cyclic quadrangle cocycle vanishing for the
clock-floor potential-resolvent and Yosida-scaled identity tier differences. -/
theorem clockFloorPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
    (a b c d : ℝ) (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d a n r j x = 0 := by
  have hquad := arbitraryOrderPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
    P RP (Jcut n) a b c d r j x
  exact ⟨hquad.1, hquad.2.1⟩

/-- Simultaneous `potentialPowerDomain (r + 2)` regularity across all four quadrangle legs and
three-hop geometric norm bound for `clockFloorPotentialResolventYosidaTierSub`. -/
theorem clockFloorPotentialYosidaTierSub_four_parameter_regularity_and_bounds
    (a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a d n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) *
        ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hmem := arbitraryOrderPotentialYosidaTierSub_four_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c d ha hb_pos hc hd hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_four_parameter_norm_bounds
    P RP (Jcut n) a b c d ha hb_pos hc hd hres hpos r j x
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier four-parameter `(a, b, c, d)` and eight-parameter
`((a, n₁), (b, n₂), (c, n₃), (d, n₄))` Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_four_and_eight_parameter_cauchy_rates
    (a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (n₁ n₂ n₃ n₄ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ ≤
      6 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_four_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c d ha hb_pos hc hd hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_eight_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) (Jcut n₄) a b c d ha hb_pos hc hd hres hpos hlinv m j r hjm hx⟩

/-- Master Four-Parameter `(a, b, c, d)` and Eight-Parameter `((a, n₁), (b, n₂), (c, n₃), (d, n₄))`
Potential-Resolvent Radial-Yosida Quadrangle Cocycle and Cauchy Rate Synthesis. -/
theorem clockFloorPotentialYosida_fourParameter_quadrangle_master_synthesis
    (a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (n₁ n₂ n₃ n₄ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k d a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k d a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a d n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + 2 * (c⁻¹) ^ r + (d⁻¹) ^ r) *
         ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c d n₁ r j x‖ ≤
      6 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k d n₄ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₄ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + 2 * c⁻¹ + d⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
    ε hε h hh hb m_mass g k a b c d n₁ r j x
  have hreg := clockFloorPotentialYosidaTierSub_four_parameter_regularity_and_bounds
    ε hε h hh hb m_mass g k a b c d ha hb_pos hc hd n₁ r j x
  have hrates := clockFloorPotentialYosida_four_and_eight_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c d ha hb_pos hc hd n₁ n₂ n₃ n₄ m j r hjm hx
  exact ⟨hcoc, ⟨hreg.2.2.2.1, hreg.2.2.2.2⟩, hrates.1, hrates.2⟩

#print axioms arbitraryOrderPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_four_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_four_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaMixedDoubleSub_commutator_and_norm_le
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_four_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_eight_parameter_bound_of_le
#print axioms clockFloorPotentialYosidaTierSub_four_parameter_quadrangle_cocycle
#print axioms clockFloorPotentialYosidaTierSub_four_parameter_regularity_and_bounds
#print axioms clockFloorPotentialYosida_four_and_eight_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_fourParameter_quadrangle_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaFourParameterQuadrangle
