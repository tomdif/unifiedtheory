/- Three-Parameter `(a, b, c)` Higher-Power Potential-Resolvent Radial-Yosida Tier Cocycles,
Mediated Two-Hop Regularity & Norm Bounds, and Six-Parameter `((a, J₁), (b, J₂), (c, J₃))`
Cauchy Rate Bounds on `Dom(P^{m+1})`:
1. Establishes the three-parameter `(a, b, c)` cyclic cocycle and mediated two-hop decomposition
   for `arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`
   across every operator-power tier `j : ℕ` and iteration order `r : ℕ`.
2. Proves:
   - Exact cyclic 3-parameter cocycle vanishing `(a, b) + (b, c) + (c, a) = 0` for both raw
     potential-resolvent tier differences and Yosida-scaled identity tier differences,
   - Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
     all three legs `(a, b)`, `(b, c)`, and `(a, c)`,
   - Mediated two-hop geometric norm bound `((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖J (P^j x)‖`
     and uniform `4 * ‖J (P^j x)‖` two-hop Yosida stability bound,
   - Mediated two-hop `(m + 1)`-tier Cauchy rate bound on `operatorPowerDomain P (m + 1)`:
     `‖sub a b‖ + ‖sub b c‖ ≤ 4 * ‖J (P^j x) - P^j x‖ + (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖P^{j+1} x‖`,
   - Joint six-parameter `((a, J₁), (b, J₂), (c, J₃))` mediated Cauchy rate bound on `Dom(P^{m+1})`,
   - Three-regularizer cutoff cyclic cocycle and contractive triangle bound,
   - Concrete clock-floor potential Hamiltonian instantiation and master synthesis. -/
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaTwoParameterCauchyRate

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle

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
  (iteratedIdentityPower)
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
   arbitraryOrderPotentialYosidaCauchyGraphNormSq
   arbitraryOrderPotentialYosidaTierSub_zero_and_cocycle
   arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain
   arbitraryOrderPotentialYosidaTierSub_norm_bounds
   arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le
   arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
   arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
   clockFloorPotentialResolventYosidaTierSub
   clockFloorPotentialIdentityYosidaTierSub
   clockFloorPotentialYosidaTierSub_regularity_and_bounds
   clockFloorPotentialYosida_twoParameter_cauchy_rate_master_synthesis)

/-! ### 1. Abstract Three-Parameter and Three-Regularizer Potential-Resolvent Yosida Cocycle Calculus -/

section AbstractThreeParameterPotentialYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact cyclic 3-parameter `(a, b, c)` cocycle vanishing `(a, b) + (b, c) + (c, a) = 0`
for `arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_three_parameter_cyclic_cocycle
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c : ℝ) (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x +
      arbitraryOrderPotentialResolventYosidaTierSub P (R c) (R a) J r j x = 0 ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x +
      arbitraryOrderPotentialIdentityYosidaTierSub P (R c) (R a) J c a r j x = 0 := by
  unfold arbitraryOrderPotentialResolventYosidaTierSub
    arbitraryOrderPotentialIdentityYosidaTierSub
  refine ⟨by abel, by abel⟩

/-- Simultaneous `operatorPowerDomain P (r + 2)` and `operatorPowerDomain P r` membership across
all three legs `(a, b)`, `(b, c)`, and `(a, c)` for `a, b, c > 0`. -/
theorem arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R c) J (r + 1) j x ∈
      operatorPowerDomain P (r + 2) ∧
    arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R c) J a c r j x ∈
      operatorPowerDomain P r := by
  have hab := arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain P R J a b ha hb hr hl r j x
  have hbc := arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain P R J b c hb hc hr hl r j x
  have hac := arbitraryOrderPotentialYosidaTierSub_mem_operatorPowerDomain P R J a c ha hc hr hl r j x
  exact ⟨hab.1, hbc.1, hac.1, hac.2⟩

/-- Mediated two-hop triangle norm bound and geometric bound across `(a, b, c)` for
`arbitraryOrderPotentialResolventYosidaTierSub` and `arbitraryOrderPotentialIdentityYosidaTierSub`. -/
theorem arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R c) J r j x‖ ≤
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ ∧
    ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ ∧
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
        ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ ≤
      4 * ‖J (iteratedOperatorPower P j x)‖ := by
  have hcoc := arbitraryOrderPotentialYosidaTierSub_zero_and_cocycle P R J a b c r j x
  have htri :
      ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R c) J r j x‖ ≤
        ‖arbitraryOrderPotentialResolventYosidaTierSub P (R a) (R b) J r j x‖ +
          ‖arbitraryOrderPotentialResolventYosidaTierSub P (R b) (R c) J r j x‖ := by
    rw [← hcoc.2.2.2.2.1]
    exact norm_add_le _ _
  have hab := arbitraryOrderPotentialYosidaTierSub_norm_bounds P R J a b ha hb hr hp r j x
  have hbc := arbitraryOrderPotentialYosidaTierSub_norm_bounds P R J b c hb hc hr hp r j x
  have hring :
      ((a⁻¹) ^ r + (b⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ +
        ((b⁻¹) ^ r + (c⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ =
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖J (iteratedOperatorPower P j x)‖ := by ring
  exact ⟨htri, by linarith [hab.1, hbc.1], by linarith [hab.2, hbc.2]⟩

/-- Three-regularizer cutoff cyclic cocycle `(J₁, J₂) + (J₂, J₃) + (J₃, J₁) = 0` and two-hop
contractive norm bound at fixed spectral shift `a > 0`. -/
theorem arbitraryOrderPotentialIdentityYosidaCutoffSub_three_regularizer_cocycle_and_bound
    (P : H →ₗ.[ℂ] H) (R J₁ J₂ J₃ : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : Resolves P R a) (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (r j : ℕ) (x : H) :
    arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x +
      arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₂ J₃ a r j x +
      arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₃ J₁ a r j x = 0 ∧
    ‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₃ a r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - J₂ (iteratedOperatorPower P j x)‖ +
        ‖J₂ (iteratedOperatorPower P j x) - J₃ (iteratedOperatorPower P j x)‖ := by
  have hcoc :
      arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x +
        arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₂ J₃ a r j x +
        arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₃ J₁ a r j x = 0 := by
    unfold arbitraryOrderPotentialIdentityYosidaCutoffSub
    abel
  have hsplit :
      arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₃ a r j x =
        arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x +
          arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₂ J₃ a r j x := by
    unfold arbitraryOrderPotentialIdentityYosidaCutoffSub
    abel
  have htri :
      ‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₃ a r j x‖ ≤
        ‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₁ J₂ a r j x‖ +
          ‖arbitraryOrderPotentialIdentityYosidaCutoffSub P R J₂ J₃ a r j x‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have h12 := (arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le P R J₁ J₂ a ha hr hp r j x).2
  have h23 := (arbitraryOrderPotentialIdentityYosidaCutoffSub_eq_and_norm_le P R J₂ J₃ a ha hr hp r j x).2
  exact ⟨hcoc, by linarith⟩

/-- Simultaneous `(m + 1)`-tier mediated three-parameter `(a, b, c)` Cauchy rate bound for all
`j ≤ m` when `x ∈ operatorPowerDomain P (m + 1)`. -/
theorem arbitraryOrderPotentialIdentityYosidaTierSub_three_parameter_cauchy_rate_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R a) (R b) J a b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierSub P (R b) (R c) J b c r j x‖ ≤
      4 * ‖J (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hab := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J a b ha hb hr hp hl m j r hjm hx
  have hbc := arbitraryOrderPotentialIdentityYosidaTierSub_all_tiers_cauchy_rate_of_le
    P R J b c hb hc hr hp hl m j r hjm hx
  have hring :
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ +
        (r : ℝ) * (b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ =
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by ring
  linarith

/-- Joint six-parameter `((a, J₁), (b, J₂), (c, J₃))` mediated Cauchy rate bound across three
spectral shifts `(a, b, c)` and three regularizers `(J₁, J₂, J₃)` on `operatorPowerDomain P (m + 1)`. -/
theorem arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le
    (P : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (J₁ J₂ J₃ : H →L[ℂ] H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : ∀ d, 0 < d → Resolves P (R d) d)
    (hp : ∀ z : P.domain, 0 ≤ (inner ℂ (P z) (z : H)).re)
    (hl : ∀ d, 0 < d → ∀ z : P.domain, R d (P z + d • (z : H)) = (z : H))
    (m j r : ℕ) (hjm : j ≤ m) {x : H} (hx : x ∈ operatorPowerDomain P (m + 1)) :
    ‖arbitraryOrderPotentialIdentityYosidaTierState P (R a) J₁ a r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x‖ +
      ‖arbitraryOrderPotentialIdentityYosidaTierState P (R b) J₂ b r j x -
        arbitraryOrderPotentialIdentityYosidaTierState P (R c) J₃ c r j x‖ ≤
      ‖J₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖J₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖J₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hab := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₁ J₂ a b ha hb hr hp hl m j r hjm hx
  have hbc := arbitraryOrderPotentialIdentityYosida_joint_four_parameter_bound_of_le
    P R J₂ J₃ b c hb hc hr hp hl m j r hjm hx
  have hring :
      (r : ℝ) * (a⁻¹ + b⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ +
        (r : ℝ) * (b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ =
      (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by ring
  linarith

end AbstractThreeParameterPotentialYosida

/-! ### 2. Concrete Clock-Floor Potential-Resolvent Three-Parameter Cocycle and Cauchy Rate Synthesis -/

section ClockFloorThreeParameterPotentialYosida

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m_mass g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m_mass g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m_mass g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m_mass g k
local notation "Jcut" => fun n : ℕ => action ε hε h (cutoff n) (cutoff_pos n)

/-- Exact cyclic 3-parameter `(a, b, c)` cocycle vanishing for the concrete clock-floor
potential-resolvent and Yosida-scaled identity tier differences at every cutoff `n`. -/
theorem clockFloorPotentialYosidaTierSub_three_parameter_cyclic_cocycle
    (a b c : ℝ) (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c a n r j x = 0 ∧
    clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n r j x +
      clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c a n r j x = 0 :=
  arbitraryOrderPotentialYosidaTierSub_three_parameter_cyclic_cocycle
    P RP (Jcut n) a b c r j x

/-- Simultaneous `potentialPowerDomain (r + 2)` regularity and mediated two-hop geometric norm
bound for `clockFloorPotentialResolventYosidaTierSub` across `(a, b, c)`. -/
theorem clockFloorPotentialYosidaTierSub_three_parameter_regularity_and_bounds
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (n r j : ℕ) (x : Hilbert) :
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a c n (r + 1) j x ∈
      potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
    ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n r j x‖ +
        ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n r j x‖ ≤
      ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖Jcut n (iteratedOperatorPower P j x)‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  have hmem := arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
    P RP (Jcut n) a b c ha hb_pos hc hres hlinv r j x
  have hnorm := arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
    P RP (Jcut n) a b c ha hb_pos hc hres hpos r j x
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.1, hnorm.2.1⟩

/-- Simultaneous `(m + 1)`-tier mediated three-parameter `(a, b, c)` and six-parameter
`((a, n₁), (b, n₂), (c, n₃))` Cauchy rate bounds on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_three_and_six_parameter_cauchy_rates
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (n₁ n₂ n₃ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ ≤
      4 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hres := KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m_mass g k
  have hlinv := KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m_mass g k
  have hpos := KFCausalClosedGraphForm.hamiltonian_positive PD
  exact ⟨arbitraryOrderPotentialIdentityYosidaTierSub_three_parameter_cauchy_rate_of_le
      P RP (Jcut n₁) a b c ha hb_pos hc hres hpos hlinv m j r hjm hx,
    arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le
      P RP (Jcut n₁) (Jcut n₂) (Jcut n₃) a b c ha hb_pos hc hres hpos hlinv m j r hjm hx⟩

/-- Master Three-Parameter `(a, b, c)` and Six-Parameter `((a, n₁), (b, n₂), (c, n₃))`
Potential-Resolvent Radial-Yosida Cocycle and Cauchy Rate Synthesis on `potentialPowerDomain (m + 1)`. -/
theorem clockFloorPotentialYosida_threeParameter_cocycle_master_synthesis
    (a b c : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c)
    (n₁ n₂ n₃ m j r : ℕ) (hjm : j ≤ m)
    {x : Hilbert} (hx : x ∈ potentialPowerDomain ε hε h hh hb m_mass g k (m + 1)) :
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k c a n₁ r j x = 0 ∧
     clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x +
       clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k c a n₁ r j x = 0) ∧
    (clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a c n₁ (r + 1) j x ∈
       potentialPowerDomain ε hε h hh hb m_mass g k (r + 2) ∧
     ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
       ‖clockFloorPotentialResolventYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ ≤
       ((a⁻¹) ^ r + 2 * (b⁻¹) ^ r + (c⁻¹) ^ r) * ‖Jcut n₁ (iteratedOperatorPower P j x)‖) ∧
    ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k a b n₁ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierSub ε hε h hh hb m_mass g k b c n₁ r j x‖ ≤
      4 * ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ ∧
    ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k a n₁ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x‖ +
      ‖clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k b n₂ r j x -
        clockFloorPotentialIdentityYosidaTierState ε hε h hh hb m_mass g k c n₃ r j x‖ ≤
      ‖Jcut n₁ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        2 * ‖Jcut n₂ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        ‖Jcut n₃ (iteratedOperatorPower P j x) - iteratedOperatorPower P j x‖ +
        (r : ℝ) * (a⁻¹ + 2 * b⁻¹ + c⁻¹) * ‖iteratedOperatorPower P (j + 1) x‖ := by
  have hcoc := clockFloorPotentialYosidaTierSub_three_parameter_cyclic_cocycle
    ε hε h hh hb m_mass g k a b c n₁ r j x
  have hreg := clockFloorPotentialYosidaTierSub_three_parameter_regularity_and_bounds
    ε hε h hh hb m_mass g k a b c ha hb_pos hc n₁ r j x
  have hrates := clockFloorPotentialYosida_three_and_six_parameter_cauchy_rates
    ε hε h hh hb m_mass g k a b c ha hb_pos hc n₁ n₂ n₃ m j r hjm hx
  exact ⟨hcoc, ⟨hreg.2.2.1, hreg.2.2.2⟩, hrates.1, hrates.2⟩

end ClockFloorThreeParameterPotentialYosida

#print axioms arbitraryOrderPotentialYosidaTierSub_three_parameter_cyclic_cocycle
#print axioms arbitraryOrderPotentialYosidaTierSub_three_parameter_mem_operatorPowerDomain
#print axioms arbitraryOrderPotentialYosidaTierSub_three_parameter_norm_bounds
#print axioms arbitraryOrderPotentialIdentityYosidaCutoffSub_three_regularizer_cocycle_and_bound
#print axioms arbitraryOrderPotentialIdentityYosidaTierSub_three_parameter_cauchy_rate_of_le
#print axioms arbitraryOrderPotentialIdentityYosida_joint_six_parameter_bound_of_le
#print axioms clockFloorPotentialYosidaTierSub_three_parameter_cyclic_cocycle
#print axioms clockFloorPotentialYosidaTierSub_three_parameter_regularity_and_bounds
#print axioms clockFloorPotentialYosida_three_and_six_parameter_cauchy_rates
#print axioms clockFloorPotentialYosida_threeParameter_cocycle_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaThreeParameterCocycle
