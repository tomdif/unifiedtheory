/- Two-Time Mixed Initial-and-Final (`(s₁, s₂)` and `(t₁, t₂)`) Four-Corner Higher-Power
Iterated Resolvent and Yosida Identity Plaquette Double-Differences, Horizontal-Vertical
Commutator Symmetry, 8-Domain and Equal-Final-Time 10-Domain + `Dom(H(t)^{r+2})`
Regularity, and Vertical Three-Time Plaquette Stacking Cocycle. -/
import UnifiedTheory.Audit.KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHigherPowerOperatorCores
  (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeEvolvedHigherPowerResolventRegularity
  (higherPowerResolventOfEvolvedState
   higherPowerIdentityOfEvolvedState)
open KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
  (crossInitialHigherPowerResolventDiff
   crossInitialHigherPowerIdentityDiff
   crossFinalHigherPowerResolventDiff
   crossFinalHigherPowerIdentityDiff
   crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
   crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
   crossFinalHigherPowerResolventDiff_mem_eight_domains_and_norm_le
   crossFinalHigherPowerIdentityDiff_mem_eight_domains_and_norm_le)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- Mixed initial-and-final `(s₁, s₂)` and `(t₁, t₂)` four-corner `(r + 2)`-fold iterated
Hamiltonian resolvent plaquette double difference at `(a, b, c, d)` and `(f₁, f₂)`:
`crossInitialHigherPowerResolventDiff s₁ s₂ t₁ a b r f₁ f₂ - crossInitialHigherPowerResolventDiff s₁ s₂ t₂ c d r f₁ f₂`. -/
def mixedInitialFinalHigherPowerResolventPlaquette
    (s₁ s₂ t₁ t₂ a b c d : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) : Hilbert :=
  crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂ -
    crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t₂ c d r f₁ f₂

/-- Mixed initial-and-final `(s₁, s₂)` and `(t₁, t₂)` four-corner `(r + 2)`-th order Yosida
identity plaquette double difference at `(a, b, c, d)` and `(f₁, f₂)`. -/
def mixedInitialFinalHigherPowerIdentityPlaquette
    (s₁ s₂ t₁ t₂ a b c d : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) : Hilbert :=
  crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂ -
    crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t₂ c d r f₁ f₂

/-- Horizontal-vertical commutator symmetry (`crossInitial - crossInitial = crossFinal - crossFinal`),
diagonal vanishing in both initial and final coordinates, and vertical 3-time `(t₁, t₂, t₃)`
plaquette stacking cocycle for `mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_commutator_and_vertical_stacking
    (s₁ s₂ t₁ t₂ t₃ a b c d e₁ e₂ : ℝ) (r : ℕ) (f₁ f₂ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂ =
      crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s₁ t₁ t₂ a c r f₁ -
        crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s₂ t₁ t₂ b d r f₂ ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂ =
      crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s₁ t₁ t₂ a c r f₁ -
        crossFinalHigherPowerIdentityDiff ε hε h hh hb m g k s₂ t₁ t₂ b d r f₂ ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₁ t₁ t₂ a a c c r f₁ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₁ a b a b r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂ +
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c d e₁ e₂ r f₁ f₂ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₃ a b e₁ e₂ r f₁ f₂ ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂ +
        mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c d e₁ e₂ r f₁ f₂ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₃ a b e₁ e₂ r f₁ f₂ := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
    crossFinalHigherPowerResolventDiff crossFinalHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel, by abel, by abel⟩

/-- Horizontal 3-initial `(s₁, s₂, s₃)` plaquette stacking cocycle for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_horizontal_stacking
    (s₁ s₂ s₃ t₁ t₂ a₁ a₂ a₃ c₁ c₂ c₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₃ t₁ t₂ a₁ a₃ c₁ c₃ r f₁ f₃ ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
        mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₃ t₁ t₂ a₁ a₃ c₁ c₃ r f₁ f₃ := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Unconditionally for all `s₁, s₂, t₁, t₂, q ∈ ℝ`, `0 < a, 0 < b, 0 < c, 0 < d`, and `r : ℕ`,
`mixedInitialFinalHigherPowerResolventPlaquette s₁ s₂ t₁ t₂ a b c d r f₁ f₂` belongs
simultaneously to all 8 time-independent / observation-time `q` domains (`K`, `Eavg q`,
`Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tres q`, `clockHalf ε`) with 4-corner geometric norm bound
`((a⁻¹)^{r+2} + (c⁻¹)^{r+2}) * ‖f₁‖ + ((b⁻¹)^{r+2} + (d⁻¹)^{r+2}) * ‖f₂‖`. -/
theorem mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    (s₁ s₂ t₁ t₂ q a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    (w ∈ (K).domain ∧
     w ∈ (Eavg q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tres q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖ := by
  intro w
  have ht1 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  have ht2 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₂ q c d hc hd r f₁ f₂
  have hnorm :
      ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
        ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖ := by
    dsimp only [w, mixedInitialFinalHigherPowerResolventPlaquette]
    have htri := norm_sub_le
      (crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂)
      (crossInitialHigherPowerResolventDiff ε hε h hh hb m g k s₁ s₂ t₂ c d r f₁ f₂)
    linarith [ht1.2.2.2.1, ht2.2.2.2.1]
  exact ⟨⟨(K).domain.sub_mem ht1.2.2.1.2.1 ht2.2.2.1.2.1,
    (Eavg q).domain.sub_mem ht1.2.2.1.2.2.2.1 ht2.2.2.1.2.2.2.1,
    (Tstat).domain.sub_mem ht1.2.2.1.2.2.2.2.1 ht2.2.2.1.2.2.2.2.1,
    (Kroot).domain.sub_mem ht1.2.2.1.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.1,
    (Tpot).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.1,
    (Tgrow).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.2.1,
    (Tres q).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.2.2 ht2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- Unconditionally for all `s₁, s₂, t₁, t₂, q ∈ ℝ`, `0 < a, 0 < b, 0 < c, 0 < d`, and `r : ℕ`,
`mixedInitialFinalHigherPowerIdentityPlaquette s₁ s₂ t₁ t₂ a b c d r f₁ f₂` belongs
simultaneously to all 8 time-independent / observation-time `q` domains with uniform
parameter-free stability `‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖`. -/
theorem mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    (s₁ s₂ t₁ t₂ q a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert) :
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    (y ∈ (K).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖ := by
  intro y
  have ht1 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b ha hb_pos r f₁ f₂
  have ht2 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₂ q c d hc hd r f₁ f₂
  have hnorm : ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖ := by
    dsimp only [y, mixedInitialFinalHigherPowerIdentityPlaquette]
    have htri := norm_sub_le
      (crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t₁ a b r f₁ f₂)
      (crossInitialHigherPowerIdentityDiff ε hε h hh hb m g k s₁ s₂ t₂ c d r f₁ f₂)
    linarith [ht1.2.2.2.1, ht2.2.2.2.1]
  exact ⟨⟨(K).domain.sub_mem ht1.2.2.1.2.1 ht2.2.2.1.2.1,
    (Eavg q).domain.sub_mem ht1.2.2.1.2.2.2.1 ht2.2.2.1.2.2.2.1,
    (Tstat).domain.sub_mem ht1.2.2.1.2.2.2.2.1 ht2.2.2.1.2.2.2.2.1,
    (Kroot).domain.sub_mem ht1.2.2.1.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.1,
    (Tpot).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.1,
    (Tgrow).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.2.1,
    (Tres q).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.2.1 ht2.2.2.1.2.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem ht1.2.2.1.2.2.2.2.2.2.2.2.2 ht2.2.2.1.2.2.2.2.2.2.2.2.2⟩,
    hnorm⟩

/-- At equal final time `t₁ = t₂ = t` with distinct shift pairs `(a, b)` and `(c, d)`,
`mixedInitialFinalHigherPowerResolventPlaquette s₁ s₂ t t a b c d r f₁ f₂` belongs
simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains. -/
theorem mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    (s₁ s₂ t q a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t t a b c d r f₁ f₂
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    w ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (w ∈ (H t).domain ∧
     w ∈ (K).domain ∧
     w ∈ (S t).domain ∧
     w ∈ (Eavg q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tres q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖ := by
  intro w
  have ht1 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b ha hb_pos r f₁ f₂
  have ht2 := crossInitialHigherPowerResolventDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q c d hc hd r f₁ f₂
  have h8 := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t t q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem ht1.1 ht2.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem ht1.2.1 ht2.2.1,
    ⟨(H t).domain.sub_mem ht1.2.2.1.1 ht2.2.2.1.1,
     h8.1.1,
     (S t).domain.sub_mem ht1.2.2.1.2.2.1 ht2.2.2.1.2.2.1,
     h8.1.2.1, h8.1.2.2.1, h8.1.2.2.2.1, h8.1.2.2.2.2.1,
     h8.1.2.2.2.2.2.1, h8.1.2.2.2.2.2.2.1, h8.1.2.2.2.2.2.2.2⟩,
    h8.2⟩

/-- At equal final time `t₁ = t₂ = t` with distinct shift pairs `(a, b)` and `(c, d)`,
`mixedInitialFinalHigherPowerIdentityPlaquette s₁ s₂ t t a b c d r f₁ f₂` belongs
simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains with `‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖`. -/
theorem mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    (s₁ s₂ t q a b c d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert) :
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t t a b c d r f₁ f₂
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    y ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (y ∈ (H t).domain ∧
     y ∈ (K).domain ∧
     y ∈ (S t).domain ∧
     y ∈ (Eavg q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tres q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖ := by
  intro y
  have ht1 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b ha hb_pos r f₁ f₂
  have ht2 := crossInitialHigherPowerIdentityDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q c d hc hd r f₁ f₂
  have h8 := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t t q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨(hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)).sub_mem ht1.1 ht2.1,
    (hamiltonianSecondPowerDomain ε hε h hh hb m g k t).sub_mem ht1.2.1 ht2.2.1,
    ⟨(H t).domain.sub_mem ht1.2.2.1.1 ht2.2.2.1.1,
     h8.1.1,
     (S t).domain.sub_mem ht1.2.2.1.2.2.1 ht2.2.2.1.2.2.1,
     h8.1.2.1, h8.1.2.2.1, h8.1.2.2.2.1, h8.1.2.2.2.2.1,
     h8.1.2.2.2.2.2.1, h8.1.2.2.2.2.2.2.1, h8.1.2.2.2.2.2.2.2⟩,
    h8.2⟩

/-- Master Two-Time Mixed Initial-and-Final Four-Corner Higher-Power Resolvent Plaquette
Synthesis Theorem. -/
theorem two_time_mixed_initial_final_higher_power_resolvent_plaquette_master_synthesis
    (s₁ s₂ t₁ t₂ t₃ q a b c d e₁ e₂ : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    let w_eq := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₁ a b c d r f₁ f₂
    (w = crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s₁ t₁ t₂ a c r f₁ -
          crossFinalHigherPowerResolventDiff ε hε h hh hb m g k s₂ t₁ t₂ b d r f₂ ∧
     w + mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c d e₁ e₂ r f₁ f₂ =
       mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₃ a b e₁ e₂ r f₁ f₂) ∧
    (w ∈ (K).domain ∧ w ∈ (Eavg q).domain ∧ w ∈ (clockHalf ε).domain ∧
     ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
       ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖) ∧
    (y ∈ (K).domain ∧ y ∈ (Eavg q).domain ∧ y ∈ (clockHalf ε).domain ∧
     ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖) ∧
    (w_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     w_eq ∈ (H t₁).domain ∧ w_eq ∈ (S t₁).domain) := by
  intro w y w_eq
  have hcomm := mixedInitialFinalHigherPowerPlaquette_commutator_and_vertical_stacking
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ t₃ a b c d e₁ e₂ r f₁ f₂
  have hw_pl := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  have hy := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  have hweq := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨⟨hcomm.1, hcomm.2.2.2.2.1⟩,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy.1.1, hy.1.2.1, hy.1.2.2.2.2.2.2.2, hy.2⟩,
    ⟨hweq.1, hweq.2.2.1.1, hweq.2.2.1.2.2.1⟩⟩

#print axioms mixedInitialFinalHigherPowerPlaquette_commutator_and_vertical_stacking
#print axioms mixedInitialFinalHigherPowerPlaquette_horizontal_stacking
#print axioms mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
#print axioms mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
#print axioms mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
#print axioms mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
#print axioms two_time_mixed_initial_final_higher_power_resolvent_plaquette_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
