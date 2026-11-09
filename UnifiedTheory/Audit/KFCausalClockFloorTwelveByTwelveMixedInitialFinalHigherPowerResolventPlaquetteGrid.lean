/- Twelve-by-Twelve `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂)` (`11 × 11 = 121`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Twelve-Step Dodecagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorElevenByElevenMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwelveByTwelveMixedInitialFinalHigherPowerResolventPlaquetteGrid

noncomputable section

open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
  (crossInitialHigherPowerResolventDiff
   crossInitialHigherPowerIdentityDiff
   crossFinalHigherPowerResolventDiff
   crossFinalHigherPowerIdentityDiff)
open UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette
   mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
   mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains)
open UnifiedTheory.Audit.KFCausalClockFloorElevenByElevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (tenByTenResolventPlaquetteGridSum
   tenByTenIdentityPlaquetteGridSum
   tenByTenPlaquetteGridSum_stokes_boundary_cancellation)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "hb_h" => hamiltonian_bound ε h hw
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tsp" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eop" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h hb_h hh m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k

/-- Sum of the one hundred twenty-one elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `12 × 12` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂)`. -/
def elevenByElevenResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) : Hilbert :=
  tenByTenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁ t₂ a₁₁ a₁₂ b₁₁ b₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₂ t₃ b₁₁ b₁₂ c₁₁ c₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₃ t₄ c₁₁ c₁₂ e₁₁ e₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₄ t₅ e₁₁ e₁₂ u₁₁ u₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₅ t₆ u₁₁ u₁₂ v₁₁ v₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₆ t₇ v₁₁ v₁₂ w₁₁ w₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₇ t₈ w₁₁ w₁₂ z₁₁ z₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₈ t₉ z₁₁ z₁₂ y₁₁ y₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₉ t₁₀ y₁₁ y₁₂ x₁₁ x₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₀ t₁₁ x₁₁ x₁₂ p₁₁ p₁₂ r f₁₁ f₁₂) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₁₁ t₁₂ p₁ p₂ d₁ d₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₁₁ t₁₂ p₂ p₃ d₂ d₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₁₁ t₁₂ p₃ p₄ d₃ d₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₁₁ t₁₂ p₄ p₅ d₄ d₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁₁ t₁₂ p₅ p₆ d₅ d₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁₁ t₁₂ p₆ p₇ d₆ d₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁₁ t₁₂ p₇ p₈ d₇ d₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁₁ t₁₂ p₈ p₉ d₈ d₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁₁ t₁₂ p₉ p₁₀ d₉ d₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₀ s₁₁ t₁₁ t₁₂ p₁₀ p₁₁ d₁₀ d₁₁ r f₁₀ f₁₁ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₁ t₁₂ p₁₁ p₁₂ d₁₁ d₁₂ r f₁₁ f₁₂)

/-- Sum of the one hundred twenty-one elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `12 × 12` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂)`. -/
def elevenByElevenIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) : Hilbert :=
  tenByTenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁ t₂ a₁₁ a₁₂ b₁₁ b₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₂ t₃ b₁₁ b₁₂ c₁₁ c₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₃ t₄ c₁₁ c₁₂ e₁₁ e₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₄ t₅ e₁₁ e₁₂ u₁₁ u₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₅ t₆ u₁₁ u₁₂ v₁₁ v₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₆ t₇ v₁₁ v₁₂ w₁₁ w₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₇ t₈ w₁₁ w₁₂ z₁₁ z₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₈ t₉ z₁₁ z₁₂ y₁₁ y₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₉ t₁₀ y₁₁ y₁₂ x₁₁ x₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₀ t₁₁ x₁₁ x₁₂ p₁₁ p₁₂ r f₁₁ f₁₂) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₁₁ t₁₂ p₁ p₂ d₁ d₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₁₁ t₁₂ p₂ p₃ d₂ d₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₁₁ t₁₂ p₃ p₄ d₃ d₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₁₁ t₁₂ p₄ p₅ d₄ d₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁₁ t₁₂ p₅ p₆ d₅ d₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁₁ t₁₂ p₆ p₇ d₆ d₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁₁ t₁₂ p₇ p₈ d₇ d₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁₁ t₁₂ p₈ p₉ d₈ d₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁₁ t₁₂ p₉ p₁₀ d₉ d₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₀ s₁₁ t₁₁ t₁₂ p₁₀ p₁₁ d₁₀ d₁₁ r f₁₀ f₁₁ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₁ t₁₂ p₁₁ p₁₂ d₁₁ d₁₂ r f₁₁ f₁₂)

/-- Exact 2D discrete Stokes boundary cancellation over the `12 × 12` grid (`11 × 11 = 121` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁` and
`t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁` cancel, leaving the outer `(s₁, s₁₂) × (t₁, t₁₂)`
boundary plaquette. -/
theorem elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₂ t₁ t₁₂ a₁ a₁₂ d₁ d₁₂ r f₁ f₁₂ ∧
    elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₂ t₁ t₁₂ a₁ a₁₂ d₁ d₁₂ r f₁ f₁₂ := by
  have h10 := tenByTenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁
  unfold elevenByElevenResolventPlaquetteGridSum elevenByElevenIdentityPlaquetteGridSum
  rw [h10.1, h10.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic twelve-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₈ → s₉ → s₁₀ → s₁₁ → s₁₂ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₈ → t₉ → t₁₀ → t₁₁ → t₁₂ → t₁)` dodecagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_twelve_initial_and_final_dodecagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ x₁ x₂ p₁ p₂ d₁ d₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₀ s₁₁ t₁ t₂ a₁₀ a₁₁ b₁₀ b₁₁ r f₁₀ f₁₁ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₁ s₁₂ t₁ t₂ a₁₁ a₁₂ b₁₁ b₁₂ r f₁₁ f₁₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₂ s₁ t₁ t₂ a₁₂ a₁ b₁₂ b₁ r f₁₂ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₀ s₁₁ t₁ t₂ a₁₀ a₁₁ b₁₀ b₁₁ r f₁₀ f₁₁ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₁ s₁₂ t₁ t₂ a₁₁ a₁₂ b₁₁ b₁₂ r f₁₁ f₁₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₂ s₁ t₁ t₂ a₁₂ a₁ b₁₂ b₁ r f₁₂ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₀ t₁₁ x₁ x₂ p₁ p₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₁ t₁₂ p₁ p₂ d₁ d₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₂ t₁ d₁ d₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₀ t₁₁ x₁ x₂ p₁ p₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₁ t₁₂ p₁ p₂ d₁ d₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₂ t₁ d₁ d₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `elevenByElevenResolventPlaquetteGridSum`. -/
theorem elevenByElevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₂ : 0 < a₁₂) (hd₁ : 0 < d₁) (hd₁₂ : 0 < d₁₂)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    let w := elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (d₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₁₂⁻¹) ^ (r + 2) + (d₁₂⁻¹) ^ (r + 2)) * ‖f₁₂‖ := by
  intro w
  have hstokes := (elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₂ t₁ t₁₂ q a₁ a₁₂ d₁ d₁₂ ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₁₂
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₁₂‖` norm bound for `elevenByElevenIdentityPlaquetteGridSum`. -/
theorem elevenByElevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₂ : 0 < a₁₂) (hd₁ : 0 < d₁) (hd₁₂ : 0 < d₁₂)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    let y := elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₂‖ := by
  intro y
  have hstokes := (elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₂ t₁ t₁₂ q a₁ a₁₂ d₁ d₁₂ ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₁₂
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₁₂ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `elevenByElevenResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁` are arbitrary). -/
theorem elevenByElevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₂ : 0 < a₁₂) (hd₁ : 0 < d₁) (hd₁₂ : 0 < d₁₂)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    let w := elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₂ t q a₁ a₁₂ d₁ d₁₂ ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₁₂
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₁₂ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `elevenByElevenIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁` are arbitrary). -/
theorem elevenByElevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₂ : 0 < a₁₂) (hd₁ : 0 < d₁) (hd₁₂ : 0 < d₁₂)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    let y := elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₂ t q a₁ a₁₂ d₁ d₁₂ ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₁₂
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Twelve-by-Twelve (`11 × 11 = 121` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem twelve_by_twelve_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₂ : 0 < a₁₂) (hd₁ : 0 < d₁) (hd₁₂ : 0 < d₁₂)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ : Hilbert) :
    let w_grid := elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    let y_grid := elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    let w_grid_eq := elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    let y_grid_eq := elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₂ t₁ t₁₂ a₁ a₁₂ d₁ d₁₂ r f₁ f₁₂ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₂ t₁ t₁₂ a₁ a₁₂ d₁ d₁₂ r f₁ f₁₂) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (d₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₁₂⁻¹) ^ (r + 2) + (d₁₂⁻¹) ^ (r + 2)) * ‖f₁₂‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₂‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  have hw_pl := elevenByElevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  have hy_pl := elevenByElevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  have hweq := elevenByElevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  have hyeq := elevenByElevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    ha₁ ha₁₂ hd₁ hd₁₂ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_twelve_initial_and_final_dodecagon_cocycles
#print axioms elevenByElevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms elevenByElevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms elevenByElevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms elevenByElevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms twelve_by_twelve_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTwelveByTwelveMixedInitialFinalHigherPowerResolventPlaquetteGrid
