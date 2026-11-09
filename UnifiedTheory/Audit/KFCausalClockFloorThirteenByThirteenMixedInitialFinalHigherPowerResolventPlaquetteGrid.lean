/- Thirteen-by-Thirteen `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂, s₁₃) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂, t₁₃)` (`12 × 12 = 144`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Thirteen-Step Tridecagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwelveByTwelveMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorTwelveByTwelveMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (elevenByElevenResolventPlaquetteGridSum
   elevenByElevenIdentityPlaquetteGridSum
   elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the one hundred forty-four elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `13 × 13` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂, s₁₃) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂, t₁₃)`. -/
def twelveByTwelveResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) : Hilbert :=
  elevenByElevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁ t₂ a₁₂ a₁₃ b₁₂ b₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₂ t₃ b₁₂ b₁₃ c₁₂ c₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₃ t₄ c₁₂ c₁₃ e₁₂ e₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₄ t₅ e₁₂ e₁₃ u₁₂ u₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₅ t₆ u₁₂ u₁₃ v₁₂ v₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₆ t₇ v₁₂ v₁₃ w₁₂ w₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₇ t₈ w₁₂ w₁₃ z₁₂ z₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₈ t₉ z₁₂ z₁₃ y₁₂ y₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₉ t₁₀ y₁₂ y₁₃ x₁₂ x₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₀ t₁₁ x₁₂ x₁₃ p₁₂ p₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₁ t₁₂ p₁₂ p₁₃ d₁₂ d₁₃ r f₁₂ f₁₃) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₁₂ t₁₃ d₁ d₂ l₁ l₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₁₂ t₁₃ d₂ d₃ l₂ l₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₁₂ t₁₃ d₃ d₄ l₃ l₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₁₂ t₁₃ d₄ d₅ l₄ l₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁₂ t₁₃ d₅ d₆ l₅ l₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁₂ t₁₃ d₆ d₇ l₆ l₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁₂ t₁₃ d₇ d₈ l₇ l₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁₂ t₁₃ d₈ d₉ l₈ l₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁₂ t₁₃ d₉ d₁₀ l₉ l₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₀ s₁₁ t₁₂ t₁₃ d₁₀ d₁₁ l₁₀ l₁₁ r f₁₀ f₁₁ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₂ t₁₃ d₁₁ d₁₂ l₁₁ l₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₂ t₁₃ d₁₂ d₁₃ l₁₂ l₁₃ r f₁₂ f₁₃)

/-- Sum of the one hundred forty-four elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `13 × 13` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀, s₁₁, s₁₂, s₁₃) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀, t₁₁, t₁₂, t₁₃)`. -/
def twelveByTwelveIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) : Hilbert :=
  elevenByElevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁ t₂ a₁₂ a₁₃ b₁₂ b₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₂ t₃ b₁₂ b₁₃ c₁₂ c₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₃ t₄ c₁₂ c₁₃ e₁₂ e₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₄ t₅ e₁₂ e₁₃ u₁₂ u₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₅ t₆ u₁₂ u₁₃ v₁₂ v₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₆ t₇ v₁₂ v₁₃ w₁₂ w₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₇ t₈ w₁₂ w₁₃ z₁₂ z₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₈ t₉ z₁₂ z₁₃ y₁₂ y₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₉ t₁₀ y₁₂ y₁₃ x₁₂ x₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₀ t₁₁ x₁₂ x₁₃ p₁₂ p₁₃ r f₁₂ f₁₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₁ t₁₂ p₁₂ p₁₃ d₁₂ d₁₃ r f₁₂ f₁₃) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₁₂ t₁₃ d₁ d₂ l₁ l₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₁₂ t₁₃ d₂ d₃ l₂ l₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₁₂ t₁₃ d₃ d₄ l₃ l₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₁₂ t₁₃ d₄ d₅ l₄ l₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁₂ t₁₃ d₅ d₆ l₅ l₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁₂ t₁₃ d₆ d₇ l₆ l₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁₂ t₁₃ d₇ d₈ l₇ l₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁₂ t₁₃ d₈ d₉ l₈ l₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁₂ t₁₃ d₉ d₁₀ l₉ l₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₀ s₁₁ t₁₂ t₁₃ d₁₀ d₁₁ l₁₀ l₁₁ r f₁₀ f₁₁ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₁ s₁₂ t₁₂ t₁₃ d₁₁ d₁₂ l₁₁ l₁₂ r f₁₁ f₁₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁₂ s₁₃ t₁₂ t₁₃ d₁₂ d₁₃ l₁₂ l₁₃ r f₁₂ f₁₃)

/-- Exact 2D discrete Stokes boundary cancellation over the `13 × 13` grid (`12 × 12 = 144` elementary
plaquettes): all interior edges at `s₂..s₁₂` and `t₂..t₁₂` cancel, leaving the outer
`(s₁, s₁₃) × (t₁, t₁₃)` boundary plaquette. -/
theorem twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ ∧
    twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ := by
  have h11 := elevenByElevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂
  unfold twelveByTwelveResolventPlaquetteGridSum twelveByTwelveIdentityPlaquetteGridSum
  rw [h11.1, h11.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic thirteen-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₈ → s₉ → s₁₀ → s₁₁ → s₁₂ → s₁₃ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₈ → t₉ → t₁₀ → t₁₁ → t₁₂ → t₁₃ → t₁)` tridecagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_thirteen_initial_and_final_tridecagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ x₁ x₂ p₁ p₂ d₁ d₂ l₁ l₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
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
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₂ s₁₃ t₁ t₂ a₁₂ a₁₃ b₁₂ b₁₃ r f₁₂ f₁₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₃ s₁ t₁ t₂ a₁₃ a₁ b₁₃ b₁ r f₁₃ f₁ = 0 ∧
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
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₂ s₁₃ t₁ t₂ a₁₂ a₁₃ b₁₂ b₁₃ r f₁₂ f₁₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₃ s₁ t₁ t₂ a₁₃ a₁ b₁₃ b₁ r f₁₃ f₁ = 0 ∧
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
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₂ t₁₃ d₁ d₂ l₁ l₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₃ t₁ l₁ l₂ a₁ a₂ r f₁ f₂ = 0 ∧
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
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₂ t₁₃ d₁ d₂ l₁ l₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₃ t₁ l₁ l₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `twelveByTwelveResolventPlaquetteGridSum`. -/
theorem twelveByTwelveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let w := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (l₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₁₃⁻¹) ^ (r + 2) + (l₁₃⁻¹) ^ (r + 2)) * ‖f₁₃‖ := by
  intro w
  have hstokes := (twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₃ t₁ t₁₃ q a₁ a₁₃ l₁ l₁₃ ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₁₃
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₁₃‖` norm bound for `twelveByTwelveIdentityPlaquetteGridSum`. -/
theorem twelveByTwelveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let y := twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₃‖ := by
  intro y
  have hstokes := (twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₃ t₁ t₁₃ q a₁ a₁₃ l₁ l₁₃ ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₁₃
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₁₃ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `twelveByTwelveResolventPlaquetteGridSum` (even when the interior
final times `t₂..t₁₂` are arbitrary). -/
theorem twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let w := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₃ t q a₁ a₁₃ l₁ l₁₃ ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₁₃
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₁₃ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `twelveByTwelveIdentityPlaquetteGridSum` (even when the interior
final times `t₂..t₁₂` are arbitrary). -/
theorem twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let y := twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₃ t q a₁ a₁₃ l₁ l₁₃ ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₁₃
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Thirteen-by-Thirteen (`12 × 12 = 144` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem thirteen_by_thirteen_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let w_grid := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    let y_grid := twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    let w_grid_eq := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    let y_grid_eq := twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (l₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₁₃⁻¹) ^ (r + 2) + (l₁₃⁻¹) ^ (r + 2)) * ‖f₁₃‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₃‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hw_pl := twelveByTwelveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hy_pl := twelveByTwelveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hweq := twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hyeq := twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_thirteen_initial_and_final_tridecagon_cocycles
#print axioms twelveByTwelveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms twelveByTwelveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms thirteen_by_thirteen_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid
