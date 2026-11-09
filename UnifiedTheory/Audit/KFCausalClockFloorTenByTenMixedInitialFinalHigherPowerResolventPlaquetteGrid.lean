/- Ten-by-Ten `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀)` (`9 × 9 = 81`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Ten-Step Decagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTenByTenMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (eightByEightResolventPlaquetteGridSum
   eightByEightIdentityPlaquetteGridSum
   eightByEightPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the eighty-one elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `10 × 10` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀)`. -/
def nineByNineResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) : Hilbert :=
  eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₂ t₃ b₉ b₁₀ c₉ c₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₃ t₄ c₉ c₁₀ e₉ e₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₄ t₅ e₉ e₁₀ u₉ u₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₅ t₆ u₉ u₁₀ v₉ v₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₆ t₇ v₉ v₁₀ w₉ w₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₇ t₈ w₉ w₁₀ z₉ z₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₈ t₉ z₉ z₁₀ y₉ y₁₀ r f₉ f₁₀) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₉ t₁₀ y₂ y₃ x₂ x₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₉ t₁₀ y₃ y₄ x₃ x₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₉ t₁₀ y₄ y₅ x₄ x₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₉ t₁₀ y₅ y₆ x₅ x₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₉ t₁₀ y₆ y₇ x₆ x₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₉ t₁₀ y₇ y₈ x₇ x₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₉ t₁₀ y₈ y₉ x₈ x₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₉ t₁₀ y₉ y₁₀ x₉ x₁₀ r f₉ f₁₀)

/-- Sum of the eighty-one elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `10 × 10` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉, s₁₀) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉, t₁₀)`. -/
def nineByNineIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) : Hilbert :=
  eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₂ t₃ b₉ b₁₀ c₉ c₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₃ t₄ c₉ c₁₀ e₉ e₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₄ t₅ e₉ e₁₀ u₉ u₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₅ t₆ u₉ u₁₀ v₉ v₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₆ t₇ v₉ v₁₀ w₉ w₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₇ t₈ w₉ w₁₀ z₉ z₁₀ r f₉ f₁₀ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₈ t₉ z₉ z₁₀ y₉ y₁₀ r f₉ f₁₀) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₉ t₁₀ y₂ y₃ x₂ x₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₉ t₁₀ y₃ y₄ x₃ x₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₉ t₁₀ y₄ y₅ x₄ x₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₉ t₁₀ y₅ y₆ x₅ x₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₉ t₁₀ y₆ y₇ x₆ x₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₉ t₁₀ y₇ y₈ x₇ x₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₉ t₁₀ y₈ y₉ x₈ x₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₉ s₁₀ t₉ t₁₀ y₉ y₁₀ x₉ x₁₀ r f₉ f₁₀)

/-- Exact 2D discrete Stokes boundary cancellation over the `10 × 10` grid (`9 × 9 = 81` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉` and `t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉`
cancel, leaving the outer `(s₁, s₁₀) × (t₁, t₁₀)` boundary plaquette. -/
theorem nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    nineByNineResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₀ t₁ t₁₀ a₁ a₁₀ x₁ x₁₀ r f₁ f₁₀ ∧
    nineByNineIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₀ t₁ t₁₀ a₁ a₁₀ x₁ x₁₀ r f₁ f₁₀ := by
  have h8 := eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  unfold nineByNineResolventPlaquetteGridSum nineByNineIdentityPlaquetteGridSum
  rw [h8.1, h8.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic ten-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₈ → s₉ → s₁₀ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₈ → t₉ → t₁₀ → t₁)` decagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_ten_initial_and_final_decagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ x₁ x₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₀ s₁ t₁ t₂ a₁₀ a₁ b₁₀ b₁ r f₁₀ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁₀ s₁ t₁ t₂ a₁₀ a₁ b₁₀ b₁ r f₁₀ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₀ t₁ x₁ x₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁₀ t₁ x₁ x₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `nineByNineResolventPlaquetteGridSum`. -/
theorem nineByNineResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₀ : 0 < a₁₀) (hx₁ : 0 < x₁) (hx₁₀ : 0 < x₁₀)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    let w := nineByNineResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (x₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₁₀⁻¹) ^ (r + 2) + (x₁₀⁻¹) ^ (r + 2)) * ‖f₁₀‖ := by
  intro w
  have hstokes := (nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₀ t₁ t₁₀ q a₁ a₁₀ x₁ x₁₀ ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₁₀
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₁₀‖` norm bound for `nineByNineIdentityPlaquetteGridSum`. -/
theorem nineByNineIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₀ : 0 < a₁₀) (hx₁ : 0 < x₁) (hx₁₀ : 0 < x₁₀)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    let y := nineByNineIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₀‖ := by
  intro y
  have hstokes := (nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₁₀ t₁ t₁₀ q a₁ a₁₀ x₁ x₁₀ ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₁₀
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₁₀ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `nineByNineResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉` are arbitrary). -/
theorem nineByNineResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₀ : 0 < a₁₀) (hx₁ : 0 < x₁) (hx₁₀ : 0 < x₁₀)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    let w := nineByNineResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₀ t q a₁ a₁₀ x₁ x₁₀ ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₁₀
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₁₀ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `nineByNineIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉` are arbitrary). -/
theorem nineByNineIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₀ : 0 < a₁₀) (hx₁ : 0 < x₁) (hx₁₀ : 0 < x₁₀)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    let y := nineByNineIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₁₀ t q a₁ a₁₀ x₁ x₁₀ ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₁₀
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Ten-by-Ten (`9 × 9 = 81` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem ten_by_ten_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₀ : 0 < a₁₀) (hx₁ : 0 < x₁) (hx₁₀ : 0 < x₁₀)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ : Hilbert) :
    let w_grid := nineByNineResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    let y_grid := nineByNineIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    let w_grid_eq := nineByNineResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    let y_grid_eq := nineByNineIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₀ t₁ t₁₀ a₁ a₁₀ x₁ x₁₀ r f₁ f₁₀ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₀ t₁ t₁₀ a₁ a₁₀ x₁ x₁₀ r f₁ f₁₀) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (x₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₁₀⁻¹) ^ (r + 2) + (x₁₀⁻¹) ^ (r + 2)) * ‖f₁₀‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₁₀‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := nineByNinePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
  have hw_pl := nineByNineResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
  have hy_pl := nineByNineIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
  have hweq := nineByNineResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
  have hyeq := nineByNineIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀
    ha₁ ha₁₀ hx₁ hx₁₀ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms nineByNinePlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_ten_initial_and_final_decagon_cocycles
#print axioms nineByNineResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms nineByNineIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms nineByNineResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms nineByNineIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms ten_by_ten_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorTenByTenMixedInitialFinalHigherPowerResolventPlaquetteGrid
