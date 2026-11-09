/- Eight-by-Eight `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈)` (`7 × 7 = 49`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Eight-Step Octagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (sixBySixResolventPlaquetteGridSum
   sixBySixIdentityPlaquetteGridSum
   sixBySixPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the forty-nine elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `8 × 8` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈)`. -/
def sevenBySevenResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) : Hilbert :=
  sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₂ t₃ b₇ b₈ c₇ c₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₃ t₄ c₇ c₈ e₇ e₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₄ t₅ e₇ e₈ u₇ u₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₅ t₆ u₇ u₈ v₇ v₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₆ t₇ v₇ v₈ w₇ w₈ r f₇ f₈) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₇ t₈ w₂ w₃ z₂ z₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₇ t₈ w₃ w₄ z₃ z₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₇ t₈ w₄ w₅ z₄ z₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₇ t₈ w₅ w₆ z₅ z₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₇ t₈ w₆ w₇ z₆ z₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₇ t₈ w₇ w₈ z₇ z₈ r f₇ f₈)

/-- Sum of the forty-nine elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `8 × 8` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈)`. -/
def sevenBySevenIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) : Hilbert :=
  sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₂ t₃ b₇ b₈ c₇ c₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₃ t₄ c₇ c₈ e₇ e₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₄ t₅ e₇ e₈ u₇ u₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₅ t₆ u₇ u₈ v₇ v₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₆ t₇ v₇ v₈ w₇ w₈ r f₇ f₈) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₇ t₈ w₂ w₃ z₂ z₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₇ t₈ w₃ w₄ z₃ z₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₇ t₈ w₄ w₅ z₄ z₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₇ t₈ w₅ w₆ z₅ z₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₇ t₈ w₆ w₇ z₆ z₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₇ t₈ w₇ w₈ z₇ z₈ r f₇ f₈)

/-- Exact 2D discrete Stokes boundary cancellation over the `8 × 8` grid (`7 × 7 = 49` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅, s₆, s₇` and `t₂, t₃, t₄, t₅, t₆, t₇` cancel,
leaving the outer `(s₁, s₈) × (t₁, t₈)` boundary plaquette. -/
theorem sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ ∧
    sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ := by
  have h6 := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  unfold sevenBySevenResolventPlaquetteGridSum sevenBySevenIdentityPlaquetteGridSum
  rw [h6.1, h6.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic eight-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₈ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₈ → t₁)` octagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_eight_initial_and_final_octagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₈ s₁ t₁ t₂ a₈ a₁ b₈ b₁ r f₈ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₈ s₁ t₁ t₂ a₈ a₁ b₈ b₁ r f₈ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₁ z₁ z₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₁ z₁ z₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `sevenBySevenResolventPlaquetteGridSum`. -/
theorem sevenBySevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    let w := sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (z₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₈⁻¹) ^ (r + 2) + (z₈⁻¹) ^ (r + 2)) * ‖f₈‖ := by
  intro w
  have hstokes := (sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₈ t₁ t₈ q a₁ a₈ z₁ z₈ ha₁ ha₈ hz₁ hz₈ r f₁ f₈
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₈‖` norm bound for `sevenBySevenIdentityPlaquetteGridSum`. -/
theorem sevenBySevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    let y := sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₈‖ := by
  intro y
  have hstokes := (sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₈ t₁ t₈ q a₁ a₈ z₁ z₈ ha₁ ha₈ hz₁ hz₈ r f₁ f₈
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₈ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `sevenBySevenResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇` are arbitrary). -/
theorem sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    let w := sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₈ t q a₁ a₈ z₁ z₈ ha₁ ha₈ hz₁ hz₈ r f₁ f₈
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₈ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `sevenBySevenIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇` are arbitrary). -/
theorem sevenBySevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    let y := sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₈ t q a₁ a₈ z₁ z₈ ha₁ ha₈ hz₁ hz₈ r f₁ f₈
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Eight-by-Eight (`7 × 7 = 49` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem eight_by_eight_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert) :
    let w_grid := sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    let y_grid := sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    let w_grid_eq := sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    let y_grid_eq := sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (z₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₈⁻¹) ^ (r + 2) + (z₈⁻¹) ^ (r + 2)) * ‖f₈‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₈‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hw_pl := sevenBySevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hy_pl := sevenBySevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hweq := sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hyeq := sevenBySevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_eight_initial_and_final_octagon_cocycles
#print axioms sevenBySevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms sevenBySevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms sevenBySevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms eight_by_eight_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid
