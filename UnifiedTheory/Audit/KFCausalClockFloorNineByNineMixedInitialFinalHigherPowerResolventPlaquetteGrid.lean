/- Nine-by-Nine `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉)` (`8 × 8 = 64`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Nine-Step Nonagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (sevenBySevenResolventPlaquetteGridSum
   sevenBySevenIdentityPlaquetteGridSum
   sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the sixty-four elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `9 × 9` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉)`. -/
def eightByEightResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) : Hilbert :=
  sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₂ t₃ b₈ b₉ c₈ c₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₃ t₄ c₈ c₉ e₈ e₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₄ t₅ e₈ e₉ u₈ u₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₅ t₆ u₈ u₉ v₈ v₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₆ t₇ v₈ v₉ w₈ w₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₇ t₈ w₈ w₉ z₈ z₉ r f₈ f₉) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₈ t₉ z₂ z₃ y₂ y₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₈ t₉ z₃ z₄ y₃ y₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₈ t₉ z₄ z₅ y₄ y₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₈ t₉ z₅ z₆ y₅ y₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₈ t₉ z₆ z₇ y₆ y₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₇ s₈ t₈ t₉ z₇ z₈ y₇ y₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₈ s₉ t₈ t₉ z₈ z₉ y₈ y₉ r f₈ f₉)

/-- Sum of the sixty-four elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `9 × 9` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉)`. -/
def eightByEightIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) : Hilbert :=
  sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₂ t₃ b₈ b₉ c₈ c₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₃ t₄ c₈ c₉ e₈ e₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₄ t₅ e₈ e₉ u₈ u₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₅ t₆ u₈ u₉ v₈ v₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₆ t₇ v₈ v₉ w₈ w₉ r f₈ f₉ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₇ t₈ w₈ w₉ z₈ z₉ r f₈ f₉) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₈ t₉ z₂ z₃ y₂ y₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₈ t₉ z₃ z₄ y₃ y₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₈ t₉ z₄ z₅ y₄ y₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₈ t₉ z₅ z₆ y₅ y₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₈ t₉ z₆ z₇ y₆ y₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₇ s₈ t₈ t₉ z₇ z₈ y₇ y₈ r f₇ f₈ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₈ s₉ t₈ t₉ z₈ z₉ y₈ y₉ r f₈ f₉)

/-- Exact 2D discrete Stokes boundary cancellation over the `9 × 9` grid (`8 × 8 = 64` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅, s₆, s₇, s₈` and `t₂, t₃, t₄, t₅, t₆, t₇, t₈`
cancel, leaving the outer `(s₁, s₉) × (t₁, t₉)` boundary plaquette. -/
theorem eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ ∧
    eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ := by
  have h7 := sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  unfold eightByEightResolventPlaquetteGridSum eightByEightIdentityPlaquetteGridSum
  rw [h7.1, h7.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic nine-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₈ → s₉ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₈ → t₉ → t₁)` nonagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_nine_initial_and_final_nonagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₉ s₁ t₁ t₂ a₉ a₁ b₉ b₁ r f₉ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₉ s₁ t₁ t₂ a₉ a₁ b₉ b₁ r f₉ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁ y₁ y₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁ y₁ y₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `eightByEightResolventPlaquetteGridSum`. -/
theorem eightByEightResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    let w := eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (y₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₉⁻¹) ^ (r + 2) + (y₉⁻¹) ^ (r + 2)) * ‖f₉‖ := by
  intro w
  have hstokes := (eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₉ t₁ t₉ q a₁ a₉ y₁ y₉ ha₁ ha₉ hy₁ hy₉ r f₁ f₉
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₉‖` norm bound for `eightByEightIdentityPlaquetteGridSum`. -/
theorem eightByEightIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    let y := eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₉‖ := by
  intro y
  have hstokes := (eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₉ t₁ t₉ q a₁ a₉ y₁ y₉ ha₁ ha₉ hy₁ hy₉ r f₁ f₉
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₉ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `eightByEightResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈` are arbitrary). -/
theorem eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    let w := eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₉ t q a₁ a₉ y₁ y₉ ha₁ ha₉ hy₁ hy₉ r f₁ f₉
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₉ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `eightByEightIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆, t₇, t₈` are arbitrary). -/
theorem eightByEightIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    let y := eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₉ t q a₁ a₉ y₁ y₉ ha₁ ha₉ hy₁ hy₉ r f₁ f₉
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Nine-by-Nine (`8 × 8 = 64` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem nine_by_nine_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert) :
    let w_grid := eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    let y_grid := eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    let w_grid_eq := eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    let y_grid_eq := eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (y₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₉⁻¹) ^ (r + 2) + (y₉⁻¹) ^ (r + 2)) * ‖f₉‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₉‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hw_pl := eightByEightResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hy_pl := eightByEightIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hweq := eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hyeq := eightByEightIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms eightByEightPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_nine_initial_and_final_nonagon_cocycles
#print axioms eightByEightResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms eightByEightIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms eightByEightIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms nine_by_nine_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid
