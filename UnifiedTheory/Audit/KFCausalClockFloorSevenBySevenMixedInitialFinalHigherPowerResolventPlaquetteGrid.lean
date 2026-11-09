/- Seven-by-Seven `(s₁, s₂, s₃, s₄, s₅, s₆, s₇) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇)` (`6 × 6 = 36`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D
Stokes Boundary Cancellation, Seven-Step Heptagon Cocycles, Eight-Domain Membership, and
Equal-Outer-Final-Time `Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (fourByFourResolventPlaquetteGridSum
   fourByFourIdentityPlaquetteGridSum)
open UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (fiveByFiveResolventPlaquetteGridSum
   fiveByFiveIdentityPlaquetteGridSum
   fiveByFivePlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the thirty-six elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `7 × 7` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇)`. -/
def sixBySixResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) : Hilbert :=
  fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
      r f₁ f₂ f₃ f₄ f₅ f₆ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₂ t₃ b₆ b₇ c₆ c₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₃ t₄ c₆ c₇ e₆ e₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₄ t₅ e₆ e₇ u₆ u₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₅ t₆ u₆ u₇ v₆ v₇ r f₆ f₇) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₆ t₇ v₂ v₃ w₂ w₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₆ t₇ v₃ v₄ w₃ w₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₆ t₇ v₄ v₅ w₄ w₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₆ t₇ v₅ v₆ w₅ w₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₆ s₇ t₆ t₇ v₆ v₇ w₆ w₇ r f₆ f₇)

/-- Sum of the thirty-six elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `7 × 7` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆, s₇) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇)`. -/
def sixBySixIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) : Hilbert :=
  fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
      r f₁ f₂ f₃ f₄ f₅ f₆ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₂ t₃ b₆ b₇ c₆ c₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₃ t₄ c₆ c₇ e₆ e₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₄ t₅ e₆ e₇ u₆ u₇ r f₆ f₇ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₅ t₆ u₆ u₇ v₆ v₇ r f₆ f₇) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₆ t₇ v₂ v₃ w₂ w₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₆ t₇ v₃ v₄ w₃ w₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₆ t₇ v₄ v₅ w₄ w₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₆ t₇ v₅ v₆ w₅ w₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₆ s₇ t₆ t₇ v₆ v₇ w₆ w₇ r f₆ f₇)

/-- Exact 2D discrete Stokes boundary cancellation over the `7 × 7` grid (`6 × 6 = 36` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅, s₆` and `t₂, t₃, t₄, t₅, t₆` cancel, leaving the
outer `(s₁, s₇) × (t₁, t₇)` boundary plaquette. -/
theorem sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
    sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ := by
  have h5 := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  unfold sixBySixResolventPlaquetteGridSum sixBySixIdentityPlaquetteGridSum
  rw [h5.1, h5.2]
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic seven-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₇ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₇ → t₁)` heptagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_seven_initial_and_final_heptagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇ c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₁ t₁ t₂ a₇ a₁ b₇ b₁ r f₇ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₇ s₁ t₁ t₂ a₇ a₁ b₇ b₁ r f₇ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₁ w₁ w₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₁ w₁ w₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `sixBySixResolventPlaquetteGridSum`. -/
theorem sixBySixResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    let w := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (w₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₇⁻¹) ^ (r + 2) + (w₇⁻¹) ^ (r + 2)) * ‖f₇‖ := by
  intro w
  have hstokes := (sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₇ t₁ t₇ q a₁ a₇ w₁ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₇
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₇‖` norm bound for `sixBySixIdentityPlaquetteGridSum`. -/
theorem sixBySixIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    let y := sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₇‖ := by
  intro y
  have hstokes := (sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₇ t₁ t₇ q a₁ a₇ w₁ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₇
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₇ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `sixBySixResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆` are arbitrary). -/
theorem sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    let w := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₇ t q a₁ a₇ w₁ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₇
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₇ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `sixBySixIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅, t₆` are arbitrary). -/
theorem sixBySixIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    let y := sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₇ t q a₁ a₇ w₁ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₇
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Seven-by-Seven (`6 × 6 = 36` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem seven_by_seven_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert) :
    let w_grid := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    let y_grid := sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    let w_grid_eq := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    let y_grid_eq := sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (w₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₇⁻¹) ^ (r + 2) + (w₇⁻¹) ^ (r + 2)) * ‖f₇‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₇‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hw_pl := sixBySixResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hy_pl := sixBySixIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hweq := sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hyeq := sixBySixIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms sixBySixPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_seven_initial_and_final_heptagon_cocycles
#print axioms sixBySixResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms sixBySixIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms sixBySixIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms seven_by_seven_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
