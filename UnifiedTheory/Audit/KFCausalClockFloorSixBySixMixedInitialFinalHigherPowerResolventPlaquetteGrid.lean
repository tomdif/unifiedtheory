/- Six-by-Six `(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)` (`5 × 5 = 25` Elementary
Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, Exact 2D Stokes Boundary
Cancellation, Six-Step Hexagon Cocycles, Eight-Domain Membership, and Equal-Outer-Final-Time
`Dom(H(t)^{r+2})` Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
   fourByFourIdentityPlaquetteGridSum
   fourByFourPlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the twenty-five elementary `2 × 2` mixed initial-and-final higher-power resolvent
plaquettes over the `6 × 6` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)`. -/
def fiveByFiveResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) : Hilbert :=
  fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
      r f₁ f₂ f₃ f₄ f₅ +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₂ t₃ b₅ b₆ c₅ c₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₃ t₄ c₅ c₆ e₅ e₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₄ t₅ e₅ e₆ u₅ u₆ r f₅ f₆) +
    (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₂ s₃ t₅ t₆ u₂ u₃ v₂ v₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₃ s₄ t₅ t₆ u₃ u₄ v₃ v₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₄ s₅ t₅ t₆ u₄ u₅ v₄ v₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₅ s₆ t₅ t₆ u₅ u₆ v₅ v₆ r f₅ f₆)

/-- Sum of the twenty-five elementary `2 × 2` mixed initial-and-final higher-power identity-power
plaquettes over the `6 × 6` two-time parameter grid
`(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)`. -/
def fiveByFiveIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) : Hilbert :=
  fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
      r f₁ f₂ f₃ f₄ f₅ +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₂ t₃ b₅ b₆ c₅ c₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₃ t₄ c₅ c₆ e₅ e₆ r f₅ f₆ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₄ t₅ e₅ e₆ u₅ u₆ r f₅ f₆) +
    (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₂ s₃ t₅ t₆ u₂ u₃ v₂ v₃ r f₂ f₃ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₃ s₄ t₅ t₆ u₃ u₄ v₃ v₄ r f₃ f₄ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₄ s₅ t₅ t₆ u₄ u₅ v₄ v₅ r f₄ f₅ +
     mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₅ s₆ t₅ t₆ u₅ u₆ v₅ v₆ r f₅ f₆)

/-- Exact 2D discrete Stokes boundary cancellation over the `6 × 6` grid (`5 × 5 = 25` elementary
plaquettes): all interior edges at `s₂, s₃, s₄, s₅` and `t₂, t₃, t₄, t₅` cancel, leaving the outer
`(s₁, s₆) × (t₁, t₆)` boundary plaquette. -/
theorem fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
    fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ := by
  unfold fiveByFiveResolventPlaquetteGridSum fiveByFiveIdentityPlaquetteGridSum
    fourByFourResolventPlaquetteGridSum fourByFourIdentityPlaquetteGridSum
    mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic six-step initial-time `(s₁ → s₂ → s₃ → s₄ → s₅ → s₆ → s₁)` and final-time
`(t₁ → t₂ → t₃ → t₄ → t₅ → t₆ → t₁)` hexagon cocycle vanishing for
`mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_six_initial_and_final_hexagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₁ t₁ t₂ a₆ a₁ b₆ b₁ r f₆ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₆ s₁ t₁ t₂ a₆ a₁ b₆ b₁ r f₆ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₁ v₁ v₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₁ v₁ v₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary norm bound for `fiveByFiveResolventPlaquetteGridSum`. -/
theorem fiveByFiveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let w := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    (w ∈ (K).domain ∧
     w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧
     w ∈ (Kroot).domain ∧
     w ∈ (Tpot).domain ∧
     w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧
     w ∈ (clockHalf ε).domain) ∧
    ‖w‖ ≤ ((a₁⁻¹) ^ (r + 2) + (v₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₆⁻¹) ^ (r + 2) + (v₆⁻¹) ^ (r + 2)) * ‖f₆‖ := by
  intro w
  have hstokes := (fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₆ t₁ t₆ q a₁ a₆ v₁ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₆
  dsimp only [w]
  rw [hstokes]
  exact houter

/-- Eight-domain membership (`K`, `Eop q`, `Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tsp q`, `clockHalf`)
and outer-boundary `2 * ‖f₁‖ + 2 * ‖f₆‖` norm bound for `fiveByFiveIdentityPlaquetteGridSum`. -/
theorem fiveByFiveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let y := fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    (y ∈ (K).domain ∧
     y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧
     y ∈ (Kroot).domain ∧
     y ∈ (Tpot).domain ∧
     y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧
     y ∈ (clockHalf ε).domain) ∧
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₆‖ := by
  intro y
  have hstokes := (fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₆ t₁ t₆ q a₁ a₆ v₁ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₆
  dsimp only [y]
  rw [hstokes]
  exact houter

/-- Equal-outer-final-time (`t₁ = t₆ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `fiveByFiveResolventPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅` are arbitrary). -/
theorem fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let w := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (w ∈ (H t).domain ∧ w ∈ (K).domain ∧ w ∈ (S t).domain ∧ w ∈ (Eop q).domain ∧
     w ∈ (Tstat).domain ∧ w ∈ (Kroot).domain ∧ w ∈ (Tpot).domain ∧ w ∈ (Tgrow).domain ∧
     w ∈ (Tsp q).domain ∧ w ∈ (clockHalf ε).domain) := by
  intro w
  have hstokes := (fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₆ t q a₁ a₆ v₁ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₆
  dsimp only [w]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Equal-outer-final-time (`t₁ = t₆ = t`) `hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2)`
and ten-domain regularity of `fiveByFiveIdentityPlaquetteGridSum` (even when the interior
final times `t₂, t₃, t₄, t₅` are arbitrary). -/
theorem fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let y := fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (y ∈ (H t).domain ∧ y ∈ (K).domain ∧ y ∈ (S t).domain ∧ y ∈ (Eop q).domain ∧
     y ∈ (Tstat).domain ∧ y ∈ (Kroot).domain ∧ y ∈ (Tpot).domain ∧ y ∈ (Tgrow).domain ∧
     y ∈ (Tsp q).domain ∧ y ∈ (clockHalf ε).domain) := by
  intro y
  have hstokes := (fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₆ t q a₁ a₆ v₁ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₆
  dsimp only [y]
  rw [hstokes]
  exact ⟨houter.1, houter.2.2.1⟩

/-- Master Six-by-Six (`5 × 5 = 25` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid Synthesis: 2D Stokes boundary cancellation, eight-domain membership,
outer-boundary norm bounds, and equal-outer-final-time `Dom(H(t)^{r+2})` regularity. -/
theorem six_by_six_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let w_grid := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    let y_grid := fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    let w_grid_eq := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    let y_grid_eq := fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eop q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (v₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
                ((a₆⁻¹) ^ (r + 2) + (v₆⁻¹) ^ (r + 2)) * ‖f₆‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eop q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₆‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     y_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2)) := by
  intro w_grid y_grid w_grid_eq y_grid_eq
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hw_pl := fiveByFiveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hy_pl := fiveByFiveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hweq := fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hyeq := fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hyeq.1⟩⟩

#print axioms fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_six_initial_and_final_hexagon_cocycles
#print axioms fiveByFiveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms fiveByFiveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms six_by_six_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
