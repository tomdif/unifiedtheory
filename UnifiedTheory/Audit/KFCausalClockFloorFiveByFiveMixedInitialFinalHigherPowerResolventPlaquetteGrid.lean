/- Five-by-Five `(s₁, s₂, s₃, s₄, s₅) × (t₁, t₂, t₃, t₄, t₅)` (`4 × 4 = 16` Elementary Plaquettes)
Mixed Initial-and-Final Higher-Power Iterated Resolvent and Yosida Identity Plaquette Grid,
Exact 2D Stokes / Green Plaquette Boundary Cancellation Across Sixteen Interior Cells,
Cyclic Five-Step Plaquette Pentagon Cocycles, and 8-Domain / Equal-Final-Time 10-Domain
Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
open UnifiedTheory.Audit.KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (threeByThreeResolventPlaquetteGridSum
   threeByThreeIdentityPlaquetteGridSum
   threeByThreePlaquetteGridSum_stokes_boundary_cancellation)

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

/-- Sum of the sixteen (`4 × 4`) elementary `(r + 2)`-fold iterated Hamiltonian resolvent plaquettes
in a `5 × 5` initial-final time grid `(s₁, s₂, s₃, s₄, s₅) × (t₁, t₂, t₃, t₄, t₅)` with spectral
parameters `(a₁..a₅)`, `(b₁..b₅)`, `(c₁..c₅)`, `(e₁..e₅)`, `(u₁..u₅)` and source vectors
`(f₁, f₂, f₃, f₄, f₅)`. -/
def fourByFourResolventPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ b₂ b₃ c₂ c₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₂ t₃ b₃ b₄ c₃ c₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₂ t₃ b₄ b₅ c₄ c₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₃ t₄ c₂ c₃ e₂ e₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₃ t₄ c₃ c₄ e₃ e₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₃ t₄ c₄ c₅ e₄ e₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₄ t₅ e₂ e₃ u₂ u₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₄ t₅ e₃ e₄ u₃ u₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₄ t₅ e₄ e₅ u₄ u₅ r f₄ f₅)

/-- Sum of the sixteen (`4 × 4`) elementary `(r + 2)`-th order Yosida identity plaquettes in a
`5 × 5` initial-final time grid `(s₁, s₂, s₃, s₄, s₅) × (t₁, t₂, t₃, t₄, t₅)`. -/
def fourByFourIdentityPlaquetteGridSum
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ b₂ b₃ c₂ c₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₂ t₃ b₃ b₄ c₃ c₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₂ t₃ b₄ b₅ c₄ c₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₃ t₄ c₂ c₃ e₂ e₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₃ t₄ c₃ c₄ e₃ e₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₃ t₄ c₄ c₅ e₄ e₅ r f₄ f₅) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₄ t₅ e₂ e₃ u₂ u₃ r f₂ f₃ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₄ t₅ e₃ e₄ u₃ u₄ r f₃ f₄ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₄ t₅ e₄ e₅ u₄ u₅ r f₄ f₅)

/-- Exact 2D Stokes / Green plaquette boundary cancellation on the `5 × 5` (`16`-cell) time-parameter
grid: `fourByFourResolventPlaquetteGridSum` and `fourByFourIdentityPlaquetteGridSum` equal the
single outer boundary plaquette between `(s₁, s₅)` and `(t₁, t₅)` at `(a₁, a₅, u₁, u₅)` and
`(f₁, f₅)`, canceling all 9 interior vertices `(s₂..s₄) × (t₂..t₄)` and all 24 interior edges. -/
theorem fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ ∧
    fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ := by
  unfold fourByFourResolventPlaquetteGridSum fourByFourIdentityPlaquetteGridSum
    mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic 5-step initial-time `(s₁, s₂, s₃, s₄, s₅)` and final-time `(t₁, t₂, t₃, t₄, t₅)`
plaquette pentagon cocycles for `mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_five_initial_and_final_pentagon_cocycles
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ e₁ e₂ u₁ u₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₁ t₁ t₂ a₅ a₁ b₅ b₁ r f₅ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₅ s₁ t₁ t₂ a₅ a₁ b₅ b₁ r f₅ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₁ u₁ u₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₁ u₁ u₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s₁..s₅, t₁..t₅, q ∈ ℝ`, `0 < a₁, a₅, u₁, u₅`, and `r : ℕ`,
`fourByFourResolventPlaquetteGridSum` belongs simultaneously to all 8 time-independent /
observation-time `q` domains with outer-corner geometric norm bound independent of all interior
times, parameters, and sources. -/
theorem fourByFourResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    let w_grid := fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    (w_grid ∈ (K).domain ∧
     w_grid ∈ (Eavg q).domain ∧
     w_grid ∈ (Tstat).domain ∧
     w_grid ∈ (Kroot).domain ∧
     w_grid ∈ (Tpot).domain ∧
     w_grid ∈ (Tgrow).domain ∧
     w_grid ∈ (Tres q).domain ∧
     w_grid ∈ (clockHalf ε).domain) ∧
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (u₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₅⁻¹) ^ (r + 2) + (u₅⁻¹) ^ (r + 2)) * ‖f₅‖ := by
  intro w_grid
  have hstokes := (fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₅ t₁ t₅ q a₁ a₅ u₁ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₅
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- Unconditionally for all `s₁..s₅, t₁..t₅, q ∈ ℝ`, `0 < a₁, a₅, u₁, u₅`, and `r : ℕ`,
`fourByFourIdentityPlaquetteGridSum` belongs simultaneously to all 8 time-independent /
observation-time `q` domains with outer-corner stability bound `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖`. -/
theorem fourByFourIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    let y_grid := fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    (y_grid ∈ (K).domain ∧
     y_grid ∈ (Eavg q).domain ∧
     y_grid ∈ (Tstat).domain ∧
     y_grid ∈ (Kroot).domain ∧
     y_grid ∈ (Tpot).domain ∧
     y_grid ∈ (Tgrow).domain ∧
     y_grid ∈ (Tres q).domain ∧
     y_grid ∈ (clockHalf ε).domain) ∧
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖ := by
  intro y_grid
  have hstokes := (fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₅ t₁ t₅ q a₁ a₅ u₁ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₅
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₅ = t`), `fourByFourResolventPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains regardless of the intermediate times `(t₂, t₃, t₄)`. -/
theorem fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    let w_grid := fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    w_grid ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    w_grid ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (w_grid ∈ (H t).domain ∧
     w_grid ∈ (K).domain ∧
     w_grid ∈ (S t).domain ∧
     w_grid ∈ (Eavg q).domain ∧
     w_grid ∈ (Tstat).domain ∧
     w_grid ∈ (Kroot).domain ∧
     w_grid ∈ (Tpot).domain ∧
     w_grid ∈ (Tgrow).domain ∧
     w_grid ∈ (Tres q).domain ∧
     w_grid ∈ (clockHalf ε).domain) ∧
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (u₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₅⁻¹) ^ (r + 2) + (u₅⁻¹) ^ (r + 2)) * ‖f₅‖ := by
  intro w_grid
  have hstokes := (fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₅ t q a₁ a₅ u₁ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₅
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₅ = t`), `fourByFourIdentityPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains with `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖`. -/
theorem fourByFourIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    let y_grid := fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    y_grid ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    y_grid ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    (y_grid ∈ (H t).domain ∧
     y_grid ∈ (K).domain ∧
     y_grid ∈ (S t).domain ∧
     y_grid ∈ (Eavg q).domain ∧
     y_grid ∈ (Tstat).domain ∧
     y_grid ∈ (Kroot).domain ∧
     y_grid ∈ (Tpot).domain ∧
     y_grid ∈ (Tgrow).domain ∧
     y_grid ∈ (Tres q).domain ∧
     y_grid ∈ (clockHalf ε).domain) ∧
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖ := by
  intro y_grid
  have hstokes := (fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₅ t q a₁ a₅ u₁ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₅
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- Master Five-by-Five `(s₁, s₂, s₃, s₄, s₅) × (t₁, t₂, t₃, t₄, t₅)` (`4 × 4 = 16` Cells) Mixed
Initial-and-Final Higher-Power Resolvent Plaquette Grid and 2D Stokes Boundary Cancellation
Synthesis. -/
theorem five_by_five_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
    let w_grid := fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    let y_grid := fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    let w_grid_eq := fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₁
      a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eavg q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (u₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
       ((a₅⁻¹) ^ (r + 2) + (u₅⁻¹) ^ (r + 2)) * ‖f₅‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eavg q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     w_grid_eq ∈ (H t₁).domain ∧ w_grid_eq ∈ (S t₁).domain) := by
  intro w_grid y_grid w_grid_eq
  have hstokes := fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
  have hw_pl := fourByFourResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  have hy_pl := fourByFourIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  have hweq := fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hweq.2.2.1.1, hweq.2.2.1.2.2.1⟩⟩

#print axioms fourByFourPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_five_initial_and_final_pentagon_cocycles
#print axioms fourByFourResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms fourByFourIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms fourByFourIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms five_by_five_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid
