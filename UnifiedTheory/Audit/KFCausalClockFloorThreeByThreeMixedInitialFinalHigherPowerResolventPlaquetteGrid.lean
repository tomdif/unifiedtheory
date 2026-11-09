/- Three-by-Three `(s₁, s₂, s₃) × (t₁, t₂, t₃)` Mixed Initial-and-Final Higher-Power
Iterated Resolvent and Yosida Identity Plaquette Grid, Exact 2D Stokes / Green Plaquette
Boundary Cancellation, Cyclic Three-Time Plaquette Cocycles, and 8-Domain / Equal-Final-Time
10-Domain Regularity. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid

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
   mixedInitialFinalHigherPowerPlaquette_commutator_and_vertical_stacking
   mixedInitialFinalHigherPowerPlaquette_horizontal_stacking
   mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
   mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
   mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains)

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

/-- Sum of the four elementary `(r + 2)`-fold iterated Hamiltonian resolvent plaquettes in a
`3 × 3` initial-final time grid `(s₁, s₂, s₃) × (t₁, t₂, t₃)` with spectral parameters
`(a₁, a₂, a₃)`, `(c₁, c₂, c₃)`, `(e₁, e₂, e₃)` and source vectors `(f₁, f₂, f₃)`. -/
def twoByTwoResolventPlaquetteGridSum
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃) +
  (mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ c₂ c₃ e₂ e₃ r f₂ f₃)

/-- Sum of the four elementary `(r + 2)`-th order Yosida identity plaquettes in a `3 × 3`
initial-final time grid `(s₁, s₂, s₃) × (t₁, t₂, t₃)`. -/
def twoByTwoIdentityPlaquetteGridSum
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) : Hilbert :=
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃) +
  (mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c₁ c₂ e₁ e₂ r f₁ f₂ +
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₂ t₃ c₂ c₃ e₂ e₃ r f₂ f₃)

/-- Exact 2D Stokes / Green plaquette boundary cancellation on the `3 × 3` time-parameter grid:
`twoByTwoResolventPlaquetteGridSum` and `twoByTwoIdentityPlaquetteGridSum` equal the single outer
boundary plaquette between `(s₁, s₃)` and `(t₁, t₃)` at `(a₁, a₃, e₁, e₃)` and `(f₁, f₃)`,
canceling all interior `(s₂, t₂)` vertices and edges. -/
theorem twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
    twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ := by
  unfold twoByTwoResolventPlaquetteGridSum twoByTwoIdentityPlaquetteGridSum
    mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel⟩

/-- Cyclic 3-step initial-time `(s₁, s₂, s₃)` and final-time `(t₁, t₂, t₃)` plaquette cocycles
for `mixedInitialFinalHigherPowerResolventPlaquette` and
`mixedInitialFinalHigherPowerIdentityPlaquette`. -/
theorem mixedInitialFinalHigherPowerPlaquette_three_initial_and_final_cyclic_cocycles
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₁ t₁ t₂ a₃ a₁ c₃ c₁ r f₃ f₁ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₁ t₁ t₂ a₃ a₁ c₃ c₁ r f₃ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₁ e₁ e₂ a₁ a₂ r f₁ f₂ = 0 ∧
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₁ e₁ e₂ a₁ a₂ r f₁ f₂ = 0 := by
  unfold mixedInitialFinalHigherPowerResolventPlaquette
    mixedInitialFinalHigherPowerIdentityPlaquette
    crossInitialHigherPowerResolventDiff crossInitialHigherPowerIdentityDiff
  refine ⟨by abel, by abel, by abel, by abel⟩

/-- Unconditionally for all `s₁, s₂, s₃, t₁, t₂, t₃, q ∈ ℝ`, `0 < a₁, a₃, e₁, e₃`, and `r : ℕ`,
`twoByTwoResolventPlaquetteGridSum` belongs simultaneously to all 8 time-independent / observation-time
`q` domains with outer-corner geometric norm bound independent of `(s₂, t₂, a₂, c₁, c₂, c₃, e₂, f₂)`. -/
theorem twoByTwoResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let w_grid := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    (w_grid ∈ (K).domain ∧
     w_grid ∈ (Eavg q).domain ∧
     w_grid ∈ (Tstat).domain ∧
     w_grid ∈ (Kroot).domain ∧
     w_grid ∈ (Tpot).domain ∧
     w_grid ∈ (Tgrow).domain ∧
     w_grid ∈ (Tres q).domain ∧
     w_grid ∈ (clockHalf ε).domain) ∧
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₃⁻¹) ^ (r + 2) + (e₃⁻¹) ^ (r + 2)) * ‖f₃‖ := by
  intro w_grid
  have hstokes := (twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₃ t₁ t₃ q a₁ a₃ e₁ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₃
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- Unconditionally for all `s₁, s₂, s₃, t₁, t₂, t₃, q ∈ ℝ`, `0 < a₁, a₃, e₁, e₃`, and `r : ℕ`,
`twoByTwoIdentityPlaquetteGridSum` belongs simultaneously to all 8 time-independent / observation-time
`q` domains with outer-corner stability bound `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₃‖`. -/
theorem twoByTwoIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    (s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let y_grid := twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    (y_grid ∈ (K).domain ∧
     y_grid ∈ (Eavg q).domain ∧
     y_grid ∈ (Tstat).domain ∧
     y_grid ∈ (Kroot).domain ∧
     y_grid ∈ (Tpot).domain ∧
     y_grid ∈ (Tgrow).domain ∧
     y_grid ∈ (Tres q).domain ∧
     y_grid ∈ (clockHalf ε).domain) ∧
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₃‖ := by
  intro y_grid
  have hstokes := (twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₃ t₁ t₃ q a₁ a₃ e₁ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₃
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₃ = t`), `twoByTwoResolventPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains regardless of the intermediate time `t₂`. -/
theorem twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let w_grid := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
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
    ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
      ((a₃⁻¹) ^ (r + 2) + (e₃⁻¹) ^ (r + 2)) * ‖f₃‖ := by
  intro w_grid
  have hstokes := (twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃).1
  have houter := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₃ t q a₁ a₃ e₁ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₃
  dsimp only [w_grid]
  rw [hstokes]
  exact houter

/-- When the outer final times coincide (`t₁ = t₃ = t`), `twoByTwoIdentityPlaquetteGridSum`
belongs simultaneously to `hamiltonianPowerDomain t (r + 2)`, `hamiltonianSecondPowerDomain t`,
and all 10 operator, form, and clock domains with `‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₃‖`. -/
theorem twoByTwoIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    (s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let y_grid := twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
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
    ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₃‖ := by
  intro y_grid
  have hstokes := (twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃).2
  have houter := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₃ t q a₁ a₃ e₁ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₃
  dsimp only [y_grid]
  rw [hstokes]
  exact houter

/-- Master Three-by-Three `(s₁, s₂, s₃) × (t₁, t₂, t₃)` Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid and 2D Stokes Boundary Cancellation Synthesis. -/
theorem three_by_three_mixed_initial_final_plaquette_grid_master_synthesis
    (s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) :
    let w_grid := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    let y_grid := twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    let w_grid_eq := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₁ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    (w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
     y_grid = mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃) ∧
    (w_grid ∈ (K).domain ∧ w_grid ∈ (Eavg q).domain ∧ w_grid ∈ (clockHalf ε).domain ∧
     ‖w_grid‖ ≤ ((a₁⁻¹) ^ (r + 2) + (e₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
       ((a₃⁻¹) ^ (r + 2) + (e₃⁻¹) ^ (r + 2)) * ‖f₃‖) ∧
    (y_grid ∈ (K).domain ∧ y_grid ∈ (Eavg q).domain ∧ y_grid ∈ (clockHalf ε).domain ∧
     ‖y_grid‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₃‖) ∧
    (w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
     w_grid_eq ∈ (H t₁).domain ∧ w_grid_eq ∈ (S t₁).domain) := by
  intro w_grid y_grid w_grid_eq
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  have hw_pl := twoByTwoResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  have hy_pl := twoByTwoIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  have hweq := twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  exact ⟨hstokes,
    ⟨hw_pl.1.1, hw_pl.1.2.1, hw_pl.1.2.2.2.2.2.2.2, hw_pl.2⟩,
    ⟨hy_pl.1.1, hy_pl.1.2.1, hy_pl.1.2.2.2.2.2.2.2, hy_pl.2⟩,
    ⟨hweq.1, hweq.2.2.1.1, hweq.2.2.1.2.2.1⟩⟩

#print axioms twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
#print axioms mixedInitialFinalHigherPowerPlaquette_three_initial_and_final_cyclic_cocycles
#print axioms twoByTwoResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms twoByTwoIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
#print axioms twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms twoByTwoIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
#print axioms three_by_three_mixed_initial_final_plaquette_grid_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
