/-
  Audit/ObservableSeparation.lean

  OBSERVABLE-SEPARATION AUDIT — THREE INPUT-ERASURE THEOREMS

  A reconstruction map must retain enough information to distinguish at
  least some physically different inputs.  This file connects definitions
  from three previously separate parts of the repository and proves that
  their current interfaces erase the variable they are meant to probe:

    1. The advertised `NoBackgroundSpace` signature cannot distinguish a
       two-element chain from a two-element antichain.
    2. The chamber Poincare action cannot distinguish the identity from a
       nonzero translation parameter.
    3. The structural mass gap and Wilson expectation cannot distinguish
       densities; the Wilson expectation cannot distinguish couplings.

  These are scope theorems, not claims that no improved construction can
  work.  They identify the minimum repair: make the observable depend on
  the order relation, scale, coupling, or symmetry parameter before using
  injectivity, convergence, or covariance as evidence of emergence.
-/

import UnifiedTheory.Audit.QuantumGeometryStatus
import UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation
import UnifiedTheory.LayerB.Clay_W1_ContinuousPoincare
import UnifiedTheory.LayerB.NoBackgroundSpace
import UnifiedTheory.LayerB.R4_ContinuumLimitConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.ObservableSeparation

open UnifiedTheory.Audit.QuantumGeometryStatus
open UnifiedTheory.LayerB.Build4_ExplicitWilsonExpectation
open UnifiedTheory.LayerB.Clay_W1_ContinuousPoincare
open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.R4_ContinuumLimitConvergence

/-! ## 1. The current advertised poset signature is not order-separating -/

/-- The quantities bundled by `NoBackgroundSpace.no_background_space` that
can be evaluated from a `FinPoset`.  This records the current definitions,
not a proposed replacement geometry observable. -/
structure AdvertisedPosetSignature where
  volume : ℚ
  kSector : ℕ
  pSector : ℕ
  spectralRatio : ℚ
  weakMixing : ℚ
  generations : ℕ
  deriving DecidableEq, Repr

/-- The current advertised signature.  Only `P.n` reaches the first three
fields; the remaining fields are repository-wide constants. -/
def advertisedPosetSignature (P : FinPoset) : AdvertisedPosetSignature where
  volume := volumeRatio P
  kSector := kSectorDim P.n
  pSector := pSectorDim P.n
  spectralRatio := eigenvalueRatio
  weakMixing := sinSqThetaW
  generations := numGenerations

/-- A two-element chain, represented by the usual total order. -/
def chainTwo : FinPoset where
  n := 2
  hn := by decide
  rel := fun i j => decide (i.val ≤ j.val)
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- A two-element antichain with only reflexive comparabilities. -/
def antichainTwo : FinPoset where
  n := 2
  hn := by decide
  rel := fun i j => decide (i = j)
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- Totality distinguishes the chain from the antichain without inspecting
dependent relation fields through an equality cast. -/
def IsTotalOrderData (P : FinPoset) : Prop :=
  ∀ i j, P.rel i j = true ∨ P.rel j i = true

theorem chainTwo_is_total : IsTotalOrderData chainTwo := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [chainTwo]

theorem antichainTwo_is_not_total : ¬ IsTotalOrderData antichainTwo := by
  intro htotal
  have hzeroOne := htotal (0 : Fin 2) (1 : Fin 2)
  simp [antichainTwo] at hzeroOne

/-- The two inputs genuinely carry different order relations. -/
theorem chainTwo_ne_antichainTwo : chainTwo ≠ antichainTwo := by
  intro h
  apply antichainTwo_is_not_total
  rw [← h]
  exact chainTwo_is_total

/-- Nevertheless every field of the current advertised signature agrees. -/
theorem chain_antichain_same_advertised_signature :
    advertisedPosetSignature chainTwo = advertisedPosetSignature antichainTwo := by
  rfl

/-- **ORDER-SEPARATION NO-GO.**  The current advertised signature is not
injective on finite posets. -/
theorem advertisedPosetSignature_not_injective :
    ¬ Function.Injective advertisedPosetSignature := by
  intro hinjective
  exact chainTwo_ne_antichainTwo
    (hinjective chain_antichain_same_advertised_signature)

/-! ## 2. The current chamber Poincare action is not faithful -/

/-- A nonzero translation parameter in the first Poincare coordinate. -/
def unitTranslation : PoincareParam :=
  fun i => if i = (0 : Fin 10) then 1 else 0

theorem unitTranslation_ne_identity : unitTranslation ≠ poincareIdentity := by
  intro h
  have hzero := congrFun h (0 : Fin 10)
  norm_num [unitTranslation, poincareIdentity] at hzero

/-- The nonzero parameter and identity act by the same chamber operator. -/
theorem unitTranslation_action_eq_identity :
    discretePoincareChamber unitTranslation =
      discretePoincareChamber poincareIdentity := by
  rfl

/-- **SYMMETRY-SEPARATION NO-GO.**  The current chamber representation is
trivial and therefore not faithful. -/
theorem discretePoincareChamber_not_injective :
    ¬ Function.Injective discretePoincareChamber := by
  intro hinjective
  exact unitTranslation_ne_identity
    (hinjective unitTranslation_action_eq_identity)

/-! ## 3. The current continuum observables have no nontrivial flow -/

/-- The mass-gap candidate has no density dependence. -/
theorem massGapAtDensity_not_density_dependent :
    ¬ HasNontrivialDensityDependence massGapAtDensity := by
  rintro ⟨ρ₁, ρ₂, hne⟩
  exact hne (massGapAtDensity_density_rigid ρ₁ ρ₂)

/-- For fixed coupling and observable, the structural Wilson expectation
has no density dependence. -/
theorem physicalWilsonExpectation_not_density_dependent (β W : ℝ) :
    ¬ HasNontrivialDensityDependence
      (fun ρ => physicalWilsonExpectation ρ β W) := by
  rintro ⟨ρ₁, ρ₂, hne⟩
  exact hne (physicalWilsonExpectation_rho_independent ρ₁ ρ₂ β W)

/-- For fixed density and observable, it also has no coupling dependence. -/
theorem physicalWilsonExpectation_not_coupling_dependent (ρ W : ℝ) :
    ¬ HasNontrivialDensityDependence
      (fun β => physicalWilsonExpectation ρ β W) := by
  rintro ⟨β₁, β₂, hne⟩
  exact hne (physicalWilsonExpectation_beta_independent ρ β₁ β₂ W)

/-! ## 4. Cross-module synthesis -/

/-- **THE INPUT-ERASURE SYNTHESIS.**

At the present interfaces, order reconstruction, chamber covariance, mass-gap
continuum convergence, and structural Wilson expectations all succeed only
after collapsing the relevant input.  A future recovery theorem must replace
at least one conjunct with a separating/nonconstant construction before it can
serve as evidence for emergent geometry or dynamics.
-/
theorem current_recovery_maps_erase_input :
    ¬ Function.Injective advertisedPosetSignature
    ∧ ¬ Function.Injective discretePoincareChamber
    ∧ ¬ HasNontrivialDensityDependence massGapAtDensity
    ∧ (∀ β W : ℝ,
        ¬ HasNontrivialDensityDependence
          (fun ρ => physicalWilsonExpectation ρ β W))
    ∧ (∀ ρ W : ℝ,
        ¬ HasNontrivialDensityDependence
          (fun β => physicalWilsonExpectation ρ β W)) := by
  exact ⟨advertisedPosetSignature_not_injective,
    discretePoincareChamber_not_injective,
    massGapAtDensity_not_density_dependent,
    physicalWilsonExpectation_not_density_dependent,
    physicalWilsonExpectation_not_coupling_dependent⟩

/-! ## Trust regression output -/

#print axioms advertisedPosetSignature_not_injective
#print axioms discretePoincareChamber_not_injective
#print axioms massGapAtDensity_not_density_dependent
#print axioms current_recovery_maps_erase_input

end UnifiedTheory.Audit.ObservableSeparation
