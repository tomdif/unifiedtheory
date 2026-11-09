/- Higher-Power Potential-Resolvent Radial-Yosida Operator Towers, Quarter-Strip
Radial/Growing Regularity, Two-Parameter Commutativity, and Strong Convergence:
1. For any shift `a > 0`, radial Yosida parameter `N > 0`, power `r : ℕ`, and vector
   `f : Hilbert`, defines the `r`-th power potential-resolvent radial-Yosida state
   `higherPowerPotentialResolventYosidaState a N hN r f := iteratedResolventPower (RP a) r (J N hN f)`
   and the `r`-th order Yosida-scaled identity state
   `higherPowerPotentialIdentityYosidaState a N hN r f := iteratedIdentityPower (RP a) a r (J N hN f)`.
2. Proves unconditional membership in the inductive `r`-th power potential domain
   `potentialPowerDomain ε hε h hh hb m g k r` (and `potentialPowerDomain ... s` for `s ≤ r`),
   membership in `(P).domain`, `potentialSecondPowerDomain`, and `(Tpot).domain` for positive
   powers, and on the quarter-strip `|h| ≤ π * ε / 4`, membership in `(K).domain` for all `r : ℕ`
   and in `(G).domain` for all `r + 1`.
3. Establishes geometric norm decay `(a⁻¹)^r * ‖f‖`, uniform contraction
   `‖higherPowerPotentialIdentityYosidaState a N hN r f‖ ≤ ‖J N hN f‖ ≤ ‖f‖` for all `r : ℕ`,
   exact first-order operator recurrence on `r + 1`, two-parameter commutativity across all
   orders `(r, s)`, exact specialization to first- and second-power radial-Yosida approximants,
   and strong convergence as `n → ∞` (`N = n + 1`). -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedPotentialResolventYosidaGraphCore
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerOperatorCores
import UnifiedTheory.Audit.KFCausalClockFloorHigherPowerYosidaGraphConvergence
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorIteratedResolventCommutativity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaCore

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm radial_domain sequence_tendsto)
open KFCausalPositiveResolventBounds (Resolves point)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le resolvent_radial_domain resolvent_growing_domain)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_mem_potential_domain
   potential_resolvent_equation
   potential_resolvent_mem_potentialForm_domain)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (potentialSecondPowerDomain)
open KFCausalClockFloorPotentialResolventYosidaInvarianceBridge
  (potentialResolventRadialYosidaApprox)
open KFCausalClockFloorIteratedPotentialResolventYosidaGraphCore
  (secondPowerShiftedSource iteratedPotentialResolventRadialYosidaApprox)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_le_of_le
   operatorPowerDomain_succ_le_domain operatorPowerDomain_add_two_le_secondPowerDomain
   iteratedResolventPower iteratedResolventPower_zero_apply iteratedResolventPower_succ_apply
   iteratedResolventPower_mem_operatorPowerDomain iteratedResolventPower_norm_bound
   iteratedResolventPower_first_order_package
   potentialPowerDomain potential_iteratedResolventPower_regularity)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedResolventPower_add_apply
   iteratedIdentityPower iteratedIdentityPower_zero iteratedIdentityPower_one
   iteratedIdentityPower_succ iteratedIdentityPower_add iteratedIdentityPower_sub
   iteratedIdentityPower_mem_operatorPowerDomain iteratedIdentityPower_norm_le)
open KFCausalClockFloorFiveOperatorIteratedResolventCommutativity
  (potentialResolvent_iteratedResolventPower_comm)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "J" => action ε hε h

/-! ### 1. Definitions, Base Cases, Recurrences, and Semigroup Addition Laws -/

/-- The `r`-th power potential-resolvent radial-Yosida state
`R_P(a)^r (J_N f) = iteratedResolventPower (RP a) r (J N hN f)`. -/
def higherPowerPotentialResolventYosidaState
    (a N : ℝ) (hN : 0 < N) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedResolventPower (RP a) r (J N hN f)

/-- The `r`-th order Yosida-scaled potential-resolvent radial-Yosida state
`(a • R_P(a))^r (J_N f) = iteratedIdentityPower (RP a) a r (J N hN f)`. -/
def higherPowerPotentialIdentityYosidaState
    (a N : ℝ) (hN : 0 < N) (r : ℕ) (f : Hilbert) : Hilbert :=
  iteratedIdentityPower (RP a) a r (J N hN f)

/-- Integer-scale (`N = n + 1`) sequence of `r`-th power potential-resolvent radial-Yosida states. -/
def higherPowerPotentialResolventYosidaSeq
    (a : ℝ) (r : ℕ) (f : Hilbert) (n : ℕ) : Hilbert :=
  higherPowerPotentialResolventYosidaState ε hε h hh hb m g k
    a ((n : ℝ) + 1) (by positivity) r f

/-- Integer-scale (`N = n + 1`) sequence of `r`-th order Yosida-scaled potential-resolvent
radial-Yosida states. -/
def higherPowerPotentialIdentityYosidaSeq
    (a : ℝ) (r : ℕ) (f : Hilbert) (n : ℕ) : Hilbert :=
  higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k
    a ((n : ℝ) + 1) (by positivity) r f

/-- At `r = 0`, `higherPowerPotentialResolventYosidaState a N hN 0 f = J N hN f`. -/
theorem higherPowerPotentialResolventYosidaState_zero
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN 0 f = J N hN f :=
  rfl

/-- At `r = 1`, `higherPowerPotentialResolventYosidaState a N hN 1 f = RP a (J N hN f)`. -/
theorem higherPowerPotentialResolventYosidaState_one
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN 1 f =
      RP a (J N hN f) :=
  rfl

/-- At `r = 2`, `higherPowerPotentialResolventYosidaState a N hN 2 f = RP a (RP a (J N hN f))`. -/
theorem higherPowerPotentialResolventYosidaState_two
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN 2 f =
      RP a (RP a (J N hN f)) :=
  rfl

/-- Step recurrence for `higherPowerPotentialResolventYosidaState`:
`higherPowerPotentialResolventYosidaState a N hN (r + 1) f = RP a (higherPowerPotentialResolventYosidaState a N hN r f)`. -/
theorem higherPowerPotentialResolventYosidaState_succ
    (a N : ℝ) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f =
      RP a (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f) :=
  rfl

/-- Semigroup addition law for `higherPowerPotentialResolventYosidaState`:
`higherPowerPotentialResolventYosidaState a N hN (r + s) f = iteratedResolventPower (RP a) r (higherPowerPotentialResolventYosidaState a N hN s f)`. -/
theorem higherPowerPotentialResolventYosidaState_add
    (a N : ℝ) (hN : 0 < N) (r s : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + s) f =
      iteratedResolventPower (RP a) r
        (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN s f) :=
  iteratedResolventPower_add_apply (RP a) r s (J N hN f)

/-- Scaling relation between `higherPowerPotentialIdentityYosidaState` and
`higherPowerPotentialResolventYosidaState`. -/
theorem higherPowerPotentialIdentityYosidaState_eq_smul
    (a N : ℝ) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f =
      ((a ^ r : ℝ) : ℂ) •
        higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f :=
  rfl

/-- At `r = 0`, `higherPowerPotentialIdentityYosidaState a N hN 0 f = J N hN f`. -/
theorem higherPowerPotentialIdentityYosidaState_zero
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN 0 f = J N hN f :=
  iteratedIdentityPower_zero (RP a) a (J N hN f)

/-- At `r = 1`, `higherPowerPotentialIdentityYosidaState a N hN 1 f = (a : ℂ) • RP a (J N hN f)`. -/
theorem higherPowerPotentialIdentityYosidaState_one
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN 1 f =
      (a : ℂ) • RP a (J N hN f) :=
  iteratedIdentityPower_one (RP a) a (J N hN f)

/-- Step recurrence for `higherPowerPotentialIdentityYosidaState`:
`higherPowerPotentialIdentityYosidaState a N hN (r + 1) f = (a : ℂ) • RP a (higherPowerPotentialIdentityYosidaState a N hN r f)`. -/
theorem higherPowerPotentialIdentityYosidaState_succ
    (a N : ℝ) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f =
      (a : ℂ) •
        RP a (higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f) :=
  iteratedIdentityPower_succ (RP a) a r (J N hN f)

/-- Semigroup addition law for `higherPowerPotentialIdentityYosidaState`. -/
theorem higherPowerPotentialIdentityYosidaState_add
    (a N : ℝ) (hN : 0 < N) (r s : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + s) f =
      iteratedIdentityPower (RP a) a r
        (higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN s f) :=
  iteratedIdentityPower_add (RP a) a r s (J N hN f)

/-! ### 2. Higher-Power Domain Regularity, Quarter-Strip Invariance, and Norm Bounds -/

/-- Unconditional membership of `higherPowerPotentialResolventYosidaState a N hN r f` in
`potentialPowerDomain ε hε h hh hb m g k r` for every `0 < a`, `0 < N`, `r : ℕ`, and `f : Hilbert`. -/
theorem higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f ∈
      potentialPowerDomain ε hε h hh hb m g k r :=
  (potential_iteratedResolventPower_regularity ε hε h hh hb m g k a ha r (J N hN f)).1

/-- Antitone domain inclusion for `higherPowerPotentialResolventYosidaState`: if `s ≤ r`, then
`higherPowerPotentialResolventYosidaState a N hN r f ∈ potentialPowerDomain ε hε h hh hb m g k s`. -/
theorem higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain_of_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) {s r : ℕ} (hsr : s ≤ r) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f ∈
      potentialPowerDomain ε hε h hh hb m g k s :=
  operatorPowerDomain_le_of_le P hsr
    (higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN r f)

/-- Every positive-power state `higherPowerPotentialResolventYosidaState a N hN (r + 1) f`
lies in `(P).domain`. -/
theorem higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈
      (P).domain :=
  operatorPowerDomain_succ_le_domain P r
    (higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN (r + 1) f)

/-- Every state of power `r + 2` lies in `potentialSecondPowerDomain`. -/
theorem higherPowerPotentialResolventYosidaState_add_two_mem_secondPowerDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 2) f ∈
      potentialSecondPowerDomain ε hε h hh hb m g k :=
  operatorPowerDomain_add_two_le_secondPowerDomain P r
    (higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN (r + 2) f)

/-- Every positive-power state `higherPowerPotentialResolventYosidaState a N hN (r + 1) f`
lies in the potential form domain `(Tpot).domain`. -/
theorem higherPowerPotentialResolventYosidaState_succ_mem_potentialForm_domain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈
      (Tpot).domain :=
  potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha
    (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f)

/-- Quarter-strip radial domain regularity across all powers `r : ℕ`: when
`|h| ≤ Real.pi * ε / 4`, `higherPowerPotentialResolventYosidaState a N hN r f ∈ (K).domain`
for every `r : ℕ` (including `r = 0`). -/
theorem higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4) (a N : ℝ) (ha : 0 < a) (hN : 0 < N) :
    ∀ r : ℕ, ∀ f : Hilbert,
      higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f ∈ (K).domain
  | 0, f => radial_domain ε hε h N hN f
  | r + 1, f =>
    resolvent_radial_domain ε hε h hb hh m g k hq a ha
      (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f)
      (higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter hq a N ha hN r f)

/-- Quarter-strip growing Hamiltonian domain regularity for all positive powers `r + 1`:
when `|h| ≤ Real.pi * ε / 4`,
`higherPowerPotentialResolventYosidaState a N hN (r + 1) f ∈ (G).domain`. -/
theorem higherPowerPotentialResolventYosidaState_succ_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4) (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈ (G).domain :=
  resolvent_growing_domain ε hε h hb hh m g k hq a ha
    (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f)
    (higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter
      ε hε h hh hb m g k hq a N ha hN r f)

/-- Geometric norm decay for `higherPowerPotentialResolventYosidaState`:
`‖higherPowerPotentialResolventYosidaState a N hN r f‖ ≤ (a⁻¹) ^ r * ‖f‖`. -/
theorem higherPowerPotentialResolventYosidaState_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f‖ ≤
      (a⁻¹) ^ r * ‖f‖ := by
  refine (potential_iteratedResolventPower_regularity
    ε hε h hh hb m g k a ha r (J N hN f)).2.trans ?_
  exact mul_le_mul_of_nonneg_left (action_norm ε hε h N hN f)
    (pow_nonneg (inv_nonneg.mpr ha.le) r)

/-- Unconditional membership of `higherPowerPotentialIdentityYosidaState a N hN r f` in
`potentialPowerDomain ε hε h hh hb m g k r`. -/
theorem higherPowerPotentialIdentityYosidaState_mem_potentialPowerDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f ∈
      potentialPowerDomain ε hε h hh hb m g k r :=
  iteratedIdentityPower_mem_operatorPowerDomain P (RP a) a
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha) r (J N hN f)

/-- Every positive-power scaled state `higherPowerPotentialIdentityYosidaState a N hN (r + 1) f`
lies in `(P).domain`. -/
theorem higherPowerPotentialIdentityYosidaState_succ_mem_potentialDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈
      (P).domain :=
  operatorPowerDomain_succ_le_domain P r
    (higherPowerPotentialIdentityYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN (r + 1) f)

/-- Quarter-strip radial domain regularity for `higherPowerPotentialIdentityYosidaState`:
when `|h| ≤ Real.pi * ε / 4`, `higherPowerPotentialIdentityYosidaState a N hN r f ∈ (K).domain`. -/
theorem higherPowerPotentialIdentityYosidaState_mem_radial_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4) (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f ∈ (K).domain := by
  rw [higherPowerPotentialIdentityYosidaState_eq_smul]
  exact (K).domain.smul_mem ((a ^ r : ℝ) : ℂ)
    (higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter
      ε hε h hh hb m g k hq a N ha hN r f)

/-- Quarter-strip growing domain regularity for `higherPowerPotentialIdentityYosidaState` at `r + 1`. -/
theorem higherPowerPotentialIdentityYosidaState_succ_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4) (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈ (G).domain := by
  rw [higherPowerPotentialIdentityYosidaState_eq_smul]
  exact (G).domain.smul_mem ((a ^ (r + 1) : ℝ) : ℂ)
    (higherPowerPotentialResolventYosidaState_succ_mem_growing_domain_of_quarter
      ε hε h hh hb m g k hq a N ha hN r f)

/-- Contraction relative to the radial Yosida state `J N hN f`:
`‖higherPowerPotentialIdentityYosidaState a N hN r f‖ ≤ ‖J N hN f‖`. -/
theorem higherPowerPotentialIdentityYosidaState_norm_le_action
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f‖ ≤
      ‖J N hN f‖ :=
  iteratedIdentityPower_norm_le P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) r (J N hN f)

/-- Uniform double contraction across all powers `r : ℕ`, shifts `a > 0`, and scales `N > 0`:
`‖higherPowerPotentialIdentityYosidaState a N hN r f‖ ≤ ‖f‖`. -/
theorem higherPowerPotentialIdentityYosidaState_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f‖ ≤ ‖f‖ :=
  (higherPowerPotentialIdentityYosidaState_norm_le_action
    ε hε h hh hb m g k a N ha hN r f).trans
    (action_norm ε hε h N hN f)

/-! ### 3. Operator Action Recurrences and Two-Parameter Commutativity -/

/-- Exact first-order potential Hamiltonian action recurrence on
`higherPowerPotentialResolventYosidaState a N hN (r + 1) f`. -/
theorem higherPowerPotentialResolventYosidaState_first_order_action_eq
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    P ⟨higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
      higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
        ε hε h hh hb m g k a N ha hN r f⟩ =
      higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f -
        (a : ℂ) •
          higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f := by
  have hpkg := iteratedResolventPower_first_order_package P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) r (J N hN f)
  exact hpkg.2.1

/-- The potential Hamiltonian output on `higherPowerPotentialResolventYosidaState a N hN (r + 1) f`
belongs to `potentialPowerDomain ε hε h hh hb m g k r`. -/
theorem higherPowerPotentialResolventYosidaState_first_order_action_mem_powerDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    P ⟨higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
      higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
        ε hε h hh hb m g k a N ha hN r f⟩ ∈
      potentialPowerDomain ε hε h hh hb m g k r := by
  have hpkg := iteratedResolventPower_first_order_package P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) r (J N hN f)
  exact hpkg.2.2.1

/-- Geometric norm bound on the potential Hamiltonian output of
`higherPowerPotentialResolventYosidaState a N hN (r + 1) f`:
`‖P (...)‖ ≤ 2 * ((a⁻¹) ^ r * ‖f‖)`. -/
theorem higherPowerPotentialResolventYosidaState_first_order_action_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖P ⟨higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
      higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
        ε hε h hh hb m g k a N ha hN r f⟩‖ ≤
      2 * ((a⁻¹) ^ r * ‖f‖) := by
  have hpkg := iteratedResolventPower_first_order_package P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) r (J N hN f)
  refine hpkg.2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (action_norm ε hε h N hN f) (pow_nonneg (inv_nonneg.mpr ha.le) r))
    (by norm_num)

/-- Exact first-order potential Hamiltonian action recurrence on the Yosida-scaled state
`higherPowerPotentialIdentityYosidaState a N hN (r + 1) f`:
`P ⟨y_{r+1}, ...⟩ = (a : ℂ) • (y_r - y_{r+1})`. -/
theorem higherPowerPotentialIdentityYosidaState_first_order_action_eq
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    P ⟨higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
      higherPowerPotentialIdentityYosidaState_succ_mem_potentialDomain
        ε hε h hh hb m g k a N ha hN r f⟩ =
      (a : ℂ) •
        (higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f -
          higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f) := by
  let u : (P).domain :=
    ⟨higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
      higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
        ε hε h hh hb m g k a N ha hN r f⟩
  have hsub :
      (⟨higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN (r + 1) f,
        higherPowerPotentialIdentityYosidaState_succ_mem_potentialDomain
          ε hε h hh hb m g k a N ha hN r f⟩ : (P).domain) =
      ((a ^ (r + 1) : ℝ) : ℂ) • u :=
    Subtype.ext (higherPowerPotentialIdentityYosidaState_eq_smul ε hε h hh hb m g k a N hN (r + 1) f)
  rw [hsub, (P).map_smul,
    higherPowerPotentialResolventYosidaState_first_order_action_eq
      ε hε h hh hb m g k a N ha hN r f,
    higherPowerPotentialIdentityYosidaState_eq_smul,
    higherPowerPotentialIdentityYosidaState_eq_smul,
    pow_succ', Complex.ofReal_mul, mul_smul]
  module

/-- Two-parameter `(a, b)` and two-order `(r, s)` commutativity for
`higherPowerPotentialResolventYosidaState`. -/
theorem higherPowerPotentialResolventYosidaState_two_param_comm
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (r s : ℕ) (f : Hilbert) :
    iteratedResolventPower (RP a) r
      (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k b N hN s f) =
    iteratedResolventPower (RP b) s
      (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f) :=
  potentialResolvent_iteratedResolventPower_comm ε hε h hh hb m g k a b ha hb_pos r s (J N hN f)

/-- Exact specialization at `r = 1` on `f = P x + a • x` to `potentialResolventRadialYosidaApprox`. -/
theorem higherPowerPotentialResolventYosidaState_connection_to_single_approx
    (a N : ℝ) (hN : 0 < N) (x : (P).domain) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN 1
      (P x + (a : ℂ) • (x : Hilbert)) =
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x :=
  rfl

/-- Exact specialization at `r = 2` on `secondPowerShiftedSource a a x hx2` to
`iteratedPotentialResolventRadialYosidaApprox a a N hN x hx2`. -/
theorem higherPowerPotentialResolventYosidaState_connection_to_diagonal_iterated_approx
    (a N : ℝ) (hN : 0 < N) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN 2
      (secondPowerShiftedSource ε hε h hh hb m g k a a x hx2) =
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a a N hN x hx2 :=
  rfl

/-! ### 4. Radial-Yosida Defect Bounds and Strong Convergence as `n → ∞` -/

/-- Norm bound for the difference between `higherPowerPotentialResolventYosidaState` and
`iteratedResolventPower (RP a) r f`:
`‖higherPowerPotentialResolventYosidaState a N hN r f - iteratedResolventPower (RP a) r f‖ ≤ (a⁻¹) ^ r * ‖J N hN f - f‖`. -/
theorem higherPowerPotentialResolventYosidaState_sub_iteratedResolventPower_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f -
      iteratedResolventPower (RP a) r f‖ ≤
      (a⁻¹) ^ r * ‖J N hN f - f‖ := by
  unfold higherPowerPotentialResolventYosidaState
  rw [← map_sub]
  exact (potential_iteratedResolventPower_regularity
    ε hε h hh hb m g k a ha r (J N hN f - f)).2

/-- Uniform-in-`(a, r)` norm bound for the difference between
`higherPowerPotentialIdentityYosidaState` and `iteratedIdentityPower (RP a) a r f`:
`‖higherPowerPotentialIdentityYosidaState a N hN r f - iteratedIdentityPower (RP a) a r f‖ ≤ ‖J N hN f - f‖`. -/
theorem higherPowerPotentialIdentityYosidaState_sub_iteratedIdentityPower_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (r : ℕ) (f : Hilbert) :
    ‖higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f -
      iteratedIdentityPower (RP a) a r f‖ ≤
      ‖J N hN f - f‖ := by
  unfold higherPowerPotentialIdentityYosidaState
  rw [← iteratedIdentityPower_sub]
  exact iteratedIdentityPower_norm_le P (RP a) a ha
    (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) r (J N hN f - f)

/-- Strong convergence as `n → ∞` (`N = n + 1`) of `higherPowerPotentialResolventYosidaSeq`
to `iteratedResolventPower (RP a) r f`. -/
theorem tendsto_higherPowerPotentialResolventYosidaSeq
    (a : ℝ) (r : ℕ) (f : Hilbert) :
    Tendsto
      (fun n : ℕ => higherPowerPotentialResolventYosidaSeq ε hε h hh hb m g k a r f n)
      atTop (𝓝 (iteratedResolventPower (RP a) r f)) :=
  ((iteratedResolventPower (RP a) r).continuous.tendsto f).comp
    (sequence_tendsto ε hε h f)

/-- Strong convergence as `n → ∞` (`N = n + 1`) of `higherPowerPotentialIdentityYosidaSeq`
to `iteratedIdentityPower (RP a) a r f`. -/
theorem tendsto_higherPowerPotentialIdentityYosidaSeq
    (a : ℝ) (r : ℕ) (f : Hilbert) :
    Tendsto
      (fun n : ℕ => higherPowerPotentialIdentityYosidaSeq ε hε h hh hb m g k a r f n)
      atTop (𝓝 (iteratedIdentityPower (RP a) a r f)) :=
  (tendsto_higherPowerPotentialResolventYosidaSeq ε hε h hh hb m g k a r f).const_smul
    ((a ^ r : ℝ) : ℂ)

/-- Master synthesis for the Higher-Power Potential-Resolvent Radial-Yosida Core:
packages `potentialPowerDomain` regularity, quarter-strip radial and growing domain
invariance, geometric norm decay and uniform contraction, two-parameter commutativity,
and strong convergence as `n → ∞`. -/
theorem higher_power_potential_resolvent_yosida_core_master_synthesis
    (hq : |h| ≤ Real.pi * ε / 4)
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (r s : ℕ) (f : Hilbert) :
    (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f ∈
      potentialPowerDomain ε hε h hh hb m g k r ∧
     higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f ∈
      potentialPowerDomain ε hε h hh hb m g k r ∧
     higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f ∈ (K).domain ∧
     higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN (r + 1) f ∈ (G).domain) ∧
    (‖higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f‖ ≤
      (a⁻¹) ^ r * ‖f‖ ∧
     ‖higherPowerPotentialIdentityYosidaState ε hε h hh hb m g k a N hN r f‖ ≤ ‖f‖) ∧
    iteratedResolventPower (RP a) r
      (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k b N hN s f) =
      iteratedResolventPower (RP b) s
        (higherPowerPotentialResolventYosidaState ε hε h hh hb m g k a N hN r f) ∧
    (Tendsto
      (fun n : ℕ => higherPowerPotentialResolventYosidaSeq ε hε h hh hb m g k a r f n)
      atTop (𝓝 (iteratedResolventPower (RP a) r f)) ∧
     Tendsto
      (fun n : ℕ => higherPowerPotentialIdentityYosidaSeq ε hε h hh hb m g k a r f n)
      atTop (𝓝 (iteratedIdentityPower (RP a) a r f))) :=
  ⟨⟨higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN r f,
    higherPowerPotentialIdentityYosidaState_mem_potentialPowerDomain
      ε hε h hh hb m g k a N ha hN r f,
    higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter
      ε hε h hh hb m g k hq a N ha hN r f,
    higherPowerPotentialResolventYosidaState_succ_mem_growing_domain_of_quarter
      ε hε h hh hb m g k hq a N ha hN r f⟩,
   ⟨higherPowerPotentialResolventYosidaState_norm_le
      ε hε h hh hb m g k a N ha hN r f,
    higherPowerPotentialIdentityYosidaState_norm_le
      ε hε h hh hb m g k a N ha hN r f⟩,
   higherPowerPotentialResolventYosidaState_two_param_comm
      ε hε h hh hb m g k a b N ha hb_pos hN r s f,
   ⟨tendsto_higherPowerPotentialResolventYosidaSeq ε hε h hh hb m g k a r f,
    tendsto_higherPowerPotentialIdentityYosidaSeq ε hε h hh hb m g k a r f⟩⟩

#print axioms higherPowerPotentialResolventYosidaState_zero
#print axioms higherPowerPotentialResolventYosidaState_one
#print axioms higherPowerPotentialResolventYosidaState_two
#print axioms higherPowerPotentialResolventYosidaState_succ
#print axioms higherPowerPotentialResolventYosidaState_add
#print axioms higherPowerPotentialIdentityYosidaState_eq_smul
#print axioms higherPowerPotentialIdentityYosidaState_zero
#print axioms higherPowerPotentialIdentityYosidaState_one
#print axioms higherPowerPotentialIdentityYosidaState_succ
#print axioms higherPowerPotentialIdentityYosidaState_add
#print axioms higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain
#print axioms higherPowerPotentialResolventYosidaState_mem_potentialPowerDomain_of_le
#print axioms higherPowerPotentialResolventYosidaState_succ_mem_potentialDomain
#print axioms higherPowerPotentialResolventYosidaState_add_two_mem_secondPowerDomain
#print axioms higherPowerPotentialResolventYosidaState_succ_mem_potentialForm_domain
#print axioms higherPowerPotentialResolventYosidaState_mem_radial_domain_of_quarter
#print axioms higherPowerPotentialResolventYosidaState_succ_mem_growing_domain_of_quarter
#print axioms higherPowerPotentialResolventYosidaState_norm_le
#print axioms higherPowerPotentialIdentityYosidaState_mem_potentialPowerDomain
#print axioms higherPowerPotentialIdentityYosidaState_succ_mem_potentialDomain
#print axioms higherPowerPotentialIdentityYosidaState_mem_radial_domain_of_quarter
#print axioms higherPowerPotentialIdentityYosidaState_succ_mem_growing_domain_of_quarter
#print axioms higherPowerPotentialIdentityYosidaState_norm_le_action
#print axioms higherPowerPotentialIdentityYosidaState_norm_le
#print axioms higherPowerPotentialResolventYosidaState_first_order_action_eq
#print axioms higherPowerPotentialResolventYosidaState_first_order_action_mem_powerDomain
#print axioms higherPowerPotentialResolventYosidaState_first_order_action_norm_le
#print axioms higherPowerPotentialIdentityYosidaState_first_order_action_eq
#print axioms higherPowerPotentialResolventYosidaState_two_param_comm
#print axioms higherPowerPotentialResolventYosidaState_connection_to_single_approx
#print axioms higherPowerPotentialResolventYosidaState_connection_to_diagonal_iterated_approx
#print axioms higherPowerPotentialResolventYosidaState_sub_iteratedResolventPower_norm_le
#print axioms higherPowerPotentialIdentityYosidaState_sub_iteratedIdentityPower_norm_le
#print axioms tendsto_higherPowerPotentialResolventYosidaSeq
#print axioms tendsto_higherPowerPotentialIdentityYosidaSeq
#print axioms higher_power_potential_resolvent_yosida_core_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorHigherPowerPotentialResolventYosidaCore
