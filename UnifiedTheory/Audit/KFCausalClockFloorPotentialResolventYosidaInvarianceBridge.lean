/- Resolvent-Regularized Potential-Domain Radial-Yosida Approximation and
Invariance Bridge for all real couplings m, g, k ∈ ℝ and positive parameters
a > 0, N > 0:
1. Defines the resolvent-regularized radial-Yosida state on Dom(P):
   potentialResolventRadialYosidaApprox a N x := R_P(a) (J_N (P x + a • x))
   and the fixed-shift sequence
   fixedShiftPotentialRadialYosidaSeq a x n := R_P(a) (J_{n+1} (P x + a • x)),
   together with the dual Yosida-scaled potential-resolvent regularizer
   dualPotentialScaledRadialYosidaApprox a N f := a • R_P(a) (J_N f).
2. Proves that for every x ∈ Dom(P), a > 0, and N > 0:
   - potentialResolventRadialYosidaApprox a N x ∈ Dom(P) and ∈ Dom(T_pot),
   - (P + a I)(potentialResolventRadialYosidaApprox a N x) = J_N (P x + a • x) ∈ Dom(K_rad),
   - on the quarter-strip |h| ≤ π * ε / 4, potentialResolventRadialYosidaApprox a N x
     lies in Dom(K_rad) and in Dom(G) = Dom(K_rad) ∩ Dom(P),
   - exact state and operator defect identities:
     potentialResolventRadialYosidaApprox a N x - x
       = R_P(a) (J_N (P x + a • x) - (P x + a • x)),
     P(potentialResolventRadialYosidaApprox a N x) - P x
       = (J_N (P x + a • x) - (P x + a • x))
         - a • (potentialResolventRadialYosidaApprox a N x - x).
3. Establishes unconditional norm and form-energy error bounds, O(N⁻¹) rate bounds
   when P x + a • x ∈ Dom(K_rad), and strong convergence in the graph norm of P:
   fixedShiftPotentialRadialYosidaSeq a x n → x and
   P(fixedShiftPotentialRadialYosidaSeq a x n) → P x as n → ∞ for every x ∈ Dom(P). -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
import UnifiedTheory.Audit.KFCausalClockFloorSecondPowerOperatorCores

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventYosidaInvarianceBridge
noncomputable section
open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm radial_domain sequence_tendsto)
open KFCausalClockFloorRadialResolventOperator
  (self_sub_action_norm_le)
open KFCausalClockFloorPotentialClockApproximation
  (cutoff cutoff_pos cutoff_tendsto)
open KFCausalYosidaApproximation
  (scaled_resolvent_strong_limit)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le resolvent_radial_domain resolvent_growing_domain)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_domain_subset_potentialForm_domain
   potential_resolvent_mem_potential_domain
   potential_resolvent_equation
   potential_resolvent_left_inverse
   potential_resolvent_mem_potentialForm_domain
   potential_resolvent_potentialForm_norm_sq_le
   potential_resolvent_operator_norm_le)

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

/-! ### 1. Definitions and Domain Regularity of Resolvent-Regularized Radial-Yosida States -/

/-- The domain `Dom(P)` of the unbounded potential Hamiltonian `P`. -/
def potentialDomain : Submodule ℂ Hilbert := (P).domain

/-- The domain `Dom(K_rad)` of the maximal radial operator `K`. -/
def radialKineticDomain : Submodule ℂ Hilbert := (K).domain

/-- The positive shifted potential resolvent `R_P(a) = (P + a I)⁻¹`. -/
def potentialResolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert := RP a

/-- The bounded radial Yosida resolvent regularizer `J_N = N (N + K_rad)⁻¹`. -/
def radialYosidaOp (N : ℝ) (hN : 0 < N) : Hilbert →L[ℂ] Hilbert := J N hN

/-- Resolvent-regularized radial-Yosida state on `Dom(P)`:
`R_P(a) (J_N (P x + a • x))`. -/
def potentialResolventRadialYosidaApprox
    (a N : ℝ) (hN : 0 < N) (x : (P).domain) : Hilbert :=
  RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)))

/-- Fixed-shift (`a > 0`) radial-Yosida potential-resolvent sequence at `N = n + 1`. -/
def fixedShiftPotentialRadialYosidaSeq
    (a : ℝ) (x : (P).domain) (n : ℕ) : Hilbert :=
  potentialResolventRadialYosidaApprox ε hε h hh hb m g k
    a ((n : ℝ) + 1) (by positivity) x

/-- Diagonal (`a = N = n + 1`) radial-Yosida potential-resolvent sequence. -/
def potentialResolventRadialYosidaSeq
    (x : (P).domain) (n : ℕ) : Hilbert :=
  potentialResolventRadialYosidaApprox ε hε h hh hb m g k
    ((n : ℝ) + 1) ((n : ℝ) + 1) (by positivity) x

/-- Dual Yosida-scaled potential-resolvent regularizer `a • R_P(a) (J_N f)`. -/
def dualPotentialScaledRadialYosidaApprox
    (a N : ℝ) (hN : 0 < N) (f : Hilbert) : Hilbert :=
  (a : ℂ) • RP a (J N hN f)

/-- Dual Yosida-scaled potential-resolvent sequence `(n + 1) • R_P(n + 1) (J_N f)`. -/
def dualPotentialScaledRadialYosidaSeq
    (N : ℝ) (hN : 0 < N) (f : Hilbert) (n : ℕ) : Hilbert :=
  (cutoff n : ℂ) • RP (cutoff n) (J N hN f)

theorem potentialResolventRadialYosidaApprox_mem_potentialDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (P).domain :=
  potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha
    (J N hN (P x + (a : ℂ) • (x : Hilbert)))

theorem potentialResolventRadialYosidaApprox_mem_potentialForm_domain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (Tpot).domain :=
  potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha
    (J N hN (P x + (a : ℂ) • (x : Hilbert)))

theorem shifted_source_radialYosida_mem_radial_domain
    (a N : ℝ) (hN : 0 < N) (x : (P).domain) :
    J N hN (P x + (a : ℂ) • (x : Hilbert)) ∈ (K).domain :=
  radial_domain ε hε h N hN (P x + (a : ℂ) • (x : Hilbert))

theorem potentialResolventRadialYosidaApprox_mem_radial_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (K).domain :=
  resolvent_radial_domain ε hε h hb hh m g k hq a ha
    (J N hN (P x + (a : ℂ) • (x : Hilbert)))
    (shifted_source_radialYosida_mem_radial_domain ε hε h hh hb m g k a N hN x)

theorem potentialResolventRadialYosidaApprox_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (G).domain :=
  resolvent_growing_domain ε hε h hb hh m g k hq a ha
    (J N hN (P x + (a : ℂ) • (x : Hilbert)))
    (shifted_source_radialYosida_mem_radial_domain ε hε h hh hb m g k a N hN x)

/-! ### 2. Exact Action, Defect Identities, and Error Bounds on `Dom(P)` -/

theorem potentialResolventRadialYosidaApprox_equation
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ =
      J N hN (P x + (a : ℂ) • (x : Hilbert)) -
        a • potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x :=
  potential_resolvent_equation ε hε h hh hb m g k a ha
    (J N hN (P x + (a : ℂ) • (x : Hilbert)))

theorem potentialResolventRadialYosidaApprox_shifted_eq
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ +
      (a : ℂ) • potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x =
      J N hN (P x + (a : ℂ) • (x : Hilbert)) := by
  rw [potentialResolventRadialYosidaApprox_equation ε hε h hh hb m g k a N ha hN x,
    ← Complex.coe_smul a (potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x),
    sub_add_cancel]

theorem potentialResolventRadialYosidaApprox_shifted_mem_radial_domain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ +
      (a : ℂ) • potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (K).domain := by
  rw [potentialResolventRadialYosidaApprox_shifted_eq ε hε h hh hb m g k a N ha hN x]
  exact shifted_source_radialYosida_mem_radial_domain ε hε h hh hb m g k a N hN x

theorem potential_resolvent_left_inverse_complex
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    RP a (P x + (a : ℂ) • (x : Hilbert)) = (x : Hilbert) := by
  rw [Complex.coe_smul]
  exact potential_resolvent_left_inverse ε hε h hh hb m g k a ha x

theorem potentialResolventRadialYosidaApprox_sub_eq
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert) =
      RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))) := by
  unfold potentialResolventRadialYosidaApprox
  rw [map_sub, potential_resolvent_left_inverse_complex ε hε h hh hb m g k a ha x]

theorem potentialResolventRadialYosidaApprox_sub_mem_potentialDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert) ∈ (P).domain :=
  (P).domain.sub_mem
    (potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x)
    x.property

theorem potential_action_on_potentialResolventRadialYosidaApprox_sub_eq_resolvent
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ -
      P x =
      P ⟨RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))),
        potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _⟩ := by
  let u : (P).domain :=
    ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩
  let w : (P).domain :=
    ⟨RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))),
      potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _⟩
  have hsub : u - x = w :=
    Subtype.ext (potentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a N ha hN x)
  exact ((P).map_sub u x).symm.trans (congrArg P hsub)

theorem potential_action_on_potentialResolventRadialYosidaApprox_sub_eq
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ -
      P x =
      (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))) -
        (a : ℂ) •
          (potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert)) := by
  rw [potential_action_on_potentialResolventRadialYosidaApprox_sub_eq_resolvent
      ε hε h hh hb m g k a N ha hN x,
    potential_resolvent_equation ε hε h hh hb m g k a ha _,
    ← potentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a N ha hN x,
    Complex.coe_smul a
      (potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert))]

theorem potentialResolventRadialYosidaApprox_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    ‖potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x‖ ≤
      a⁻¹ * ‖P x + (a : ℂ) • (x : Hilbert)‖ :=
  (potential_resolvent_norm_le ε hε h hb hh m g k a ha _).trans
    (mul_le_mul_of_nonneg_left
      (action_norm ε hε h N hN (P x + (a : ℂ) • (x : Hilbert)))
      (inv_nonneg.mpr ha.le))

theorem potentialResolventRadialYosidaApprox_operator_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    ‖P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩‖ ≤
      ‖P x + (a : ℂ) • (x : Hilbert)‖ :=
  (potential_resolvent_operator_norm_le ε hε h hh hb m g k a ha _).trans
    (action_norm ε hε h N hN (P x + (a : ℂ) • (x : Hilbert)))

theorem potentialResolventRadialYosidaApprox_sub_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    ‖potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert)‖ ≤
      a⁻¹ * ‖J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))‖ := by
  rw [potentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a N ha hN x]
  exact potential_resolvent_norm_le ε hε h hb hh m g k a ha _

theorem potential_action_on_potentialResolventRadialYosidaApprox_sub_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    ‖P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ -
      P x‖ ≤
      ‖J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))‖ := by
  rw [potential_action_on_potentialResolventRadialYosidaApprox_sub_eq_resolvent
      ε hε h hh hb m g k a N ha hN x]
  exact potential_resolvent_operator_norm_le ε hε h hh hb m g k a ha _

theorem potentialResolventRadialYosidaApprox_potentialForm_sub_norm_sq_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    ‖Tpot ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert),
      potential_domain_subset_potentialForm_domain ε hε h hh hb m g k
        ⟨_, potentialResolventRadialYosidaApprox_sub_mem_potentialDomain
          ε hε h hh hb m g k a N ha hN x⟩⟩‖ ^ 2 ≤
      a⁻¹ * ‖J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))‖ ^ 2 := by
  let uDiff : (Tpot).domain :=
    ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert),
      potential_domain_subset_potentialForm_domain ε hε h hh hb m g k
        ⟨_, potentialResolventRadialYosidaApprox_sub_mem_potentialDomain
          ε hε h hh hb m g k a N ha hN x⟩⟩
  let uRes : (Tpot).domain :=
    ⟨RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert))),
      potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha _⟩
  have hsub : uDiff = uRes :=
    Subtype.ext (potentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a N ha hN x)
  exact (congrArg (fun v : (Tpot).domain => ‖Tpot v‖ ^ 2) hsub).trans_le
    (potential_resolvent_potentialForm_norm_sq_le ε hε h hh hb m g k a ha _)

theorem potentialResolventRadialYosidaApprox_sub_norm_le_inv_N_of_radial
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain)
    (hr : P x + (a : ℂ) • (x : Hilbert) ∈ (K).domain) :
    ‖potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert)‖ ≤
      a⁻¹ * (N⁻¹ * ‖K ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩‖) := by
  refine (potentialResolventRadialYosidaApprox_sub_norm_le ε hε h hh hb m g k a N ha hN x).trans ?_
  rw [norm_sub_rev (J N hN (P x + (a : ℂ) • (x : Hilbert)))]
  exact mul_le_mul_of_nonneg_left
    (self_sub_action_norm_le ε hε h N hN
      (P x + (a : ℂ) • (x : Hilbert))
      (K ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩)
      ((K).mem_graph ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩))
    (inv_nonneg.mpr ha.le)

theorem potential_action_sub_norm_le_inv_N_of_radial
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain)
    (hr : P x + (a : ℂ) • (x : Hilbert) ∈ (K).domain) :
    ‖P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
      potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ -
      P x‖ ≤
      N⁻¹ * ‖K ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩‖ := by
  refine (potential_action_on_potentialResolventRadialYosidaApprox_sub_norm_le
    ε hε h hh hb m g k a N ha hN x).trans ?_
  rw [norm_sub_rev (J N hN (P x + (a : ℂ) • (x : Hilbert)))]
  exact self_sub_action_norm_le ε hε h N hN
    (P x + (a : ℂ) • (x : Hilbert))
    (K ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩)
    ((K).mem_graph ⟨P x + (a : ℂ) • (x : Hilbert), hr⟩)

/-! ### 3. Strong Operator-Graph Convergence on `Dom(P)` & Dual Regularizer Limits -/

theorem fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain
    (a : ℝ) (ha : 0 < a) (x : (P).domain) (n : ℕ) :
    fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n ∈ (P).domain :=
  potentialResolventRadialYosidaApprox_mem_potentialDomain
    ε hε h hh hb m g k a ((n : ℝ) + 1) ha (by positivity) x

theorem fixedShiftPotentialRadialYosidaSeq_shifted_mem_radial_domain
    (a : ℝ) (ha : 0 < a) (x : (P).domain) (n : ℕ) :
    P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
      fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩ +
      (a : ℂ) • fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n ∈ (K).domain :=
  potentialResolventRadialYosidaApprox_shifted_mem_radial_domain
    ε hε h hh hb m g k a ((n : ℝ) + 1) ha (by positivity) x

theorem fixedShiftPotentialRadialYosidaSeq_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (x : (P).domain) (n : ℕ) :
    fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n ∈ (G).domain :=
  potentialResolventRadialYosidaApprox_mem_growing_domain_of_quarter
    ε hε h hh hb m g k hq a ((n : ℝ) + 1) ha (by positivity) x

theorem tendsto_shifted_source_radialYosida_sub
    (a : ℝ) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      J ((n : ℝ) + 1) (by positivity) (P x + (a : ℂ) • (x : Hilbert)) -
        (P x + (a : ℂ) • (x : Hilbert)))
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (sequence_tendsto ε hε h (P x + (a : ℂ) • (x : Hilbert))).sub_const
      (P x + (a : ℂ) • (x : Hilbert))

theorem tendsto_fixedShiftPotentialRadialYosidaSeq
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ => fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n)
      atTop (𝓝 (x : Hilbert)) := by
  have h1 := ((RP a).continuous.tendsto (P x + (a : ℂ) • (x : Hilbert))).comp
    (sequence_tendsto ε hε h (P x + (a : ℂ) • (x : Hilbert)))
  simpa only [Function.comp_def, fixedShiftPotentialRadialYosidaSeq,
    potentialResolventRadialYosidaApprox,
    potential_resolvent_left_inverse_complex ε hε h hh hb m g k a ha x] using h1

theorem tendsto_fixedShiftPotentialRadialYosidaSeq_sub_norm
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      ‖fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n - (x : Hilbert)‖)
      atTop (𝓝 0) := by
  have hsub : Tendsto (fun n : ℕ =>
      fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n - (x : Hilbert))
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a ha x).sub_const (x : Hilbert)
  simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : Hilbert)).comp hsub

theorem tendsto_fixedShiftPotentialRadialYosidaSeq_potential_action
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩)
      atTop (𝓝 (P x)) := by
  have h1 := sequence_tendsto ε hε h (P x + (a : ℂ) • (x : Hilbert))
  have h2 := (tendsto_fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a ha x).const_smul a
  have hdiff := h1.sub h2
  have htarget : (P x + (a : ℂ) • (x : Hilbert)) - a • (x : Hilbert) = P x := by
    rw [Complex.coe_smul, add_sub_cancel_right]
  rw [htarget] at hdiff
  refine hdiff.congr' (Eventually.of_forall fun n => ?_)
  exact (potentialResolventRadialYosidaApprox_equation
    ε hε h hh hb m g k a ((n : ℝ) + 1) ha (by positivity) x).symm

theorem tendsto_fixedShiftPotentialRadialYosidaSeq_action_sub_norm
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      ‖P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩ -
        P x‖)
      atTop (𝓝 0) := by
  have hsub : Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩ -
        P x)
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_fixedShiftPotentialRadialYosidaSeq_potential_action
        ε hε h hh hb m g k a ha x).sub_const (P x)
  simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : Hilbert)).comp hsub

theorem tendsto_fixedShiftPotentialRadialYosidaSeq_graph_error_norm
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      ‖fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n - (x : Hilbert)‖ +
        ‖P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
          fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩ -
          P x‖)
      atTop (𝓝 0) := by
  simpa only [add_zero] using
    (tendsto_fixedShiftPotentialRadialYosidaSeq_sub_norm ε hε h hh hb m g k a ha x).add
      (tendsto_fixedShiftPotentialRadialYosidaSeq_action_sub_norm ε hε h hh hb m g k a ha x)

theorem tendsto_fixedShiftPotentialRadialYosidaSeq_graph
    (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    Tendsto (fun n : ℕ =>
      (fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
          fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩))
      atTop (𝓝 ((x : Hilbert), P x)) :=
  (tendsto_fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a ha x).prodMk_nhds
    (tendsto_fixedShiftPotentialRadialYosidaSeq_potential_action ε hε h hh hb m g k a ha x)

theorem dualPotentialScaledRadialYosidaApprox_mem_potentialDomain
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (f : Hilbert) :
    dualPotentialScaledRadialYosidaApprox ε hε h hh hb m g k a N hN f ∈ (P).domain :=
  (P).domain.smul_mem (a : ℂ)
    (potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha (J N hN f))

theorem dualPotentialScaledRadialYosidaApprox_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (f : Hilbert) :
    dualPotentialScaledRadialYosidaApprox ε hε h hh hb m g k a N hN f ∈ (G).domain :=
  (G).domain.smul_mem (a : ℂ)
    (resolvent_growing_domain ε hε h hb hh m g k hq a ha (J N hN f)
      (radial_domain ε hε h N hN f))

theorem dualPotentialScaledRadialYosidaApprox_norm_le
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (f : Hilbert) :
    ‖dualPotentialScaledRadialYosidaApprox ε hε h hh hb m g k a N hN f‖ ≤ ‖f‖ := by
  unfold dualPotentialScaledRadialYosidaApprox
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have h1 := mul_le_mul_of_nonneg_left
    (potential_resolvent_norm_le ε hε h hb hh m g k a ha (J N hN f)) ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h1
  exact h1.trans (action_norm ε hε h N hN f)

theorem tendsto_dualPotentialScaledRadialYosidaSeq
    (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    Tendsto (fun n : ℕ => dualPotentialScaledRadialYosidaSeq ε hε h hh hb m g k N hN f n)
      atTop (𝓝 (J N hN f)) := by
  unfold dualPotentialScaledRadialYosidaSeq
  simpa only [Complex.coe_smul] using
    (scaled_resolvent_strong_limit P RP
      (KFCausalClosedGraphForm.hamiltonian_dense PD)
      (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
      (KFCausalClosedGraphForm.hamiltonian_positive PD)
      (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k)
      (J N hN f)).comp cutoff_tendsto

theorem potential_resolvent_radial_yosida_invariance_master_bridge
    (a N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x ∈ (P).domain ∧
    (P ⟨potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x,
        potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x⟩ +
      (a : ℂ) • potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x =
      J N hN (P x + (a : ℂ) • (x : Hilbert))) ∧
    (potentialResolventRadialYosidaApprox ε hε h hh hb m g k a N hN x - (x : Hilbert) =
      RP a (J N hN (P x + (a : ℂ) • (x : Hilbert)) - (P x + (a : ℂ) • (x : Hilbert)))) ∧
    (∀ n : ℕ,
      fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n ∈ (P).domain ∧
      P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩ +
        (a : ℂ) • fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n ∈ (K).domain) ∧
    Tendsto (fun n : ℕ =>
      (fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
        P ⟨fixedShiftPotentialRadialYosidaSeq ε hε h hh hb m g k a x n,
          fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n⟩))
      atTop (𝓝 ((x : Hilbert), P x)) :=
  ⟨potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k a N ha hN x,
   potentialResolventRadialYosidaApprox_shifted_eq ε hε h hh hb m g k a N ha hN x,
   potentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a N ha hN x,
   fun n => ⟨fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain ε hε h hh hb m g k a ha x n,
     fixedShiftPotentialRadialYosidaSeq_shifted_mem_radial_domain ε hε h hh hb m g k a ha x n⟩,
   tendsto_fixedShiftPotentialRadialYosidaSeq_graph ε hε h hh hb m g k a ha x⟩

#print axioms potentialResolventRadialYosidaApprox_mem_potentialDomain
#print axioms potentialResolventRadialYosidaApprox_mem_potentialForm_domain
#print axioms shifted_source_radialYosida_mem_radial_domain
#print axioms potentialResolventRadialYosidaApprox_mem_radial_domain_of_quarter
#print axioms potentialResolventRadialYosidaApprox_mem_growing_domain_of_quarter
#print axioms potentialResolventRadialYosidaApprox_equation
#print axioms potentialResolventRadialYosidaApprox_shifted_eq
#print axioms potentialResolventRadialYosidaApprox_shifted_mem_radial_domain
#print axioms potential_resolvent_left_inverse_complex
#print axioms potentialResolventRadialYosidaApprox_sub_eq
#print axioms potentialResolventRadialYosidaApprox_sub_mem_potentialDomain
#print axioms potential_action_on_potentialResolventRadialYosidaApprox_sub_eq_resolvent
#print axioms potential_action_on_potentialResolventRadialYosidaApprox_sub_eq
#print axioms potentialResolventRadialYosidaApprox_norm_le
#print axioms potentialResolventRadialYosidaApprox_operator_norm_le
#print axioms potentialResolventRadialYosidaApprox_sub_norm_le
#print axioms potential_action_on_potentialResolventRadialYosidaApprox_sub_norm_le
#print axioms potentialResolventRadialYosidaApprox_potentialForm_sub_norm_sq_le
#print axioms potentialResolventRadialYosidaApprox_sub_norm_le_inv_N_of_radial
#print axioms potential_action_sub_norm_le_inv_N_of_radial
#print axioms fixedShiftPotentialRadialYosidaSeq_mem_potentialDomain
#print axioms fixedShiftPotentialRadialYosidaSeq_shifted_mem_radial_domain
#print axioms fixedShiftPotentialRadialYosidaSeq_mem_growing_domain_of_quarter
#print axioms tendsto_shifted_source_radialYosida_sub
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq_sub_norm
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq_potential_action
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq_action_sub_norm
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq_graph_error_norm
#print axioms tendsto_fixedShiftPotentialRadialYosidaSeq_graph
#print axioms dualPotentialScaledRadialYosidaApprox_mem_potentialDomain
#print axioms dualPotentialScaledRadialYosidaApprox_mem_growing_domain_of_quarter
#print axioms dualPotentialScaledRadialYosidaApprox_norm_le
#print axioms tendsto_dualPotentialScaledRadialYosidaSeq
#print axioms potential_resolvent_radial_yosida_invariance_master_bridge
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventYosidaInvarianceBridge
