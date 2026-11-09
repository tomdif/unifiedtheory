/- Iterated Potential-Resolvent Radial-Yosida Second-Power Graph Core,
Two-Parameter Symmetry, and Simultaneous Three-Tier Convergence on Dom(P²):
1. For any x ∈ Dom(P), defines the two-parameter potential-resolvent radial-Yosida
   smoother
   potentialSecondPowerRadialYosidaApprox a b N x := R_P(a)(potentialResolventRadialYosidaApprox b N x)
   and proves that it lies unconditionally in Dom(P²) = potentialSecondPowerDomain
   (and on the quarter-strip |h| ≤ π * ε / 4, in Dom(K_rad) and Dom(G)).
2. Establishes two-parameter first resolvent difference and commutativity identities
   for radial-Yosida regularized states:
   R_P(a)(J_N f) - R_P(b)(J_N f) = ((b - a : ℝ) : ℂ) • R_P(a)(R_P(b)(J_N f))
   and R_P(a)(R_P(b)(J_N f)) = R_P(b)(R_P(a)(J_N f)).
3. For every x ∈ Dom(P²) (i.e. x ∈ Dom(P) with P x ∈ Dom(P)), defines the double-shifted
   source g_x := (P + a I)((P + b I) x), the second-power radial-Yosida state
   iteratedPotentialResolventRadialYosidaApprox a b N x := R_P(a)(R_P(b)(J_N g_x)),
   and the integer-scale sequence fixedShiftPotentialSecondPowerRadialYosidaSeq a b x n,
   proving exact zeroth-, first-, and second-order defect formulas, explicit norm bounds,
   and simultaneous three-tier strong convergence as n → ∞:
   - fixedShiftPotentialSecondPowerRadialYosidaSeq a b x n → x,
   - P(fixedShiftPotentialSecondPowerRadialYosidaSeq a b x n) → P x,
   - P(P(fixedShiftPotentialSecondPowerRadialYosidaSeq a b x n)) → P(P x). -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventYosidaInvarianceBridge
import UnifiedTheory.Audit.KFCausalClockFloorFiveOperatorFirstResolventIdentity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorIteratedPotentialResolventYosidaGraphCore
noncomputable section
open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer
  (action action_norm radial_domain sequence_tendsto)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (potential_resolvent_norm_le resolvent_radial_domain resolvent_growing_domain)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_resolvent_mem_potential_domain
   potential_resolvent_equation
   potential_resolvent_left_inverse
   potential_resolvent_mem_potentialForm_domain
   potential_resolvent_operator_norm_le)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerDomain secondPowerGraph)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (potentialSecondPowerDomain
   potential_resolvent_mem_secondPowerDomain
   potential_iterated_resolvent_secondPower)
open KFCausalClockFloorPotentialResolventYosidaInvarianceBridge
  (potentialResolventRadialYosidaApprox
   potentialResolventRadialYosidaApprox_mem_potentialDomain
   potentialResolventRadialYosidaApprox_mem_radial_domain_of_quarter
   potential_resolvent_left_inverse_complex
   shifted_source_radialYosida_mem_radial_domain)
open KFCausalClockFloorFiveOperatorFirstResolventIdentity
  (potentialResolvent_sub_potentialResolvent
   potentialResolvent_comm
   norm_potentialResolvent_sub_le)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "J" => action ε hε h

/-! ### 1. Two-Parameter Radial-Yosida Potential-Resolvent Commutativity and Smoother on `Dom(P)` -/

/-- Simpler iterated potential-resolvent radial-Yosida smoother for any `x ∈ Dom(P)`:
`R_P(a) (potentialResolventRadialYosidaApprox b N x) = R_P(a) (R_P(b) (J_N (P x + b • x)))`. -/
def potentialSecondPowerRadialYosidaApprox
    (a b N : ℝ) (hN : 0 < N) (x : (P).domain) : Hilbert :=
  RP a (potentialResolventRadialYosidaApprox ε hε h hh hb m g k b N hN x)

theorem potentialResolvent_radialYosida_sub_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (f : Hilbert) :
    RP a (J N hN f) - RP b (J N hN f) =
      ((b - a : ℝ) : ℂ) • RP a (RP b (J N hN f)) :=
  potentialResolvent_sub_potentialResolvent ε hε h hh hb m g k a b ha hb_pos (J N hN f)

theorem potentialResolvent_radialYosida_comm
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (f : Hilbert) :
    RP a (RP b (J N hN f)) = RP b (RP a (J N hN f)) :=
  potentialResolvent_comm ε hε h hh hb m g k a b ha hb_pos (J N hN f)

theorem potentialResolvent_radialYosida_sub_mem_secondPowerDomain
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (f : Hilbert) :
    RP a (J N hN f) - RP b (J N hN f) ∈
      potentialSecondPowerDomain ε hε h hh hb m g k :=
  KFCausalClockFloorFiveOperatorFirstResolventIdentity.potentialResolvent_sub_mem_potentialSecondPowerDomain
    ε hε h hh hb m g k a b ha hb_pos (J N hN f)

theorem potentialResolvent_radialYosida_sub_norm_le
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (f : Hilbert) :
    ‖RP a (J N hN f) - RP b (J N hN f)‖ ≤ |a - b| * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  refine (norm_potentialResolvent_sub_le ε hε h hh hb m g k a b ha hb_pos (J N hN f)).trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (action_norm ε hε h N hN f) (inv_nonneg.mpr hb_pos.le))
      (inv_nonneg.mpr ha.le))
    (abs_nonneg (a - b))

theorem potentialSecondPowerRadialYosidaApprox_mem_potentialDomain
    (a b N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) :
    potentialSecondPowerRadialYosidaApprox ε hε h hh hb m g k a b N hN x ∈ (P).domain :=
  potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha
    (potentialResolventRadialYosidaApprox ε hε h hh hb m g k b N hN x)

theorem potentialSecondPowerRadialYosidaApprox_mem_secondPowerDomain
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (x : (P).domain) :
    potentialSecondPowerRadialYosidaApprox ε hε h hh hb m g k a b N hN x ∈
      potentialSecondPowerDomain ε hε h hh hb m g k :=
  potential_resolvent_mem_secondPowerDomain ε hε h hh hb m g k a ha
    (potentialResolventRadialYosidaApprox_mem_potentialDomain ε hε h hh hb m g k b N hb_pos hN x)

theorem potentialSecondPowerRadialYosidaApprox_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (x : (P).domain) :
    potentialSecondPowerRadialYosidaApprox ε hε h hh hb m g k a b N hN x ∈ (G).domain :=
  resolvent_growing_domain ε hε h hb hh m g k hq a ha
    (potentialResolventRadialYosidaApprox ε hε h hh hb m g k b N hN x)
    (potentialResolventRadialYosidaApprox_mem_radial_domain_of_quarter
      ε hε h hh hb m g k hq b N hb_pos hN x)

theorem potentialSecondPowerRadialYosidaApprox_norm_le
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N) (x : (P).domain) :
    ‖potentialSecondPowerRadialYosidaApprox ε hε h hh hb m g k a b N hN x‖ ≤
      a⁻¹ * (b⁻¹ * ‖P x + (b : ℂ) • (x : Hilbert)‖) :=
  (potential_resolvent_norm_le ε hε h hb hh m g k a ha _).trans
    (mul_le_mul_of_nonneg_left
      (KFCausalClockFloorPotentialResolventYosidaInvarianceBridge.potentialResolventRadialYosidaApprox_norm_le
        ε hε h hh hb m g k b N hb_pos hN x)
      (inv_nonneg.mpr ha.le))

/-! ### 2. Second-Power (`Dom(P²)`) Double-Shifted Source and Iterated Radial-Yosida State -/

/-- For `x ∈ Dom(P)` with `P x ∈ Dom(P)`, the shifted vector `P x + b • x` packaged as an
element of `Dom(P)`. -/
def shiftedPotentialDomainElem
    (b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) : (P).domain :=
  ⟨P x, hx2⟩ + (b : ℂ) • x

theorem shiftedPotentialDomainElem_coe
    (b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    (shiftedPotentialDomainElem ε hε h hh hb m g k b x hx2 : Hilbert) =
      P x + (b : ℂ) • (x : Hilbert) :=
  rfl

theorem shiftedPotentialDomainElem_action_eq
    (b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    P (shiftedPotentialDomainElem ε hε h hh hb m g k b x hx2) =
      P ⟨P x, hx2⟩ + (b : ℂ) • P x := by
  unfold shiftedPotentialDomainElem
  rw [(P).map_add, (P).map_smul]

/-- For `x ∈ Dom(P²)`, the double-shifted source
`g_x := (P + a I)((P + b I) x) = P(P x + b • x) + a • (P x + b • x)`. -/
def secondPowerShiftedSource
    (a b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) : Hilbert :=
  P (shiftedPotentialDomainElem ε hε h hh hb m g k b x hx2) +
    (a : ℂ) • (shiftedPotentialDomainElem ε hε h hh hb m g k b x hx2 : Hilbert)

theorem secondPowerShiftedSource_expand
    (a b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    secondPowerShiftedSource ε hε h hh hb m g k a b x hx2 =
      P ⟨P x, hx2⟩ + ((a + b : ℝ) : ℂ) • P x + ((a * b : ℝ) : ℂ) • (x : Hilbert) := by
  unfold secondPowerShiftedSource
  rw [shiftedPotentialDomainElem_action_eq, shiftedPotentialDomainElem_coe]
  push_cast
  module

theorem secondPowerShiftedSource_comm
    (a b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    secondPowerShiftedSource ε hε h hh hb m g k a b x hx2 =
      secondPowerShiftedSource ε hε h hh hb m g k b a x hx2 := by
  rw [secondPowerShiftedSource_expand, secondPowerShiftedSource_expand]
  push_cast
  module

theorem potentialResolvent_secondPowerShiftedSource_right
    (a b : ℝ) (hb_pos : 0 < b) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    RP b (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) =
      P x + (a : ℂ) • (x : Hilbert) := by
  rw [secondPowerShiftedSource_comm]
  exact potential_resolvent_left_inverse_complex ε hε h hh hb m g k b hb_pos
    (shiftedPotentialDomainElem ε hε h hh hb m g k a x hx2)

theorem potentialResolvent_secondPowerShiftedSource_left
    (a b : ℝ) (ha : 0 < a) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    RP a (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) =
      P x + (b : ℂ) • (x : Hilbert) :=
  potential_resolvent_left_inverse_complex ε hε h hh hb m g k a ha
    (shiftedPotentialDomainElem ε hε h hh hb m g k b x hx2)

theorem iterated_potentialResolvent_secondPowerShiftedSource
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    RP a (RP b (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) = (x : Hilbert) := by
  rw [potentialResolvent_secondPowerShiftedSource_right ε hε h hh hb m g k a b hb_pos x hx2]
  exact potential_resolvent_left_inverse_complex ε hε h hh hb m g k a ha x

/-- Second-power (`Dom(P²)`) resolvent-regularized radial-Yosida state:
`R_P(a) (R_P(b) (J_N (P(P x + b • x) + a • (P x + b • x))))`. -/
def iteratedPotentialResolventRadialYosidaApprox
    (a b N : ℝ) (hN : 0 < N) (x : (P).domain) (hx2 : P x ∈ (P).domain) : Hilbert :=
  RP a (RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)))

/-- Integer-scale (`N = n + 1`) fixed-shift second-power radial-Yosida sequence on `Dom(P²)`. -/
def fixedShiftPotentialSecondPowerRadialYosidaSeq
    (a b : ℝ) (x : (P).domain) (hx2 : P x ∈ (P).domain) (n : ℕ) : Hilbert :=
  iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k
    a b ((n : ℝ) + 1) (by positivity) x hx2

theorem iteratedPotentialResolventRadialYosidaApprox_comm
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 =
      iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k b a N hN x hx2 := by
  unfold iteratedPotentialResolventRadialYosidaApprox
  rw [secondPowerShiftedSource_comm ε hε h hh hb m g k a b x hx2,
    potentialResolvent_comm ε hε h hh hb m g k a b ha hb_pos]

theorem iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
    (a b N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 ∈ (P).domain :=
  potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha _

theorem iteratedPotentialResolventRadialYosidaApprox_mem_secondPowerDomain
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 ∈
      potentialSecondPowerDomain ε hε h hh hb m g k :=
  (potential_iterated_resolvent_secondPower ε hε h hh hb m g k a b ha hb_pos
    (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))).1

theorem iteratedPotentialResolventRadialYosidaApprox_mem_growing_domain_of_quarter
    (hq : |h| ≤ Real.pi * ε / 4)
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 ∈ (G).domain :=
  resolvent_growing_domain ε hε h hb hh m g k hq a ha _
    (resolvent_radial_domain ε hε h hb hh m g k hq b hb_pos _
      (radial_domain ε hε h N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)))

/-! ### 3. Exact Zeroth-, First-, and Second-Order Defect Identities on `Dom(P²)` -/

theorem iteratedPotentialResolventRadialYosidaApprox_first_shifted_eq
    (a b N : ℝ) (ha : 0 < a) (hN : 0 < N) (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
      iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2⟩ +
      (a : ℂ) • iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 =
      RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) := by
  unfold iteratedPotentialResolventRadialYosidaApprox
  rw [potential_resolvent_equation ε hε h hh hb m g k a ha _,
    ← Complex.coe_smul a (RP a (RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)))),
    sub_add_cancel]

theorem iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
      iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2⟩ ∈ (P).domain := by
  have heq :
      P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b N ha hN x hx2⟩ =
      RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) -
        (a : ℂ) • iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 := by
    rw [Complex.coe_smul]
    exact potential_resolvent_equation ε hε h hh hb m g k a ha _
  rw [heq]
  exact (P).domain.sub_mem
    (potential_resolvent_mem_potential_domain ε hε h hh hb m g k b hb_pos _)
    ((P).domain.smul_mem (a : ℂ)
      (iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2))

theorem iteratedPotentialResolventRadialYosidaApprox_second_shifted_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    let z := iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2
    let hz := iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
      ε hε h hh hb m g k a b N ha hN x hx2
    let w := P ⟨z, hz⟩ + (a : ℂ) • z
    let hw_dom : w ∈ (P).domain :=
      (P).domain.add_mem
        (iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
          ε hε h hh hb m g k a b N ha hb_pos hN x hx2)
        ((P).domain.smul_mem (a : ℂ) hz)
    P ⟨w, hw_dom⟩ + (b : ℂ) • w =
      J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) ∧
    P ⟨w, hw_dom⟩ + (b : ℂ) • w ∈ (K).domain := by
  intro z hz w hw_dom
  have hw_eq : w = RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) :=
    iteratedPotentialResolventRadialYosidaApprox_first_shifted_eq
      ε hε h hh hb m g k a b N ha hN x hx2
  have hsub : (⟨w, hw_dom⟩ : (P).domain) =
      ⟨RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)),
        potential_resolvent_mem_potential_domain ε hε h hh hb m g k b hb_pos _⟩ :=
    Subtype.ext hw_eq
  have h1 : P ⟨w, hw_dom⟩ + (b : ℂ) • w =
      J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) := by
    rw [hsub, hw_eq, potential_resolvent_equation ε hε h hh hb m g k b hb_pos _,
      ← Complex.coe_smul b (RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))),
      sub_add_cancel]
  exact ⟨h1, h1.symm ▸ radial_domain ε hε h N hN _⟩

theorem iteratedPotentialResolventRadialYosidaApprox_sub_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 - (x : Hilbert) =
      RP a (RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) := by
  unfold iteratedPotentialResolventRadialYosidaApprox
  rw [map_sub, map_sub,
    iterated_potentialResolvent_secondPowerShiftedSource ε hε h hh hb m g k a b ha hb_pos x hx2]

theorem iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    (P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
      iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2⟩ +
      (a : ℂ) • iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2) -
      (P x + (a : ℂ) • (x : Hilbert)) =
      RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) := by
  rw [iteratedPotentialResolventRadialYosidaApprox_first_shifted_eq
      ε hε h hh hb m g k a b N ha hN x hx2,
    map_sub,
    potentialResolvent_secondPowerShiftedSource_right ε hε h hh hb m g k a b hb_pos x hx2]

theorem iteratedPotentialResolventRadialYosidaApprox_action_sub_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
      iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2⟩ - P x =
      RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        (a : ℂ) •
          (iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 -
            (x : Hilbert)) := by
  have h1 := iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_eq
    ε hε h hh hb m g k a b N ha hb_pos hN x hx2
  rw [← h1]
  module

theorem iteratedPotentialResolventRadialYosidaApprox_second_action_eq
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    let z := iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2
    let hz := iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
      ε hε h hh hb m g k a b N ha hN x hx2
    let hPz := iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
      ε hε h hh hb m g k a b N ha hb_pos hN x hx2
    P ⟨P ⟨z, hz⟩, hPz⟩ =
      (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        (b : ℂ) • RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))) -
        (a : ℂ) • P ⟨z, hz⟩ := by
  intro z hz hPz
  let u_w : (P).domain :=
    ⟨RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)),
      potential_resolvent_mem_potential_domain ε hε h hh hb m g k b hb_pos _⟩
  let u_z : (P).domain := ⟨z, hz⟩
  have hsub : (⟨P ⟨z, hz⟩, hPz⟩ : (P).domain) = u_w - (a : ℂ) • u_z := by
    apply Subtype.ext
    change P ⟨z, hz⟩ = RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) -
      (a : ℂ) • z
    rw [Complex.coe_smul]
    exact potential_resolvent_equation ε hε h hh hb m g k a ha _
  rw [hsub, (P).map_sub, (P).map_smul]
  have huw : P u_w =
      J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        (b : ℂ) • RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) := by
    rw [Complex.coe_smul]
    exact potential_resolvent_equation ε hε h hh hb m g k b hb_pos _
  rw [huw]

theorem iteratedPotentialResolventRadialYosidaApprox_sub_norm_le
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    ‖iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 -
      (x : Hilbert)‖ ≤
      a⁻¹ * (b⁻¹ *
        ‖J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
          secondPowerShiftedSource ε hε h hh hb m g k a b x hx2‖) := by
  rw [iteratedPotentialResolventRadialYosidaApprox_sub_eq ε hε h hh hb m g k a b N ha hb_pos hN x hx2]
  exact (potential_resolvent_norm_le ε hε h hb hh m g k a ha _).trans
    (mul_le_mul_of_nonneg_left
      (potential_resolvent_norm_le ε hε h hb hh m g k b hb_pos _)
      (inv_nonneg.mpr ha.le))

theorem iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_norm_le
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    ‖(P ⟨iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2,
      iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
        ε hε h hh hb m g k a b N ha hN x hx2⟩ +
      (a : ℂ) • iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2) -
      (P x + (a : ℂ) • (x : Hilbert))‖ ≤
      b⁻¹ *
        ‖J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
          secondPowerShiftedSource ε hε h hh hb m g k a b x hx2‖ := by
  rw [iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_eq
    ε hε h hh hb m g k a b N ha hb_pos hN x hx2]
  exact potential_resolvent_norm_le ε hε h hb hh m g k b hb_pos _

/-! ### 4. Simultaneous Three-Tier Strong Convergence on `Dom(P²)` as `n → ∞` -/

theorem fixedShiftPotentialSecondPowerRadialYosidaSeq_mem_secondPowerDomain
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) (n : ℕ) :
    fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n ∈
      potentialSecondPowerDomain ε hε h hh hb m g k :=
  iteratedPotentialResolventRadialYosidaApprox_mem_secondPowerDomain
    ε hε h hh hb m g k a b ((n : ℝ) + 1) ha hb_pos (by positivity) x hx2

theorem tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_first_shifted
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩ +
        (a : ℂ) • fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n)
      atTop (𝓝 (P x + (a : ℂ) • (x : Hilbert))) := by
  let g_x := secondPowerShiftedSource ε hε h hh hb m g k a b x hx2
  have h1 := ((RP b).continuous.tendsto g_x).comp (sequence_tendsto ε hε h g_x)
  rw [potentialResolvent_secondPowerShiftedSource_right ε hε h hh hb m g k a b hb_pos x hx2] at h1
  refine h1.congr' (Eventually.of_forall fun n => ?_)
  exact (iteratedPotentialResolventRadialYosidaApprox_first_shifted_eq
    ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2).symm

theorem tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n)
      atTop (𝓝 (x : Hilbert)) := by
  have h1 := ((RP b).continuous.tendsto
    (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)).comp
    (sequence_tendsto ε hε h (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))
  have h2 := ((RP a).continuous.tendsto
    (RP b (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))).comp h1
  simpa only [Function.comp_def, fixedShiftPotentialSecondPowerRadialYosidaSeq,
    iteratedPotentialResolventRadialYosidaApprox,
    iterated_potentialResolvent_secondPowerShiftedSource
      ε hε h hh hb m g k a b ha hb_pos x hx2] using h2

theorem tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_action
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩)
      atTop (𝓝 (P x)) := by
  have h1 := tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_first_shifted
    ε hε h hh hb m g k a b ha hb_pos x hx2
  have h2 := (tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq
    ε hε h hh hb m g k a b ha hb_pos x hx2).const_smul (a : ℂ)
  have hdiff := h1.sub h2
  rw [add_sub_cancel_right] at hdiff
  refine hdiff.congr' (Eventually.of_forall fun n => ?_)
  exact add_sub_cancel_right _ _

theorem tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_second_action
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      P ⟨P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩,
        iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha hb_pos (by positivity) x hx2⟩)
      atTop (𝓝 (P ⟨P x, hx2⟩)) := by
  have hJ := sequence_tendsto ε hε h (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)
  have h_w :=
    (((RP b).continuous.tendsto
      (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)).comp hJ).const_smul (b : ℂ)
  have hPz :=
    (tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_action
      ε hε h hh hb m g k a b ha hb_pos x hx2).const_smul (a : ℂ)
  have hcomb := (hJ.sub h_w).sub hPz
  have htarget :
      (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2 -
        (b : ℂ) • RP b (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2)) -
        (a : ℂ) • P x = P ⟨P x, hx2⟩ := by
    rw [potentialResolvent_secondPowerShiftedSource_right ε hε h hh hb m g k a b hb_pos x hx2,
      secondPowerShiftedSource_expand]
    push_cast
    module
  rw [htarget] at hcomb
  refine hcomb.congr' (Eventually.of_forall fun n => ?_)
  exact (iteratedPotentialResolventRadialYosidaApprox_second_action_eq
    ε hε h hh hb m g k a b ((n : ℝ) + 1) ha hb_pos (by positivity) x hx2).symm

theorem tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_three_tier
    (a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    Tendsto (fun n : ℕ =>
      fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n)
      atTop (𝓝 (x : Hilbert)) ∧
    Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩)
      atTop (𝓝 (P x)) ∧
    Tendsto (fun n : ℕ =>
      P ⟨P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩,
        iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha hb_pos (by positivity) x hx2⟩)
      atTop (𝓝 (P ⟨P x, hx2⟩)) :=
  ⟨tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b ha hb_pos x hx2,
   tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_action
     ε hε h hh hb m g k a b ha hb_pos x hx2,
   tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_second_action
     ε hε h hh hb m g k a b ha hb_pos x hx2⟩

theorem iterated_potential_resolvent_yosida_graph_core_master_synthesis
    (a b N : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hN : 0 < N)
    (x : (P).domain) (hx2 : P x ∈ (P).domain) :
    (potentialSecondPowerRadialYosidaApprox ε hε h hh hb m g k a b N hN x ∈
      potentialSecondPowerDomain ε hε h hh hb m g k ∧
     iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 ∈
      potentialSecondPowerDomain ε hε h hh hb m g k) ∧
    (iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 =
      iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k b a N hN x hx2 ∧
     iteratedPotentialResolventRadialYosidaApprox ε hε h hh hb m g k a b N hN x hx2 - (x : Hilbert) =
      RP a (RP b (J N hN (secondPowerShiftedSource ε hε h hh hb m g k a b x hx2) -
        secondPowerShiftedSource ε hε h hh hb m g k a b x hx2))) ∧
    (Tendsto (fun n : ℕ =>
      fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n)
      atTop (𝓝 (x : Hilbert)) ∧
     Tendsto (fun n : ℕ =>
      P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩)
      atTop (𝓝 (P x)) ∧
     Tendsto (fun n : ℕ =>
      P ⟨P ⟨fixedShiftPotentialSecondPowerRadialYosidaSeq ε hε h hh hb m g k a b x hx2 n,
        iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha (by positivity) x hx2⟩,
        iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
          ε hε h hh hb m g k a b ((n : ℝ) + 1) ha hb_pos (by positivity) x hx2⟩)
      atTop (𝓝 (P ⟨P x, hx2⟩))) :=
  ⟨⟨potentialSecondPowerRadialYosidaApprox_mem_secondPowerDomain
      ε hε h hh hb m g k a b N ha hb_pos hN x,
    iteratedPotentialResolventRadialYosidaApprox_mem_secondPowerDomain
      ε hε h hh hb m g k a b N ha hb_pos hN x hx2⟩,
   ⟨iteratedPotentialResolventRadialYosidaApprox_comm
      ε hε h hh hb m g k a b N ha hb_pos hN x hx2,
    iteratedPotentialResolventRadialYosidaApprox_sub_eq
      ε hε h hh hb m g k a b N ha hb_pos hN x hx2⟩,
   tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_three_tier
      ε hε h hh hb m g k a b ha hb_pos x hx2⟩

#print axioms potentialResolvent_radialYosida_sub_eq
#print axioms potentialResolvent_radialYosida_comm
#print axioms potentialResolvent_radialYosida_sub_mem_secondPowerDomain
#print axioms potentialResolvent_radialYosida_sub_norm_le
#print axioms potentialSecondPowerRadialYosidaApprox_mem_potentialDomain
#print axioms potentialSecondPowerRadialYosidaApprox_mem_secondPowerDomain
#print axioms potentialSecondPowerRadialYosidaApprox_mem_growing_domain_of_quarter
#print axioms potentialSecondPowerRadialYosidaApprox_norm_le
#print axioms shiftedPotentialDomainElem_coe
#print axioms shiftedPotentialDomainElem_action_eq
#print axioms secondPowerShiftedSource_expand
#print axioms secondPowerShiftedSource_comm
#print axioms potentialResolvent_secondPowerShiftedSource_right
#print axioms potentialResolvent_secondPowerShiftedSource_left
#print axioms iterated_potentialResolvent_secondPowerShiftedSource
#print axioms iteratedPotentialResolventRadialYosidaApprox_comm
#print axioms iteratedPotentialResolventRadialYosidaApprox_mem_potentialDomain
#print axioms iteratedPotentialResolventRadialYosidaApprox_mem_secondPowerDomain
#print axioms iteratedPotentialResolventRadialYosidaApprox_mem_growing_domain_of_quarter
#print axioms iteratedPotentialResolventRadialYosidaApprox_first_shifted_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_action_mem_potentialDomain
#print axioms iteratedPotentialResolventRadialYosidaApprox_second_shifted_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_sub_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_action_sub_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_second_action_eq
#print axioms iteratedPotentialResolventRadialYosidaApprox_sub_norm_le
#print axioms iteratedPotentialResolventRadialYosidaApprox_first_shifted_sub_norm_le
#print axioms fixedShiftPotentialSecondPowerRadialYosidaSeq_mem_secondPowerDomain
#print axioms tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_first_shifted
#print axioms tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq
#print axioms tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_action
#print axioms tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_second_action
#print axioms tendsto_fixedShiftPotentialSecondPowerRadialYosidaSeq_three_tier
#print axioms iterated_potential_resolvent_yosida_graph_core_master_synthesis
end
end UnifiedTheory.Audit.KFCausalClockFloorIteratedPotentialResolventYosidaGraphCore
