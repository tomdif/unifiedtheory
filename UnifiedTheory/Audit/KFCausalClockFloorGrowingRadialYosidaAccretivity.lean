/- Unconditional linear and quadratic radial-Yosida (`M_N`), radial-Yosida
square-root (`M_N^(1/2)`), and radial-resolvent (`J_N = (1 + N⁻¹ K_rad)⁻¹`)
accretivity and coercive lower bounds for the maximal radial operator `K_rad`
and for the full growing clock-floor Hamiltonian `G = K_rad + P`:
1. On `Dom(K_rad)` for all `h : ℝ` and `N > 0`:
   - `K_rad x = M_N x + N⁻¹ • M_N (K_rad x)`
   - `‖M_N x‖² ≤ Re ⟨K_rad x, M_N x⟩`
   - `Re ⟨K_rad x, J_N x⟩ = ‖M_N^(1/2) x‖²`
   - `‖M_N^(1/2) (M_N x)‖² ≤ Re ⟨K_rad x, M_N (M_N x)⟩`
   - `Re ⟨K_rad x, J_N (J_N x)⟩ = ‖K_root (J_N x)‖²`
2. On `Dom(G)` for the full strip `|h| ≤ π * ε / 3`:
   - `‖M_N x‖² ≤ Re ⟨G x, M_N x⟩ = Re ⟨M_N^(1/2) (G x), M_N^(1/2) x⟩`
   - `‖M_N^(1/2) x‖² ≤ Re ⟨G x, J_N x⟩`
3. On `Dom(G)` for the quarter-strip `|h| ≤ π * ε / 4` (and `|h| ≤ π * ε / 6`):
   - `‖M_N^(1/2) (M_N x)‖² ≤ Re ⟨G x, M_N (M_N x)⟩`
   - `‖K_root (J_N x)‖² ≤ Re ⟨G x, J_N (J_N x)⟩` -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialRadialYosidaAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRootRegularity
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialYosidaAccretivity
noncomputable section
open scoped InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)
open KFCausalClockFloorGrowingRadialDomination (radial_domain)
open KFCausalClockFloorRadialResolventRegularizer (action radial_graph)
open KFCausalClockFloorRadialResolventGrowingDomain
  (root_radial_pairing radial_action_commute radial_domain_le_root_domain
    growingHamiltonian_in_potentialHamiltonian_domain
    growingHamiltonian_eq_radial_add_potential)
open KFCausalClockFloorPotentialRadialYosidaAccretivity
  (potential_yosida_accretive potential_resolvent_accretive
    potential_yosida_sq_accretive potential_resolvent_sq_accretive)
open KFCausalClockFloorRadialYosidaQuarterStripSector
  (quarter_le_third sixth_le_quarter)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (yosidaRootAction yosidaRootAction_selfAdjoint_pairing
    yosidaRootAction_sq_eq_yosida yosidaRootAction_sq_inner
    yosidaRootAction_norm_sq_eq_inner)

private theorem conj_inv_ofReal (N : ℝ) :
    (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

private theorem re_inv_ofReal_mul (N : ℝ) (z : ℂ) :
    (((N : ℂ)⁻¹) * z).re = N⁻¹ * z.re := by
  rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

private theorem add_re_lower_of_eq {g_x k_x p_x v : Hilbert} {L : ℝ}
    (heq : g_x = k_x + p_x)
    (hk : L ≤ (inner ℂ k_x v).re)
    (hp : 0 ≤ (inner ℂ p_x v).re) :
    L ≤ (inner ℂ g_x v).re := by
  rw [heq, inner_add_left, Complex.add_re]
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "J" => action ε hε h N hN
local notation "Mroot" => yosidaRootAction ε hε h N hN
local notation "Kr" => operator ε hε h
local notation "Kroot" => rootOperator ε hε h

/-! ### 1. Pure Radial Yosida and Resolvent Operator Identities and Lower Bounds -/

theorem yosida_selfAdjoint_pairing (u v : Hilbert) :
    inner ℂ u (M v) = inner ℂ (M u) v := by
  rw [← yosidaRootAction_sq_eq_yosida ε hε h N hN u,
    ← yosidaRootAction_sq_eq_yosida ε hε h N hN v,
    yosidaRootAction_selfAdjoint_pairing ε hε h N hN (Mroot u) v,
    yosidaRootAction_selfAdjoint_pairing ε hε h N hN u (Mroot v)]

theorem resolvent_selfAdjoint_pairing (u v : Hilbert) :
    inner ℂ u (J v) = inner ℂ (J u) v := by
  change inner ℂ u (v - (N⁻¹ : ℂ) • M v) = inner ℂ (u - (N⁻¹ : ℂ) • M u) v
  rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
    conj_inv_ofReal, yosida_selfAdjoint_pairing ε hε h N hN u v]

theorem resolvent_add_scaled_yosida (f : Hilbert) :
    J f + (N⁻¹ : ℂ) • M f = f := by
  change (f - (N⁻¹ : ℂ) • M f) + (N⁻¹ : ℂ) • M f = f
  exact sub_add_cancel f ((N⁻¹ : ℂ) • M f)

theorem radial_eq_yosida_add_scaled_yosida_radial (x : (Kr).domain) :
    Kr x = M (x : Hilbert) + (N⁻¹ : ℂ) • M (Kr x) := by
  have hc := radial_action_commute ε hε h N hN (x : Hilbert) (Kr x) ((Kr).mem_graph x)
  have hj := resolvent_add_scaled_yosida ε hε h N hN (Kr x)
  rw [← hc] at hj
  exact hj.symm

theorem yosida_resolvent_pairing_eq_root_norm_sq (f : Hilbert) :
    inner ℂ (M f) (J f) =
      ((‖Kroot ⟨J f, radial_domain_le_root_domain ε hε h (J f)
        (KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN f)⟩‖ ^ 2 : ℝ) : ℂ) := by
  let hj := radial_domain_le_root_domain ε hε h (J f)
    (KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN f)
  let r := Kroot ⟨J f, hj⟩
  have hp := root_radial_pairing ε hε h (J f) (J f) r r (M f)
    ((Kroot).mem_graph ⟨J f, hj⟩) ((Kroot).mem_graph ⟨J f, hj⟩)
    (radial_graph ε hε h N hN f)
  exact hp.symm.trans (KFCausalShiftedForm.complex_inner_square r)

theorem yosida_resolvent_re_nonneg (f : Hilbert) :
    0 ≤ (inner ℂ (M f) (J f)).re := by
  rw [yosida_resolvent_pairing_eq_root_norm_sq ε hε h N hN f, Complex.ofReal_re]
  exact sq_nonneg _

theorem yosidaRoot_comm_yosida (f : Hilbert) :
    Mroot (M f) = M (Mroot f) := by
  rw [← yosidaRootAction_sq_eq_yosida ε hε h N hN f,
    yosidaRootAction_sq_eq_yosida ε hε h N hN (Mroot f)]

theorem yosidaRoot_comm_resolvent (f : Hilbert) :
    Mroot (J f) = J (Mroot f) := by
  change Mroot (f - (N⁻¹ : ℂ) • M f) = Mroot f - (N⁻¹ : ℂ) • M (Mroot f)
  rw [map_sub, map_smul, yosidaRoot_comm_yosida ε hε h N hN f]

theorem yosida_sq_resolvent_pairing_eq (f : Hilbert) :
    inner ℂ (M (M f)) (J f) = inner ℂ (M (Mroot f)) (J (Mroot f)) := by
  rw [← yosidaRootAction_sq_eq_yosida ε hε h N hN (M f),
    yosidaRoot_comm_yosida ε hε h N hN f,
    yosidaRootAction_selfAdjoint_pairing ε hε h N hN (M (Mroot f)) (J f),
    yosidaRoot_comm_resolvent ε hε h N hN f]

theorem yosida_sq_resolvent_re_nonneg (f : Hilbert) :
    0 ≤ (inner ℂ (M (M f)) (J f)).re := by
  rw [yosida_sq_resolvent_pairing_eq ε hε h N hN f]
  exact yosida_resolvent_re_nonneg ε hε h N hN (Mroot f)

theorem radial_yosida_lower (x : (Kr).domain) :
    ‖M (x : Hilbert)‖ ^ 2 ≤ (inner ℂ (Kr x) (M (x : Hilbert))).re := by
  have heq := radial_eq_yosida_add_scaled_yosida_radial ε hε h N hN x
  have hc := radial_action_commute ε hε h N hN (x : Hilbert) (Kr x) ((Kr).mem_graph x)
  have hsplit : inner ℂ (Kr x) (M (x : Hilbert)) =
      inner ℂ (M (x : Hilbert)) (M (x : Hilbert)) +
        (N⁻¹ : ℂ) * inner ℂ (M (Kr x)) (J (Kr x)) := by
    calc
      inner ℂ (Kr x) (M (x : Hilbert)) =
          inner ℂ (M (x : Hilbert) + (N⁻¹ : ℂ) • M (Kr x)) (M (x : Hilbert)) := by
        rw [← heq]
      _ = inner ℂ (M (x : Hilbert)) (M (x : Hilbert)) +
            inner ℂ ((N⁻¹ : ℂ) • M (Kr x)) (M (x : Hilbert)) :=
        inner_add_left _ _ _
      _ = inner ℂ (M (x : Hilbert)) (M (x : Hilbert)) +
            (N⁻¹ : ℂ) * inner ℂ (M (Kr x)) (J (Kr x)) := by
        rw [inner_smul_left, conj_inv_ofReal, hc]
  rw [hsplit, KFCausalShiftedForm.complex_inner_square (M (x : Hilbert)),
    yosida_resolvent_pairing_eq_root_norm_sq ε hε h N hN (Kr x),
    Complex.add_re, re_inv_ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have hpos : 0 ≤ N⁻¹ * ‖Kroot ⟨J (Kr x), radial_domain_le_root_domain ε hε h (J (Kr x))
      (KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN (Kr x))⟩‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hN.le) (sq_nonneg _)
  linarith

theorem radial_yosida_accretive (x : (Kr).domain) :
    0 ≤ (inner ℂ (Kr x) (M (x : Hilbert))).re :=
  (sq_nonneg _).trans (radial_yosida_lower ε hε h N hN x)

theorem radial_resolvent_re_eq_yosidaRoot_norm_sq (x : (Kr).domain) :
    (inner ℂ (Kr x) (J (x : Hilbert))).re = ‖Mroot (x : Hilbert)‖ ^ 2 := by
  rw [resolvent_selfAdjoint_pairing ε hε h N hN (Kr x) (x : Hilbert),
    ← radial_action_commute ε hε h N hN (x : Hilbert) (Kr x) ((Kr).mem_graph x),
    ← yosida_selfAdjoint_pairing ε hε h N hN (x : Hilbert) (x : Hilbert),
    ← yosidaRootAction_norm_sq_eq_inner ε hε h N hN (x : Hilbert)]

theorem radial_resolvent_accretive (x : (Kr).domain) :
    0 ≤ (inner ℂ (Kr x) (J (x : Hilbert))).re := by
  rw [radial_resolvent_re_eq_yosidaRoot_norm_sq ε hε h N hN x]
  exact sq_nonneg _

theorem radial_yosida_sq_lower (x : (Kr).domain) :
    ‖Mroot (M (x : Hilbert))‖ ^ 2 ≤ (inner ℂ (Kr x) (M (M (x : Hilbert)))).re := by
  have heq := radial_eq_yosida_add_scaled_yosida_radial ε hε h N hN x
  have hc := radial_action_commute ε hε h N hN (x : Hilbert) (Kr x) ((Kr).mem_graph x)
  have hsplit : inner ℂ (Kr x) (M (M (x : Hilbert))) =
      inner ℂ (M (x : Hilbert)) (M (M (x : Hilbert))) +
        (N⁻¹ : ℂ) * inner ℂ (M (M (Kr x))) (J (Kr x)) := by
    calc
      inner ℂ (Kr x) (M (M (x : Hilbert))) =
          inner ℂ (M (x : Hilbert) + (N⁻¹ : ℂ) • M (Kr x)) (M (M (x : Hilbert))) := by
        rw [← heq]
      _ = inner ℂ (M (x : Hilbert)) (M (M (x : Hilbert))) +
            inner ℂ ((N⁻¹ : ℂ) • M (Kr x)) (M (M (x : Hilbert))) :=
        inner_add_left _ _ _
      _ = inner ℂ (M (x : Hilbert)) (M (M (x : Hilbert))) +
            (N⁻¹ : ℂ) * inner ℂ (M (M (Kr x))) (J (Kr x)) := by
        rw [inner_smul_left, conj_inv_ofReal,
          yosida_selfAdjoint_pairing ε hε h N hN (M (Kr x)) (M (x : Hilbert)), hc]
  rw [hsplit, Complex.add_re, re_inv_ofReal_mul,
    ← yosidaRootAction_norm_sq_eq_inner ε hε h N hN (M (x : Hilbert))]
  have hpos : 0 ≤ N⁻¹ * (inner ℂ (M (M (Kr x))) (J (Kr x))).re :=
    mul_nonneg (inv_nonneg.mpr hN.le) (yosida_sq_resolvent_re_nonneg ε hε h N hN (Kr x))
  linarith

theorem radial_yosida_sq_accretive (x : (Kr).domain) :
    0 ≤ (inner ℂ (Kr x) (M (M (x : Hilbert)))).re :=
  (sq_nonneg _).trans (radial_yosida_sq_lower ε hε h N hN x)

theorem radial_resolvent_sq_re_eq_root_norm_sq (x : (Kr).domain) :
    (inner ℂ (Kr x) (J (J (x : Hilbert)))).re =
      ‖Kroot ⟨J (x : Hilbert), radial_domain_le_root_domain ε hε h (J (x : Hilbert))
        (KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN (x : Hilbert))⟩‖ ^ 2 := by
  rw [resolvent_selfAdjoint_pairing ε hε h N hN (Kr x) (J (x : Hilbert)),
    ← radial_action_commute ε hε h N hN (x : Hilbert) (Kr x) ((Kr).mem_graph x),
    yosida_resolvent_pairing_eq_root_norm_sq ε hε h N hN (x : Hilbert),
    Complex.ofReal_re]

theorem radial_resolvent_sq_accretive (x : (Kr).domain) :
    0 ≤ (inner ℂ (Kr x) (J (J (x : Hilbert)))).re := by
  rw [radial_resolvent_sq_re_eq_root_norm_sq ε hε h N hN x]
  exact sq_nonneg _

/-! ### 2. Full-Strip and Quarter-Strip Accretivity on Dom(G) -/

variable (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k

theorem growing_yosida_lower (x : (G).domain) :
    ‖M (x : Hilbert)‖ ^ 2 ≤ (inner ℂ (G x) (M (x : Hilbert))).re :=
  add_re_lower_of_eq
    (growingHamiltonian_eq_radial_add_potential ε hε h hb hh m g k x)
    (radial_yosida_lower ε hε h N hN ⟨(x : Hilbert), radial_domain ε hε h hh hb m g k x⟩)
    (potential_yosida_accretive ε hε h N hN hb hh m g k
      ⟨(x : Hilbert), growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
        (x : Hilbert) x.property⟩)

theorem growing_yosida_accretive (x : (G).domain) :
    0 ≤ (inner ℂ (G x) (M (x : Hilbert))).re :=
  (sq_nonneg _).trans (growing_yosida_lower ε hε h N hN hb hh m g k x)

theorem growing_yosidaRoot_pairing_eq (x : (G).domain) :
    inner ℂ (Mroot (G x)) (Mroot (x : Hilbert)) =
      inner ℂ (G x) (M (x : Hilbert)) :=
  yosidaRootAction_sq_inner ε hε h N hN (G x) (x : Hilbert)

theorem growing_yosidaRoot_lower (x : (G).domain) :
    ‖M (x : Hilbert)‖ ^ 2 ≤ (inner ℂ (Mroot (G x)) (Mroot (x : Hilbert))).re := by
  rw [growing_yosidaRoot_pairing_eq ε hε h N hN hb hh m g k x]
  exact growing_yosida_lower ε hε h N hN hb hh m g k x

theorem growing_yosidaRoot_accretive (x : (G).domain) :
    0 ≤ (inner ℂ (Mroot (G x)) (Mroot (x : Hilbert))).re := by
  rw [growing_yosidaRoot_pairing_eq ε hε h N hN hb hh m g k x]
  exact growing_yosida_accretive ε hε h N hN hb hh m g k x

theorem growing_resolvent_lower (x : (G).domain) :
    ‖Mroot (x : Hilbert)‖ ^ 2 ≤ (inner ℂ (G x) (J (x : Hilbert))).re :=
  add_re_lower_of_eq
    (growingHamiltonian_eq_radial_add_potential ε hε h hb hh m g k x)
    (radial_resolvent_re_eq_yosidaRoot_norm_sq ε hε h N hN
      ⟨(x : Hilbert), radial_domain ε hε h hh hb m g k x⟩).symm.le
    (potential_resolvent_accretive ε hε h N hN hb hh m g k
      ⟨(x : Hilbert), growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb hh m g k
        (x : Hilbert) x.property⟩)

theorem growing_resolvent_accretive (x : (G).domain) :
    0 ≤ (inner ℂ (G x) (J (x : Hilbert))).re :=
  (sq_nonneg _).trans (growing_resolvent_lower ε hε h N hN hb hh m g k x)

theorem growing_yosida_sq_lower (hq : |h| ≤ Real.pi * ε / 4)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k).domain) :
    ‖Mroot (M (x : Hilbert))‖ ^ 2 ≤
      (inner ℂ
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian
          ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k x)
        (M (M (x : Hilbert)))).re :=
  let hb' := quarter_le_third ε hε h hq
  add_re_lower_of_eq
    (growingHamiltonian_eq_radial_add_potential ε hε h hb' hh m g k x)
    (radial_yosida_sq_lower ε hε h N hN ⟨(x : Hilbert), radial_domain ε hε h hh hb' m g k x⟩)
    (potential_yosida_sq_accretive ε hε h N hN hb' hh m g k hq
      ⟨(x : Hilbert), growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb' hh m g k
        (x : Hilbert) x.property⟩)

theorem growing_yosida_sq_accretive (hq : |h| ≤ Real.pi * ε / 4)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k).domain) :
    0 ≤ (inner ℂ
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian
        ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k x)
      (M (M (x : Hilbert)))).re :=
  (sq_nonneg _).trans (growing_yosida_sq_lower ε hε h N hN hh m g k hq x)

theorem growing_resolvent_sq_lower (hq : |h| ≤ Real.pi * ε / 4)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k).domain) :
    ‖Kroot ⟨J (x : Hilbert), radial_domain_le_root_domain ε hε h (J (x : Hilbert))
      (KFCausalClockFloorRadialResolventRegularizer.radial_domain ε hε h N hN (x : Hilbert))⟩‖ ^ 2 ≤
      (inner ℂ
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian
          ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k x)
        (J (J (x : Hilbert)))).re :=
  let hb' := quarter_le_third ε hε h hq
  add_re_lower_of_eq
    (growingHamiltonian_eq_radial_add_potential ε hε h hb' hh m g k x)
    (radial_resolvent_sq_re_eq_root_norm_sq ε hε h N hN
      ⟨(x : Hilbert), radial_domain ε hε h hh hb' m g k x⟩).symm.le
    (potential_resolvent_sq_accretive ε hε h N hN hb' hh m g k hq
      ⟨(x : Hilbert), growingHamiltonian_in_potentialHamiltonian_domain ε hε h hb' hh m g k
        (x : Hilbert) x.property⟩)

theorem growing_resolvent_sq_accretive (hq : |h| ≤ Real.pi * ε / 4)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k).domain) :
    0 ≤ (inner ℂ
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian
        ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k x)
      (J (J (x : Hilbert)))).re :=
  (sq_nonneg _).trans (growing_resolvent_sq_lower ε hε h N hN hh m g k hq x)

theorem growing_yosida_sq_accretive_sixth_strip (hbn : |h| ≤ Real.pi * ε / 6)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh
      (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
      m g k).domain) :
    0 ≤ (inner ℂ
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian
        ε hε h hh
        (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
        m g k x)
      (M (M (x : Hilbert)))).re :=
  growing_yosida_sq_accretive ε hε h N hN hh m g k (sixth_le_quarter ε hε h hbn) x

theorem growing_resolvent_sq_accretive_sixth_strip (hbn : |h| ≤ Real.pi * ε / 6)
    (x : (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh
      (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
      m g k).domain) :
    0 ≤ (inner ℂ
      (KFCausalClockFloorGrowingHamiltonian.hamiltonian
        ε hε h hh
        (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
        m g k x)
      (J (J (x : Hilbert)))).re :=
  growing_resolvent_sq_accretive ε hε h N hN hh m g k (sixth_le_quarter ε hε h hbn) x

#print axioms yosida_selfAdjoint_pairing
#print axioms resolvent_selfAdjoint_pairing
#print axioms resolvent_add_scaled_yosida
#print axioms radial_eq_yosida_add_scaled_yosida_radial
#print axioms yosida_resolvent_pairing_eq_root_norm_sq
#print axioms yosida_resolvent_re_nonneg
#print axioms yosidaRoot_comm_yosida
#print axioms yosidaRoot_comm_resolvent
#print axioms yosida_sq_resolvent_pairing_eq
#print axioms yosida_sq_resolvent_re_nonneg
#print axioms radial_yosida_lower
#print axioms radial_yosida_accretive
#print axioms radial_resolvent_re_eq_yosidaRoot_norm_sq
#print axioms radial_resolvent_accretive
#print axioms radial_yosida_sq_lower
#print axioms radial_yosida_sq_accretive
#print axioms radial_resolvent_sq_re_eq_root_norm_sq
#print axioms radial_resolvent_sq_accretive
#print axioms growing_yosida_lower
#print axioms growing_yosida_accretive
#print axioms growing_yosidaRoot_pairing_eq
#print axioms growing_yosidaRoot_lower
#print axioms growing_yosidaRoot_accretive
#print axioms growing_resolvent_lower
#print axioms growing_resolvent_accretive
#print axioms growing_yosida_sq_lower
#print axioms growing_yosida_sq_accretive
#print axioms growing_resolvent_sq_lower
#print axioms growing_resolvent_sq_accretive
#print axioms growing_yosida_sq_accretive_sixth_strip
#print axioms growing_resolvent_sq_accretive_sixth_strip
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialYosidaAccretivity
