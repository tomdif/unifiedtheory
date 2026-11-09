/- Unconditional radial and growing-Hamiltonian regularity of the positive
potential resolvent `R_P(a) = (P + a)⁻¹` (`a > 0`) on the quarter-strip
`|h| ≤ π * ε / 4` (including `|h| ≤ π * ε / 6`):
- For all `f : Hilbert`, `‖M_N (R_P(a) f)‖ ≤ a⁻¹ * ‖M_N f‖` and
  `‖J_N (R_P(a) f)‖ ≤ a⁻¹ * ‖J_N f‖`.
- For all `f ∈ Dom(K_rad)`, `R_P(a) f ∈ Dom(K_rad)` with
  `‖K_rad (R_P(a) f)‖ ≤ a⁻¹ * ‖K_rad f‖`, and `R_P(a) f ∈ Dom(G)` with
  `‖G (R_P(a) f)‖ ≤ a⁻¹ * ‖K_rad f‖ + 2 * ‖f‖`. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialRadialYosidaAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockResolvent
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
noncomputable section
open MeasureTheory
open scoped InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaSymbol (symbol)
open KFCausalClockFloorRadialResolventRegularizer (multiplier action action_coe action_norm)
open KFCausalClockFloorRadialYosidaDomain
  (operator domain_of_uniform_bound norm_of_uniform_bound)
open KFCausalClockFloorRadialResolventOperator (yosida_eq_action_on_graph)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)
open KFCausalClockFloorRadialResolventGrowingDomain
  (root_yosida_pairing radial_domain_le_root_domain
    potentialHamiltonian_and_radial_to_growingHamiltonian_graph
    growingHamiltonian_domain_iff)
open KFCausalClockFloorPotentialRadialYosidaAccretivity
  (potential_yosida_accretive potential_resolvent_accretive
    potential_yosida_sq_accretive potential_resolvent_sq_accretive)
open KFCausalClockFloorRadialYosidaQuarterStripSector (sixth_le_quarter)
open KFCausalClockFloorPotentialClockResolvent (resolvent resolves)
open KFCausalPositiveResolventBounds (point point_value resolvent_apply_norm_bound)

private theorem real_multiplier_symm (m : KFCausalEuclideanProductCoordinates.Joint 2 4 → ℝ)
    (A : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f : Hilbert, chargeCoordinates (A f) =ᵐ[volume]
      fun x => (m x : ℂ) * (chargeCoordinates f) x)
    (f g : Hilbert) :
    inner ℂ f (A g) = inner ℂ (A f) g := by
  rw [← chargeCoordinates.inner_map_map f (A g),
    ← chargeCoordinates.inner_map_map (A f) g,
    L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA f, hA g] with x hf hg
  change inner ℂ ((chargeCoordinates f) x) ((chargeCoordinates (A g)) x) =
    inner ℂ ((chargeCoordinates (A f)) x) ((chargeCoordinates g) x)
  rw [hf, hg]
  change inner ℂ ((chargeCoordinates f) x) ((m x : ℂ) • (chargeCoordinates g) x) =
    inner ℂ ((m x : ℂ) • (chargeCoordinates f) x) ((chargeCoordinates g) x)
  rw [inner_smul_right, inner_smul_left, Complex.conj_ofReal]

theorem yosidaAction_selfAdjoint_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f g : Hilbert) :
    inner ℂ f (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN g) =
      inner ℂ (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f) g :=
  real_multiplier_symm (symbol ε h N)
    (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN)
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN) f g

theorem resolventAction_selfAdjoint_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f g : Hilbert) :
    inner ℂ f (action ε hε h N hN g) =
      inner ℂ (action ε hε h N hN f) g :=
  real_multiplier_symm (multiplier ε h N)
    (action ε hε h N hN)
    (action_coe ε hε h N hN) f g

theorem yosida_norm_le_radial_of_domain (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f : Hilbert) (hf : f ∈ (operator ε hε h).domain) :
    ‖KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f‖ ≤
      ‖operator ε hε h ⟨f, hf⟩‖ := by
  have heq := yosida_eq_action_on_graph ε hε h N hN f
    (operator ε hε h ⟨f, hf⟩) ((operator ε hε h).mem_graph ⟨f, hf⟩)
  rw [heq]
  exact action_norm ε hε h N hN (operator ε hε h ⟨f, hf⟩)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "J" => action ε hε h N hN
local notation "Kr" => operator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "R" => resolvent ε hε h hh hw m g k

theorem potential_resolvent_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖R a f‖ ≤ a⁻¹ * ‖f‖ :=
  resolvent_apply_norm_bound P (R a) a ha
    (resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) f

theorem potential_resolvent_residual_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖f - a • R a f‖ ≤ 2 * ‖f‖ := by
  have hr := potential_resolvent_norm_le ε hε h hb hh m g k a ha f
  have h1 : ‖f - a • R a f‖ ≤ ‖f‖ + ‖a • R a f‖ := norm_sub_le f (a • R a f)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h1
  have h2 : a * ‖R a f‖ ≤ ‖f‖ := by
    calc
      a * ‖R a f‖ ≤ a * (a⁻¹ * ‖f‖) := mul_le_mul_of_nonneg_left hr ha.le
      _ = (a * a⁻¹) * ‖f‖ := by ring
      _ = ‖f‖ := by rw [mul_inv_cancel₀ ha.ne', one_mul]
  linarith

private theorem resolvent_inner_le_of_accretive
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S : Hilbert →L[ℂ] Hilbert)
    (hS_acc : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (S (x : Hilbert))).re)
    (f : Hilbert) :
    a * (inner ℂ (R_a f) (S (R_a f))).re ≤ (inner ℂ f (S (R_a f))).re := by
  have hp := hS_acc (point T R_a a hr f)
  change 0 ≤ (inner ℂ (T (point T R_a a hr f)) (S (R_a f))).re at hp
  rw [point_value, inner_sub_left, inner_smul_left_eq_smul] at hp
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  linarith

private theorem bound_of_sq_accretive
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S : Hilbert →L[ℂ] Hilbert)
    (hS_symm : ∀ u v : Hilbert, inner ℂ u (S v) = inner ℂ (S u) v)
    (hS_acc : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (S (S (x : Hilbert)))).re)
    (f : Hilbert) :
    ‖S (R_a f)‖ ≤ a⁻¹ * ‖S f‖ := by
  have hp := hS_acc (point T R_a a hr f)
  change 0 ≤ (inner ℂ (T (point T R_a a hr f)) (S (S (R_a f)))).re at hp
  rw [point_value, inner_sub_left, inner_smul_left_eq_smul,
    hS_symm f (S (R_a f)), hS_symm (R_a f) (S (R_a f)),
    KFCausalShiftedForm.complex_inner_square] at hp
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  have hl : a * ‖S (R_a f)‖ ^ 2 ≤ (inner ℂ (S f) (S (R_a f))).re := by
    nlinarith
  by_cases hz : S (R_a f) = 0
  · rw [hz, norm_zero]
    positivity
  have hn : 0 < ‖S (R_a f)‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hi : (inner ℂ (S f) (S (R_a f))).re ≤ ‖S f‖ * ‖S (R_a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (S f) (S (R_a f))
  nlinarith

theorem resolvent_yosida_inner_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * (inner ℂ (R a f) (M (R a f))).re ≤ (inner ℂ f (M (R a f))).re :=
  resolvent_inner_le_of_accretive P (R a) a
    (resolves ε hε h hh hw m g k a ha) M
    (potential_yosida_accretive ε hε h N hN hb hh m g k) f

theorem resolvent_regularizer_inner_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * (inner ℂ (R a f) (J (R a f))).re ≤ (inner ℂ f (J (R a f))).re :=
  resolvent_inner_le_of_accretive P (R a) a
    (resolves ε hε h hh hw m g k a ha) J
    (potential_resolvent_accretive ε hε h N hN hb hh m g k) f

theorem yosida_resolvent_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (R a f)‖ ≤ a⁻¹ * ‖M f‖ :=
  bound_of_sq_accretive P (R a) a ha
    (resolves ε hε h hh hw m g k a ha) M
    (yosidaAction_selfAdjoint_pairing ε hε h N hN)
    (potential_yosida_sq_accretive ε hε h N hN hb hh m g k hq) f

theorem regularizer_resolvent_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖J (R a f)‖ ≤ a⁻¹ * ‖J f‖ :=
  bound_of_sq_accretive P (R a) a ha
    (resolves ε hε h hh hw m g k a ha) J
    (resolventAction_selfAdjoint_pairing ε hε h N hN)
    (potential_resolvent_sq_accretive ε hε h N hN hb hh m g k hq) f

theorem yosida_resolvent_norm_le_radial (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖M (R a f)‖ ≤ a⁻¹ * ‖Kr ⟨f, hf⟩‖ :=
  (yosida_resolvent_norm_le ε hε h N hN hb hh m g k hq a ha f).trans
    (mul_le_mul_of_nonneg_left
      (yosida_norm_le_radial_of_domain ε hε h N hN f hf)
      (inv_nonneg.mpr ha.le))

theorem resolvent_radial_domain (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    R a f ∈ (Kr).domain :=
  domain_of_uniform_bound ε hε h (R a f) (a⁻¹ * ‖Kr ⟨f, hf⟩‖)
    (fun n => yosida_resolvent_norm_le_radial ε hε h ((n : ℝ) + 1) (by positivity)
      hb hh m g k hq a ha f hf)

theorem resolvent_radial_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖Kr ⟨R a f, resolvent_radial_domain ε hε h hb hh m g k hq a ha f hf⟩‖ ≤
      a⁻¹ * ‖Kr ⟨f, hf⟩‖ :=
  norm_of_uniform_bound ε hε h (R a f) (a⁻¹ * ‖Kr ⟨f, hf⟩‖)
    (fun n => yosida_resolvent_norm_le_radial ε hε h ((n : ℝ) + 1) (by positivity)
      hb hh m g k hq a ha f hf)

theorem resolvent_root_domain (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    R a f ∈ (Kroot).domain :=
  radial_domain_le_root_domain ε hε h (R a f)
    (resolvent_radial_domain ε hε h hb hh m g k hq a ha f hf)

theorem resolvent_root_yosida_inner_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    a * (inner ℂ (J (Kroot ⟨R a f, resolvent_root_domain ε hε h hb hh m g k hq a ha f hf⟩))
        (Kroot ⟨R a f, resolvent_root_domain ε hε h hb hh m g k hq a ha f hf⟩)).re ≤
      (inner ℂ (J (Kroot ⟨f, radial_domain_le_root_domain ε hε h f hf⟩))
        (Kroot ⟨R a f, resolvent_root_domain ε hε h hb hh m g k hq a ha f hf⟩)).re := by
  let hrf := radial_domain_le_root_domain ε hε h f hf
  let hrR := resolvent_root_domain ε hε h hb hh m g k hq a ha f hf
  have h1 := root_yosida_pairing ε hε h N hN (R a f) (R a f)
    (Kroot ⟨R a f, hrR⟩) (Kroot ⟨R a f, hrR⟩)
    ((Kroot).mem_graph ⟨R a f, hrR⟩) ((Kroot).mem_graph ⟨R a f, hrR⟩)
  have h2 := root_yosida_pairing ε hε h N hN f (R a f)
    (Kroot ⟨f, hrf⟩) (Kroot ⟨R a f, hrR⟩)
    ((Kroot).mem_graph ⟨f, hrf⟩) ((Kroot).mem_graph ⟨R a f, hrR⟩)
  rw [h1, h2, ← yosidaAction_selfAdjoint_pairing ε hε h N hN f (R a f),
    ← yosidaAction_selfAdjoint_pairing ε hε h N hN (R a f) (R a f)]
  exact resolvent_yosida_inner_le ε hε h N hN hb hh m g k a ha f

theorem resolvent_growing_domain (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    R a f ∈ (G).domain :=
  (growingHamiltonian_domain_iff ε hε h hb hh m g k (R a f)).mpr
    ⟨resolvent_radial_domain ε hε h hb hh m g k hq a ha f hf,
      (resolves ε hε h hh hw m g k a ha f).choose⟩

theorem resolvent_growing_eq (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    G ⟨R a f, resolvent_growing_domain ε hε h hb hh m g k hq a ha f hf⟩ =
      Kr ⟨R a f, resolvent_radial_domain ε hε h hb hh m g k hq a ha f hf⟩ +
        (f - a • R a f) := by
  let hkr := resolvent_radial_domain ε hε h hb hh m g k hq a ha f hf
  let hr := resolves ε hε h hh hw m g k a ha
  have hpg : (R a f, f - a • R a f) ∈ (P).graph := by
    have hm : (R a f, P (point P (R a) a hr f)) ∈ (P).graph :=
      (P).mem_graph (point P (R a) a hr f)
    rwa [point_value P (R a) a hr f] at hm
  have hgg := potentialHamiltonian_and_radial_to_growingHamiltonian_graph ε hε h hb hh m g k
    (R a f) (Kr ⟨R a f, hkr⟩) (f - a • R a f)
    ((Kr).mem_graph ⟨R a f, hkr⟩) hpg
  exact (G).mem_graph_snd_inj'
    ((G).mem_graph ⟨R a f, resolvent_growing_domain ε hε h hb hh m g k hq a ha f hf⟩)
    hgg rfl

theorem resolvent_growing_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖G ⟨R a f, resolvent_growing_domain ε hε h hb hh m g k hq a ha f hf⟩‖ ≤
      a⁻¹ * ‖Kr ⟨f, hf⟩‖ + 2 * ‖f‖ := by
  rw [resolvent_growing_eq ε hε h hb hh m g k hq a ha f hf]
  exact (norm_add_le _ _).trans (add_le_add
    (resolvent_radial_norm_le ε hε h hb hh m g k hq a ha f hf)
    (potential_resolvent_residual_norm_le ε hε h hb hh m g k a ha f))

theorem resolvent_radial_domain_sixth (hs : |h| ≤ Real.pi * ε / 6)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    R a f ∈ (Kr).domain :=
  resolvent_radial_domain ε hε h hb hh m g k (sixth_le_quarter ε hε h hs) a ha f hf

theorem resolvent_growing_domain_sixth (hs : |h| ≤ Real.pi * ε / 6)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    R a f ∈ (G).domain :=
  resolvent_growing_domain ε hε h hb hh m g k (sixth_le_quarter ε hε h hs) a ha f hf

#print axioms yosidaAction_selfAdjoint_pairing
#print axioms resolventAction_selfAdjoint_pairing
#print axioms yosida_norm_le_radial_of_domain
#print axioms potential_resolvent_norm_le
#print axioms potential_resolvent_residual_norm_le
#print axioms resolvent_yosida_inner_le
#print axioms resolvent_regularizer_inner_le
#print axioms yosida_resolvent_norm_le
#print axioms regularizer_resolvent_norm_le
#print axioms yosida_resolvent_norm_le_radial
#print axioms resolvent_radial_domain
#print axioms resolvent_radial_norm_le
#print axioms resolvent_root_domain
#print axioms resolvent_root_yosida_inner_le
#print axioms resolvent_growing_domain
#print axioms resolvent_growing_eq
#print axioms resolvent_growing_norm_le
#print axioms resolvent_radial_domain_sixth
#print axioms resolvent_growing_domain_sixth
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
