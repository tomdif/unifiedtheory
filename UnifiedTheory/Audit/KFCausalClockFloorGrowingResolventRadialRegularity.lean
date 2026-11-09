/- Unconditional full-strip (`|h| ≤ π * ε / 3`) and quarter-strip (`|h| ≤ π * ε / 4`
and `|h| ≤ π * ε / 6`) radial-Yosida, radial square-root (`K_root`), and maximal
radial (`K_rad`) regularity of the positive growing Hamiltonian resolvent
`R_G(a) = (G + a)⁻¹` (`a > 0`):
1. On the full strip `|h| ≤ π * ε / 3`:
   - `‖M_N (R_G(a) f)‖² + a * ‖M_N^(1/2) (R_G(a) f)‖² ≤ Re ⟨M_N^(1/2) f, M_N^(1/2) (R_G(a) f)⟩`
   - `‖M_N^(1/2) (R_G(a) f)‖ ≤ a⁻¹ * ‖M_N^(1/2) f‖`
   - `‖M_N (R_G(a) f)‖ ≤ a^(-1/2) * ‖M_N^(1/2) f‖`
   - For every `f ∈ Dom(K_root)`:
     `‖K_root (R_G(a) f)‖ ≤ a⁻¹ * ‖K_root f‖` and
     `‖K_rad (R_G(a) f)‖ ≤ min ‖f‖ (a^(-1/2) * ‖K_root f‖)`.
2. On the quarter-strip `|h| ≤ π * ε / 4` (and `|h| ≤ π * ε / 6`):
   - `‖M_N (R_G(a) f)‖ ≤ a⁻¹ * ‖M_N f‖` and `‖J_N (R_G(a) f)‖ ≤ a⁻¹ * ‖J_N f‖`
   - For every `f ∈ Dom(K_rad)`:
     `‖K_rad (R_G(a) f)‖ ≤ min ‖f‖ (a⁻¹ * ‖K_rad f‖)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialYosidaAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingComponentResolventBounds
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRootRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventRadialRegularity
noncomputable section
open scoped InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator norm_of_uniform_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator)
open KFCausalClockFloorRadialResolventRegularizer (action)
open KFCausalClockFloorRadialResolventGrowingDomain (radial_domain_le_root_domain)
open KFCausalClockFloorRadialYosidaQuarterStripSector (quarter_le_third sixth_le_quarter)
open KFCausalClockFloorPotentialResolventRadialRegularity
  (yosida_norm_le_radial_of_domain)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (yosidaRootAction yosidaRootAction_selfAdjoint_pairing
    yosidaRootAction_sq_eq_yosida yosidaRootAction_norm_le_rootOperator
    root_norm_of_uniform_bound)
open KFCausalClockFloorGrowingRadialYosidaAccretivity
  (yosida_selfAdjoint_pairing resolvent_selfAdjoint_pairing
    growing_yosida_lower growing_yosida_accretive
    growing_yosida_sq_accretive growing_resolvent_sq_accretive)
open KFCausalClockFloorGrowingComponentResolventBounds
  (resolventPoint resolvent_mem_radial_domain resolvent_radial_norm_le)
open KFCausalPositiveResolventBounds (point point_value)

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

private theorem output_bound_of_resolvent_bound
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S : Hilbert →L[ℂ] Hilbert) (f : Hilbert)
    (hbnd : ‖S (R_a f)‖ ≤ a⁻¹ * ‖S f‖) :
    ‖S (T (point T R_a a hr f))‖ ≤ 2 * ‖S f‖ := by
  have hv : T (point T R_a a hr f) = f - a • R_a f := point_value T R_a a hr f
  rw [hv, ← Complex.coe_smul, map_sub, map_smul]
  have h1 : ‖S f - (a : ℂ) • S (R_a f)‖ ≤ ‖S f‖ + ‖(a : ℂ) • S (R_a f)‖ :=
    norm_sub_le _ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at h1
  have h2 : a * ‖S (R_a f)‖ ≤ ‖S f‖ := by
    calc
      a * ‖S (R_a f)‖ ≤ a * (a⁻¹ * ‖S f‖) := mul_le_mul_of_nonneg_left hbnd ha.le
      _ = (a * a⁻¹) * ‖S f‖ := by ring
      _ = ‖S f‖ := by rw [mul_inv_cancel₀ ha.ne', one_mul]
  linarith

private theorem lower_add_scaled_sq_le_inner
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S S2 : Hilbert →L[ℂ] Hilbert) (L : Hilbert → ℝ)
    (hS_symm : ∀ u v : Hilbert, inner ℂ u (S v) = inner ℂ (S u) v)
    (hS2 : ∀ u : Hilbert, S (S u) = S2 u)
    (hlow : ∀ x : T.domain, L (x : Hilbert) ≤ (inner ℂ (T x) (S2 (x : Hilbert))).re)
    (f : Hilbert) :
    L (R_a f) + a * ‖S (R_a f)‖ ^ 2 ≤ (inner ℂ (S f) (S (R_a f))).re := by
  have hp := hlow (point T R_a a hr f)
  change L (R_a f) ≤ (inner ℂ (T (point T R_a a hr f)) (S2 (R_a f))).re at hp
  rw [← hS2 (R_a f), point_value, inner_sub_left, inner_smul_left_eq_smul,
    hS_symm f (S (R_a f)), hS_symm (R_a f) (S (R_a f)),
    KFCausalShiftedForm.complex_inner_square] at hp
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  linarith

private theorem bound_of_sq_accretive_eq
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S S2 : Hilbert →L[ℂ] Hilbert)
    (hS_symm : ∀ u v : Hilbert, inner ℂ u (S v) = inner ℂ (S u) v)
    (hS2 : ∀ u : Hilbert, S (S u) = S2 u)
    (hS_acc : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (S2 (x : Hilbert))).re)
    (f : Hilbert) :
    ‖S (R_a f)‖ ≤ a⁻¹ * ‖S f‖ :=
  bound_of_sq_accretive T R_a a ha hr S hS_symm
    (fun x => by rw [hS2 (x : Hilbert)]; exact hS_acc x) f

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "J" => action ε hε h N hN
local notation "Mroot" => yosidaRootAction ε hε h N hN
local notation "Kr" => operator ε hε h
local notation "Kroot" => rootOperator ε hε h
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k

/-! ### 1. Full-Strip (`|h| ≤ π * ε / 3`) Radial Square-Root and Parabolic Smoothing Bounds -/

theorem growing_resolvent_yosida_add_yosidaRoot_sq_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (RG a f)‖ ^ 2 + a * ‖Mroot (RG a f)‖ ^ 2 ≤
      (inner ℂ (Mroot f) (Mroot (RG a f))).re :=
  lower_add_scaled_sq_le_inner G (RG a) a
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha)
    Mroot M (fun u => ‖M u‖ ^ 2)
    (fun u v => (yosidaRootAction_selfAdjoint_pairing ε hε h N hN u v).symm)
    (yosidaRootAction_sq_eq_yosida ε hε h N hN)
    (growing_yosida_lower ε hε h N hN hb hh m g k) f

theorem growing_resolvent_yosidaRoot_inner_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * ‖Mroot (RG a f)‖ ^ 2 ≤
      (inner ℂ (Mroot f) (Mroot (RG a f))).re := by
  have h1 := growing_resolvent_yosida_add_yosidaRoot_sq_le ε hε h N hN hb hh m g k a ha f
  have h2 : 0 ≤ ‖M (RG a f)‖ ^ 2 := sq_nonneg _
  linarith

theorem growing_resolvent_yosidaRoot_norm_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Mroot (RG a f)‖ ≤ a⁻¹ * ‖Mroot f‖ :=
  bound_of_sq_accretive_eq G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) Mroot M
    (fun u v => (yosidaRootAction_selfAdjoint_pairing ε hε h N hN u v).symm)
    (yosidaRootAction_sq_eq_yosida ε hε h N hN)
    (growing_yosida_accretive ε hε h N hN hb hh m g k) f

theorem growing_resolvent_output_yosidaRoot_norm_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Mroot (G (resolventPoint ε hε h hh hb m g k a ha f))‖ ≤
      2 * ‖Mroot f‖ :=
  output_bound_of_resolvent_bound G (RG a) a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k a ha) Mroot f
    (growing_resolvent_yosidaRoot_norm_le ε hε h N hN hb hh m g k a ha f)

theorem growing_resolvent_yosida_add_yosidaRoot_sq_le_yosidaRoot
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (RG a f)‖ ^ 2 + a * ‖Mroot (RG a f)‖ ^ 2 ≤ a⁻¹ * ‖Mroot f‖ ^ 2 := by
  have h1 := growing_resolvent_yosida_add_yosidaRoot_sq_le ε hε h N hN hb hh m g k a ha f
  have hcs : (inner ℂ (Mroot f) (Mroot (RG a f))).re ≤
      ‖Mroot f‖ * ‖Mroot (RG a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (Mroot f) (Mroot (RG a f))
  have hbnd := growing_resolvent_yosidaRoot_norm_le ε hε h N hN hb hh m g k a ha f
  have hmul : ‖Mroot f‖ * ‖Mroot (RG a f)‖ ≤ ‖Mroot f‖ * (a⁻¹ * ‖Mroot f‖) :=
    mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
  linarith [show ‖Mroot f‖ * (a⁻¹ * ‖Mroot f‖) = a⁻¹ * ‖Mroot f‖ ^ 2 by ring]

theorem growing_resolvent_yosida_norm_le_yosidaRoot
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (RG a f)‖ ≤ Real.sqrt (a⁻¹) * ‖Mroot f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  have h1 := growing_resolvent_yosida_add_yosidaRoot_sq_le_yosidaRoot
    ε hε h N hN hb hh m g k a ha f
  have h2 : 0 ≤ a * ‖Mroot (RG a f)‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem growing_resolvent_mem_radialRoot_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (Kroot).domain :=
  radial_domain_le_root_domain ε hε h (RG a f)
    (resolvent_mem_radial_domain ε hε h hh hb m g k a ha f)

theorem growing_resolvent_yosidaRoot_norm_le_rootOperator
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Mroot (RG a f)‖ ≤ a⁻¹ * ‖Kroot ⟨f, hf⟩‖ :=
  (growing_resolvent_yosidaRoot_norm_le ε hε h N hN hb hh m g k a ha f).trans
    (mul_le_mul_of_nonneg_left
      (yosidaRootAction_norm_le_rootOperator ε hε h N hN f hf)
      (inv_nonneg.mpr ha.le))

theorem growing_resolvent_radialRoot_norm_le_of_rootDomain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kroot ⟨RG a f,
      growing_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f⟩‖ ≤
      a⁻¹ * ‖Kroot ⟨f, hf⟩‖ :=
  root_norm_of_uniform_bound ε hε h (RG a f) (a⁻¹ * ‖Kroot ⟨f, hf⟩‖)
    (fun n => growing_resolvent_yosidaRoot_norm_le_rootOperator
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k a ha f hf)

theorem growing_resolvent_yosida_norm_le_rootOperator
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖M (RG a f)‖ ≤ Real.sqrt (a⁻¹) * ‖Kroot ⟨f, hf⟩‖ :=
  (growing_resolvent_yosida_norm_le_yosidaRoot ε hε h N hN hb hh m g k a ha f).trans
    (mul_le_mul_of_nonneg_left
      (yosidaRootAction_norm_le_rootOperator ε hε h N hN f hf)
      (Real.sqrt_nonneg _))

theorem growing_resolvent_radial_norm_le_of_rootDomain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kr ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      Real.sqrt (a⁻¹) * ‖Kroot ⟨f, hf⟩‖ :=
  norm_of_uniform_bound ε hε h (RG a f) (Real.sqrt (a⁻¹) * ‖Kroot ⟨f, hf⟩‖)
    (fun n => growing_resolvent_yosida_norm_le_rootOperator
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k a ha f hf)

theorem growing_resolvent_radial_norm_le_min_of_rootDomain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kr ⟨RG a f, resolvent_mem_radial_domain ε hε h hh hb m g k a ha f⟩‖ ≤
      min ‖f‖ (Real.sqrt (a⁻¹) * ‖Kroot ⟨f, hf⟩‖) :=
  le_min (resolvent_radial_norm_le ε hε h hh hb m g k a ha f)
    (growing_resolvent_radial_norm_le_of_rootDomain ε hε h hb hh m g k a ha f hf)

/-! ### 2. Quarter-Strip (`|h| ≤ π * ε / 4` and `|h| ≤ π * ε / 6`) Maximal Radial Contraction -/

theorem growing_resolvent_yosida_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f)‖ ≤
      a⁻¹ * ‖M f‖ :=
  let hb' := quarter_le_third ε hε h hq
  let hw' := wide_bound ε hε h hb'
  bound_of_sq_accretive
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw' m g k)
    (KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw' m g k a)
    a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw' m g k a ha)
    M
    (yosida_selfAdjoint_pairing ε hε h N hN)
    (growing_yosida_sq_accretive ε hε h N hN hh m g k hq) f

theorem growing_resolvent_regularizer_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖J (KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f)‖ ≤
      a⁻¹ * ‖J f‖ :=
  let hb' := quarter_le_third ε hε h hq
  let hw' := wide_bound ε hε h hb'
  bound_of_sq_accretive
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw' m g k)
    (KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw' m g k a)
    a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw' m g k a ha)
    J
    (resolvent_selfAdjoint_pairing ε hε h N hN)
    (growing_resolvent_sq_accretive ε hε h N hN hh m g k hq) f

theorem growing_resolvent_output_yosida_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k
      (resolventPoint ε hε h hh (quarter_le_third ε hε h hq) m g k a ha f))‖ ≤
      2 * ‖M f‖ :=
  let hb' := quarter_le_third ε hε h hq
  let hw' := wide_bound ε hε h hb'
  output_bound_of_resolvent_bound
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw' m g k)
    (KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw' m g k a)
    a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw' m g k a ha)
    M f
    (growing_resolvent_yosida_norm_le ε hε h N hN hh m g k hq a ha f)

theorem growing_resolvent_output_regularizer_norm_le (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖J (KFCausalClockFloorGrowingHamiltonian.hamiltonian
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k
      (resolventPoint ε hε h hh (quarter_le_third ε hε h hq) m g k a ha f))‖ ≤
      2 * ‖J f‖ :=
  let hb' := quarter_le_third ε hε h hq
  let hw' := wide_bound ε hε h hb'
  output_bound_of_resolvent_bound
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw' m g k)
    (KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw' m g k a)
    a ha
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw' m g k a ha)
    J f
    (growing_resolvent_regularizer_norm_le ε hε h N hN hh m g k hq a ha f)

theorem growing_resolvent_yosida_norm_le_radial (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖M (KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f)‖ ≤
      a⁻¹ * ‖Kr ⟨f, hf⟩‖ :=
  (growing_resolvent_yosida_norm_le ε hε h N hN hh m g k hq a ha f).trans
    (mul_le_mul_of_nonneg_left
      (yosida_norm_le_radial_of_domain ε hε h N hN f hf)
      (inv_nonneg.mpr ha.le))

theorem growing_resolvent_radial_norm_le_of_radialDomain (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖Kr ⟨KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f,
      resolvent_mem_radial_domain ε hε h hh (quarter_le_third ε hε h hq) m g k a ha f⟩‖ ≤
      a⁻¹ * ‖Kr ⟨f, hf⟩‖ :=
  norm_of_uniform_bound ε hε h
    (KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f)
    (a⁻¹ * ‖Kr ⟨f, hf⟩‖)
    (fun n => growing_resolvent_yosida_norm_le_radial
      ε hε h ((n : ℝ) + 1) (by positivity) hh m g k hq a ha f hf)

theorem growing_resolvent_radial_norm_le_min_of_radialDomain (hq : |h| ≤ Real.pi * ε / 4)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖Kr ⟨KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh (wide_bound ε hε h (quarter_le_third ε hε h hq)) m g k a f,
      resolvent_mem_radial_domain ε hε h hh (quarter_le_third ε hε h hq) m g k a ha f⟩‖ ≤
      min ‖f‖ (a⁻¹ * ‖Kr ⟨f, hf⟩‖) :=
  le_min
    (resolvent_radial_norm_le ε hε h hh (quarter_le_third ε hε h hq) m g k a ha f)
    (growing_resolvent_radial_norm_le_of_radialDomain ε hε h hh m g k hq a ha f hf)

theorem growing_resolvent_yosida_norm_le_sixth_strip (hbn : |h| ≤ Real.pi * ε / 6)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖M (KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh
      (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
      m g k a f)‖ ≤
      a⁻¹ * ‖M f‖ :=
  growing_resolvent_yosida_norm_le ε hε h N hN hh m g k
    (sixth_le_quarter ε hε h hbn) a ha f

theorem growing_resolvent_radial_norm_le_sixth_strip (hbn : |h| ≤ Real.pi * ε / 6)
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kr).domain) :
    ‖Kr ⟨KFCausalClockFloorGrowingYosida.resolvent
      ε hε h hh
      (wide_bound ε hε h (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)))
      m g k a f,
      resolvent_mem_radial_domain ε hε h hh
        (quarter_le_third ε hε h (sixth_le_quarter ε hε h hbn)) m g k a ha f⟩‖ ≤
      a⁻¹ * ‖Kr ⟨f, hf⟩‖ :=
  growing_resolvent_radial_norm_le_of_radialDomain ε hε h hh m g k
    (sixth_le_quarter ε hε h hbn) a ha f hf

#print axioms growing_resolvent_yosida_add_yosidaRoot_sq_le
#print axioms growing_resolvent_yosidaRoot_inner_le
#print axioms growing_resolvent_yosidaRoot_norm_le
#print axioms growing_resolvent_output_yosidaRoot_norm_le
#print axioms growing_resolvent_yosida_add_yosidaRoot_sq_le_yosidaRoot
#print axioms growing_resolvent_yosida_norm_le_yosidaRoot
#print axioms growing_resolvent_mem_radialRoot_domain
#print axioms growing_resolvent_yosidaRoot_norm_le_rootOperator
#print axioms growing_resolvent_radialRoot_norm_le_of_rootDomain
#print axioms growing_resolvent_yosida_norm_le_rootOperator
#print axioms growing_resolvent_radial_norm_le_of_rootDomain
#print axioms growing_resolvent_radial_norm_le_min_of_rootDomain
#print axioms growing_resolvent_yosida_norm_le
#print axioms growing_resolvent_regularizer_norm_le
#print axioms growing_resolvent_output_yosida_norm_le
#print axioms growing_resolvent_output_regularizer_norm_le
#print axioms growing_resolvent_yosida_norm_le_radial
#print axioms growing_resolvent_radial_norm_le_of_radialDomain
#print axioms growing_resolvent_radial_norm_le_min_of_radialDomain
#print axioms growing_resolvent_yosida_norm_le_sixth_strip
#print axioms growing_resolvent_radial_norm_le_sixth_strip
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingResolventRadialRegularity
