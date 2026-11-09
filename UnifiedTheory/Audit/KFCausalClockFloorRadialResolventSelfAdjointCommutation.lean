/- The radial Yosida symbol action and the radial resolvent regularizer are
bounded self-adjoint nonnegative multipliers in charge coordinates, commute
pairwise across all positive cutoffs, and satisfy the exact two-cutoff
resolvent difference identity. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventSelfAdjointCommutation
noncomputable section
open MeasureTheory
open scoped InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_nonnegative symbol symbol_nonnegative)
open KFCausalClockFloorRadialResolventRegularizer (multiplier multiplier_nonnegative action action_coe)

private theorem charge_real_multiplier_inner
    (w : Joint 2 4 → ℝ) (A : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f, chargeCoordinates (A f) =ᵐ[volume]
      fun x => (w x : ℂ) * chargeCoordinates f x)
    (f g : Hilbert) :
    inner ℂ (A f) g = inner ℂ f (A g) := by
  rw [← chargeCoordinates.inner_map_map (A f) g,
    ← chargeCoordinates.inner_map_map f (A g), L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA f, hA g] with x hf hg
  rw [hf, hg]
  change inner ℂ ((w x : ℂ) • chargeCoordinates f x) (chargeCoordinates g x) =
    inner ℂ (chargeCoordinates f x) ((w x : ℂ) • chargeCoordinates g x)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

private theorem charge_real_multiplier_re_nonneg
    (w : Joint 2 4 → ℝ) (hw : ∀ x, 0 ≤ w x) (A : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f, chargeCoordinates (A f) =ᵐ[volume]
      fun x => (w x : ℂ) * chargeCoordinates f x)
    (f : Hilbert) :
    0 ≤ (inner ℂ (A f) f).re := by
  rw [charge_real_multiplier_inner w A hA f f,
    ← chargeCoordinates.inner_map_map f (A f)]
  have he := integral_re
    (L2.integrable_inner (𝕜 := ℂ) (chargeCoordinates f) (chargeCoordinates (A f)))
  change (∫ x, (inner ℂ (chargeCoordinates f x) (chargeCoordinates (A f) x)).re ∂volume) =
    (∫ x, inner ℂ (chargeCoordinates f x) (chargeCoordinates (A f) x) ∂volume).re at he
  rw [L2.inner_def, ← he]
  apply integral_nonneg_of_ae
  filter_upwards [hA f] with x hx
  rw [hx]
  change 0 ≤ (inner ℂ (chargeCoordinates f x) ((w x : ℂ) • chargeCoordinates f x)).re
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((w x : ℂ) * ((‖chargeCoordinates f x‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (hw x) (sq_nonneg _)

private theorem charge_multiplier_commute
    (w₁ w₂ : Joint 2 4 → ℂ) (A B : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f, chargeCoordinates (A f) =ᵐ[volume]
      fun x => w₁ x * chargeCoordinates f x)
    (hB : ∀ f, chargeCoordinates (B f) =ᵐ[volume]
      fun x => w₂ x * chargeCoordinates f x)
    (f : Hilbert) :
    A (B f) = B (A f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [hA (B f), hB f, hB (A f), hA f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "J" => action ε hε h N hN

theorem yosida_selfAdjoint (f g : Hilbert) :
    inner ℂ (M f) g = inner ℂ f (M g) :=
  charge_real_multiplier_inner (symbol ε h N) M
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN) f g

theorem resolvent_selfAdjoint (f g : Hilbert) :
    inner ℂ (J f) g = inner ℂ f (J g) :=
  charge_real_multiplier_inner (multiplier ε h N) J
    (action_coe ε hε h N hN) f g

theorem yosida_inner_re_nonneg (f : Hilbert) :
    0 ≤ (inner ℂ (M f) f).re :=
  charge_real_multiplier_re_nonneg (symbol ε h N)
    (symbol_nonnegative ε hε h N hN) M
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN) f

theorem resolvent_inner_re_nonneg (f : Hilbert) :
    0 ≤ (inner ℂ (J f) f).re :=
  charge_real_multiplier_re_nonneg (multiplier ε h N)
    (multiplier_nonnegative ε hε h N hN) J
    (action_coe ε hε h N hN) f

theorem resolvent_commute (N' : ℝ) (hN' : 0 < N') (f : Hilbert) :
    J (action ε hε h N' hN' f) = action ε hε h N' hN' (J f) :=
  charge_multiplier_commute
    (fun x => (multiplier ε h N x : ℂ))
    (fun x => (multiplier ε h N' x : ℂ))
    J (action ε hε h N' hN')
    (action_coe ε hε h N hN)
    (action_coe ε hε h N' hN') f

theorem yosida_resolvent_commute (N' : ℝ) (hN' : 0 < N') (f : Hilbert) :
    M (action ε hε h N' hN' f) = action ε hε h N' hN' (M f) :=
  charge_multiplier_commute
    (fun x => (symbol ε h N x : ℂ))
    (fun x => (multiplier ε h N' x : ℂ))
    M (action ε hε h N' hN')
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN)
    (action_coe ε hε h N' hN') f

theorem yosida_commute (N' : ℝ) (hN' : 0 < N') (f : Hilbert) :
    M (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N' hN' f) =
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N' hN' (M f) :=
  charge_multiplier_commute
    (fun x => (symbol ε h N x : ℂ))
    (fun x => (symbol ε h N' x : ℂ))
    M (KFCausalClockFloorRadialYosidaSymbol.action ε hε h N' hN')
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN)
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N' hN') f

include hε hN in
theorem multiplier_sub_multiplier (N' : ℝ) (hN' : 0 < N') (x : Joint 2 4) :
    multiplier ε h N x - multiplier ε h N' x =
      (N'⁻¹ - N⁻¹) * (symbol ε h N x * multiplier ε h N' x) := by
  have hr := radial_nonnegative ε hε h x
  have hdN : N + radial ε h x ≠ 0 := (add_pos_of_pos_of_nonneg hN hr).ne'
  have hdN' : N' + radial ε h x ≠ 0 := (add_pos_of_pos_of_nonneg hN' hr).ne'
  have hNe : N ≠ 0 := hN.ne'
  have hN'e : N' ≠ 0 := hN'.ne'
  unfold multiplier symbol
  field_simp
  ring

theorem resolvent_sub_resolvent (N' : ℝ) (hN' : 0 < N') (f : Hilbert) :
    J f - action ε hε h N' hN' f =
      ((N'⁻¹ - N⁻¹ : ℝ) : ℂ) • M (action ε hε h N' hN' f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  let JN := J f
  let JN' := action ε hε h N' hN' f
  let MN := M JN'
  have hsub : chargeCoordinates (JN - JN') = chargeCoordinates JN - chargeCoordinates JN' :=
    map_sub chargeCoordinates JN JN'
  have hsmul : chargeCoordinates (((N'⁻¹ - N⁻¹ : ℝ) : ℂ) • MN) =
      ((N'⁻¹ - N⁻¹ : ℝ) : ℂ) • chargeCoordinates MN :=
    map_smul chargeCoordinates ((N'⁻¹ - N⁻¹ : ℝ) : ℂ) MN
  rw [hsub, hsmul]
  filter_upwards [Lp.coeFn_sub (chargeCoordinates JN) (chargeCoordinates JN'),
    action_coe ε hε h N hN f,
    action_coe ε hε h N' hN' f,
    Lp.coeFn_smul ((N'⁻¹ - N⁻¹ : ℝ) : ℂ) (chargeCoordinates MN),
    KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN JN']
    with x hs h1 h2 hsm h3
  rw [hs, hsm]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2, h3, h2]
  have hm := multiplier_sub_multiplier ε hε h N hN N' hN' x
  rw [← sub_mul, ← Complex.ofReal_sub, hm]
  push_cast
  ring

#print axioms yosida_selfAdjoint
#print axioms resolvent_selfAdjoint
#print axioms yosida_inner_re_nonneg
#print axioms resolvent_inner_re_nonneg
#print axioms resolvent_commute
#print axioms yosida_resolvent_commute
#print axioms yosida_commute
#print axioms multiplier_sub_multiplier
#print axioms resolvent_sub_resolvent
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventSelfAdjointCommutation
