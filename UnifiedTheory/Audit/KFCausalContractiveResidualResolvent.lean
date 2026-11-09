/- Positive resolvents constructed from a contractive residual. The inverse
exists by the norm-convergent Neumann series, with its sharp 1/b bound. -/
import UnifiedTheory.Audit.KFCausalInvariantRangeCore
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalContractiveResidualResolvent
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/- This lower bound is derived from contractivity, not assumed coercivity. -/
omit [CompleteSpace V] in
theorem lower_bound (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : b*‖x‖ ≤ ‖F x+(b:ℂ) • x‖ := by
  have he : ((1+b:ℝ):ℂ) • x = (F x+(b:ℂ) • x)+residual F x := by
    change ((1+b:ℝ):ℂ) • x = (F x+(b:ℂ) • x)+(x-F x)
    push_cast
    module
  have hn := norm_add_le (F x+(b:ℂ) • x) (residual F x)
  rw [← he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 1+b)] at hn
  linarith [hF x]

omit [CompleteSpace V] in
theorem scaled_residual_lt (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) : ‖(((1+b)⁻¹:ℝ):ℂ) • residual F‖ < 1 := by
  have hn : ‖residual F‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using hF)
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (1+b)⁻¹)]
  have hr : (1+b)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_lt (by simpa using hr)

def unit (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (b : ℝ) (hb : 0 < b) :
    (V →L[ℂ] V)ˣ := Units.oneSub ((((1+b)⁻¹:ℝ):ℂ) • residual F) (scaled_residual_lt F hF b hb)

def resolvent (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (b : ℝ) (hb : 0 < b) :
    V →L[ℂ] V := (((1+b)⁻¹:ℝ):ℂ) • (unit F hF b hb).inv

theorem equation (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) :
    F (resolvent F hF b hb x)+(b:ℂ) • resolvent F hF b hb x = x := by
  let r : ℂ := (((1+b)⁻¹:ℝ):ℂ)
  let y := (unit F hF b hb).inv x
  have he := congrArg (fun T : V →L[ℂ] V => T x) (unit F hF b hb).val_inv
  change y-r • (y-F y) = x at he
  have hr : (b:ℂ)*r = 1-r := by
    dsimp [r]
    push_cast
    have hn : (1+(b:ℂ)) ≠ 0 := by
      exact_mod_cast (show (1+b:ℝ) ≠ 0 from by linarith)
    field_simp [hn]
    ring
  change F (r • y)+(b:ℂ) • (r • y) = x
  rw [map_smul,smul_smul,hr]
  calc
    _ = y-r • (y-F y) := by module
    _ = x := he

omit [CompleteSpace V] in
theorem shifted_injective (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) : Function.Injective (fun x => F x+(b:ℂ) • x) := by
  intro x y he
  have hl := lower_bound F hF b hb (x-y)
  have hz : F (x-y)+(b:ℂ) • (x-y) = 0 := by
    calc
      _ = (F x+(b:ℂ) • x)-(F y+(b:ℂ) • y) := by rw [map_sub,smul_sub]; abel
      _ = 0 := sub_eq_zero.mpr he
  rw [hz,norm_zero] at hl
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg (x-y)]) (norm_nonneg _)))

theorem reverse_equation (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : resolvent F hF b hb (F x+(b:ℂ) • x) = x :=
  shifted_injective F hF b hb (equation F hF b hb _)

theorem resolvent_norm (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : ‖resolvent F hF b hb x‖ ≤ b⁻¹*‖x‖ := by
  have he := lower_bound F hF b hb (resolvent F hF b hb x)
  rw [equation] at he
  exact (le_inv_mul_iff₀ hb).mpr he

theorem intertwine (J : V →L[ℂ] W) (F : V →L[ℂ] V) (D : W →L[ℂ] W)
    (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (hD : ∀ x, ‖residual D x‖ ≤ ‖x‖)
    (hJ : ∀ x, J (F x) = D (J x)) (b : ℝ) (hb : 0 < b) (x : V) :
    J (resolvent F hF b hb x) = resolvent D hD b hb (J x) := by
  apply shifted_injective D hD b hb
  change D (J (resolvent F hF b hb x))+(b:ℂ) • J (resolvent F hF b hb x) =
    D (resolvent D hD b hb (J x))+(b:ℂ) • resolvent D hD b hb (J x)
  rw [equation,← hJ,← map_smul,← map_add,equation]

#print axioms lower_bound
#print axioms scaled_residual_lt
#print axioms equation
#print axioms shifted_injective
#print axioms reverse_equation
#print axioms resolvent_norm
#print axioms intertwine
end
end UnifiedTheory.Audit.KFCausalContractiveResidualResolvent
