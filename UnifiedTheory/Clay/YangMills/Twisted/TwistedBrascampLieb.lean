/- **Brascamp–Lieb for linear observables, from Prékopa.** Let `V` be an action on `ℝᵐ` that is
at least as convex as a positive semidefinite quadratic form `½ xᵀHx`, i.e. `V − ½ xᵀHx` is
convex. For any vector `w`, put `t = Hw` and `L(x) = t·x`. The tilted weight
`Z(s) = ∫ e^{sL(x) − V(x)} dx` then satisfies

  `log Z(s) + log Z(−s) − 2 log Z(0) ≤ s² wᵀHw  (= s² tᵀH⁻¹t when H is invertible)`.

Equivalently `E[e^{sL}] E[e^{−sL}] ≤ e^{s² tᵀH⁻¹t}` under the measure `e^{−V}/Z(0)`. This is a
symmetrized sub-Gaussian bound, and at second order in `s` it reads `Var(L) ≤ tᵀH⁻¹t`, the
Brascamp–Lieb variance inequality for linear observables.

Proof: `K(x, s) = V(x) − s t·x + (s²/2) wᵀHw = [V − ½xᵀHx] + ½(x − sw)ᵀH(x − sw)` is jointly
convex, so by `prekopa_pi` the function `s ↦ −log ∫ e^{−K(x,s)} dx = (s²/2) wᵀHw − log Z(s)` is
convex. Then compare its values at `−s`, `0`, `s`. No derivatives and no matrix inverse are used. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb

open Matrix MeasureTheory Set
open UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

variable {m : ℕ}

theorem quad_sym (H : Matrix (Fin m) (Fin m) ℝ) (hHs : Hᵀ = H) (x y : Fin m → ℝ) :
    y ⬝ᵥ (H *ᵥ x) = x ⬝ᵥ (H *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hHs, dotProduct_comm]

/-- A positive semidefinite quadratic form is convex. -/
theorem quad_convex (H : Matrix (Fin m) (Fin m) ℝ) (hHs : Hᵀ = H)
    (hHp : ∀ v, 0 ≤ v ⬝ᵥ (H *ᵥ v)) : ConvexOn ℝ univ (fun x : Fin m → ℝ => x ⬝ᵥ (H *ᵥ x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hxy := hHp (x - y)
  have hs := quad_sym H hHs x y
  simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hxy ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) hxy]

/-- The tilted partition function `Z(s) = ∫ e^{s (Hw)·x − V(x)} dx`. -/
noncomputable def Ztilt (V : (Fin m → ℝ) → ℝ) (H : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ)
    (s : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (s * ((H *ᵥ w) ⬝ᵥ x) - V x))

/-- **Brascamp–Lieb for linear observables (exponential-moment form).** -/
theorem brascamp_lieb_linear (V : (Fin m → ℝ) → ℝ) (H : Matrix (Fin m) (Fin m) ℝ) (hHs : Hᵀ = H)
    (hHp : ∀ v, 0 ≤ v ⬝ᵥ (H *ᵥ v))
    (hV : ConvexOn ℝ univ (fun x => V x - (1 / 2) * (x ⬝ᵥ (H *ᵥ x)))) (hVm : Measurable V)
    (w : Fin m → ℝ) (hfin : ∀ s, Ztilt V H w s ≠ ⊤) (hpos : ∀ s, Ztilt V H w s ≠ 0) (s : ℝ) :
    Real.log (Ztilt V H w s).toReal + Real.log (Ztilt V H w (-s)).toReal
      - 2 * Real.log (Ztilt V H w 0).toReal ≤ s ^ 2 * (w ⬝ᵥ (H *ᵥ w)) := by
  set q : (Fin m → ℝ) → ℝ := fun x => x ⬝ᵥ (H *ᵥ x)
  set K : (Fin m → ℝ) → ℝ → ℝ := fun x s => V x - s * ((H *ᵥ w) ⬝ᵥ x) + s ^ 2 / 2 * q w
  -- joint convexity of K
  set L : ((Fin m → ℝ) × ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.fst ℝ (Fin m → ℝ) ℝ - (LinearMap.snd ℝ (Fin m → ℝ) ℝ).smulRight w
  have h1 : ConvexOn ℝ univ (fun p : (Fin m → ℝ) × ℝ => V p.1 - (1 / 2) * q p.1) := by
    simpa using hV.comp_linearMap (LinearMap.fst ℝ (Fin m → ℝ) ℝ)
  have h2 : ConvexOn ℝ univ (fun p : (Fin m → ℝ) × ℝ => (1 / 2) * q (L p)) := by
    have := ((quad_convex H hHs hHp).comp_linearMap L).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using this
  have hK : ConvexOn ℝ univ (fun p : (Fin m → ℝ) × ℝ => K p.1 p.2) := by
    convert h1.add h2 using 1
    funext p
    obtain ⟨x, s⟩ := p
    have hs := quad_sym H hHs x w
    simp only [K, q, L, Pi.add_apply, LinearMap.sub_apply, LinearMap.fst_apply,
      LinearMap.smulRight_apply, LinearMap.snd_apply, mulVec_sub, mulVec_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm (H *ᵥ w) x, hs]
    ring
  have hKm : ∀ s, Measurable fun x => K x s := fun s => by
    simp only [K]
    exact (hVm.sub (measurable_const.mul
      (Continuous.measurable (by fun_prop)))).add_const _
  have hZ : ∀ s, ZM volume K s =
      ENNReal.ofReal (Real.exp (-(s ^ 2 / 2 * q w))) * Ztilt V H w s := by
    intro s
    simp only [ZM, Ztilt, K]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hKfin : ∀ s, ZM volume K s ≠ ⊤ := fun s => by
    rw [hZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s)
  have hKpos : ∀ s, ZM volume K s ≠ 0 := fun s => by
    rw [hZ]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hpos s)
  have hconv := prekopa_pi m K hK hKm hKfin hKpos
  have hφ : ∀ s, -Real.log (ZM volume K s).toReal
      = s ^ 2 / 2 * q w - Real.log (Ztilt V H w s).toReal := by
    intro s
    rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos (hpos s) (hfin s)).ne', Real.log_exp]
    ring
  have key := hconv.2 (mem_univ s) (mem_univ (-s)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at key
  rw [show 1 / 2 * s + 1 / 2 * -s = (0 : ℝ) by ring, hφ, hφ, hφ] at key
  simp only [q] at key
  nlinarith [key]

end UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb
