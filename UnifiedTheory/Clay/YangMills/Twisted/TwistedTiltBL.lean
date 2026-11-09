/- **The localization covariance bound in the convex regime.** Stochastic localization tilts a measure
`e^{−V}` to `μ_{t,y} ∝ e^{⟨y,x⟩ − (t/2)|x|² − V(x)}`, and the criterion of the README ("Stochastic
localization") needs `α_t = ‖Cov μ_{t,y}‖_op` with `∫₀ᵀ α_t dt` controlled. If `V − ½ xᵀHx` is convex with
`H ≥ λ·I`, the tilt adds `t·I` to the Hessian and leaves the convexity defect unchanged. So Brascamp–Lieb
(`TwistedBrascampLieb.brascamp_lieb_linear`) applied with `H + t·I` gives, for every direction `u` and
**every** tilt `y`,

  `log Z(s) + log Z(−s) − 2 log Z(0) ≤ s² |u|² / (λ + t)`,   `Z(s) = ∫ e^{s u·x − V_{t,y}(x)} dx`.

At second order in `s` this is `Var_{μ_{t,y}}(u·x) ≤ |u|²/(λ + t)`, so `α_t ≤ 1/(λ + t)` and
`∫₀ᵀ α_t ≤ log(1 + T/λ)`. That is the Gaussian-sharp value ("Gaussian sharpness" in the README), and it
holds for all `y`, with no almost-sure issue. All of this is for a convex action on `ℝᵐ`. The SU(2)
measure is not of this form, which is exactly the large-field problem.

The bound `wᵀAw ≤ |Aw|²/κ` for `A ≥ κ·I` is proved from `0 ≤ |Aw − κw|²`, with no spectral theorem. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb
import UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedTiltBL

open Matrix MeasureTheory Set
open UnifiedTheory.Clay.YangMills.Twisted.TwistedBrascampLieb
open UnifiedTheory.Clay.YangMills.Twisted.TwistedGaussianStep

variable {m : ℕ}

/-- For `A` with `κ|w|² ≤ wᵀAw` and `κ > 0`: `κ · wᵀAw ≤ |Aw|²`. -/
theorem quad_le_sq_div (A : Matrix (Fin m) (Fin m) ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hcoer : ∀ v, κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) (w : Fin m → ℝ) :
    κ * (w ⬝ᵥ (A *ᵥ w)) ≤ (A *ᵥ w) ⬝ᵥ (A *ᵥ w) := by
  have h0 : 0 ≤ (A *ᵥ w - κ • w) ⬝ᵥ (A *ᵥ w - κ • w) := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hs : (A *ᵥ w) ⬝ᵥ w = w ⬝ᵥ (A *ᵥ w) := by
    rw [dotProduct_comm]
  have hc := hcoer w
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    hs] at h0
  nlinarith [mul_le_mul_of_nonneg_left hc hκ.le]

/-- The tilted moment generating function of the localization measure. -/
noncomputable def Zsl (V : (Fin m → ℝ) → ℝ) (y : Fin m → ℝ) (t : ℝ) (u : Fin m → ℝ) (s : ℝ) :
    ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (s * (u ⬝ᵥ x) - (V x - y ⬝ᵥ x + t / 2 * (x ⬝ᵥ x))))

/-- **Localization covariance bound for a convex action.** If `V − ½ xᵀHx` is convex and
`H ≥ λ·I`, then for every tilt `y`, every `t` with `λ + t > 0` and every direction `u`, the
tilted measure satisfies the symmetrized sub-Gaussian bound with variance proxy
`|u|²/(λ + t)`. -/
theorem sl_tilt_sub_gaussian (V : (Fin m → ℝ) → ℝ) (H : Matrix (Fin m) (Fin m) ℝ) (hHs : Hᵀ = H)
    (lam t : ℝ) (hpos : 0 < lam + t)
    (hHl : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H *ᵥ v))
    (hV : ConvexOn ℝ univ (fun x => V x - (1 / 2) * (x ⬝ᵥ (H *ᵥ x)))) (hVm : Measurable V)
    (y u : Fin m → ℝ) (hfin : ∀ s, Zsl V y t u s ≠ ⊤) (hZpos : ∀ s, Zsl V y t u s ≠ 0) (s : ℝ) :
    Real.log (Zsl V y t u s).toReal + Real.log (Zsl V y t u (-s)).toReal
      - 2 * Real.log (Zsl V y t u 0).toReal ≤ s ^ 2 * (u ⬝ᵥ u) / (lam + t) := by
  set Ht : Matrix (Fin m) (Fin m) ℝ := H + t • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hHtv : ∀ v, Ht *ᵥ v = H *ᵥ v + t • v := fun v => by
    simp [Ht, add_mulVec, smul_mulVec]
  have hHts : Htᵀ = Ht := by simp [Ht, transpose_add, hHs]
  have hcoer : ∀ v, (lam + t) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Ht *ᵥ v) := fun v => by
    rw [hHtv, dotProduct_add, dotProduct_smul, smul_eq_mul]; nlinarith [hHl v]
  have hHtp : ∀ v, 0 ≤ v ⬝ᵥ (Ht *ᵥ v) := fun v => by
    have hvv : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    nlinarith [hcoer v, mul_nonneg hpos.le hvv]
  have hdet := isUnit_det_of_coercive Ht (lam + t) hpos hcoer
  set w := Ht⁻¹ *ᵥ u
  have hw : Ht *ᵥ w = u := by
    simp only [w, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  set Vt : (Fin m → ℝ) → ℝ := fun x => V x - y ⬝ᵥ x + t / 2 * (x ⬝ᵥ x)
  have hlin : ConvexOn ℝ univ (fun x : Fin m → ℝ => -(y ⬝ᵥ x)) := by
    refine ⟨convex_univ, fun a _ b _ p q _ _ _ => le_of_eq ?_⟩
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
  have hVt : ConvexOn ℝ univ (fun x => Vt x - (1 / 2) * (x ⬝ᵥ (Ht *ᵥ x))) := by
    have heq : (fun x => Vt x - (1 / 2) * (x ⬝ᵥ (Ht *ᵥ x))) =
        fun x => (V x - (1 / 2) * (x ⬝ᵥ (H *ᵥ x))) + -(y ⬝ᵥ x) := by
      funext x; simp only [Vt, hHtv, dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    rw [heq]; exact hV.add hlin
  have hcont : Continuous fun x : Fin m → ℝ => y ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  have hcont2 : Continuous fun x : Fin m → ℝ => x ⬝ᵥ x := by
    simp only [dotProduct]; fun_prop
  have hVtm : Measurable Vt :=
    (hVm.sub hcont.measurable).add (measurable_const.mul hcont2.measurable)
  have hZ : ∀ s, Ztilt Vt Ht w s = Zsl V y t u s := fun s => by
    simp only [Ztilt, Zsl, hw, Vt]
  have key := brascamp_lieb_linear Vt Ht hHts hHtp hVt hVtm w
    (fun s => by rw [hZ]; exact hfin s) (fun s => by rw [hZ]; exact hZpos s) s
  rw [hZ, hZ, hZ] at key
  have hq := quad_le_sq_div Ht (lam + t) hpos hcoer w
  have he : (Ht *ᵥ w) ⬝ᵥ (Ht *ᵥ w) = u ⬝ᵥ u := by rw [hw]
  have hb : w ⬝ᵥ (Ht *ᵥ w) ≤ (u ⬝ᵥ u) / (lam + t) := by
    rw [le_div_iff₀ hpos]; linarith
  calc _ ≤ s ^ 2 * (w ⬝ᵥ (Ht *ᵥ w)) := key
    _ ≤ s ^ 2 * ((u ⬝ᵥ u) / (lam + t)) := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
    _ = s ^ 2 * (u ⬝ᵥ u) / (lam + t) := by ring

end UnifiedTheory.Clay.YangMills.Twisted.TwistedTiltBL
