/- Pointwise bounds on the twisted fluctuation covariance. Two arguments, on the finite lattice. Combes-Thomas:
conjugating a local form by opposite weights `exp(±φ)` is a difference of squares, so it moves the form only at
second order in the gradient of `φ`. Sobolev: in four dimensions a field is bounded at a point by its covariant
gradient and its average at a large scale, with a constant free of the lattice size. The dyadic telescope gives the
inequality for scalars, and the diamagnetic inequality transfers it to any pointwise isometric transport with no
commutator cost.

"Covariance" below means the solution operator of a symmetric coercive form. That it is the covariance of the
Gaussian with this quadratic form is the standard integral, not formalized here.

Proved, with no open hypothesis:
* `sobolev_scalar`, `point_le_grad`: `‖f x‖ ≤ ∑ ν, ‖D_ν f‖ + 4^(-K) ‖f‖` when `2^K ≤ N`, for plain translations and
  for any pointwise isometric transport.
* `flat_point`: the massless flat covariance of each colour has `|g ν x| ≤ 9 |v|` for every `N`. There is no decay
  statement for this form. Since `dist1 ≤ 2N` on the torus, a factor `exp(-dist/(cN))` stays above `exp(-2/c)`, so
  it would say nothing. Numerically the kernel decays like `0.10/dist²`, with no `N`-uniform exponential rate.
* `cov_point`, `cov_decay_unif`: for curl² + div² + (1/4L²)·penalty on quaternion-valued fields, with all defects at
  most `1/(1000 L²)` and `L ≤ N`: `‖g ν x‖ ≤ 63 ‖v‖` and `‖g ν x‖ ≤ 126 exp(-dist/(32 L)) ‖v‖`. On an `L²` source,
  `cov_point_source` gives `‖g ν x‖² ≤ 540 L² ‖s‖²`.
* `hess_point`, `hess_decay_unif`: for `β` times the actual second derivative plus div² plus the penalty, on
  imaginary fields, the same hypotheses: `‖g ν x‖ ≤ (116/β) ‖v‖` and `‖g ν x‖ ≤ (232/β) exp(-dist/(100 L)) ‖v‖`. On an
  `L²` source, `hess_point_source` gives `‖g ν x‖² ≤ (1856 L²/β²) ‖s‖²`.
* `cov_point_avoid`, `cov_decay_avoid_unif`, `hess_decay_avoid_unif`: for an arbitrary field `U`, the same bounds for
  the Dirichlet problem on directions vanishing on the links of bad plaquettes.
* `cov_decay`, `hess_decay` and their `_avoid` forms: the older bounds with prefactors `16 L²` and `32 L²/β`. They do
  not need `L ≤ N`, and they are the better ones only at small `L`.

How to read the exponential. The decay bounds beat the point bounds only past `dist > 22.2 L` for `cov_decay_unif`, so
`N > 11.1 L`, and past `dist > 69.4 L` for `hess_decay_unif`, so `N > 34.7 L`. Below those distances, and on smaller
tori, the exponential carries no information. The prefactors are also far above the truth. Numerically, at the flat
field, the diagonal is about `0.15` for `N ≫ L`. It is largest in the real component on the smallest tori, at `4` for
`N = L = 1` and `1.13` for `N = L = 2`. Below `0.15`, `cov_decay_unif` says something only past `dist > 214 L`.

Not proved:
* Anything about the measure. These are bounds on a linear operator at a fixed background, with no effective action.
* Any uniform decay coming from the action. The `N`-uniform rate comes entirely from the added penalty, which is on
  running averages and is not a block-spin constraint on the group.
* The size `1/d²` of the propagator at distance `d`. The bounds here are `O(1)` for `d ≲ L`.
* Any statement at a `U` as a saddle: at a nonzero defect `U` is not a critical point, and the linear term of the
  action around it is not treated.
* In the `_avoid` theorems, anything about the excluded directions, where the form can be negative. If every link
  touches a bad plaquette, or the source link is excluded, the solution is `0` and the bound is empty. By
  `measure_bad_density` the excluded links are a small fraction only at `β` of order `10⁶ L⁴` times a logarithm. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedCovarianceDecay
noncomputable section
open CommutingShifts BlockShifts
open scoped RealInnerProductSpace

/-! ### Multiplication by a weight -/

section Weights

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Sites to `F`, with the `L²` norm. -/
abbrev Fld (ι F : Type*) [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] :=
  PiLp 2 (fun _ : ι => F)

/-- Multiplication by a real weight. -/
def mulW (w : ι → ℝ) : Fld ι F →ₗ[ℝ] Fld ι F where
  toFun f := WithLp.toLp 2 fun x => w x • f x
  map_add' f g := by
    ext x : 1
    simp [smul_add]
  map_smul' c f := by
    ext x : 1
    exact smul_comm _ _ _

theorem mulW_apply (w : ι → ℝ) (f : Fld ι F) (x : ι) : mulW w f x = w x • f x := rfl

theorem mulW_mulW (v w : ι → ℝ) (f : Fld ι F) :
    mulW v (mulW w f) = mulW (fun x => v x * w x) f := by
  ext x : 1
  simp [mulW_apply, smul_smul]

theorem mulW_one (f : Fld ι F) : mulW (fun _ => 1) f = f := by
  ext x : 1
  simp [mulW_apply]

theorem inner_mulW (w : ι → ℝ) (f g : Fld ι F) : ⟪mulW w f, g⟫ = ⟪f, mulW w g⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mulW_apply, mulW_apply, real_inner_smul_left, real_inner_smul_right]

theorem norm_sq_fld (f : Fld ι F) : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

theorem norm_mulW_le (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ x, |w x| ≤ C) (f : Fld ι F) :
    ‖mulW w f‖ ≤ C * ‖f‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, norm_sq_fld, norm_sq_fld, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [mulW_apply, norm_smul, Real.norm_eq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hw x) (norm_nonneg _)) 2

/-- Multiplication by `exp φ`. -/
def Mw (φ : ι → ℝ) : Fld ι F →ₗ[ℝ] Fld ι F := mulW fun x => Real.exp (φ x)

theorem Mw_apply (φ : ι → ℝ) (f : Fld ι F) (x : ι) : Mw φ f x = Real.exp (φ x) • f x := rfl

theorem Mw_neg_Mw (φ : ι → ℝ) (f : Fld ι F) : Mw (-φ) (Mw φ f) = f := by
  ext x : 1
  simp [Mw_apply, smul_smul, ← Real.exp_add]

theorem Mw_Mw_neg (φ : ι → ℝ) (f : Fld ι F) : Mw φ (Mw (-φ) f) = f := by
  ext x : 1
  simp [Mw_apply, smul_smul, ← Real.exp_add]

theorem inner_Mw (φ : ι → ℝ) (f g : Fld ι F) : ⟪Mw φ f, g⟫ = ⟪f, Mw φ g⟫ := inner_mulW _ _ _

/-- Conjugation by the weight, linear in the operator. -/
def cj (φ : ι → ℝ) : (Fld ι F →ₗ[ℝ] Fld ι F) →ₗ[ℝ] (Fld ι F →ₗ[ℝ] Fld ι F) where
  toFun G := Mw φ ∘ₗ G ∘ₗ Mw (-φ)
  map_add' G H := by
    ext f x : 3
    simp
  map_smul' c G := by
    ext f x : 3
    simp

theorem cj_apply (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    cj φ G f = Mw φ (G (Mw (-φ) f)) := rfl

theorem cj_comp (φ : ι → ℝ) (G H : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    cj φ (G ∘ₗ H) f = cj φ G (cj φ H f) := by
  simp only [cj_apply, LinearMap.comp_apply, Mw_neg_Mw]

theorem cj_id (φ : ι → ℝ) : cj φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) = 1 := by
  ext f x : 3
  change (Mw φ (Mw (-φ) f)) x = f x
  rw [Mw_Mw_neg]

/-- The even and odd parts of the conjugation. -/
def ev (φ : ι → ℝ) : (Fld ι F →ₗ[ℝ] Fld ι F) →ₗ[ℝ] (Fld ι F →ₗ[ℝ] Fld ι F) :=
  (1 / 2 : ℝ) • (cj φ + cj (-φ))

def od (φ : ι → ℝ) : (Fld ι F →ₗ[ℝ] Fld ι F) →ₗ[ℝ] (Fld ι F →ₗ[ℝ] Fld ι F) :=
  (1 / 2 : ℝ) • (cj φ - cj (-φ))

theorem ev_apply (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    ev φ G f = (1 / 2 : ℝ) • (cj φ G f + cj (-φ) G f) := rfl

theorem od_apply (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    od φ G f = (1 / 2 : ℝ) • (cj φ G f - cj (-φ) G f) := rfl

theorem cj_eq_add (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    cj φ G f = ev φ G f + od φ G f := by
  rw [ev_apply, od_apply, ← smul_add]
  rw [show cj φ G f + cj (-φ) G f + (cj φ G f - cj (-φ) G f) = (2 : ℝ) • cj φ G f by
    rw [two_smul]; abel]
  rw [smul_smul]
  norm_num

theorem cj_neg_eq_sub (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (f : Fld ι F) :
    cj (-φ) G f = ev φ G f - od φ G f := by
  rw [ev_apply, od_apply, ← smul_sub]
  rw [show cj φ G f + cj (-φ) G f - (cj φ G f - cj (-φ) G f) = (2 : ℝ) • cj (-φ) G f by
    rw [two_smul]; abel]
  rw [smul_smul]
  norm_num

/-- `G` moves sites by at most `r` as measured by `φ`, and is a contraction. The second and third fields
are what a sum of transports of length at most `r` satisfies. -/
structure Tame (φ : ι → ℝ) (G : Fld ι F →ₗ[ℝ] Fld ι F) (r : ℝ) : Prop where
  contr : ∀ f, ‖G f‖ ≤ ‖f‖
  odd : ∀ f, ‖od φ G f‖ ≤ Real.sinh r * ‖f‖
  even : ∀ f, ‖ev φ G f - G f‖ ≤ (Real.cosh r - 1) * ‖f‖

theorem Tame.ev_norm {φ : ι → ℝ} {G : Fld ι F →ₗ[ℝ] Fld ι F} {r : ℝ} (h : Tame φ G r) (f : Fld ι F) :
    ‖ev φ G f‖ ≤ Real.cosh r * ‖f‖ := by
  have e : ev φ G f = (ev φ G f - G f) + G f := by abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := h.even f
  have h2 := h.contr f
  linarith only [h1, h2]

theorem Tame.comp {φ : ι → ℝ} {G H : Fld ι F →ₗ[ℝ] Fld ι F} {r s : ℝ} (hG : Tame φ G r)
    (hH : Tame φ H s) (hr : 0 ≤ r) (hs : 0 ≤ s) : Tame φ (G ∘ₗ H) (r + s) := by
  have hodd (f : Fld ι F) : od φ (G ∘ₗ H) f = od φ G (ev φ H f) + ev φ G (od φ H f) := by
    rw [od_apply, cj_comp, cj_comp, cj_eq_add φ H f, cj_neg_eq_sub φ H f, map_add, map_sub,
      cj_eq_add φ G, cj_eq_add φ G, cj_neg_eq_sub φ G, cj_neg_eq_sub φ G]
    have : ∀ a b c d : Fld ι F, a + b + (c + d) - (a - b - (c - d)) = (2 : ℝ) • (b + c) := by
      intro a b c d
      rw [two_smul]
      abel
    rw [this, smul_smul]
    norm_num
  have heven (f : Fld ι F) : ev φ (G ∘ₗ H) f = ev φ G (ev φ H f) + od φ G (od φ H f) := by
    rw [ev_apply, cj_comp, cj_comp, cj_eq_add φ H f, cj_neg_eq_sub φ H f, map_add, map_sub,
      cj_eq_add φ G, cj_eq_add φ G, cj_neg_eq_sub φ G, cj_neg_eq_sub φ G]
    have : ∀ a b c d : Fld ι F, a + b + (c + d) + (a - b - (c - d)) = (2 : ℝ) • (a + d) := by
      intro a b c d
      rw [two_smul]
      abel
    rw [this, smul_smul]
    norm_num
  have hch0 : 0 ≤ Real.cosh r := (Real.cosh_pos r).le
  have hcs0 : 0 ≤ Real.cosh s := (Real.cosh_pos s).le
  have hsr0 : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.2 hr
  have hss0 : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.2 hs
  refine ⟨fun f => (hG.contr _).trans (hH.contr _), fun f => ?_, fun f => ?_⟩
  · rw [hodd, Real.sinh_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hG.odd (ev φ H f)).trans
      (mul_le_mul_of_nonneg_left (hH.ev_norm f) hsr0)
    have h2 := (hG.ev_norm (od φ H f)).trans
      (mul_le_mul_of_nonneg_left (hH.odd f) hch0)
    nlinarith only [h1, h2]
  · have e : ev φ (G ∘ₗ H) f - (G ∘ₗ H) f = (ev φ G (ev φ H f) - G (ev φ H f)) +
        G (ev φ H f - H f) + od φ G (od φ H f) := by
      rw [heven, map_sub, LinearMap.comp_apply]
      abel
    rw [e, Real.cosh_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := (hG.even (ev φ H f)).trans
      (mul_le_mul_of_nonneg_left (hH.ev_norm f) (by
        have := Real.one_le_cosh r
        linarith only [this]))
    have h2 := (hG.contr (ev φ H f - H f)).trans (hH.even f)
    have h3 := (hG.odd (od φ H f)).trans (mul_le_mul_of_nonneg_left (hH.odd f) hsr0)
    have h4 := norm_add_le (ev φ G (ev φ H f) - G (ev φ H f)) (G (ev φ H f - H f))
    nlinarith only [h1, h2, h3, h4]

theorem Tame.mono {φ : ι → ℝ} {G : Fld ι F →ₗ[ℝ] Fld ι F} {r s : ℝ} (h : Tame φ G r) (hr : 0 ≤ r)
    (hrs : r ≤ s) : Tame φ G s := by
  have h1 : Real.sinh r ≤ Real.sinh s := Real.sinh_le_sinh.2 hrs
  have h2 : Real.cosh r ≤ Real.cosh s := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hr, abs_of_nonneg (hr.trans hrs)]
    exact hrs
  refine ⟨h.contr, fun f => (h.odd f).trans ?_, fun f => (h.even f).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (by linarith only [h2]) (norm_nonneg _)

theorem tame_id (φ : ι → ℝ) : Tame φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) 0 := by
  have h1 (f : Fld ι F) : ev φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) f = f := by
    rw [ev_apply, cj_id, cj_id, Module.End.one_apply, ← two_smul ℝ f, smul_smul]
    norm_num
  have h2 (f : Fld ι F) : od φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) f = 0 := by
    rw [od_apply, cj_id, cj_id, sub_self, smul_zero]
  refine ⟨fun f => le_rfl, fun f => ?_, fun f => ?_⟩
  · simp [h2]
  · simp [h1]

/-- A uniform average of tame operators is tame. -/
theorem Tame.avg {φ : ι → ℝ} (G : ℕ → Fld ι F →ₗ[ℝ] Fld ι F) (L : ℕ) (hL : 1 ≤ L) (r : ℝ)
    (hG : ∀ j < L, Tame φ (G j) r) :
    Tame φ ((1 / (L : ℝ)) • ∑ j ∈ Finset.range L, G j) r := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have bound (P : ℕ → Fld ι F → Fld ι F) (f : Fld ι F) (C : ℝ)
      (hP : ∀ j < L, ‖P j f‖ ≤ C) : ‖(1 / (L : ℝ)) • ∑ j ∈ Finset.range L, P j f‖ ≤ C := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h : ‖∑ j ∈ Finset.range L, P j f‖ ≤ L * C := by
      refine (norm_sum_le _ _).trans ?_
      have := Finset.sum_le_sum (s := Finset.range L) fun j hj => hP j (Finset.mem_range.1 hj)
      simpa using this
    calc 1 / (L : ℝ) * ‖∑ j ∈ Finset.range L, P j f‖ ≤ 1 / (L : ℝ) * (L * C) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C := by field_simp
  refine ⟨fun f => ?_, fun f => ?_, fun f => ?_⟩
  · have := bound (fun j f => G j f) f ‖f‖ fun j hj => (hG j hj).contr f
    simpa [LinearMap.sum_apply] using this
  · have := bound (fun j f => od φ (G j) f) f _ fun j hj => (hG j hj).odd f
    simpa [map_sum, LinearMap.sum_apply] using this
  · have := bound (fun j f => ev φ (G j) f - G j f) f _ fun j hj => (hG j hj).even f
    have e : ev φ ((1 / (L : ℝ)) • ∑ j ∈ Finset.range L, G j) f -
        ((1 / (L : ℝ)) • ∑ j ∈ Finset.range L, G j) f =
        (1 / (L : ℝ)) • ∑ j ∈ Finset.range L, (ev φ (G j) f - G j f) := by
      simp [map_sum, LinearMap.sum_apply, Finset.sum_sub_distrib, smul_sub]
    rw [e]
    exact this

/-! ### Transports -/

/-- `T` carries multiplication by `w` to multiplication by `w ∘ π`. -/
def Intertwines (π : ι → ι) (T : Fld ι F →ₗ[ℝ] Fld ι F) : Prop :=
  ∀ w f, T (mulW w f) = mulW (fun x => w (π x)) (T f)

theorem tame_of_intertwines {φ : ι → ℝ} (π : ι → ι) (T : Fld ι F →ₗ[ℝ] Fld ι F)
    (hT : Intertwines π T) (hc : ∀ f, ‖T f‖ ≤ ‖f‖) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ x, |φ x - φ (π x)| ≤ r) : Tame φ T r := by
  have hcj (ψ : ι → ℝ) (f : Fld ι F) :
      cj ψ T f = mulW (fun x => Real.exp (ψ x - ψ (π x))) (T f) := by
    rw [cj_apply]
    change mulW _ (T (mulW _ f)) = _
    rw [hT, mulW_mulW]
    congr 2
    funext x
    rw [Pi.neg_apply, ← Real.exp_add]
    rfl
  have hodd (f : Fld ι F) :
      od φ T f = mulW (fun x => Real.sinh (φ x - φ (π x))) (T f) := by
    ext x : 1
    rw [od_apply, hcj, hcj]
    simp only [PiLp.smul_apply, PiLp.sub_apply, mulW_apply, Pi.neg_apply, Real.sinh_eq]
    rw [show -φ x - -φ (π x) = -(φ x - φ (π x)) by ring, ← sub_smul, smul_smul]
    congr 1
    ring
  have heven (f : Fld ι F) :
      ev φ T f - T f = mulW (fun x => Real.cosh (φ x - φ (π x)) - 1) (T f) := by
    ext x : 1
    rw [ev_apply, hcj, hcj]
    simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, mulW_apply, Pi.neg_apply,
      Real.cosh_eq]
    rw [show -φ x - -φ (π x) = -(φ x - φ (π x)) by ring, ← add_smul, smul_smul, sub_smul, one_smul]
    congr 2
    ring
  refine ⟨hc, fun f => ?_, fun f => ?_⟩
  · rw [hodd]
    refine (norm_mulW_le _ (Real.sinh r) (Real.sinh_nonneg_iff.2 hr0) (fun x => ?_) _).trans
      (mul_le_mul_of_nonneg_left (hc f) (Real.sinh_nonneg_iff.2 hr0))
    rw [Real.abs_sinh]
    exact Real.sinh_le_sinh.2 (hr x)
  · rw [heven]
    have h1 := Real.one_le_cosh r
    refine (norm_mulW_le _ (Real.cosh r - 1) (by linarith only [h1]) (fun x => ?_) _).trans
      (mul_le_mul_of_nonneg_left (hc f) (by linarith only [h1]))
    have h2 := Real.one_le_cosh (φ x - φ (π x))
    rw [abs_of_nonneg (by linarith only [h2])]
    have h3 : Real.cosh (φ x - φ (π x)) ≤ Real.cosh r := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hr0]
      exact hr x
    linarith only [h3]

/-! ### Shift families on a lattice -/

/-- The running average, as a linear map. -/
def savgL (A : Shift (Fld ι F)) (L : ℕ) : Fld ι F →ₗ[ℝ] Fld ι F :=
  (1 / (L : ℝ)) • ∑ j ∈ Finset.range L, spow A j

theorem savgL_apply (A : Shift (Fld ι F)) (L : ℕ) (x : Fld ι F) : savgL A L x = savg A L x := by
  simp [savgL, savg, LinearMap.sum_apply]

/-- The ordered block average, as a linear map. -/
def blockL (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) : Fld ι F →ₗ[ℝ] Fld ι F :=
  savgL (A 0) L ∘ₗ savgL (A 1) L ∘ₗ savgL (A 2) L ∘ₗ savgL (A 3) L

theorem blockL_apply (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (x : Fld ι F) :
    blockL A L x = blockAvg A L x := by
  simp [blockL, blockAvg, savgL_apply]

theorem intertwines_S (A : Shift (Fld ι F)) (π : ι ≃ ι) (h : Intertwines π A.T) :
    Intertwines π.symm A.S := by
  intro w f
  have e : A.T (mulW (fun x => w (π.symm x)) (A.S f)) = mulW w f := by
    rw [h, A.right]
    simp
  have := congrArg A.S e
  rw [A.left] at this
  exact this.symm

section Family

variable {φ : ι → ℝ} {m : ℝ}

theorem tame_T (A : Shift (Fld ι F)) (π : ι ≃ ι) (h : Intertwines π A.T) (hm : 0 ≤ m)
    (hφ : ∀ x, |φ x - φ (π x)| ≤ m) : Tame φ A.T m :=
  tame_of_intertwines π A.T h (fun f => (A.norm_T f).le) m hm hφ

theorem tame_S (A : Shift (Fld ι F)) (π : ι ≃ ι) (h : Intertwines π A.T) (hm : 0 ≤ m)
    (hφ : ∀ x, |φ x - φ (π x)| ≤ m) : Tame φ A.S m := by
  refine tame_of_intertwines π.symm A.S (intertwines_S A π h) (fun f => (A.norm_S f).le) m hm ?_
  intro x
  have := hφ (π.symm x)
  rw [Equiv.apply_symm_apply, abs_sub_comm] at this
  exact this

theorem tame_spow (A : Shift (Fld ι F)) (hT : Tame φ A.T m) (hm : 0 ≤ m) (j : ℕ) :
    Tame φ (spow A j) (j * m) := by
  induction j with
  | zero =>
    have : spow A 0 = (1 : Fld ι F →ₗ[ℝ] Fld ι F) := by simp [spow]
    rw [this]
    simpa using tame_id φ
  | succ j ih =>
    have e : spow A (j + 1) = A.T ∘ₗ spow A j := by
      ext x : 1
      exact spow_succ A j x
    rw [e]
    have := hT.comp ih hm (by positivity)
    convert this using 1
    push_cast
    ring

theorem tame_savg (A : Shift (Fld ι F)) (hT : Tame φ A.T m) (hm : 0 ≤ m) (L : ℕ) (hL : 1 ≤ L) :
    Tame φ (savgL A L) (L * m) := by
  refine Tame.avg (spow A) L hL _ fun j hj => (tame_spow A hT hm j).mono (by positivity) ?_
  have : (j : ℝ) ≤ L := by exact_mod_cast hj.le
  exact mul_le_mul_of_nonneg_right this hm

theorem tame_block (A : Fin 4 → Shift (Fld ι F)) (hT : ∀ μ, Tame φ (A μ).T m) (hm : 0 ≤ m) (L : ℕ)
    (hL : 1 ≤ L) : Tame φ (blockL A L) (4 * L * m) := by
  have hr : (0 : ℝ) ≤ L * m := by positivity
  have h3 := tame_savg (A 3) (hT 3) hm L hL
  have h2 := (tame_savg (A 2) (hT 2) hm L hL).comp h3 hr hr
  have h1 := (tame_savg (A 1) (hT 1) hm L hL).comp h2 hr (by positivity)
  have h0 := (tame_savg (A 0) (hT 0) hm L hL).comp h1 hr (by positivity)
  have e : (L : ℝ) * m + (L * m + (L * m + L * m)) = 4 * L * m := by ring
  rw [e] at h0
  exact h0

end Family

/-! ### First-order operators -/

/-- The three bounds a conjugated first-order operator needs. -/
structure FO (φ : ι → ℝ) (K : Fld ι F →ₗ[ℝ] Fld ι F) (n y σ : ℝ) : Prop where
  norm : ∀ x, ‖K x‖ ≤ n * ‖x‖
  even : ∀ x, ‖ev φ K x - K x‖ ≤ y * ‖x‖
  odd : ∀ x, ‖od φ K x‖ ≤ σ * ‖x‖

theorem FO.neg {φ : ι → ℝ} {K : Fld ι F →ₗ[ℝ] Fld ι F} {n y σ : ℝ} (h : FO φ K n y σ) :
    FO φ (-K) n y σ := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · simpa using h.norm x
  · have := h.even x
    rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply, neg_sub_neg, norm_sub_rev]
    exact this
  · have := h.odd x
    rw [map_neg, LinearMap.neg_apply, norm_neg]
    exact this

theorem FO_of_tame {φ : ι → ℝ} {G : Fld ι F →ₗ[ℝ] Fld ι F} {r : ℝ} (h : Tame φ G r) :
    FO φ G 1 (Real.cosh r - 1) (Real.sinh r) :=
  ⟨fun x => by simpa using h.contr x, h.even, h.odd⟩

/-- The difference `G - 1` of a tame operator. -/
theorem FO_sub_one {φ : ι → ℝ} {G : Fld ι F →ₗ[ℝ] Fld ι F} {r : ℝ} (h : Tame φ G r) :
    FO φ (G - 1) 2 (Real.cosh r - 1) (Real.sinh r) := by
  have h1 (x : Fld ι F) : ev φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) x = x := by
    rw [ev_apply, cj_id, cj_id, Module.End.one_apply, ← two_smul ℝ x, smul_smul]
    norm_num
  have h2 (x : Fld ι F) : od φ (1 : Fld ι F →ₗ[ℝ] Fld ι F) x = 0 := by
    rw [od_apply, cj_id, cj_id, sub_self, smul_zero]
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [LinearMap.sub_apply, Module.End.one_apply]
    refine (norm_sub_le _ _).trans ?_
    have := h.contr x
    linarith only [this]
  · have e : ev φ (G - 1) x - (G - 1) x = ev φ G x - G x := by
      rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, h1, Module.End.one_apply]
      abel
    rw [e]
    exact h.even x
  · have e : od φ (G - 1) x = od φ G x := by
      rw [map_sub, LinearMap.sub_apply, h2, sub_zero]
    rw [e]
    exact h.odd x

/-- Vector fields: four components. -/
abbrev VF (ι F : Type*) [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] :=
  Fin 4 → Fld ι F

/-- The weight acting on all four components. -/
def Wt (φ : ι → ℝ) (h : VF ι F) : VF ι F := fun μ => Mw φ (h μ)

theorem Wt_neg_Wt (φ : ι → ℝ) (h : VF ι F) : Wt (-φ) (Wt φ h) = h :=
  funext fun μ => Mw_neg_Mw φ (h μ)

theorem Wt_Wt_neg (φ : ι → ℝ) (h : VF ι F) : Wt φ (Wt (-φ) h) = h :=
  funext fun μ => Mw_Mw_neg φ (h μ)

/-- The inner product and squared norm of vector fields. -/
def ip (f g : VF ι F) : ℝ := ∑ μ, ⟪f μ, g μ⟫

def nsq (f : VF ι F) : ℝ := ∑ μ, ‖f μ‖ ^ 2

theorem nsq_nonneg (f : VF ι F) : 0 ≤ nsq f := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_eq_ip (f : VF ι F) : nsq f = ip f f :=
  Finset.sum_congr rfl fun _ _ => (real_inner_self_eq_norm_sq _).symm

theorem nsq_eq_zero {f : VF ι F} (h : nsq f ≤ 0) : f = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun μ _ => sq_nonneg ‖f μ‖)).1
    (le_antisymm h (nsq_nonneg f))
  funext μ
  simpa using hz μ (Finset.mem_univ μ)

theorem ip_Wt (φ : ι → ℝ) (f g : VF ι F) : ip (Wt φ f) g = ip f (Wt φ g) :=
  Finset.sum_congr rfl fun _ _ => inner_Mw φ _ _

theorem ip_sq_le (f g : VF ι F) : ip f g ^ 2 ≤ nsq f * nsq g := by
  have h1 : ip f g ≤ ∑ μ, ‖f μ‖ * ‖g μ‖ :=
    Finset.sum_le_sum fun μ _ => real_inner_le_norm _ _
  have h2 : -ip f g ≤ ∑ μ, ‖f μ‖ * ‖g μ‖ := by
    unfold ip
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun μ _ => ?_
    have := abs_real_inner_le_norm (f μ) (g μ)
    linarith only [(abs_le.1 this).1]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun μ => ‖f μ‖) (fun μ => ‖g μ‖)
  have h4 : ip f g ^ 2 ≤ (∑ μ, ‖f μ‖ * ‖g μ‖) ^ 2 := by
    rw [← sq_abs (ip f g)]
    refine pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨by linarith only [h2], h1⟩) 2
  exact h4.trans h3

/-- A row of first-order operators acting on chosen components. -/
def rowL {I : Type*} [Fintype I] (ρ : I → Fin 4) (K : I → Fld ι F →ₗ[ℝ] Fld ι F) :
    VF ι F →ₗ[ℝ] Fld ι F :=
  ∑ i, K i ∘ₗ LinearMap.proj (ρ i)

theorem rowL_apply {I : Type*} [Fintype I] (ρ : I → Fin 4) (K : I → Fld ι F →ₗ[ℝ] Fld ι F)
    (f : VF ι F) : rowL ρ K f = ∑ i, K i (f (ρ i)) := by
  simp [rowL, LinearMap.sum_apply]

/-- The split behind Combes-Thomas: the part of first order in the weight has no effect at first order,
because a product of conjugations by opposite weights is a difference of squares. -/
theorem row_lower {I : Type*} [Fintype I] (φ : ι → ℝ) (ρ : I → Fin 4)
    (K : I → Fld ι F →ₗ[ℝ] Fld ι F) (n y σ : ℝ) (hn : 0 ≤ n)
    (hK : ∀ i, FO φ (K i) n y σ) (h : VF ι F) :
    ‖rowL ρ K h‖ ^ 2 - (2 * n * y + σ ^ 2) * (∑ i, ‖h (ρ i)‖) ^ 2 ≤
      ⟪rowL ρ K (Wt φ h), rowL ρ K (Wt (-φ) h)⟫ := by
  set t := ∑ i, ‖h (ρ i)‖ with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set a := ∑ i, ev φ (K i) (h (ρ i)) with ha
  set b := ∑ i, od φ (K i) (h (ρ i)) with hb
  set u := rowL ρ K h with hu
  have hq : Mw φ (rowL ρ K (Wt (-φ) h)) = a + b := by
    rw [rowL_apply, map_sum, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cj_eq_add]
    rfl
  have hp : Mw (-φ) (rowL ρ K (Wt φ h)) = a - b := by
    rw [rowL_apply, map_sum, ha, hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← cj_neg_eq_sub, cj_apply, neg_neg]
    rfl
  have hin : ⟪rowL ρ K (Wt φ h), rowL ρ K (Wt (-φ) h)⟫ = ⟪a - b, a + b⟫ := by
    rw [← hp, ← hq, inner_Mw, Mw_neg_Mw]
  have hdiff : ⟪a - b, a + b⟫ = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
    rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm a b]
    ring
  have hub : ‖u‖ ≤ n * t := by
    rw [hu, rowL_apply, ht, Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (hK i).norm _)
  have hbb : ‖b‖ ≤ σ * t := by
    rw [ht, Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (hK i).odd _)
  have hcb : ‖a - u‖ ≤ y * t := by
    have e : a - u = ∑ i, (ev φ (K i) (h (ρ i)) - K i (h (ρ i))) := by
      rw [hu, rowL_apply, ha, Finset.sum_sub_distrib]
    rw [e, ht, Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (hK i).even _)
  have ha2 : ‖u‖ ^ 2 - 2 * (n * t) * (y * t) ≤ ‖a‖ ^ 2 := by
    have e : a = u + (a - u) := by abel
    have h1 : ‖a‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, a - u⟫ + ‖a - u‖ ^ 2 := by
      conv_lhs => rw [e]
      exact norm_add_sq_real _ _
    have h2 : -(‖u‖ * ‖a - u‖) ≤ ⟪u, a - u⟫ := by
      have := abs_real_inner_le_norm u (a - u)
      linarith only [(abs_le.1 this).1]
    have h3 : ‖u‖ * ‖a - u‖ ≤ (n * t) * (y * t) :=
      mul_le_mul hub hcb (norm_nonneg _) (by positivity)
    nlinarith only [h1, h2, h3, sq_nonneg ‖a - u‖]
  have hb2 : ‖b‖ ^ 2 ≤ (σ * t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbb 2
  rw [hin, hdiff]
  nlinarith only [ha2, hb2]

/-! ### The weighted estimate -/

/-- The Agmon step. If `B` stays coercive after conjugation by opposite weights on a subspace preserved
by weights, the solution of the weak equation inherits the weight of its source. -/
theorem agmon (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (φ : ι → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hV : ∀ (ψ : ι → ℝ) h, P h → P (Wt ψ h))
    (hconj : ∀ h, P h → κ * nsq h ≤ B (Wt φ h) (Wt (-φ) h))
    (g s : VF ι F) (hg : P g) (hs : ∀ f, P f → B f g = ip f s) :
    κ ^ 2 * nsq (Wt φ g) ≤ nsq (Wt φ s) := by
  set h := Wt φ g with hh
  have hPh : P h := hV φ g hg
  have h1 := hconj h hPh
  have e : Wt (-φ) h = g := Wt_neg_Wt φ g
  rw [e, hs _ (hV φ h hPh), ip_Wt] at h1
  have h2 := ip_sq_le h (Wt φ s)
  have hn := nsq_nonneg h
  have hm := nsq_nonneg (Wt φ s)
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hm
  · have h3 : (κ * nsq h) ^ 2 ≤ nsq h * nsq (Wt φ s) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    have h4 : nsq h * (κ ^ 2 * nsq h) ≤ nsq h * nsq (Wt φ s) := by
      nlinarith only [h3]
    exact le_of_mul_le_mul_left h4 hpos

/-- The weak equation has one solution, in any finite-dimensional setting with a coercive form. -/
theorem exists_unique_solution [FiniteDimensional ℝ F] (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ)
    (V : Submodule ℝ (VF ι F)) (c : ℝ) (hc : 0 < c) (hB : ∀ h ∈ V, c * nsq h ≤ B h h)
    (s : VF ι F) : ∃! g, g ∈ V ∧ ∀ f ∈ V, B f g = ip f s := by
  have hinj0 (g : VF ι F) (hg : g ∈ V) (h0 : B g g = 0) : g = 0 := by
    have := hB g hg
    rw [h0] at this
    refine nsq_eq_zero ?_
    by_contra hneg
    have : 0 < c * nsq g := mul_pos hc (not_le.1 hneg)
    linarith only [this, ‹c * nsq g ≤ 0›]
  let Φ : V →ₗ[ℝ] Module.Dual ℝ V := B.flip.domRestrict₁₂ V V
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : B g g = 0 := by
      have := LinearMap.congr_fun hg g
      simpa [Φ] using this
    exact Subtype.ext (hinj0 g g.2 h0)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hΦ
  let ℓ : Module.Dual ℝ V :=
    { toFun := fun f => ip (f : VF ι F) s
      map_add' := fun a b => by
        simp [ip, inner_add_left, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp [ip, inner_smul_left, Finset.mul_sum] }
  obtain ⟨g, hg⟩ := hsurj ℓ
  refine ⟨g, ⟨g.2, fun f hf => ?_⟩, ?_⟩
  · have := LinearMap.congr_fun hg ⟨f, hf⟩
    simpa [Φ, ℓ] using this
  · rintro g' ⟨hg'V, hg'⟩
    have hsame : ∀ f, f ∈ V → B f (g' - g) = 0 := by
      intro f hf
      have := LinearMap.congr_fun hg ⟨f, hf⟩
      have h1 : B f g = ip f s := by simpa [Φ, ℓ] using this
      rw [map_sub, hg' f hf, h1, sub_self]
    have hd : g' - (g : VF ι F) ∈ V := V.sub_mem hg'V g.2
    have := hinj0 _ hd (hsame _ hd)
    exact sub_eq_zero.1 this

/-! ### The fluctuation form -/

/-- The bilinear form of a first-order operator. -/
def bil (G : VF ι F →ₗ[ℝ] Fld ι F) : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ :=
  (innerₗ (Fld ι F)).compl₁₂ G G

theorem bil_apply (G : VF ι F →ₗ[ℝ] Fld ι F) (f g : VF ι F) : bil G f g = ⟪G f, G g⟫ := rfl

/-- The curl component in a plane, as a row. -/
def curlRow (A : Fin 4 → Shift (Fld ι F)) (μ ν : Fin 4) : VF ι F →ₗ[ℝ] Fld ι F :=
  rowL ![ν, μ] ![(A μ).T - 1, -((A ν).T - 1)]

theorem curlRow_apply (A : Fin 4 → Shift (Fld ι F)) (μ ν : Fin 4) (f : VF ι F) :
    curlRow A μ ν f = curl A f μ ν := by
  simp [curlRow, rowL_apply, Fin.sum_univ_two, curl, Shift.D, sub_eq_add_neg]

/-- The divergence, as a row. -/
def divRow (A : Fin 4 → Shift (Fld ι F)) : VF ι F →ₗ[ℝ] Fld ι F :=
  rowL id fun μ => (A μ).S - 1

theorem divRow_apply (A : Fin 4 → Shift (Fld ι F)) (f : VF ι F) : divRow A f = div A f := by
  simp [divRow, rowL_apply, div, Shift.Dstar]

/-- One block-average component, as a row. -/
def blockRow (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (μ : Fin 4) : VF ι F →ₗ[ℝ] Fld ι F :=
  rowL (fun _ : Fin 1 => μ) fun _ => blockL A L

theorem blockRow_apply (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (μ : Fin 4) (f : VF ι F) :
    blockRow A L μ f = blockAvg A L (f μ) := by
  simp [blockRow, rowL_apply, blockL_apply]

/-- **The fluctuation form:** curl energy, divergence, and `p` times the block penalty. -/
def fluct (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (p : ℝ) : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ :=
  ∑ μ, ∑ ν, (if μ < ν then bil (curlRow A μ ν) else 0) + bil (divRow A) +
    p • ∑ μ, bil (blockRow A L μ)

theorem fluct_apply (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (p : ℝ) (f g : VF ι F) :
    fluct A L p f g = ∑ μ, ∑ ν, (if μ < ν then ⟪curl A f μ ν, curl A g μ ν⟫ else 0) +
      ⟪div A f, div A g⟫ + p * ∑ μ, ⟪blockAvg A L (f μ), blockAvg A L (g μ)⟫ := by
  have h1 (μ ν : Fin 4) : (if μ < ν then bil (curlRow A μ ν) else 0) f g =
      if μ < ν then ⟪curl A f μ ν, curl A g μ ν⟫ else 0 := by
    split_ifs
    · rw [bil_apply, curlRow_apply, curlRow_apply]
    · rfl
  simp only [fluct, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, h1, bil_apply,
    divRow_apply, blockRow_apply, smul_eq_mul]

theorem fluct_self (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (p : ℝ) (f : VF ι F) :
    fluct A L p f f = curlEnergy A f + ‖div A f‖ ^ 2 + p * ∑ μ, ‖blockAvg A L (f μ)‖ ^ 2 := by
  rw [fluct_apply]
  simp only [real_inner_self_eq_norm_sq, curlEnergy]

theorem fluct_comm (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (p : ℝ) (f g : VF ι F) :
    fluct A L p f g = fluct A L p g f := by
  rw [fluct_apply, fluct_apply]
  simp only [real_inner_comm]

/-- The cost of the weight on the fluctuation form. Of second order in `m`. -/
def Err (m : ℝ) (L : ℕ) (p : ℝ) : ℝ :=
  40 * (Real.cosh m - 1) + 10 * Real.sinh m ^ 2 +
    p * (2 * (Real.cosh (4 * L * m) - 1) + Real.sinh (4 * L * m) ^ 2)

theorem plane_bound (h : VF ι F) :
    ∑ μ, ∑ ν, (if μ < ν then (‖h ν‖ + ‖h μ‖) ^ 2 else 0) ≤ 6 * nsq h := by
  simp only [nsq, Fin.sum_univ_four]
  simp (decide := true) only [if_true, if_false]
  generalize ‖h 0‖ = a
  generalize ‖h 1‖ = b
  generalize ‖h 2‖ = c
  generalize ‖h 3‖ = e
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

theorem four_bound (h : VF ι F) : (∑ μ, ‖h μ‖) ^ 2 ≤ 4 * nsq h := by
  simp only [nsq, Fin.sum_univ_four]
  generalize ‖h 0‖ = a
  generalize ‖h 1‖ = b
  generalize ‖h 2‖ = c
  generalize ‖h 3‖ = e
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

/-- Conjugating the divergence term. -/
theorem div_conj (A : Fin 4 → Shift (Fld ι F)) (φ : ι → ℝ) (m : ℝ)
    (hS : ∀ μ, Tame φ (A μ).S m) (h : VF ι F) :
    ‖div A h‖ ^ 2 - (2 * 2 * (Real.cosh m - 1) + Real.sinh m ^ 2) * (4 * nsq h) ≤
      ⟪div A (Wt φ h), div A (Wt (-φ) h)⟫ := by
  have hy1 : 0 ≤ Real.cosh m - 1 := by linarith only [Real.one_le_cosh m]
  have hdiv := row_lower φ id (fun μ => (A μ).S - 1) 2 _ _ (by norm_num)
    (fun μ => FO_sub_one (hS μ)) h
  have e2 : rowL id (fun μ => (A μ).S - 1) = divRow A := rfl
  rw [e2, divRow_apply, divRow_apply, divRow_apply] at hdiv
  have hE : 0 ≤ 2 * 2 * (Real.cosh m - 1) + Real.sinh m ^ 2 := by positivity
  exact le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_left (four_bound h) hE) _) hdiv

/-- Conjugating the block penalty. -/
theorem block_conj (A : Fin 4 → Shift (Fld ι F)) (φ : ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hT : ∀ μ, Tame φ (A μ).T m) (L : ℕ) (hL : 1 ≤ L) (h : VF ι F) :
    ∑ μ, ‖blockAvg A L (h μ)‖ ^ 2 -
      (2 * 1 * (Real.cosh (4 * L * m) - 1) + Real.sinh (4 * L * m) ^ 2) * nsq h ≤
      ∑ μ, ⟪blockAvg A L ((Wt φ h) μ), blockAvg A L ((Wt (-φ) h) μ)⟫ := by
  have hB := tame_block A hT hm L hL
  have hblock (μ : Fin 4) := row_lower φ (fun _ : Fin 1 => μ) (fun _ => blockL A L) 1 _ _
    (by norm_num) (fun _ => FO_of_tame hB) h
  unfold nsq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  have := hblock μ
  have e1 : rowL (fun _ : Fin 1 => μ) (fun _ => blockL A L) = blockRow A L μ := rfl
  rw [e1, blockRow_apply, blockRow_apply, blockRow_apply] at this
  simpa using this

/-- **Combes-Thomas for the first-order forms.** Conjugating the form by opposite weights costs only
second order in the weight's gradient. -/
theorem fluct_conj (A : Fin 4 → Shift (Fld ι F)) (φ : ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hT : ∀ μ, Tame φ (A μ).T m) (hS : ∀ μ, Tame φ (A μ).S m) (L : ℕ) (hL : 1 ≤ L) (p : ℝ)
    (hp : 0 ≤ p) (h : VF ι F) :
    fluct A L p h h - Err m L p * nsq h ≤ fluct A L p (Wt φ h) (Wt (-φ) h) := by
  have hy1 : 0 ≤ Real.cosh m - 1 := by linarith only [Real.one_le_cosh m]
  have hcurl (μ ν : Fin 4) := row_lower φ ![ν, μ] ![(A μ).T - 1, -((A ν).T - 1)] 2 _ _ (by norm_num)
    (fun i => by
      fin_cases i
      · exact FO_sub_one (hT μ)
      · exact (FO_sub_one (hT ν)).neg) h
  have hcsum : ∑ μ, ∑ ν, (if μ < ν then ‖curl A h μ ν‖ ^ 2 else 0) -
      (2 * 2 * (Real.cosh m - 1) + Real.sinh m ^ 2) * (6 * nsq h) ≤
      ∑ μ, ∑ ν, (if μ < ν then ⟪curl A (Wt φ h) μ ν, curl A (Wt (-φ) h) μ ν⟫ else 0) := by
    have hE : 0 ≤ 2 * 2 * (Real.cosh m - 1) + Real.sinh m ^ 2 := by positivity
    refine le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_left (plane_bound h) hE) _) ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ν _ => ?_
    split_ifs with hlt
    · have := hcurl μ ν
      have e1 : rowL ![ν, μ] ![(A μ).T - 1, -((A ν).T - 1)] = curlRow A μ ν := rfl
      rw [e1, curlRow_apply, curlRow_apply, curlRow_apply, Fin.sum_univ_two] at this
      simpa using this
    · simp
  have hdiv' := div_conj A φ m hS h
  have hb' := mul_le_mul_of_nonneg_left (block_conj A φ m hm hT L hL h) hp
  rw [fluct_self, fluct_apply]
  unfold Err curlEnergy
  nlinarith only [hcsum, hdiv', hb']

/-! ### From a weighted estimate to pointwise decay -/

open Classical in
/-- The source supported at one link. -/
def pt (μ : Fin 4) (y : ι) (v : F) : VF ι F := fun ν =>
  WithLp.toLp 2 fun x => if ν = μ ∧ x = y then v else 0

theorem ip_pt (f : VF ι F) (μ : Fin 4) (y : ι) (v : F) : ip f (pt μ y v) = ⟪f μ y, v⟫ := by
  classical
  unfold ip
  rw [Finset.sum_eq_single μ, PiLp.inner_apply, Finset.sum_eq_single y]
  · simp [pt]
  · intro x _ hx
    simp [pt, hx]
  · simp
  · intro ν _ hν
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [pt, hν]
  · simp

theorem nsq_Wt_pt (φ : ι → ℝ) (μ : Fin 4) (y : ι) (v : F) :
    nsq (Wt φ (pt μ y v)) = (Real.exp (φ y) * ‖v‖) ^ 2 := by
  classical
  unfold nsq
  rw [Finset.sum_eq_single μ, norm_sq_fld, Finset.sum_eq_single y]
  · simp [Wt, Mw_apply, pt, norm_smul, abs_of_pos (Real.exp_pos _)]
  · intro x _ hx
    simp [Wt, Mw_apply, pt, hx]
  · simp
  · intro ν _ hν
    rw [norm_sq_fld]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Wt, Mw_apply, pt, hν]
  · simp

theorem point_le_nsq (φ : ι → ℝ) (g : VF ι F) (ν : Fin 4) (x : ι) :
    (Real.exp (φ x) * ‖g ν x‖) ^ 2 ≤ nsq (Wt φ g) := by
  have h1 : ‖Wt φ g ν x‖ ^ 2 ≤ ‖Wt φ g ν‖ ^ 2 := by
    rw [norm_sq_fld]
    exact Finset.single_le_sum (f := fun x => ‖Wt φ g ν x‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ x)
  have h2 : ‖Wt φ g ν‖ ^ 2 ≤ nsq (Wt φ g) :=
    Finset.single_le_sum (f := fun ν => ‖Wt φ g ν‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ν)
  have e : ‖Wt φ g ν x‖ = Real.exp (φ x) * ‖g ν x‖ := by
    change ‖Real.exp (φ x) • g ν x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [e] at h1
  exact h1.trans h2

/-- **Pointwise decay.** The value at `x` of the solution with a source at `y` is bounded by the weight
difference. -/
theorem green_decay (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (φ : ι → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hV : ∀ (ψ : ι → ℝ) h, P h → P (Wt ψ h))
    (hconj : ∀ h, P h → κ * nsq h ≤ B (Wt φ h) (Wt (-φ) h))
    (g : VF ι F) (hg : P g) (μ : Fin 4) (y : ι) (v : F)
    (hs : ∀ f, P f → B f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : ι) :
    κ * ‖g ν x‖ ≤ Real.exp (φ y - φ x) * ‖v‖ := by
  have h1 := agmon B P φ κ hκ hV hconj g (pt μ y v) hg (fun f hf => by rw [hs f hf, ip_pt])
  rw [nsq_Wt_pt] at h1
  have h2 := point_le_nsq φ g ν x
  have h3 : (κ * (Real.exp (φ x) * ‖g ν x‖)) ^ 2 ≤ (Real.exp (φ y) * ‖v‖) ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h1
  have h4 := abs_le_of_sq_le_sq' h3 (by positivity)
  have h5 : Real.exp (φ x) * (κ * ‖g ν x‖) ≤ Real.exp (φ x) * (Real.exp (φ y - φ x) * ‖v‖) := by
    have e : Real.exp (φ x) * (Real.exp (φ y - φ x) * ‖v‖) = Real.exp (φ y) * ‖v‖ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e]
    nlinarith only [h4.2]
  exact le_of_mul_le_mul_left h5 (Real.exp_pos _)

/-- The `L²` bound on the same solution. -/
theorem spectral_bound (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (c : ℝ) (hc : 0 < c)
    (hB : ∀ h, P h → c * nsq h ≤ B h h) (g s : VF ι F) (hg : P g)
    (hs : ∀ f, P f → B f g = ip f s) : c ^ 2 * nsq g ≤ nsq s := by
  have h1 := hB g hg
  rw [hs g hg] at h1
  have h2 := ip_sq_le g s
  have hn := nsq_nonneg g
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact nsq_nonneg s
  · have h3 : (c * nsq g) ^ 2 ≤ nsq g * nsq s :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    have h4 : nsq g * (c ^ 2 * nsq g) ≤ nsq g * nsq s := by
      nlinarith only [h3]
    exact le_of_mul_le_mul_left h4 hpos

/-- The solution operator of a symmetric form is symmetric, and positive with the same constant. This is
what makes it a covariance. That it is the covariance of the Gaussian with density `exp (-B/2)` is the
standard integral, which is not formalized here. -/
theorem green_symm (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop)
    (hsym : ∀ f g, B f g = B g f) (g g' s s' : VF ι F) (hg : P g) (hg' : P g')
    (hs : ∀ f, P f → B f g = ip f s) (hs' : ∀ f, P f → B f g' = ip f s') :
    ip g' s = ip g s' := by
  rw [← hs g' hg', ← hs' g hg, hsym]

theorem Wt_zero (h : VF ι F) : Wt (fun _ => 0) h = h := by
  funext μ
  ext x : 1
  simp [Wt, Mw_apply]

/-- **The energy-norm weighted estimate.** If the weighted form keeps a fraction `θ` of the energy and the energy
controls point values with constant `C`, then the solution with a source at `y` satisfies the bound below. Unlike
`green_decay`, the prefactor does not contain the spectral floor. -/
theorem green_energy (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (φ : ι → ℝ) (θ C : ℝ)
    (hθ : 0 < θ) (hC : 0 ≤ C) (hV : ∀ (ψ : ι → ℝ) h, P h → P (Wt ψ h))
    (hconj : ∀ h, P h → θ * B h h ≤ B (Wt φ h) (Wt (-φ) h))
    (hpt : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ C * B h h)
    (g : VF ι F) (hg : P g) (μ : Fin 4) (y : ι) (v : F)
    (hs : ∀ f, P f → B f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : ι) :
    θ * ‖g ν x‖ ≤ C * Real.exp (φ y - φ x) * ‖v‖ := by
  set h := Wt φ g with hh
  have hPh : P h := hV _ _ hg
  have e1 : Wt (-φ) h = g := Wt_neg_Wt φ g
  have h1 := hconj h hPh
  rw [e1, hs _ (hV _ _ hPh)] at h1
  have e2 : (Wt φ h) μ y = Real.exp (φ y) • h μ y := rfl
  rw [e2, real_inner_smul_left] at h1
  set E := Real.exp (φ y) * ‖v‖ with hE
  have hE0 : 0 ≤ E := by positivity
  set A := ‖h μ y‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have h2 : θ * B h h ≤ E * A := by
    refine h1.trans ?_
    have := real_inner_le_norm (h μ y) v
    rw [hE, mul_assoc, mul_comm ‖v‖ A]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  have h3 : A ^ 2 ≤ C * B h h := hpt h hPh μ y
  have h4 : θ * A ≤ C * E := by
    rcases hA0.eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      positivity
    · have : A * (θ * A) ≤ A * (C * E) := by
        have m1 := mul_le_mul_of_nonneg_left h3 hθ.le
        have m2 := mul_le_mul_of_nonneg_left h2 hC
        nlinarith only [m1, m2]
      exact le_of_mul_le_mul_left this hpos
  set w := ‖h ν x‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  have h5 : w ^ 2 ≤ C * B h h := hpt h hPh ν x
  have h6 : (θ * w) ^ 2 ≤ (C * E) ^ 2 := by
    have m1 := mul_le_mul_of_nonneg_left h5 (sq_nonneg θ)
    have m2 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hθ.le)
    have m3 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC hE0)
    nlinarith only [m1, m2, m3]
  have h7 : θ * w ≤ C * E := (abs_le_of_sq_le_sq' h6 (by positivity)).2
  have e3 : w = Real.exp (φ x) * ‖g ν x‖ := by
    change ‖Real.exp (φ x) • g ν x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h8 : Real.exp (φ x) * (θ * ‖g ν x‖) ≤ Real.exp (φ x) * (C * Real.exp (φ y - φ x) * ‖v‖) := by
    have e : Real.exp (φ x) * (C * Real.exp (φ y - φ x) * ‖v‖) = C * E := by
      have : Real.exp (φ x) * Real.exp (φ y - φ x) = Real.exp (φ y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hE, ← this]
      ring
    rw [e]
    rw [e3] at h7
    linarith only [h7]
  exact le_of_mul_le_mul_left h8 (Real.exp_pos _)

/-- The unweighted case: the point value of the solution is at most `C` times the source, at every distance. -/
theorem green_point (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (C : ℝ) (hC : 0 ≤ C)
    (hV : ∀ (ψ : ι → ℝ) h, P h → P (Wt ψ h))
    (hpt : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ C * B h h)
    (g : VF ι F) (hg : P g) (μ : Fin 4) (y : ι) (v : F)
    (hs : ∀ f, P f → B f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : ι) : ‖g ν x‖ ≤ C * ‖v‖ := by
  have e0 : (-fun _ : ι => (0 : ℝ)) = fun _ => 0 := by
    funext z
    simp
  have key := green_energy B P (fun _ => 0) 1 C one_pos hC hV
    (fun h _ => by rw [e0, Wt_zero, one_mul]) hpt g hg μ y v hs ν x
  simpa using key

/-- The solution with an `L²` source: coercivity with constant `c` and a point-energy constant `C` give
`c ‖g ν x‖² ≤ C ‖s‖²`. For a source spread over a box of side `L` with total mass one, `‖s‖² = L⁻⁴`. -/
theorem green_source (B : VF ι F →ₗ[ℝ] VF ι F →ₗ[ℝ] ℝ) (P : VF ι F → Prop) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : ∀ h, P h → c * nsq h ≤ B h h) (hpt : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ C * B h h)
    (g s : VF ι F) (hg : P g) (hs : ∀ f, P f → B f g = ip f s) (ν : Fin 4) (x : ι) :
    c * ‖g ν x‖ ^ 2 ≤ C * nsq s := by
  have h1 := hB g hg
  have h2 := ip_sq_le g s
  have h3 := hpt g hg ν x
  rw [hs g hg] at h1 h3
  have hg0 := nsq_nonneg g
  have hs0 := nsq_nonneg s
  have h4 : c * ip g s ≤ nsq s := by
    rcases hg0.eq_or_lt with h0 | hpos
    · have : ip g s ^ 2 ≤ 0 := by
        rw [← h0, zero_mul] at h2
        exact h2
      have h5 : ip g s = 0 := by nlinarith only [this, sq_nonneg (ip g s)]
      rw [h5, mul_zero]
      exact hs0
    · have h5 : (c * nsq g) ^ 2 ≤ ip g s ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have h6 : c ^ 2 * nsq g ≤ nsq s := by
        have : nsq g * (c ^ 2 * nsq g) ≤ nsq g * nsq s := by nlinarith only [h5, h2]
        exact le_of_mul_le_mul_left this hpos
      have h7 : (c * ip g s) ^ 2 ≤ nsq s ^ 2 := by
        have m := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
        have m2 := mul_le_mul_of_nonneg_right h6 hs0
        nlinarith only [m, m2]
      exact (abs_le_of_sq_le_sq' h7 hs0).2
  have m := mul_le_mul_of_nonneg_left h3 hc.le
  have m2 := mul_le_mul_of_nonneg_left h4 hC
  nlinarith only [m, m2]

/-- The form is bounded above, so the spectrum lies in an interval whose top does not see the lattice. -/
theorem fluct_le (A : Fin 4 → Shift (Fld ι F)) (L : ℕ) (hL : 1 ≤ L) (p : ℝ) (hp : 0 ≤ p)
    (h : VF ι F) : fluct A L p h h ≤ (40 + p) * nsq h := by
  have hD (B : Shift (Fld ι F)) (x : Fld ι F) : ‖B.D x‖ ≤ 2 * ‖x‖ := by
    unfold Shift.D
    refine (norm_sub_le _ _).trans ?_
    rw [B.norm_T]
    linarith only []
  have hDs (B : Shift (Fld ι F)) (x : Fld ι F) : ‖B.Dstar x‖ ≤ 2 * ‖x‖ := by
    rw [B.norm_Dstar]
    exact hD B x
  have hc (μ ν : Fin 4) : ‖curl A h μ ν‖ ^ 2 ≤ 4 * (‖h ν‖ + ‖h μ‖) ^ 2 := by
    have h1 : ‖curl A h μ ν‖ ≤ 2 * (‖h ν‖ + ‖h μ‖) := by
      unfold curl
      refine (norm_sub_le _ _).trans ?_
      linarith only [hD (A μ) (h ν), hD (A ν) (h μ)]
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith only [this]
  have hcs : curlEnergy A h ≤ 4 * (6 * nsq h) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (plane_bound h) (by norm_num))
    unfold curlEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    split_ifs
    · exact hc μ ν
    · simp
  have hds : ‖div A h‖ ^ 2 ≤ 4 * (4 * nsq h) := by
    have h1 : ‖div A h‖ ≤ 2 * ∑ μ, ‖h μ‖ := by
      unfold div
      rw [Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => hDs _ _)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := four_bound h
    nlinarith only [h2, h3]
  have hbs : ∑ μ, ‖blockAvg A L (h μ)‖ ^ 2 ≤ nsq h := by
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 : ‖blockAvg A L (h μ)‖ ≤ ‖h μ‖ := by
      unfold blockAvg
      refine (norm_avg_le _ L hL _).trans ((norm_avg_le _ L hL _).trans
        ((norm_avg_le _ L hL _).trans (norm_avg_le _ L hL _)))
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hm := mul_le_mul_of_nonneg_left hbs hp
  rw [fluct_self]
  nlinarith only [hcs, hds, hm]

/-- **The decay theorem for the form with block penalty, on any lattice shift family.** -/
theorem fluct_decay (A : Fin 4 → Shift (Fld ι F)) (π : Fin 4 → ι ≃ ι)
    (hA : ∀ μ, Intertwines (π μ) (A μ).T) (φ : ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hφ : ∀ μ x, |φ x - φ (π μ x)| ≤ m) (L : ℕ) (hL : 1 ≤ L) (p : ℝ) (hp : 0 ≤ p)
    (P : VF ι F → Prop) (hV : ∀ (ψ : ι → ℝ) h, P h → P (Wt ψ h)) (c : ℝ)
    (hc : ∀ h, P h → c * nsq h ≤ fluct A L p h h) (hκ : 0 < c - Err m L p)
    (g : VF ι F) (hg : P g) (μ : Fin 4) (y : ι) (v : F)
    (hs : ∀ f, P f → fluct A L p f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : ι) :
    (c - Err m L p) * ‖g ν x‖ ≤ Real.exp (φ y - φ x) * ‖v‖ := by
  refine green_decay (fluct A L p) P φ _ hκ hV (fun h hP => ?_) g hg μ y v hs ν x
  have h1 := hc h hP
  have h2 := fluct_conj A φ m hm (fun μ => tame_T _ (π μ) (hA μ) hm (hφ μ))
    (fun μ => tame_S _ (π μ) (hA μ) hm (hφ μ)) L hL p hp h
  rw [sub_mul]
  linarith only [h1, h2]

end Weights

/-! ### Numerical bounds on the weight's cost -/

theorem cosh_sub_one_le (x : ℝ) (hx : |x| ≤ 1 / 2) : Real.cosh x - 1 ≤ 3 / 5 * x ^ 2 := by
  have hsq : x ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at this
    linarith only [this]
  set u := x ^ 2 / 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 8 := by rw [hu]; linarith only [hsq]
  have h1 := Real.cosh_le_exp_half_sq x
  have h2 := Real.exp_bound_div_one_sub_of_interval hu0 (by linarith only [hu1])
  have h3 : 1 / (1 - u) ≤ 1 + 6 / 5 * u := by
    rw [div_le_iff₀ (by linarith only [hu1])]
    nlinarith only [hu0, hu1, mul_nonneg hu0 (sub_nonneg.2 hu1)]
  have e : 3 / 5 * x ^ 2 = 6 / 5 * u := by rw [hu]; ring
  rw [e]
  linarith only [h1, h2, h3]

theorem sinh_sq_le (x : ℝ) (hx : |x| ≤ 1 / 2) : Real.sinh x ^ 2 ≤ 4 / 3 * x ^ 2 := by
  have hsq : x ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at this
    linarith only [this]
  have h1 := cosh_sub_one_le x hx
  have h2 := Real.one_le_cosh x
  have h3 := Real.cosh_sq x
  set y := Real.cosh x - 1 with hy
  have e : Real.sinh x ^ 2 = y * (y + 2) := by
    rw [hy]
    nlinarith only [h3]
  rw [e]
  have hy0 : 0 ≤ y := by rw [hy]; linarith only [h2]
  have hx0 := sq_nonneg x
  nlinarith only [h1, hy0, hx0, hsq, mul_nonneg hy0 hx0, mul_nonneg hx0 (sub_nonneg.2 hsq),
    mul_nonneg (sub_nonneg.2 h1) hy0, mul_nonneg (sub_nonneg.2 h1) hx0]

/-- With the penalty of `block_coercive`. -/
theorem Err_block_le (m : ℝ) (L : ℕ) (hL : 1 ≤ L) (hm0 : 0 ≤ m) (hm : 4 * L * m ≤ 1 / 2) :
    Err m L (1 / (4 * (L : ℝ) ^ 2)) ≤ 712 / 15 * m ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  have hmh : m ≤ 1 / 2 := by nlinarith only [hm, hm0, hL1]
  have hab : |m| ≤ 1 / 2 := by rwa [abs_of_nonneg hm0]
  have ht0 : 0 ≤ 4 * (L : ℝ) * m := by positivity
  have hab2 : |4 * (L : ℝ) * m| ≤ 1 / 2 := by rwa [abs_of_nonneg ht0]
  have h1 := cosh_sub_one_le m hab
  have h2 := sinh_sq_le m hab
  have h3 := cosh_sub_one_le _ hab2
  have h4 := sinh_sq_le _ hab2
  have h5 : 2 * (Real.cosh (4 * L * m) - 1) + Real.sinh (4 * L * m) ^ 2 ≤
      38 / 15 * (16 * (L : ℝ) ^ 2 * m ^ 2) := by
    have e : (4 * (L : ℝ) * m) ^ 2 = 16 * (L : ℝ) ^ 2 * m ^ 2 := by ring
    rw [e] at h3 h4
    linarith only [h3, h4]
  have hp : 0 ≤ 1 / (4 * (L : ℝ) ^ 2) := by positivity
  have h6 := mul_le_mul_of_nonneg_left h5 hp
  have e2 : 1 / (4 * (L : ℝ) ^ 2) * (38 / 15 * (16 * (L : ℝ) ^ 2 * m ^ 2)) = 152 / 15 * m ^ 2 := by
    field_simp
    ring
  rw [e2] at h6
  unfold Err
  linarith only [h1, h2, h6]

/-! ### The distance on the torus -/

section Torus

open PeriodicLattice4

theorem cast_abs_le_one (p q : ℕ) (h1 : (p : ℤ) - q ≤ 1) (h2 : -1 ≤ (p : ℤ) - q) :
    |(p : ℝ) - q| ≤ 1 := by
  have h : |(p : ℤ) - q| ≤ 1 := abs_le.2 ⟨h2, h1⟩
  have := (Int.cast_le (R := ℝ)).2 h
  push_cast at this
  exact this

theorem natAbs_valMinAbs_succ {N : ℕ} [NeZero N] (a : ZMod N) :
    |((a + 1).valMinAbs.natAbs : ℝ) - a.valMinAbs.natAbs| ≤ 1 := by
  have hN : 0 < N := NeZero.pos N
  have hk := a.valMinAbs_mem_Ioc
  set k := a.valMinAbs with hkdef
  have hcoe : ((k : ZMod N)) = a := a.coe_valMinAbs
  by_cases hin : (k + 1) * 2 ∈ Set.Ioc (-(N : ℤ)) N
  · have hv : (a + 1).valMinAbs = k + 1 :=
      (ZMod.valMinAbs_spec _ _).2 ⟨by push_cast; rw [hcoe], hin⟩
    rw [hv]
    exact cast_abs_le_one _ _ (by omega) (by omega)
  · have hk1 := hk.1
    have hk2 := hk.2
    have hout : N < (k + 1) * 2 := by
      by_contra hle
      exact hin ⟨by omega, by omega⟩
    have hv : (a + 1).valMinAbs = k + 1 - N := by
      refine (ZMod.valMinAbs_spec _ _).2 ⟨?_, ?_⟩
      · push_cast
        rw [hcoe]
        simp
      · constructor <;> omega
    rw [hv]
    exact cast_abs_le_one _ _ (by omega) (by omega)

/-- The graph distance on the torus, as a sum over the four directions of the circular distance. -/
def dist1 {N : ℕ} [NeZero N] (x y : Vertex N) : ℕ := ∑ μ, (x μ - y μ).valMinAbs.natAbs

theorem dist1_self {N : ℕ} [NeZero N] (y : Vertex N) : dist1 y y = 0 := by
  simp [dist1]

theorem dist1_step {N : ℕ} [NeZero N] (x y : Vertex N) (μ : Fin 4) :
    |(dist1 (step N x μ) y : ℝ) - dist1 x y| ≤ 1 := by
  unfold dist1
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single μ]
  · have e : step N x μ μ - y μ = (x μ - y μ) + 1 := by
      simp [step]
      ring
    rw [e]
    exact natAbs_valMinAbs_succ _
  · intro ρ _ hρ
    have : step N x μ ρ = x ρ := by simp [step, hρ]
    rw [this, sub_self]
  · simp

/-- The weight `m · dist(·, y)`. -/
def distW {N : ℕ} [NeZero N] (m : ℝ) (y : Vertex N) (x : Vertex N) : ℝ := m * dist1 x y

theorem distW_lip {N : ℕ} [NeZero N] (m : ℝ) (hm : 0 ≤ m) (y x : Vertex N) (μ : Fin 4) :
    |distW m y x - distW m y (step N x μ)| ≤ m := by
  unfold distW
  rw [← mul_sub, abs_mul, abs_of_nonneg hm, abs_sub_comm]
  have := mul_le_mul_of_nonneg_left (dist1_step x y μ) hm
  rwa [mul_one] at this

theorem distW_diff {N : ℕ} [NeZero N] (m : ℝ) (x y : Vertex N) :
    distW m y y - distW m y x = -(m * dist1 x y) := by
  simp [distW, dist1_self]

end Torus

/-! ### Dyadic averages of commuting shifts -/

section Dyadic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem savg_add (A : Shift E) (L : ℕ) (x y : E) :
    savg A L (x + y) = savg A L x + savg A L y := by
  simp only [savg, map_add, Finset.sum_add_distrib, smul_add]

theorem savg_sub (A : Shift E) (L : ℕ) (x y : E) :
    savg A L (x - y) = savg A L x - savg A L y := by
  simp only [savg, map_sub, Finset.sum_sub_distrib, smul_sub]

theorem savg_smul (A : Shift E) (L : ℕ) (c : ℝ) (x : E) :
    savg A L (c • x) = c • savg A L x := by
  simp only [savg, map_smul, ← Finset.smul_sum]
  rw [smul_comm]

theorem savg_one (A : Shift E) (x : E) : savg A 1 x = x := by
  simp [savg, spow]

theorem spow_add (A : Shift E) (i j : ℕ) (x : E) : spow A (i + j) x = spow A i (spow A j x) := by
  simp only [spow, pow_add, Module.End.mul_apply]

/-- The average of a point and its translate by `ℓ`. -/
def dbl (A : Shift E) (l : ℕ) (x : E) : E := (1 / 2 : ℝ) • (x + spow A l x)

theorem savg_two_mul (A : Shift E) (l : ℕ) (hl : 1 ≤ l) (x : E) :
    savg A (2 * l) x = savg A l (dbl A l x) := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (0 : ℝ) < l := by exact_mod_cast hl
    exact this.ne'
  unfold dbl
  rw [savg_smul, savg_add]
  unfold savg
  rw [two_mul, Finset.sum_range_add]
  have e : ∀ j, spow A (l + j) x = spow A j (spow A l x) := fun j => by
    rw [add_comm, spow_add]
  simp only [e, smul_add, smul_smul]
  have hc : ((1 : ℝ) / ((l + l : ℕ) : ℝ)) = 1 / 2 * (1 / (l : ℝ)) := by
    push_cast
    field_simp
    norm_num
  rw [hc]

theorem spow_comm (A B : Shift E) (hc : ∀ x, A.T (B.T x) = B.T (A.T x)) (i j : ℕ) (x : E) :
    spow A i (spow B j x) = spow B j (spow A i x) := by
  have h : Commute A.T B.T := LinearMap.ext hc
  have := (h.pow_pow i j).eq
  simpa [spow, Module.End.mul_apply] using congrArg (fun F => F x) this

theorem savg_spow_comm (A B : Shift E) (hc : ∀ x, A.T (B.T x) = B.T (A.T x)) (m j : ℕ) (x : E) :
    savg A m (spow B j x) = spow B j (savg A m x) := by
  unfold savg
  rw [map_smul, map_sum]
  simp only [spow_comm A B hc]

theorem dbl_savg_comm (A B : Shift E) (hc : ∀ x, A.T (B.T x) = B.T (A.T x)) (l m : ℕ) (x : E) :
    dbl B l (savg A m x) = savg A m (dbl B l x) := by
  unfold dbl
  rw [savg_smul, savg_add, savg_spow_comm A B hc]

theorem dbl_sub (A : Shift E) (l : ℕ) (x y : E) : dbl A l (x - y) = dbl A l x - dbl A l y := by
  unfold dbl spow
  rw [map_sub, ← smul_sub]
  congr 1
  abel

theorem norm_dbl_le (A : Shift E) (l : ℕ) (x : E) : ‖dbl A l x‖ ≤ ‖x‖ := by
  unfold dbl
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  have := norm_add_le x (spow A l x)
  rw [BlockShifts.norm_pow] at this
  linarith only [this]

theorem sub_dbl_le (A : Shift E) (l : ℕ) (x : E) : ‖x - dbl A l x‖ ≤ l / 2 * ‖A.D x‖ := by
  have e : x - dbl A l x = (1 / 2 : ℝ) • (x - spow A l x) := by
    unfold dbl
    rw [smul_add, smul_sub]
    have : x = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by
      rw [← add_smul]
      norm_num
    nth_rewrite 1 [this]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (by norm_num)]
  have := sub_pow_le A l x
  linarith only [this]

/-- All four doublings at once. -/
def dbl4 (A : Fin 4 → Shift E) (l : ℕ) (x : E) : E :=
  dbl (A 0) l (dbl (A 1) l (dbl (A 2) l (dbl (A 3) l x)))

theorem blockAvg_two_mul (A : Fin 4 → Shift E)
    (hc : ∀ μ ν x, (A μ).T ((A ν).T x) = (A ν).T ((A μ).T x)) (l : ℕ) (hl : 1 ≤ l) (x : E) :
    blockAvg A (2 * l) x = blockAvg A l (dbl4 A l x) := by
  unfold blockAvg dbl4
  simp only [savg_two_mul _ l hl]
  simp only [dbl_savg_comm _ _ (hc _ _)]

theorem sub_dbl4_le (A : Fin 4 → Shift E) (l : ℕ) (x : E) :
    ‖x - dbl4 A l x‖ ≤ l / 2 * ∑ ν, ‖(A ν).D x‖ := by
  have step (B : Shift E) (y z : E) : ‖y - dbl B l z‖ ≤ ‖y - dbl B l y‖ + ‖y - z‖ := by
    have e : y - dbl B l z = (y - dbl B l y) + dbl B l (y - z) := by
      rw [dbl_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_dbl_le B l (y - z)
    linarith only [this]
  have h3 := sub_dbl_le (A 3) l x
  have h2 := sub_dbl_le (A 2) l x
  have h1 := sub_dbl_le (A 1) l x
  have h0 := sub_dbl_le (A 0) l x
  have s2 := step (A 2) x (dbl (A 3) l x)
  have s1 := step (A 1) x (dbl (A 2) l (dbl (A 3) l x))
  have s0 := step (A 0) x (dbl (A 1) l (dbl (A 2) l (dbl (A 3) l x)))
  unfold dbl4
  rw [Fin.sum_univ_four]
  linarith only [h0, h1, h2, h3, s0, s1, s2]

end Dyadic

/-! ### The scalar Sobolev inequality on the four-torus -/

section Sobolev

open PeriodicLattice4 TwistedHessian

variable {N : ℕ} [NeZero N]

/-- The plain translation on scalar functions. -/
abbrev tau (μ : Fin 4) : Shift (Section N) := colourShift false false μ

theorem tau_T (μ : Fin 4) (f : Section N) (x : Vertex N) : (tau μ).T f x = f (step N x μ) := by
  change eta false false x μ * f (step N x μ) = _
  simp [eta]

theorem tau_comm (μ ν : Fin 4) (f : Section N) : (tau μ).T ((tau ν).T f) = (tau ν).T ((tau μ).T f) :=
  colourShift_commute false false μ ν f

theorem tau_spow (μ : Fin 4) (j : ℕ) (f : Section N) (x : Vertex N) :
    spow (tau μ) j f x = f (x + Pi.single μ (j : ZMod N)) := by
  induction j generalizing x with
  | zero => simp [spow]
  | succ j ih =>
    rw [spow_succ, tau_T, ih]
    have e : step N x μ + Pi.single μ (j : ZMod N) = x + Pi.single μ ((j + 1 : ℕ) : ZMod N) := by
      unfold step
      rw [add_assoc, ← Pi.single_add]
      push_cast
      rw [add_comm (1 : ZMod N)]
    rw [e]

theorem tau_savg (μ : Fin 4) (l : ℕ) (f : Section N) (x : Vertex N) :
    savg (tau μ) l f x = 1 / (l : ℝ) * ∑ j ∈ Finset.range l, f (x + Pi.single μ (j : ZMod N)) := by
  unfold savg
  rw [PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [tau_spow]

/-- A vertex of the box of side `l` based at `x`. -/
def boxPt (x : Vertex N) (p : ℕ × ℕ × ℕ × ℕ) : Vertex N :=
  x + Pi.single 0 (p.1 : ZMod N) + Pi.single 1 (p.2.1 : ZMod N) + Pi.single 2 (p.2.2.1 : ZMod N) +
    Pi.single 3 (p.2.2.2 : ZMod N)

/-- The box of side `l`. -/
def box (l : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range l ×ˢ Finset.range l ×ˢ Finset.range l ×ˢ Finset.range l

theorem tau_block (l : ℕ) (f : Section N) (x : Vertex N) :
    blockAvg (tau (N := N)) l f x = 1 / (l : ℝ) ^ 4 * ∑ p ∈ box l, f (boxPt x p) := by
  unfold blockAvg box boxPt
  simp only [tau_savg, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring

theorem boxPt_injOn (x : Vertex N) (l : ℕ) (hl : l ≤ N) : Set.InjOn (boxPt x) (box l : Set _) := by
  have hcast (i j : ℕ) (hi : i < l) (hj : j < l) (h : (i : ZMod N) = j) : i = j := by
    have := (ZMod.natCast_eq_natCast_iff' i j N).1 h
    rwa [Nat.mod_eq_of_lt (hi.trans_le hl), Nat.mod_eq_of_lt (hj.trans_le hl)] at this
  rintro ⟨a, b, c, e⟩ h1 ⟨a', b', c', e'⟩ h2 h
  simp only [box, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at h1 h2
  obtain ⟨h1a, h1b, h1c, h1e⟩ := h1
  obtain ⟨h2a, h2b, h2c, h2e⟩ := h2
  have hat (ρ : Fin 4) := congrFun h ρ
  have h0 := hat 0
  have h1' := hat 1
  have h2' := hat 2
  have h3 := hat 3
  simp [boxPt] at h0 h1' h2' h3
  have := hcast _ _ h1a h2a h0
  have := hcast _ _ h1b h2b h1'
  have := hcast _ _ h1c h2c h2'
  have := hcast _ _ h1e h2e h3
  simp_all

/-- **The average over a box of side `l` costs `l²` from the `L²` norm.** The dimension four is here. -/
theorem block_point (l : ℕ) (hl : 1 ≤ l) (hlN : l ≤ N) (b : Section N) (x : Vertex N) :
    (l : ℝ) ^ 2 * |blockAvg (tau (N := N)) l b x| ≤ ‖b‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hcard : ((box l).card : ℝ) = (l : ℝ) ^ 4 := by
    simp [box, Finset.card_product]
    ring
  have hsum : ∑ p ∈ box l, b (boxPt x p) ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have e := Finset.sum_image (s := box l) (g := boxPt x) (f := fun z => b z ^ 2)
      (fun p hp q hq h => boxPt_injOn x l hlN hp hq h)
    simp only [Real.norm_eq_abs, sq_abs]
    rw [← e]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hcs := sq_sum_le_card_mul_sum_sq (s := box l) (f := fun p => b (boxPt x p))
  rw [hcard] at hcs
  rw [tau_block]
  set sb := ∑ p ∈ box l, b (boxPt x p) with hsb
  have hkey : ((l : ℝ) ^ 2 * |1 / (l : ℝ) ^ 4 * sb|) ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [mul_pow, sq_abs, mul_pow]
    have e2 : ((l : ℝ) ^ 2) ^ 2 * ((1 / (l : ℝ) ^ 4) ^ 2 * sb ^ 2) = sb ^ 2 / (l : ℝ) ^ 4 := by
      field_simp
    rw [e2, div_le_iff₀ (by positivity)]
    nlinarith only [hcs, hsum, pow_pos hl0 4]
  exact (abs_le_of_sq_le_sq' hkey (norm_nonneg _)).2

theorem block_sub (l : ℕ) (a b : Section N) :
    blockAvg (tau (N := N)) l (a - b) = blockAvg tau l a - blockAvg tau l b := by
  unfold blockAvg
  simp only [savg_sub]

/-- The dyadic telescope: moving from scale `2^K` to scale `2^(K+1)` costs `2^(-K-1)` times the gradient,
because `2^(-2K)` from `block_point` beats the `2^K` from the length of the translation. -/
theorem sobolev_chain (a : Section N) (x : Vertex N) (K : ℕ) (hK : 2 ^ K ≤ N) :
    |a x - blockAvg (tau (N := N)) (2 ^ K) a x| ≤ (1 - 1 / (2 : ℝ) ^ K) * ∑ ν, ‖(tau (N := N) ν).D a‖ := by
  induction K with
  | zero =>
    simp [blockAvg, savg_one]
  | succ K ih =>
    set l : ℕ := 2 ^ K with hl
    have hl1 : 1 ≤ l := Nat.one_le_two_pow
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
    have hle : l ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K)) hK
    have hih := ih hle
    have hG : 0 ≤ ∑ ν, ‖(tau (N := N) ν).D a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have e2 : (2 : ℕ) ^ (K + 1) = 2 * l := by rw [hl, pow_succ, mul_comm]
    rw [e2, blockAvg_two_mul _ tau_comm l hl1]
    have hpt := block_point l hl1 hle (a - dbl4 tau l a) x
    rw [block_sub] at hpt
    have hd := sub_dbl4_le (tau (N := N)) l a
    set u := blockAvg (tau (N := N)) l a x with hu
    set w := blockAvg (tau (N := N)) l (dbl4 tau l a) x with hw
    have e3 : (blockAvg (tau (N := N)) l a - blockAvg tau l (dbl4 tau l a)) x = u - w := rfl
    rw [e3] at hpt
    have hreal : (2 : ℝ) ^ K = l := by rw [hl]; push_cast; rfl
    have hreal2 : (2 : ℝ) ^ (K + 1) = 2 * l := by rw [pow_succ, hreal]; ring
    rw [hreal] at hih
    rw [hreal2]
    set G := ∑ ν, ‖(tau (N := N) ν).D a‖ with hGdef
    have h1 : (l : ℝ) ^ 2 * |u - w| ≤ l / 2 * G := hpt.trans hd
    have h2 : |u - w| ≤ 1 / (2 * l) * G := by
      have e : (l : ℝ) ^ 2 * (1 / (2 * l) * G) = l / 2 * G := by
        field_simp
      rw [← e] at h1
      exact le_of_mul_le_mul_left h1 (by positivity)
    have e4 : a x - w = (a x - u) + (u - w) := by ring
    rw [e4]
    refine (abs_add_le _ _).trans ?_
    have e5 : (1 - 1 / (2 * (l : ℝ))) * G = (1 - 1 / (l : ℝ)) * G + 1 / (2 * l) * G := by
      field_simp
      ring
    rw [e5]
    exact add_le_add hih h2

/-- **The discrete Sobolev inequality in four dimensions.** A function on the torus is bounded pointwise by its
gradient and its average at scale `2^K`, with no constant depending on `N`. In dimension `d` the telescoping term at
scale `2^k` is `2^(-(d/2 - 1) k)` times the gradient, which sums exactly when `d > 2`. -/
theorem sobolev_scalar (a : Section N) (K : ℕ) (hK : 2 ^ K ≤ N) (x : Vertex N) :
    |a x| ≤ ∑ ν, ‖(tau (N := N) ν).D a‖ + 1 / 4 ^ K * ‖a‖ := by
  have h1 := sobolev_chain a x K hK
  have hl1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have h2 := block_point (2 ^ K) hl1 hK a x
  have hreal : (((2 ^ K : ℕ) : ℝ)) ^ 2 = 4 ^ K := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hreal] at h2
  have h4 : (0 : ℝ) < 4 ^ K := by positivity
  have h3 : |blockAvg (tau (N := N)) (2 ^ K) a x| ≤ 1 / 4 ^ K * ‖a‖ := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ h4, mul_comm]
    exact h2
  have hG : 0 ≤ ∑ ν, ‖(tau (N := N) ν).D a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h5 : (0 : ℝ) < 1 / (2 : ℝ) ^ K := by positivity
  have h6 : (1 - 1 / (2 : ℝ) ^ K) * ∑ ν, ‖(tau (N := N) ν).D a‖ ≤ ∑ ν, ‖(tau (N := N) ν).D a‖ := by
    nlinarith only [hG, h5]
  have e : a x = (a x - blockAvg (tau (N := N)) (2 ^ K) a x) + blockAvg (tau (N := N)) (2 ^ K) a x := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith only [h1, h3, h6]

/-! ### Kato: the norm of a covariant field has less gradient -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The pointwise norm of a field. -/
def normF (f : Fld (Vertex N) F) : Section N := WithLp.toLp 2 fun x => ‖f x‖

theorem normF_norm (f : Fld (Vertex N) F) : ‖normF f‖ = ‖f‖ := by
  have h : ‖normF f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, norm_sq_fld]
    refine Finset.sum_congr rfl fun x _ => ?_
    change ‖‖f x‖‖ ^ 2 = _
    rw [norm_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Diamagnetic inequality.** Only the fact that the transport is pointwise isometric is used. -/
theorem kato (A : Shift (Fld (Vertex N) F)) (μ : Fin 4)
    (hA : ∀ g x, ‖A.T g x‖ = ‖g (step N x μ)‖) (f : Fld (Vertex N) F) :
    ‖(tau μ).D (normF f)‖ ≤ ‖A.D f‖ := by
  refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
  rw [EuclideanSpace.norm_sq_eq, norm_sq_fld]
  refine Finset.sum_le_sum fun x _ => ?_
  have e1 : (tau (N := N) μ).D (normF f) x = ‖f (step N x μ)‖ - ‖f x‖ := by
    unfold Shift.D
    change (tau (N := N) μ).T (normF f) x - ‖f x‖ = _
    rw [tau_T]
    rfl
  have e2 : A.D f x = A.T f x - f x := rfl
  rw [e1, e2, ← hA f x, Real.norm_eq_abs, sq_abs]
  have := abs_norm_sub_norm_le (A.T f x) (f x)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- **The covariant Sobolev inequality.** The same for any pointwise isometric transport. No commutator of the
shifts enters, because the scalar average of the norm sees plain translations. -/
theorem point_le_grad (A : Fin 4 → Shift (Fld (Vertex N) F))
    (hA : ∀ μ g x, ‖(A μ).T g x‖ = ‖g (step N x μ)‖) (f : Fld (Vertex N) F) (K : ℕ) (hK : 2 ^ K ≤ N)
    (x : Vertex N) : ‖f x‖ ≤ ∑ ν, ‖(A ν).D f‖ + 1 / 4 ^ K * ‖f‖ := by
  have h := sobolev_scalar (normF f) K hK x
  rw [normF_norm] at h
  have e : |normF f x| = ‖f x‖ := by
    change |‖f x‖| = _
    exact abs_norm _
  rw [e] at h
  exact h.trans (add_le_add (Finset.sum_le_sum fun ν _ => kato (A ν) ν (hA ν) f) le_rfl)

/-- **The value of a field at a point is bounded by its energy, with a constant free of `N` and of `L`.** The
inputs are that the energy controls all covariant differences and that it controls the norm with `L²`. The `L²`
is absorbed by the average at scale `L`. -/
theorem point_sq_le (A : Fin 4 → Shift (Fld (Vertex N) F))
    (hA : ∀ μ g x, ‖(A μ).T g x‖ = ‖g (step N x μ)‖) (h : VF (Vertex N) F) (Y C₁ C₂ t : ℝ)
    (hY : 0 ≤ Y) (hC₂ : 0 ≤ C₂) (ht : 0 < t)
    (hg : ∑ μ, ∑ ν, ‖(A ν).D (h μ)‖ ^ 2 ≤ C₁ * Y) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hn : nsq h ≤ C₂ * (L : ℝ) ^ 2 * Y) (ν : Fin 4) (x : Vertex N) :
    ‖h ν x‖ ^ 2 ≤ ((1 + t) * (4 * C₁) + (1 + 1 / t) * (4 * C₂)) * Y := by
  set K := Nat.log 2 L with hKdef
  have hK1 : 2 ^ K ≤ L := Nat.pow_log_le_self 2 (by omega)
  have hK2 : L < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hpt := point_le_grad A hA (h ν) K (hK1.trans hLN) x
  set a := ∑ ρ, ‖(A ρ).D (h ν)‖ with ha
  set b := 1 / (4 : ℝ) ^ K * ‖h ν‖ with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 ≤ 4 * (C₁ * Y) := by
    have h1 : a ^ 2 ≤ 4 * ∑ ρ, ‖(A ρ).D (h ν)‖ ^ 2 := by
      rw [ha]
      simp only [Fin.sum_univ_four]
      generalize ‖(A 0).D (h ν)‖ = p
      generalize ‖(A 1).D (h ν)‖ = q
      generalize ‖(A 2).D (h ν)‖ = r
      generalize ‖(A 3).D (h ν)‖ = s
      nlinarith only [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r),
        sq_nonneg (q - s), sq_nonneg (r - s)]
    have h2 : ∑ ρ, ‖(A ρ).D (h ν)‖ ^ 2 ≤ ∑ μ, ∑ ρ, ‖(A ρ).D (h μ)‖ ^ 2 :=
      Finset.single_le_sum (f := fun μ => ∑ ρ, ‖(A ρ).D (h μ)‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ ν)
    linarith only [h1, h2, hg]
  have hb2 : b ^ 2 ≤ 4 * (C₂ * Y) := by
    have h1 : ‖h ν‖ ^ 2 ≤ C₂ * (L : ℝ) ^ 2 * Y :=
      (Finset.single_le_sum (f := fun μ => ‖h μ‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ν)).trans hn
    have h4 : (0 : ℝ) < 4 ^ K := by positivity
    have h41 : (1 : ℝ) ≤ 4 ^ K := one_le_pow₀ (by norm_num)
    have hL2 : (L : ℝ) ^ 2 ≤ 4 * 4 ^ K := by
      have h5 : (L : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by exact_mod_cast hK2.le
      have h6 := pow_le_pow_left₀ (Nat.cast_nonneg L) h5 2
      have e : ((2 : ℝ) ^ (K + 1)) ^ 2 = 4 * 4 ^ K := by
        rw [← pow_mul, mul_comm, pow_mul, pow_succ]
        norm_num
        ring
      rwa [e] at h6
    have hCY : 0 ≤ C₂ * Y := mul_nonneg hC₂ hY
    have h7 : ‖h ν‖ ^ 2 ≤ 4 * 4 ^ K * (C₂ * Y) := by
      have := mul_le_mul_of_nonneg_right hL2 hCY
      nlinarith only [h1, this]
    have e : b ^ 2 = ‖h ν‖ ^ 2 / (4 ^ K * 4 ^ K) := by
      rw [hb]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h8 : 4 * 4 ^ K * (C₂ * Y) ≤ 4 * (C₂ * Y) * (4 ^ K * 4 ^ K) := by
      have := mul_le_mul_of_nonneg_left h41 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h4.le) hCY)
      nlinarith only [this]
    linarith only [h7, h8]
  have hab : (a + b) ^ 2 ≤ (1 + t) * a ^ 2 + (1 + 1 / t) * b ^ 2 := by
    have h1 : 0 ≤ (t * a - b) ^ 2 / t := by positivity
    have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + 1 / t * b ^ 2 := by
      field_simp
      ring
    rw [e] at h1
    nlinarith only [h1]
  have hx : ‖h ν x‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpt 2
  have m1 := mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ 1 + t)
  have m2 := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ 1 + 1 / t)
  nlinarith only [hx, hab, m1, m2]

end Sobolev

/-! ### The flat twisted covariance -/

section Flat

open PeriodicLattice4 TwistedHessian TwistedSmallField

variable {N : ℕ} [NeZero N]

/-- The Feynman-gauge form of colour `a`: curl energy plus divergence. Its operator is the twisted lattice
Laplacian on each component, by the Weitzenböck identity. -/
abbrev flatForm (a : Fin 3) : VF (Vertex N) ℝ →ₗ[ℝ] VF (Vertex N) ℝ →ₗ[ℝ] ℝ := fluct (shifts a) 1 0

theorem flatForm_coercive (a : Fin 3) (h : VF (Vertex N) ℝ) :
    lam N * nsq h ≤ flatForm a h h := by
  rw [fluct_self, zero_mul, add_zero]
  exact colour_bound a h

/-- **The flat twisted covariance exists,** at every `N`, with the sharp spectral floor. -/
theorem flat_exists_unique (a : Fin 3) (s : VF (Vertex N) ℝ) :
    ∃! g, g ∈ (⊤ : Submodule ℝ (VF (Vertex N) ℝ)) ∧ ∀ f ∈ (⊤ : Submodule ℝ (VF (Vertex N) ℝ)),
      flatForm a f g = ip f s :=
  exists_unique_solution _ ⊤ (lam N) (lam_pos N) (fun h _ => flatForm_coercive a h) s

/-- **The flat spectral bound.** The `L²` operator norm of the covariance is at most `1/(4 sin²(π/2N))`, so at most
`N²/4`. This is not uniform in `N`, and cannot be: `lam N` is numerically the true bottom of the spectrum for the
colours `i` and `j`, and half of it for `k`. The
pointwise bound `flat_point` is uniform. -/
theorem flat_spectral (a : Fin 3) (g s : VF (Vertex N) ℝ)
    (hs : ∀ f, flatForm a f g = ip f s) : lam N ^ 2 * nsq g ≤ nsq s :=
  spectral_bound (flatForm a) (fun _ => True) (lam N) (lam_pos N)
    (fun h _ => flatForm_coercive a h) g s trivial fun f _ => hs f

/-- The colour transport is pointwise isometric. -/
theorem shifts_iso (a : Fin 3) (μ : Fin 4) (g : Section N) (x : Vertex N) :
    ‖(shifts a μ).T g x‖ = ‖g (step N x μ)‖ := by
  change ‖eta (bundle a).1 (bundle a).2 x μ * g (step N x μ)‖ = _
  rw [norm_mul]
  have h := eta_sq (bundle a).1 (bundle a).2 x μ
  have : ‖eta (bundle a).1 (bundle a).2 x μ‖ = 1 := by
    rw [Real.norm_eq_abs]
    have h2 : |eta (bundle a).1 (bundle a).2 x μ| ^ 2 = 1 := by
      rw [sq_abs, sq]
      exact h
    nlinarith only [h2, abs_nonneg (eta (bundle a).1 (bundle a).2 x μ)]
  rw [this, one_mul]

/-- The energy of the massless flat form controls point values, with a constant free of `N`. -/
theorem flat_energy (a : Fin 3) (h : VF (Vertex N) ℝ) (ν : Fin 4) (x : Vertex N) :
    ‖h ν x‖ ^ 2 ≤ 9 * flatForm a h h := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hc := flatForm_coercive a h
  have hl := lam_lower N
  have hnn := nsq_nonneg h
  have hl2 : 4 / (N : ℝ) ^ 2 * nsq h ≤ flatForm a h h :=
    (mul_le_mul_of_nonneg_right hl hnn).trans hc
  have hY0 : 0 ≤ flatForm a h h := le_trans (by positivity) hl2
  have hn : nsq h ≤ 1 / 4 * (N : ℝ) ^ 2 * flatForm a h h := by
    have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 4)
    have e : (N : ℝ) ^ 2 / 4 * (4 / (N : ℝ) ^ 2 * nsq h) = nsq h := by
      field_simp
    rw [e] at this
    linarith only [this]
  have hg : ∑ μ, ∑ ρ, ‖(shifts (N := N) a ρ).D (h μ)‖ ^ 2 ≤ 1 * flatForm a h h := by
    rw [fluct_self, zero_mul, add_zero, one_mul]
    exact (weitzenbock (shifts a) (fun μ ν φ => colourShift_commute (bundle a).1 (bundle a).2 μ ν φ) h).symm.le
  have key := point_sq_le (shifts (N := N) a) (fun μ g x => shifts_iso a μ g x) h _ 1 (1 / 4) (1 / 2) hY0
    (by norm_num) (by norm_num) hg N (NeZero.pos N) le_rfl hn ν x
  have e : ((1 + 1 / 2 : ℝ) * (4 * 1) + (1 + 1 / (1 / 2)) * (4 * (1 / 4))) = 9 := by norm_num
  rwa [e] at key

/-- **The massless flat covariance is bounded pointwise, uniformly in `N`.** This is the four-dimensional fact: the
spectral bound is `N²/4`, but the kernel stays `O(1)`. No penalty is used, and no decay is claimed. -/
theorem flat_point (a : Fin 3) (g : VF (Vertex N) ℝ) (μ : Fin 4) (y : Vertex N) (v : ℝ)
    (hs : ∀ f : VF (Vertex N) ℝ, flatForm a f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    |g ν x| ≤ 9 * |v| := by
  have := green_point (flatForm a) (fun _ => True) 9 (by norm_num) (fun _ _ _ => trivial)
    (fun h _ ν x => flat_energy a h ν x) g trivial μ y v (fun f _ => hs f) ν x
  simpa [Real.norm_eq_abs] using this

end Flat

/-! ### The covariant block propagator -/

section Covariant

open PeriodicLattice4 TwistedFlat TwistedHessian TwistedCovariant TwistedStability TwistedBadSet
open WilsonSingleLinkStaples (Q)
open scoped Quaternion

variable {N : ℕ} [NeZero N]

/-- The adjoint action as a linear map. -/
def AdLin (u : Q) : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] where
  toFun := Ad u
  map_add' := Ad_add u
  map_smul' := Ad_smul u

theorem cov_intertwines (U : Vertex N → Fin 4 → Q) (μ : Fin 4) :
    Intertwines (stepEquiv (N := N) μ) (covShift U μ).T := by
  intro w f
  ext x : 1
  exact Ad_smul _ _ _

/-- The fluctuation form at the background `U`, with penalty on running averages of length `L`. It acts on all
quaternion-valued fields. The real component is not a Lie-algebra direction: it is a periodic scalar whose only
spectral floor at zero momentum comes from the penalty. -/
abbrev blockForm (U : Vertex N → Fin 4 → Q) (L : ℕ) :
    VF (Vertex N) ℍ[ℝ] →ₗ[ℝ] VF (Vertex N) ℍ[ℝ] →ₗ[ℝ] ℝ :=
  fluct (covShift U) L (1 / (4 * (L : ℝ) ^ 2))

/-- The numbers: the constant of `block_coercive` at `δ = 1/(1000 L²)` survives the weight `1/(32 L)`. -/
theorem block_numbers (L : ℕ) (hL : 1 ≤ L) :
    1 / (16 * (L : ℝ) ^ 2) ≤ (1 / (8 * (L : ℝ) ^ 2) - 8 * (1 / (1000 * (L : ℝ) ^ 2))) -
      Err (1 / (32 * L)) L (1 / (4 * (L : ℝ) ^ 2)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  have h4 : 4 * (L : ℝ) * (1 / (32 * L)) = 1 / 8 := by
    field_simp
    norm_num
  have hE := Err_block_le (1 / (32 * L)) L hL (by positivity) (by rw [h4]; norm_num)
  have e : (1 : ℝ) / (32 * L) = 1 / 32 * (1 / L) := by
    field_simp
  set y : ℝ := 1 / (L : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have e1 : 712 / 15 * ((1 : ℝ) / (32 * L)) ^ 2 = 712 / 15 / 1024 * y := by
    rw [hy]
    field_simp
    norm_num
  have e2 : 1 / (16 * (L : ℝ) ^ 2) = y / 16 := by
    rw [hy]
    field_simp
  have e3 : 1 / (8 * (L : ℝ) ^ 2) = y / 8 := by
    rw [hy]
    field_simp
  have e4 : 1 / (1000 * (L : ℝ) ^ 2) = y / 1000 := by
    rw [hy]
    field_simp
  rw [e1] at hE
  rw [e2, e3, e4]
  nlinarith only [hE, hy0]

/-- The decay statement for the form with block penalty, on a weight-stable set where the form is
coercive with the constant of `block_coercive` at `δ = 1/(1000 L²)`. -/
theorem blockForm_decay (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (P : VF (Vertex N) ℍ[ℝ] → Prop) (hV : ∀ (ψ : Vertex N → ℝ) h, P h → P (Wt ψ h))
    (hc : ∀ h, P h → (1 / (8 * (L : ℝ) ^ 2) - 8 * (1 / (1000 * (L : ℝ) ^ 2))) * nsq h ≤
      blockForm U L h h)
    (g : VF (Vertex N) ℍ[ℝ]) (hg : P g) (μ : Fin 4) (y : Vertex N) (v : ℍ[ℝ])
    (hs : ∀ f, P f → blockForm U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 16 * (L : ℝ) ^ 2 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set m : ℝ := 1 / (32 * L) with hm
  have hm0 : 0 ≤ m := by positivity
  have hn := block_numbers L hL
  rw [← hm] at hn
  have hpos : 0 < 1 / (16 * (L : ℝ) ^ 2) := by positivity
  have key := fluct_decay (covShift U) (fun μ => stepEquiv (N := N) μ)
    (fun μ => cov_intertwines U μ) (distW m y) m hm0 (fun μ x => distW_lip m hm0 y x μ) L hL _
    (by positivity) P hV _ hc (by linarith only [hn, hpos]) g hg μ y v hs ν x
  rw [distW_diff] at key
  have e3 : m * (dist1 x y : ℝ) = (dist1 x y : ℝ) / (32 * L) := by
    rw [hm]
    ring
  rw [e3] at key
  have h1 : 1 / (16 * (L : ℝ) ^ 2) * ‖g ν x‖ ≤ Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ :=
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans key
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 16 * (L : ℝ) ^ 2)
  have e4 : 16 * (L : ℝ) ^ 2 * (1 / (16 * (L : ℝ) ^ 2) * ‖g ν x‖) = ‖g ν x‖ := by
    field_simp
  rw [e4] at h2
  calc ‖g ν x‖ ≤ _ := h2
    _ = _ := by ring

/-- `block_coercive` for the covariant shifts. -/
theorem blockForm_coercive (U : Vertex N → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (L : ℕ) (hL : 1 ≤ L) (h : VF (Vertex N) ℍ[ℝ]) :
    (1 / (8 * (L : ℝ) ^ 2) - 8 * δ) * nsq h ≤ blockForm U L h h := by
  have := block_coercive (covShift U) L hL (2 * δ) (by positivity)
    (fun μ ν φ => cov_comm U δ hδ0 hδ μ ν φ) h
  rw [fluct_self]
  have e : 4 * (2 * δ) = 8 * δ := by ring
  rw [e] at this
  exact this

/-- **Existence of the block covariance at a near-flat background.** -/
theorem cov_exists_unique (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2)) (s : VF (Vertex N) ℍ[ℝ]) :
    ∃! g, g ∈ (⊤ : Submodule ℝ (VF (Vertex N) ℍ[ℝ])) ∧
      ∀ f ∈ (⊤ : Submodule ℝ (VF (Vertex N) ℍ[ℝ])), blockForm U L f g = ip f s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hn := block_numbers L hL
  have hE : 0 ≤ Err (1 / (32 * L)) L (1 / (4 * (L : ℝ) ^ 2)) := by
    have h1 := Real.one_le_cosh ((1 : ℝ) / (32 * L))
    have h2 := Real.one_le_cosh (4 * (L : ℝ) * (1 / (32 * L)))
    unfold Err
    have h3 : (0 : ℝ) ≤ 1 / (4 * (L : ℝ) ^ 2) := by positivity
    have h4 : 0 ≤ 2 * (Real.cosh (4 * (L : ℝ) * (1 / (32 * L))) - 1) +
        Real.sinh (4 * (L : ℝ) * (1 / (32 * L))) ^ 2 := by
      have := sq_nonneg (Real.sinh (4 * (L : ℝ) * (1 / (32 * L))))
      linarith only [this, h2]
    have h5 := mul_nonneg h3 h4
    have := sq_nonneg (Real.sinh ((1 : ℝ) / (32 * L)))
    linarith only [this, h1, h5]
  have hpos : 0 < 1 / (16 * (L : ℝ) ^ 2) := by positivity
  refine exists_unique_solution _ ⊤ _ (by linarith only [hn, hE, hpos] :
    0 < 1 / (8 * (L : ℝ) ^ 2) - 8 * (1 / (1000 * (L : ℝ) ^ 2))) (fun h _ => ?_) s
  exact blockForm_coercive U _ (by positivity) hδ L hL h

/-- **Pointwise decay of the block covariance at a near-flat background, uniform in `N`, with prefactor `L²`.** If
all plaquette defects are at most `1/(1000 L²)`, the solution with a source at the link `(y, μ)` satisfies
`‖g ν x‖ ≤ 16 L² exp(-dist(x,y)/(32 L)) ‖v‖`. Neither constant involves `N` or the distance from flat. Coercivity
alone gives `(1000/117) L²` at every distance, so this has content only past `dist > 20 L`, so `N > 10 L`. For
`L ≥ 3` it is superseded by `cov_decay_unif`, which needs `L ≤ N`, and for `L ≥ 2` by `cov_point` at short distance. -/
theorem cov_decay (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF (Vertex N) ℍ[ℝ]) (μ : Fin 4) (y : Vertex N) (v : ℍ[ℝ])
    (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 16 * (L : ℝ) ^ 2 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ :=
  blockForm_decay U L hL (fun _ => True) (fun _ _ _ => trivial)
    (fun h _ => blockForm_coercive U _ (by positivity) hδ L hL h) g trivial μ y v
    (fun f _ => hs f) ν x

/-- The flat field has no plaquette defect. -/
theorem defect_flat (x : Vertex N) (μ ν : Fin 4) (h : μ < ν) : defect flatLink μ ν x = 0 := by
  unfold defect
  rw [TwistedFlat.flatLink_flat x μ ν h]
  simp [d]

/-- `cov_decay` at the flat field, whose hypothesis holds exactly. -/
theorem flat_block_decay (L : ℕ) (hL : 1 ≤ L) (g : VF (Vertex N) ℍ[ℝ]) (μ : Fin 4) (y : Vertex N)
    (v : ℍ[ℝ]) (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm flatLink L f g = ⟪f μ y, v⟫) (ν : Fin 4)
    (x : Vertex N) :
    ‖g ν x‖ ≤ 16 * (L : ℝ) ^ 2 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ := by
  refine cov_decay flatLink L hL (fun x μ ν h => ?_) g μ y v hs ν x
  rw [defect_flat x μ ν h]
  positivity

/-- At the flat field the adjoint transport of one link, on an imaginary value written in colour components, is the
colour shift of `TwistedHessian`. This is a statement about a single transport. No theorem here identifies `flatForm`
with `blockForm flatLink` or `hessForm` on colour components, and those forms are treated separately. -/
theorem covT_flat (X : Fin 3 → Section N) (μ : Fin 4) (x : Vertex N) :
    Ad (flatLink x μ) (∑ a, X a (step N x μ) • TwistedHessian.basis a) =
      ∑ a, (shifts a μ).T (X a) x • TwistedHessian.basis a := by
  have hl : ∀ q : ℍ[ℝ], Ad (flatLink x μ) q = (AdLin (flatLink x μ)) q := fun _ => rfl
  rw [hl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, ← hl]
  have h := ad_flatLink (N := N) a x μ
  change X a (step N x μ) • ((flatLink x μ : Q) * TwistedHessian.basis a * ((flatLink x μ)⁻¹ : Q)) =
    (eta (bundle a).1 (bundle a).2 x μ * X a (step N x μ)) • TwistedHessian.basis a
  rw [h, smul_smul, mul_comm]

/-- The covariant transport is pointwise isometric. -/
theorem cov_iso (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (g : QField N) (x : Vertex N) :
    ‖(covShift U μ).T g x‖ = ‖g (step N x μ)‖ := norm_Ad _ _

/-- **The energy controls point values at the block scale, with a constant free of `N` and `L`.** The hypothesis
on `h` is the commutator estimate of `block_coercive_of_cross` at `δ = 1/(1000 L²)`. -/
theorem blockForm_point_of_cross (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (h : VF (Vertex N) ℍ[ℝ])
    (hbd : ∀ μ ν, |⟪(covShift U μ).Dstar (h μ), (covShift U ν).Dstar (h ν)⟫ -
      ⟪(covShift U ν).D (h μ), (covShift U μ).D (h ν)⟫| ≤
        (2 * (1 / (1000 * (L : ℝ) ^ 2))) * ‖h μ‖ * ‖h ν‖) (ν : Fin 4) (x : Vertex N) :
    ‖h ν x‖ ^ 2 ≤ 63 * blockForm U L h h := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set y : ℝ := 1 / (L : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have eLy : (L : ℝ) ^ 2 * y = 1 := by
    rw [hy]
    field_simp
  have hκ : 0 ≤ 2 * (1 / (1000 * (L : ℝ) ^ 2)) := by positivity
  have hco := block_coercive_of_cross (covShift U) L hL _ hκ h hbd
  have hW := weitzenbock_of_cross (covShift U) _ hκ h hbd
  have e1 : 1 / (1000 * (L : ℝ) ^ 2) = y / 1000 := by
    rw [hy]
    field_simp
  have e2 : 1 / (8 * (L : ℝ) ^ 2) = y / 8 := by
    rw [hy]
    field_simp
  have hp : 0 ≤ 1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (h μ)‖ ^ 2 := by positivity
  rw [e1, e2] at hco
  rw [e1] at hW
  have hY : blockForm U L h h = curlEnergy (covShift U) h + ‖div (covShift U) h‖ ^ 2 +
      1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (h μ)‖ ^ 2 := fluct_self _ _ _ _
  rw [← hY] at hco
  set Y := blockForm U L h h with hYd
  have hnn : 0 ≤ nsq h := nsq_nonneg h
  have hco' : 117 / 1000 * (y * nsq h) ≤ Y := by
    have e : (y / 8 - 4 * (2 * (y / 1000))) * ∑ μ, ‖h μ‖ ^ 2 = 117 / 1000 * (y * nsq h) := by
      unfold nsq
      ring
    rwa [e] at hco
  have hyn : 0 ≤ y * nsq h := by positivity
  have hY0 : 0 ≤ Y := le_trans (by positivity) hco'
  have hn : nsq h ≤ 171 / 20 * (L : ℝ) ^ 2 * Y := by
    have m := mul_le_mul_of_nonneg_left hco' (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
    have e : (L : ℝ) ^ 2 * (117 / 1000 * (y * nsq h)) = 117 / 1000 * nsq h := by
      calc _ = 117 / 1000 * ((L : ℝ) ^ 2 * y) * nsq h := by ring
        _ = _ := by rw [eLy, mul_one]
    rw [e] at m
    have hLY : 0 ≤ (L : ℝ) ^ 2 * Y := by positivity
    nlinarith only [m, hLY]
  have hg : ∑ μ, ∑ ρ, ‖(covShift U ρ).D (h μ)‖ ^ 2 ≤ 107 / 100 * Y := by
    have e : 4 * (2 * (y / 1000)) * ∑ μ, ‖h μ‖ ^ 2 = 1 / 125 * (y * nsq h) := by
      unfold nsq
      ring
    rw [e] at hW
    have hY' : curlEnergy (covShift U) h + ‖div (covShift U) h‖ ^ 2 ≤ Y := by
      rw [hY]
      linarith only [hp]
    nlinarith only [hW, hY', hco', hY0]
  have key := point_sq_le (covShift U) (fun μ g x => cov_iso U μ g x) h Y (107 / 100) (171 / 20) 3 hY0
    (by norm_num) (by norm_num) hg L hL hLN hn ν x
  refine key.trans (mul_le_mul_of_nonneg_right (by norm_num) hY0)

/-- The energy-norm decay for the form with block penalty, on a weight-stable set where the energy controls
point values. -/
theorem blockForm_decay_unif (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (P : VF (Vertex N) ℍ[ℝ] → Prop) (hV : ∀ (ψ : Vertex N → ℝ) h, P h → P (Wt ψ h))
    (hc : ∀ h, P h → (1 / (8 * (L : ℝ) ^ 2) - 8 * (1 / (1000 * (L : ℝ) ^ 2))) * nsq h ≤
      blockForm U L h h)
    (hpt : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ 63 * blockForm U L h h)
    (g : VF (Vertex N) ℍ[ℝ]) (hg : P g) (μ : Fin 4) (y : Vertex N) (v : ℍ[ℝ])
    (hs : ∀ f, P f → blockForm U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 126 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set m : ℝ := 1 / (32 * L) with hm
  have hm0 : 0 ≤ m := by positivity
  have hn := block_numbers L hL
  rw [← hm] at hn
  have hconj : ∀ h, P h → 1 / 2 * blockForm U L h h ≤
      blockForm U L (Wt (distW m y) h) (Wt (-distW m y) h) := by
    intro h hP
    have h1 := hc h hP
    have h2 := fluct_conj (covShift U) (distW m y) m hm0
      (fun μ => tame_T _ (stepEquiv μ) (cov_intertwines U μ) hm0 (fun x => distW_lip m hm0 y x μ))
      (fun μ => tame_S _ (stepEquiv μ) (cov_intertwines U μ) hm0 (fun x => distW_lip m hm0 y x μ))
      L hL (1 / (4 * (L : ℝ) ^ 2)) (by positivity) h
    have h3 := mul_le_mul_of_nonneg_right hn (nsq_nonneg h)
    have hnn := nsq_nonneg h
    set z : ℝ := 1 / (L : ℝ) ^ 2 with hz
    have hz0 : 0 < z := by positivity
    have e1 : 1 / (16 * (L : ℝ) ^ 2) = z / 16 := by
      rw [hz]
      field_simp
    have e2 : 1 / (8 * (L : ℝ) ^ 2) = z / 8 := by
      rw [hz]
      field_simp
    have e3 : 1 / (1000 * (L : ℝ) ^ 2) = z / 1000 := by
      rw [hz]
      field_simp
    rw [e1, e2, e3] at h3
    rw [e2, e3] at h1
    have hzn := mul_nonneg hz0.le hnn
    change blockForm U L h h - Err m L (1 / (4 * (L : ℝ) ^ 2)) * nsq h ≤ _ at h2
    nlinarith only [h1, h2, h3, hzn]
  have key := green_energy (blockForm U L) P (distW m y) (1 / 2) 63 (by norm_num) (by norm_num) hV hconj hpt
    g hg μ y v hs ν x
  rw [distW_diff] at key
  have e3 : m * (dist1 x y : ℝ) = (dist1 x y : ℝ) / (32 * L) := by
    rw [hm]
    ring
  rw [e3] at key
  linarith only [key]

/-- **The diagonal of the block covariance is bounded uniformly in `L` and `N`.** The `L²` of the spectral floor does
not appear. At the flat field the true diagonal is numerically about `0.15` for `N ≫ L`, so the constant is loose by a
factor of about `400` there, and `4` at `N = L = 1`, a factor of about `16`. -/
theorem cov_point (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF (Vertex N) ℍ[ℝ]) (μ : Fin 4) (y : Vertex N) (v : ℍ[ℝ])
    (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 63 * ‖v‖ :=
  green_point (blockForm U L) (fun _ => True) 63 (by norm_num) (fun _ _ _ => trivial)
    (fun h _ ν x => blockForm_point_of_cross U L hL hLN h
      (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _) ν x)
    g trivial μ y v (fun f _ => hs f) ν x

/-- **Pointwise decay of the block covariance, with prefactor free of `L` and `N`.** The rate `1/(32 L)` and the
form are those of `cov_decay`. This improves on `cov_point` only past `dist > 22.2 L`, so `N > 11.1 L`. -/
theorem cov_decay_unif (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF (Vertex N) ℍ[ℝ]) (μ : Fin 4) (y : Vertex N) (v : ℍ[ℝ])
    (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 126 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ :=
  blockForm_decay_unif U L hL (fun _ => True) (fun _ _ _ => trivial)
    (fun h _ => blockForm_coercive U _ (by positivity) hδ L hL h)
    (fun h _ ν x => blockForm_point_of_cross U L hL hLN h
      (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _) ν x)
    g trivial μ y v (fun f _ => hs f) ν x

/-- **The block covariance on an `L²` source:** `‖g ν x‖² ≤ 540 L² ‖s‖²`. For a source spread over a box of side `L`
with total mass one this gives `‖g ν x‖ ≤ 24/L`. The diagonal `cov_point` gives only `O(1)`, which is what it is for a
point source. -/
theorem cov_point_source (U : Vertex N → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g s : VF (Vertex N) ℍ[ℝ]) (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm U L f g = ip f s) (ν : Fin 4)
    (x : Vertex N) : ‖g ν x‖ ^ 2 ≤ 540 * (L : ℝ) ^ 2 * nsq s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  set z : ℝ := 1 / (L : ℝ) ^ 2 with hz
  have hz0 : 0 < z := by positivity
  have eLz : (L : ℝ) ^ 2 * z = 1 := by
    rw [hz]
    field_simp
  have hco : ∀ h : VF (Vertex N) ℍ[ℝ], 117 / 1000 * z * nsq h ≤ blockForm U L h h := by
    intro h
    have := blockForm_coercive U _ (by positivity) hδ L hL h
    have e : (1 : ℝ) / (8 * (L : ℝ) ^ 2) - 8 * (1 / (1000 * (L : ℝ) ^ 2)) = 117 / 1000 * z := by
      rw [hz]
      field_simp
      norm_num
    rwa [e] at this
  have key := green_source (blockForm U L) (fun _ => True) (117 / 1000 * z) 63 (by positivity) (by norm_num)
    (fun h _ => hco h)
    (fun h _ ν x => blockForm_point_of_cross U L hL hLN h
      (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _) ν x)
    g s trivial (fun f _ => hs f) ν x
  have hsn := nsq_nonneg s
  have m := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
  have e1 : (L : ℝ) ^ 2 * (117 / 1000 * z * ‖g ν x‖ ^ 2) = 117 / 1000 * ‖g ν x‖ ^ 2 := by
    calc _ = 117 / 1000 * ((L : ℝ) ^ 2 * z) * ‖g ν x‖ ^ 2 := by ring
      _ = _ := by rw [eLz, mul_one]
  rw [e1] at m
  have hLs : 0 ≤ (L : ℝ) ^ 2 * nsq s := by positivity
  nlinarith only [m, hLs]

/-- `cov_decay_unif` at the flat field, whose hypothesis holds exactly. -/
theorem flat_block_decay_unif (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N) (g : VF (Vertex N) ℍ[ℝ]) (μ : Fin 4)
    (y : Vertex N) (v : ℍ[ℝ]) (hs : ∀ f : VF (Vertex N) ℍ[ℝ], blockForm flatLink L f g = ⟪f μ y, v⟫)
    (ν : Fin 4) (x : Vertex N) :
    ‖g ν x‖ ≤ 126 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ := by
  refine cov_decay_unif flatLink L hL hLN (fun x μ ν h => ?_) g μ y v hs ν x
  rw [defect_flat x μ ν h]
  positivity

/-! ### The same estimate with the hypothesis localized -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Fields vanishing on the links of plaquettes with defect above `δ`. -/
def avoidV (U : V' → Fin 4 → Q) (δ : ℝ) : Submodule ℝ (VF V' ℍ[ℝ]) where
  carrier := {h | ∀ l ∈ badLinks n U δ, h l.2 l.1 = 0}
  add_mem' := by
    intro a b ha hb l hl
    change a l.2 l.1 + b l.2 l.1 = 0
    rw [ha l hl, hb l hl, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha l hl
    change c • a l.2 l.1 = 0
    rw [ha l hl, smul_zero]

theorem avoidV_Wt (U : V' → Fin 4 → Q) (δ : ℝ) (ψ : V' → ℝ) (h : VF V' ℍ[ℝ])
    (hh : h ∈ avoidV n U δ) : Wt ψ h ∈ avoidV n U δ := by
  intro l hl
  change Real.exp (ψ l.1) • h l.2 l.1 = 0
  rw [hh l hl, smul_zero]

theorem cross_avoidV (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ) (h : VF V' ℍ[ℝ])
    (hh : h ∈ avoidV n U δ) (μ ν : Fin 4) :
    |⟪(covShift U μ).Dstar (h μ), (covShift U ν).Dstar (h ν)⟫ -
        ⟪(covShift U ν).D (h μ), (covShift U μ).D (h ν)⟫| ≤ 2 * δ * ‖h μ‖ * ‖h ν‖ := by
  rw [cross_eq]
  have hu : ‖(covShift U μ).S (h μ)‖ = ‖h μ‖ := (covShift U μ).norm_S _
  have key := cross_local n U δ hδ0 μ ν ((covShift U μ).S (h μ)) (h ν) ?_
  · rw [hu] at key
    exact key
  · intro z hz
    unfold pd at hz
    split_ifs at hz with h1 h2
    · have hp : ((z, ⟨(μ, ν), h1⟩) : PlaquetteIndex (2 * n)) ∈ badPlaq n U δ :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
      exact hh (step (2 * n) z μ, ν) (Finset.mem_biUnion.2 ⟨_, hp, by simp [plaqLinks]⟩)
    · have hp : ((z, ⟨(ν, μ), h2⟩) : PlaquetteIndex (2 * n)) ∈ badPlaq n U δ :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
      exact hh (step (2 * n) z μ, ν) (Finset.mem_biUnion.2 ⟨_, hp, by simp [plaqLinks]⟩)
    · exact absurd hz (not_lt.2 hδ0)

/-- Coercivity on the good subspace, with nothing assumed on the bad plaquettes. -/
theorem blockForm_coercive_avoid (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ) (L : ℕ) (hL : 1 ≤ L)
    (h : VF V' ℍ[ℝ]) (hh : h ∈ avoidV n U δ) :
    (1 / (8 * (L : ℝ) ^ 2) - 8 * δ) * nsq h ≤ blockForm U L h h := by
  have := block_coercive_of_cross (covShift U) L hL (2 * δ) (by positivity) h
    (cross_avoidV n U δ hδ0 h hh)
  rw [fluct_self]
  have e : 4 * (2 * δ) = 8 * δ := by ring
  rw [e] at this
  exact this

/-- **Pointwise decay with the hypothesis localized.** For an arbitrary field `U`, restrict the form to
fluctuations vanishing on the links of plaquettes with defect above `1/(1000 L²)`. The Dirichlet solution
satisfies the same bound as in `cov_decay`. Nothing is assumed about `U`, but the statement degenerates for rough
`U`: if every link is excluded then `avoidV` is `{0}`, and if the source link is excluded then `g = 0`. The decay is
that of the restricted problem. It says nothing about the excluded directions, where the form can be negative. -/
theorem cov_decay_avoid (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (g : VF V' ℍ[ℝ]) (hg : g ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2)), blockForm U L f g = ⟪f μ y, v⟫)
    (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 16 * (L : ℝ) ^ 2 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ :=
  blockForm_decay U L hL (· ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2)))
    (fun ψ h hh => avoidV_Wt n U _ ψ h hh)
    (fun h hh => blockForm_coercive_avoid n U _ (by positivity) L hL h hh) g hg μ y v hs ν x

/-- `cov_point` for an arbitrary field, on directions avoiding bad plaquettes. The caveats of `cov_decay_avoid` apply. -/
theorem cov_point_avoid (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n)
    (g : VF V' ℍ[ℝ]) (hg : g ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2)), blockForm U L f g = ⟪f μ y, v⟫)
    (ν : Fin 4) (x : V') : ‖g ν x‖ ≤ 63 * ‖v‖ :=
  green_point (blockForm U L) (· ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))) 63 (by norm_num)
    (fun ψ h hh => avoidV_Wt n U _ ψ h hh)
    (fun h hh ν x => blockForm_point_of_cross U L hL hLN h
      (cross_avoidV n U _ (by positivity) h hh) ν x)
    g hg μ y v hs ν x

/-- `cov_decay_unif` for an arbitrary field, on directions avoiding bad plaquettes. -/
theorem cov_decay_avoid_unif (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n)
    (g : VF V' ℍ[ℝ]) (hg : g ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2)), blockForm U L f g = ⟪f μ y, v⟫)
    (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 126 * Real.exp (-((dist1 x y : ℝ) / (32 * L))) * ‖v‖ :=
  blockForm_decay_unif U L hL (· ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2)))
    (fun ψ h hh => avoidV_Wt n U _ ψ h hh)
    (fun h hh => blockForm_coercive_avoid n U _ (by positivity) L hL h hh)
    (fun h hh ν x => blockForm_point_of_cross U L hL hLN h
      (cross_avoidV n U _ (by positivity) h hh) ν x)
    g hg μ y v hs ν x

end Covariant

/-! ### The actual Hessian -/

section Hessian

open PeriodicLattice4 TwistedFlat TwistedHessian TwistedCovariant TwistedStability TwistedBadSet
open TwistedHessianField TwistedActionJet TwistedSmallField TwistedReflection
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-- Four quaternions, the frame-transported rotations of one plaquette. -/
abbrev PT := Fin 4 → ℍ[ℝ]

/-- The sum of the four norms. -/
def sumN (Y : PT) : ℝ := ∑ i, ‖Y i‖

theorem sumN_nonneg (Y : PT) : 0 ≤ sumN Y := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sumN_smul_le (c : Fin 4 → ℝ) (C : ℝ) (hc : ∀ i, |c i| ≤ C) (Y : PT) :
    sumN (fun i => c i • Y i) ≤ C * sumN Y := by
  unfold sumN
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)

/-- A product of two coordinates, as a bilinear map. -/
def m2 (u v : PT →ₗ[ℝ] ℍ[ℝ]) : PT →ₗ[ℝ] PT →ₗ[ℝ] ℍ[ℝ] := (LinearMap.mul ℝ ℍ[ℝ]).compl₁₂ u v

abbrev pr (i : Fin 4) : PT →ₗ[ℝ] ℍ[ℝ] := LinearMap.proj i

/-- A bilinear form with `secondCoeff` on the diagonal. -/
def polar : PT →ₗ[ℝ] PT →ₗ[ℝ] ℍ[ℝ] :=
  m2 (pr 0) (pr 0) + m2 (pr 0) (pr 1) + (m2 (pr 0) (pr 1) + m2 (pr 1) (pr 1)) +
    m2 (pr 0 + pr 1) (pr 2 + pr 3) + (m2 (pr 0 + pr 1) (pr 2 + pr 3) +
      (m2 (pr 2) (pr 2) + m2 (pr 2) (pr 3) + (m2 (pr 2) (pr 3) + m2 (pr 3) (pr 3))))

theorem polar_apply (Y Y' : PT) : polar Y Y' =
    Y 0 * Y' 0 + Y 0 * Y' 1 + (Y 0 * Y' 1 + Y 1 * Y' 1) + (Y 0 + Y 1) * (Y' 2 + Y' 3) +
      ((Y 0 + Y 1) * (Y' 2 + Y' 3) + (Y 2 * Y' 2 + Y 2 * Y' 3 + (Y 2 * Y' 3 + Y 3 * Y' 3))) := rfl

theorem polar_self (Y : PT) : polar Y Y = secondCoeff (Y 0) (Y 1) (Y 2) (Y 3) := rfl

theorem polar_norm (Y Y' : PT) : ‖polar Y Y'‖ ≤ 2 * sumN Y * sumN Y' := by
  rw [polar_apply]
  simp only [sumN, Fin.sum_univ_four]
  have hm (x y : ℍ[ℝ]) : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  generalize Y 0 = A at *
  generalize Y 1 = B at *
  generalize Y 2 = C at *
  generalize Y 3 = D at *
  generalize Y' 0 = A' at *
  generalize Y' 1 = B' at *
  generalize Y' 2 = C' at *
  generalize Y' 3 = D' at *
  have hab : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
  have hcd : ‖C' + D'‖ ≤ ‖C'‖ + ‖D'‖ := norm_add_le _ _
  have hcross : ‖A + B‖ * ‖C' + D'‖ ≤ (‖A‖ + ‖B‖) * (‖C'‖ + ‖D'‖) :=
    mul_le_mul hab hcd (norm_nonneg _) (by positivity)
  have h0 := norm_add_le (A * A' + A * B' + (A * B' + B * B') + (A + B) * (C' + D'))
    ((A + B) * (C' + D') + (C * C' + C * D' + (C * D' + D * D')))
  have h1 := norm_add_le (A * A' + A * B' + (A * B' + B * B')) ((A + B) * (C' + D'))
  have h2 := norm_add_le (A * A' + A * B') (A * B' + B * B')
  have h3 := norm_add_le (A * A') (A * B')
  have h4 := norm_add_le (A * B') (B * B')
  have h5 := norm_add_le ((A + B) * (C' + D')) (C * C' + C * D' + (C * D' + D * D'))
  have h6 := norm_add_le (C * C' + C * D') (C * D' + D * D')
  have h7 := norm_add_le (C * C') (C * D')
  have h8 := norm_add_le (C * D') (D * D')
  simp only [hm] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have na := norm_nonneg A
  have nb := norm_nonneg B
  have nc := norm_nonneg C
  have nd := norm_nonneg D
  have na' := norm_nonneg A'
  have nb' := norm_nonneg B'
  have nc' := norm_nonneg C'
  have nd' := norm_nonneg D'
  have key : ‖A‖ * ‖A'‖ + ‖A‖ * ‖B'‖ + (‖A‖ * ‖B'‖ + ‖B‖ * ‖B'‖) + (‖A‖ + ‖B‖) * (‖C'‖ + ‖D'‖) +
      ((‖A‖ + ‖B‖) * (‖C'‖ + ‖D'‖) + (‖C‖ * ‖C'‖ + ‖C‖ * ‖D'‖ + (‖C‖ * ‖D'‖ + ‖D‖ * ‖D'‖))) ≤
      2 * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) * (‖A'‖ + ‖B'‖ + ‖C'‖ + ‖D'‖) := by
    have p1 := mul_nonneg na na'
    have p2 := mul_nonneg nb na'
    have p3 := mul_nonneg nc na'
    have p4 := mul_nonneg nd na'
    have p5 := mul_nonneg nb nb'
    have p6 := mul_nonneg nc nb'
    have p7 := mul_nonneg nd nb'
    have p8 := mul_nonneg nc nc'
    have p9 := mul_nonneg nd nc'
    have p10 := mul_nonneg nc nd'
    have p11 := mul_nonneg nd nd'
    nlinarith only [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, hcross, key]

/-- The linear functional `x ↦ -Re (x c)`. -/
def negReMul (c : ℍ[ℝ]) : ℍ[ℝ] →ₗ[ℝ] ℝ where
  toFun x := -(x * c).re
  map_add' a b := by
    rw [add_mul, Quaternion.re_add]
    ring
  map_smul' r a := by
    rw [smul_mul_assoc, Quaternion.re_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
    ring

/-- The symmetric bilinear form of one plaquette. -/
def pb (c : ℍ[ℝ]) : PT →ₗ[ℝ] PT →ₗ[ℝ] ℝ := (polar + polar.flip).compr₂ (negReMul c)

theorem pb_apply (c : ℍ[ℝ]) (Y Y' : PT) : pb c Y Y' = -((polar Y Y' + polar Y' Y) * c).re := rfl

theorem pb_comm (c : ℍ[ℝ]) (Y Y' : PT) : pb c Y Y' = pb c Y' Y := by
  rw [pb_apply, pb_apply, add_comm]

theorem pb_bound (c : ℍ[ℝ]) (hc : ‖c‖ ≤ 1) (Y Y' : PT) :
    |pb c Y Y'| ≤ 4 * sumN Y * sumN Y' := by
  rw [pb_apply, abs_neg]
  refine (re_abs_le _).trans ?_
  rw [norm_mul]
  have h1 := polar_norm Y Y'
  have h2 := polar_norm Y' Y
  have h3 := norm_add_le (polar Y Y') (polar Y' Y)
  have h4 : ‖polar Y Y' + polar Y' Y‖ ≤ 4 * sumN Y * sumN Y' := by
    linarith only [h1, h2, h3]
  calc _ ≤ ‖polar Y Y' + polar Y' Y‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact h4

/-- **Locality does the work.** A symmetric bilinear form on the four links of a plaquette, conjugated by
weights that differ by at most `m` across the plaquette, moves by order `m²`. No smallness of the form or of
the plaquette defect is needed. -/
theorem plaq_conj (b : PT →ₗ[ℝ] PT →ₗ[ℝ] ℝ) (K : ℝ) (hK : 0 ≤ K) (hsym : ∀ Y Y', b Y Y' = b Y' Y)
    (hb : ∀ Y Y', |b Y Y'| ≤ K * sumN Y * sumN Y') (ψ : Fin 4 → ℝ) (E m : ℝ) (hm : 0 ≤ m)
    (hψ : ∀ i, |ψ i| ≤ m) (Y : PT) :
    |b (fun i => Real.exp (E + ψ i) • Y i) (fun i => Real.exp (-(E + ψ i)) • Y i) - b Y Y| ≤
      2 * K * Real.sinh m ^ 2 * sumN Y ^ 2 := by
  set a : PT := fun i => Real.cosh (ψ i) • Y i with ha
  set k : PT := fun i => Real.sinh (ψ i) • Y i with hk
  have e1 : (fun i => Real.exp (E + ψ i) • Y i) = Real.exp E • (a + k) := by
    funext i
    change _ = Real.exp E • (Real.cosh (ψ i) • Y i + Real.sinh (ψ i) • Y i)
    rw [← add_smul, smul_smul, Real.cosh_add_sinh, ← Real.exp_add]
  have e2 : (fun i => Real.exp (-(E + ψ i)) • Y i) = Real.exp (-E) • (a - k) := by
    funext i
    change _ = Real.exp (-E) • (Real.cosh (ψ i) • Y i - Real.sinh (ψ i) • Y i)
    rw [← sub_smul, smul_smul, Real.cosh_sub_sinh, ← Real.exp_add, neg_add]
  have hch := Real.cosh_sq m
  have hc1 := Real.one_le_cosh m
  have hs0 : 0 ≤ Real.sinh m := Real.sinh_nonneg_iff.2 hm
  have main : b (Real.exp E • (a + k)) (Real.exp (-E) • (a - k)) - b Y Y =
      b (a - Y) a + b Y (a - Y) - b k k := by
    have hexp : Real.exp E * Real.exp (-E) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_add, map_sub, LinearMap.add_apply,
      LinearMap.sub_apply]
    rw [hsym k a]
    linear_combination (b a a - b a k + (b a k - b k k)) * hexp
  rw [e1, e2, main]
  set t := sumN Y with ht
  have ht0 : 0 ≤ t := sumN_nonneg Y
  have hay : sumN (a - Y) ≤ (Real.cosh m - 1) * t := by
    have e : a - Y = fun i => (Real.cosh (ψ i) - 1) • Y i := by
      funext i
      change Real.cosh (ψ i) • Y i - Y i = _
      rw [sub_smul, one_smul]
    rw [e]
    refine sumN_smul_le _ _ (fun i => ?_) Y
    have h1 := Real.one_le_cosh (ψ i)
    rw [abs_of_nonneg (by linarith only [h1])]
    have h2 : Real.cosh (ψ i) ≤ Real.cosh m := by
      rw [Real.cosh_le_cosh, abs_of_nonneg hm]
      exact hψ i
    linarith only [h2]
  have haa : sumN a ≤ Real.cosh m * t := by
    refine sumN_smul_le _ _ (fun i => ?_) Y
    rw [abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh, abs_of_nonneg hm]
    exact hψ i
  have hkk : sumN k ≤ Real.sinh m * t := by
    refine sumN_smul_le _ _ (fun i => ?_) Y
    rw [Real.abs_sinh]
    exact Real.sinh_le_sinh.2 (hψ i)
  have b1 : |b (a - Y) a| ≤ K * ((Real.cosh m - 1) * t) * (Real.cosh m * t) :=
    (hb _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hay hK) haa (sumN_nonneg _)
      (mul_nonneg hK (mul_nonneg (by linarith only [hc1]) ht0)))
  have b2 : |b Y (a - Y)| ≤ K * t * ((Real.cosh m - 1) * t) :=
    (hb _ _).trans (mul_le_mul_of_nonneg_left hay (mul_nonneg hK ht0))
  have b3 : |b k k| ≤ K * (Real.sinh m * t) * (Real.sinh m * t) :=
    (hb _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hkk hK) hkk (sumN_nonneg _)
      (mul_nonneg hK (mul_nonneg hs0 ht0)))
  have tri : |b (a - Y) a + b Y (a - Y) - b k k| ≤ |b (a - Y) a| + |b Y (a - Y)| + |b k k| :=
    (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
  refine tri.trans ?_
  have e3 : K * ((Real.cosh m - 1) * t) * (Real.cosh m * t) + K * t * ((Real.cosh m - 1) * t) +
      K * (Real.sinh m * t) * (Real.sinh m * t) = 2 * K * Real.sinh m ^ 2 * t ^ 2 := by
    linear_combination K * t ^ 2 * hch
  linarith only [b1, b2, b3, e3]

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Evaluation at one link. -/
def atL (ν : Fin 4) (z : V') : VF V' ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] where
  toFun f := f ν z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The four frame-transported rotations of a plaquette, linear in the field. -/
def Yp (U : V' → Fin 4 → Q) (p : PlaquetteIndex (2 * n)) : VF V' ℍ[ℝ] →ₗ[ℝ] PT :=
  LinearMap.pi ![atL n p.2.1.1 p.1,
    AdLin (U p.1 p.2.1.1) ∘ₗ atL n p.2.1.2 (step (2 * n) p.1 p.2.1.1),
    -(AdLin (U p.1 p.2.1.1 * U (step (2 * n) p.1 p.2.1.1) p.2.1.2 *
      (U (step (2 * n) p.1 p.2.1.2) p.2.1.1)⁻¹) ∘ₗ atL n p.2.1.1 (step (2 * n) p.1 p.2.1.2)),
    -(AdLin (U p.1 p.2.1.1 * U (step (2 * n) p.1 p.2.1.1) p.2.1.2 *
      (U (step (2 * n) p.1 p.2.1.2) p.2.1.1)⁻¹ * (U p.1 p.2.1.2)⁻¹) ∘ₗ atL n p.2.1.2 p.1)]

/-- The base points of the four links. -/
def site (p : PlaquetteIndex (2 * n)) : Fin 4 → V' :=
  ![p.1, step (2 * n) p.1 p.2.1.1, step (2 * n) p.1 p.2.1.2, p.1]

theorem Yp_Wt (U : V' → Fin 4 → Q) (p : PlaquetteIndex (2 * n)) (φ : V' → ℝ) (h : VF V' ℍ[ℝ]) (i : Fin 4) :
    Yp n U p (Wt φ h) i = Real.exp (φ (site n p i)) • Yp n U p h i := by
  fin_cases i
  · rfl
  · exact Ad_smul _ _ _
  · change -Ad _ (Real.exp _ • _) = Real.exp _ • -Ad _ _
    rw [Ad_smul, smul_neg]
    rfl
  · change -Ad _ (Real.exp _ • _) = Real.exp _ • -Ad _ _
    rw [Ad_smul, smul_neg]
    rfl

/-- The plaquette value with its twist sign removed. -/
def cp (U : V' → Fin 4 → Q) (p : PlaquetteIndex (2 * n)) : ℍ[ℝ] :=
  (if twistExp p.2.1.1 p.2.1.2 p.1 = 1 then (-1 : ℝ) else 1) •
    ((U p.1 p.2.1.1 * U (step (2 * n) p.1 p.2.1.1) p.2.1.2 *
      (U (step (2 * n) p.1 p.2.1.2) p.2.1.1)⁻¹ * (U p.1 p.2.1.2)⁻¹ : Q) : ℍ[ℝ])

theorem cp_norm (U : V' → Fin 4 → Q) (p : PlaquetteIndex (2 * n)) : ‖cp n U p‖ ≤ 1 := by
  unfold cp
  rw [norm_smul, TwistedStability.norm_coe]
  split_ifs <;> simp

/-- **The Hessian of the action as a bilinear form.** Its diagonal is `hess_eq`. -/
def hessB (U : V' → Fin 4 → Q) : VF V' ℍ[ℝ] →ₗ[ℝ] VF V' ℍ[ℝ] →ₗ[ℝ] ℝ :=
  ∑ p : PlaquetteIndex (2 * n), (pb (cp n U p)).compl₁₂ (Yp n U p) (Yp n U p)

theorem hessB_apply (U : V' → Fin 4 → Q) (f g : VF V' ℍ[ℝ]) :
    hessB n U f g = ∑ p : PlaquetteIndex (2 * n), pb (cp n U p) (Yp n U p f) (Yp n U p g) := by
  simp [hessB, LinearMap.sum_apply]

theorem hessB_comm (U : V' → Fin 4 → Q) (f g : VF V' ℍ[ℝ]) : hessB n U f g = hessB n U g f := by
  rw [hessB_apply, hessB_apply]
  exact Finset.sum_congr rfl fun p _ => pb_comm _ _ _

/-- The direction `X` as a vector field. -/
abbrev Xf (X : Fin 3 → Fin 4 → Section (2 * n)) : VF V' ℍ[ℝ] := fun μ => Xh n X μ

theorem hess_diag (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    hessB n U (Xf n X) (Xf n X) = ∑ p : PlaquetteIndex (2 * n),
      -(2 * (secondCoeff (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₂
        (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₄ *
          plaqC n U X p.1 p.2.1.1 p.2.1.2).re) := by
  rw [hessB_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pb_apply, polar_self, add_mul, Quaternion.re_add]
  have e : secondCoeff (Yp n U p (Xf n X) 0) (Yp n U p (Xf n X) 1) (Yp n U p (Xf n X) 2)
      (Yp n U p (Xf n X) 3) * cp n U p =
      secondCoeff (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₂
        (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₄ *
          plaqC n U X p.1 p.2.1.1 p.2.1.2 := rfl
  rw [e]
  ring

/-- **The form is the actual second derivative.** For every `β`, every field `U` and every direction. -/
theorem hess_eq (β : ℝ) (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 =
      β * hessB n U (Xf n X) (Xf n X) := by
  rw [second_derivative_field, hess_diag]

/-- Conjugating the Hessian. Nothing about `U` enters. -/
theorem hessB_conj (U : V' → Fin 4 → Q) (φ : V' → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hφ : ∀ μ x, |φ x - φ (step (2 * n) x μ)| ≤ m) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    |hessB n U (Wt φ (Xf n X)) (Wt (-φ) (Xf n X)) - hessB n U (Xf n X) (Xf n X)| ≤
      192 * Real.sinh m ^ 2 * nsq (Xf n X) := by
  rw [hessB_apply, hessB_apply, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hp (p : PlaquetteIndex (2 * n)) :
      |pb (cp n U p) (Yp n U p (Wt φ (Xf n X))) (Yp n U p (Wt (-φ) (Xf n X))) -
        pb (cp n U p) (Yp n U p (Xf n X)) (Yp n U p (Xf n X))| ≤
      32 * Real.sinh m ^ 2 * linkSq n X p.1 p.2.1.1 p.2.1.2 := by
    set ψ : Fin 4 → ℝ := fun i => φ (site n p i) - φ p.1 with hψ
    have e1 : Yp n U p (Wt φ (Xf n X)) =
        fun i => Real.exp (φ p.1 + ψ i) • Yp n U p (Xf n X) i := by
      funext i
      rw [Yp_Wt, hψ, add_sub_cancel]
    have e2 : Yp n U p (Wt (-φ) (Xf n X)) =
        fun i => Real.exp (-(φ p.1 + ψ i)) • Yp n U p (Xf n X) i := by
      funext i
      rw [Yp_Wt, hψ, add_sub_cancel]
      rfl
    have hbound : ∀ i, |ψ i| ≤ m := by
      intro i
      rw [hψ]
      fin_cases i
      · simpa [site] using hm
      · have := hφ p.2.1.1 p.1
        rw [abs_sub_comm] at this
        exact this
      · have := hφ p.2.1.2 p.1
        rw [abs_sub_comm] at this
        exact this
      · simpa [site] using hm
    have key := plaq_conj (pb (cp n U p)) 4 (by norm_num) (pb_comm _)
      (pb_bound _ (cp_norm n U p)) ψ (φ p.1) m hm hbound (Yp n U p (Xf n X))
    rw [← e1, ← e2] at key
    have hs : sumN (Yp n U p (Xf n X)) = linkSum n X p.1 p.2.1.1 p.2.1.2 := by
      have := plaq_norms n U X p.1 p.2.1.1 p.2.1.2
      rw [← this]
      simp only [sumN, Fin.sum_univ_four]
      rfl
    rw [hs] at key
    have hl := linkSum_sq n X p.1 p.2.1.1 p.2.1.2
    have hsh := sq_nonneg (Real.sinh m)
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hsh)
    refine key.trans ?_
    nlinarith only [this]
  refine (Finset.sum_le_sum fun p _ => hp p).trans (le_of_eq ?_)
  have hc : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  rw [← Finset.mul_sum, hc]
  have e : nsq (Xf n X) = ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := Xh_norm n X
  rw [e]
  ring

/-! ### The full fluctuation form -/

/-- **The fluctuation form at a background:** the Hessian, the covariant divergence, and the block penalty,
exactly the right side of `cov_block_coercive` at `β = 1`. -/
def hessForm (U : V' → Fin 4 → Q) (L : ℕ) : VF V' ℍ[ℝ] →ₗ[ℝ] VF V' ℍ[ℝ] →ₗ[ℝ] ℝ :=
  hessB n U + bil (divRow (covShift U)) + (1 / (4 * (L : ℝ) ^ 2)) • ∑ μ, bil (blockRow (covShift U) L μ)

theorem hessForm_apply (U : V' → Fin 4 → Q) (L : ℕ) (f g : VF V' ℍ[ℝ]) :
    hessForm n U L f g = hessB n U f g + ⟪div (covShift U) f, div (covShift U) g⟫ +
      1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ⟪blockAvg (covShift U) L (f μ), blockAvg (covShift U) L (g μ)⟫ := by
  simp only [hessForm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, bil_apply,
    divRow_apply, blockRow_apply, smul_eq_mul]

theorem hessForm_comm (U : V' → Fin 4 → Q) (L : ℕ) (f g : VF V' ℍ[ℝ]) :
    hessForm n U L f g = hessForm n U L g f := by
  rw [hessForm_apply, hessForm_apply, hessB_comm]
  simp only [real_inner_comm]

/-- **The diagonal of `β · hessForm` is the actual fluctuation form,** the right side of `cov_block_coercive`. At a
nonzero defect `U` is not a critical point of the action, so this is the second-order term around a non-saddle, and
the first-order term is not treated. -/
theorem hessForm_diag (β : ℝ) (U : V' → Fin 4 → Q) (L : ℕ) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    β * hessForm n U L (Xf n X) (Xf n X) =
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 +
        β * (‖div (covShift U) (Xh n X)‖ ^ 2 +
          1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (Xh n X μ)‖ ^ 2) := by
  rw [hess_eq, hessForm_apply]
  simp only [real_inner_self_eq_norm_sq]
  ring

/-- The cost of the weight on the full form. -/
def ErrH (m : ℝ) (L : ℕ) : ℝ :=
  192 * Real.sinh m ^ 2 + (16 * (Real.cosh m - 1) + 4 * Real.sinh m ^ 2) +
    1 / (4 * (L : ℝ) ^ 2) * (2 * (Real.cosh (4 * L * m) - 1) + Real.sinh (4 * L * m) ^ 2)

/-- The cost at the rate `1/(100 L)` leaves half of the constant of `cov_block_coercive`. -/
theorem hess_numbers (L : ℕ) (hL : 1 ≤ L) :
    1 / (32 * (L : ℝ) ^ 2) ≤ 1 / (16 * (L : ℝ) ^ 2) - ErrH (1 / (100 * L)) L := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set m : ℝ := 1 / (100 * L) with hm
  have hm0 : 0 ≤ m := by positivity
  have h4 : 4 * (L : ℝ) * m = 1 / 25 := by
    rw [hm]
    field_simp
    norm_num
  have hmh : m ≤ 1 / 2 := by
    nlinarith only [h4, hm0, hL1]
  have hab : |m| ≤ 1 / 2 := by rwa [abs_of_nonneg hm0]
  have h1 := cosh_sub_one_le m hab
  have h2 := sinh_sq_le m hab
  have hab2 : |4 * (L : ℝ) * m| ≤ 1 / 2 := by
    rw [h4, abs_of_nonneg (by norm_num)]
    norm_num
  have h3 := cosh_sub_one_le _ hab2
  have h5 := sinh_sq_le _ hab2
  have h6 : 2 * (Real.cosh (4 * L * m) - 1) + Real.sinh (4 * L * m) ^ 2 ≤
      38 / 15 * (16 * (L : ℝ) ^ 2 * m ^ 2) := by
    have e : (4 * (L : ℝ) * m) ^ 2 = 16 * (L : ℝ) ^ 2 * m ^ 2 := by ring
    rw [e] at h3 h5
    linarith only [h3, h5]
  have hp : 0 ≤ 1 / (4 * (L : ℝ) ^ 2) := by positivity
  have h7 := mul_le_mul_of_nonneg_left h6 hp
  have e2 : 1 / (4 * (L : ℝ) ^ 2) * (38 / 15 * (16 * (L : ℝ) ^ 2 * m ^ 2)) = 152 / 15 * m ^ 2 := by
    field_simp
    ring
  rw [e2] at h7
  set y : ℝ := 1 / (L : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have e3 : m ^ 2 = y / 10000 := by
    rw [hm, hy]
    field_simp
    norm_num
  have e4 : 1 / (16 * (L : ℝ) ^ 2) = y / 16 := by
    rw [hy]
    field_simp
  have e5 : 1 / (32 * (L : ℝ) ^ 2) = y / 32 := by
    rw [hy]
    field_simp
  rw [e4, e5]
  unfold ErrH
  rw [e3] at h1 h2 h7
  nlinarith only [h1, h2, h7, hy0]

/-! ### Imaginary fields -/

/-- Fields with values in the Lie algebra. -/
def imagV : Submodule ℝ (VF V' ℍ[ℝ]) where
  carrier := {h | ∀ μ x, (h μ x).re = 0}
  add_mem' := by
    intro a b ha hb μ x
    change (a μ x + b μ x).re = 0
    rw [Quaternion.re_add, ha, hb, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c a ha μ x
    change (c • a μ x).re = 0
    rw [Quaternion.re_smul, ha, smul_zero]

theorem imagV_Wt (ψ : V' → ℝ) (h : VF V' ℍ[ℝ]) (hh : h ∈ imagV n) : Wt ψ h ∈ imagV n := by
  intro μ x
  change (Real.exp (ψ x) • h μ x).re = 0
  rw [Quaternion.re_smul, hh, smul_zero]

/-- Colour coordinates of an imaginary field. -/
def toX (h : VF V' ℍ[ℝ]) : Fin 3 → Fin 4 → Section (2 * n) := fun a μ =>
  WithLp.toLp 2 fun x => ![(h μ x).imI, (h μ x).imJ, (h μ x).imK] a

theorem Xf_toX (h : VF V' ℍ[ℝ]) (hh : h ∈ imagV n) : Xf n (toX n h) = h := by
  funext μ
  ext x : 1
  change imag (toX n h) μ x = h μ x
  have h0 := hh μ x
  ext <;> simp [imag, toX, Fin.sum_univ_three, basis, h0]

/-- Conjugating the full form. -/
theorem hessForm_conj (U : V' → Fin 4 → Q) (φ : V' → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hφ : ∀ μ x, |φ x - φ (step (2 * n) x μ)| ≤ m) (L : ℕ) (hL : 1 ≤ L) (h : VF V' ℍ[ℝ])
    (hh : h ∈ imagV n) :
    hessForm n U L h h - ErrH m L * nsq h ≤ hessForm n U L (Wt φ h) (Wt (-φ) h) := by
  have hT (μ : Fin 4) : Tame φ (covShift U μ).T m :=
    tame_T _ (stepEquiv μ) (cov_intertwines U μ) hm (hφ μ)
  have hS (μ : Fin 4) : Tame φ (covShift U μ).S m :=
    tame_S _ (stepEquiv μ) (cov_intertwines U μ) hm (hφ μ)
  have h1 := hessB_conj n U φ m hm hφ (toX n h)
  rw [Xf_toX n h hh] at h1
  have h2 := div_conj (covShift U) φ m hS h
  have h3 := mul_le_mul_of_nonneg_left (block_conj (covShift U) φ m hm hT L hL h)
    (by positivity : (0 : ℝ) ≤ 1 / (4 * (L : ℝ) ^ 2))
  have h4 := (abs_le.1 h1).1
  rw [hessForm_apply, hessForm_apply, real_inner_self_eq_norm_sq]
  simp only [real_inner_self_eq_norm_sq]
  unfold ErrH
  nlinarith only [h2, h3, h4]

/-- **The coercive constant of the actual form,** from `cov_block_coercive`. -/
theorem hessForm_coercive (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2)) (h : VF V' ℍ[ℝ])
    (hh : h ∈ imagV n) : 1 / (16 * (L : ℝ) ^ 2) * nsq h ≤ hessForm n U L h h := by
  have key := cov_block_coercive n 1 (by norm_num) U (toX n h) L hL hδ
  rw [hess_eq] at key
  have hX := Xf_toX n h hh
  have hn : ∑ a, ∑ μ, ‖toX n h a μ‖ ^ 2 = nsq h := by
    rw [← Xh_norm n (toX n h)]
    change nsq (Xf n (toX n h)) = _
    rw [hX]
  rw [hn] at key
  have e1 : Xh n (toX n h) = h := hX
  rw [hessForm_apply]
  simp only [real_inner_self_eq_norm_sq]
  simp only [one_mul, e1] at key
  rw [hX] at key
  linarith only [key]

/-- Coercivity away from bad plaquettes, from `block_coercive_avoids`. -/
theorem hessForm_coercive_avoid (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (h : VF V' ℍ[ℝ])
    (hh : h ∈ imagV n) (ha : h ∈ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))) :
    1 / (16 * (L : ℝ) ^ 2) * nsq h ≤ hessForm n U L h h := by
  have hX := Xf_toX n h hh
  have hav : Avoids n U (1 / (1000 * (L : ℝ) ^ 2)) (toX n h) := by
    intro l hl
    have := ha l hl
    have e : Xh n (toX n h) l.2 l.1 = h l.2 l.1 := by
      rw [show (Xh n (toX n h) : Fin 4 → QField (2 * n)) = h from hX]
    rw [← e] at this
    exact this
  have key := block_coercive_avoids n 1 (by norm_num) U (toX n h) L hL hav
  rw [hess_eq] at key
  have hn : ∑ a, ∑ μ, ‖toX n h a μ‖ ^ 2 = nsq h := by
    rw [← Xh_norm n (toX n h)]
    change nsq (Xf n (toX n h)) = _
    rw [hX]
  rw [hn] at key
  rw [hessForm_apply]
  simp only [real_inner_self_eq_norm_sq]
  simp only [one_mul] at key
  rw [hX] at key
  have e2 : div (covShift U) (Xh n (toX n h)) = div (covShift U) h := by
    rw [show (Xh n (toX n h) : Fin 4 → QField (2 * n)) = h from hX]
  have e3 : ∀ μ, blockAvg (covShift U) L (Xh n (toX n h) μ) = blockAvg (covShift U) L (h μ) := by
    intro μ
    rw [show (Xh n (toX n h) : Fin 4 → QField (2 * n)) = h from hX]
  simp only [e2, e3] at key
  linarith only [key]

/-- The decay statement for the actual form on a weight-stable subspace of the imaginary fields where it
is coercive with the constant of `cov_block_coercive`. -/
theorem hessForm_decay (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (P : VF V' ℍ[ℝ] → Prop) (hPi : ∀ h, P h → h ∈ imagV n)
    (hV : ∀ (ψ : V' → ℝ) h, P h → P (Wt ψ h))
    (hc : ∀ h, P h → 1 / (16 * (L : ℝ) ^ 2) * nsq h ≤ hessForm n U L h h)
    (g : VF V' ℍ[ℝ]) (hg : P g) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f, P f → β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 32 * (L : ℝ) ^ 2 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set m : ℝ := 1 / (100 * L) with hm
  have hm0 : 0 ≤ m := by positivity
  have hn := hess_numbers L hL
  rw [← hm] at hn
  have hconj : ∀ h, P h → β * (1 / (32 * (L : ℝ) ^ 2)) * nsq h ≤
      (β • hessForm n U L) (Wt (distW m y) h) (Wt (-distW m y) h) := by
    intro h hP
    have h1 := hc h hP
    have h2 := hessForm_conj n U (distW m y) m hm0 (fun μ x => distW_lip m hm0 y x μ) L hL h (hPi h hP)
    have h3 := mul_le_mul_of_nonneg_right hn (nsq_nonneg h)
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    rw [sub_mul] at h3
    linarith only [h1, h2, h3]
  have hpos : 0 < β * (1 / (32 * (L : ℝ) ^ 2)) := by positivity
  have key := green_decay (β • hessForm n U L) P (distW m y) _ hpos hV hconj g hg μ y v
    (fun f hf => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      exact hs f hf) ν x
  rw [distW_diff] at key
  have e3 : m * (dist1 x y : ℝ) = (dist1 x y : ℝ) / (100 * L) := by
    rw [hm]
    ring
  rw [e3] at key
  have h2 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 32 * (L : ℝ) ^ 2 / β)
  have e4 : 32 * (L : ℝ) ^ 2 / β * (β * (1 / (32 * (L : ℝ) ^ 2)) * ‖g ν x‖) = ‖g ν x‖ := by
    field_simp
  rw [e4] at h2
  calc ‖g ν x‖ ≤ _ := h2
    _ = _ := by ring

/-- **The block-scale covariance of the actual action at a near-flat background exists.** -/
theorem hess_exists_unique (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2)) (s : VF V' ℍ[ℝ]) :
    ∃! g, g ∈ imagV n ∧ ∀ f ∈ imagV n, (β • hessForm n U L) f g = ip f s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  refine exists_unique_solution _ (imagV n) (β * (1 / (16 * (L : ℝ) ^ 2))) (by positivity)
    (fun h hh => ?_) s
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hessForm_coercive n U L hL hδ h hh) hβ.le

/-- **Pointwise decay of the covariance of the actual action, uniform in `N`, with prefactor `L²`.** Let `U` have all
plaquette defects at most `1/(1000 L²)`. Let `g` solve the weak equation for the second derivative of the actual
twisted action plus `β` times the covariant divergence and block penalty, with a source at the link `(y, μ)`. Then
`‖g ν x‖ ≤ (32 L²/β) exp(-dist(x,y)/(100 L)) ‖v‖`. No constant involves `N` or the distance from flat. Coercivity
alone gives `16 L²/β` at every distance, so this has content only past `dist > 69.4 L`, so `N > 34.7 L`. The uniform
rate comes from the added penalty. For `L ≥ 3` this is superseded by `hess_decay_unif`, which needs `L ≤ 2n`. -/
theorem hess_decay (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF V' ℍ[ℝ]) (hg : g ∈ imagV n) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ imagV n, β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 32 * (L : ℝ) ^ 2 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ :=
  hessForm_decay n β hβ U L hL (· ∈ imagV n) (fun _ h => h) (fun ψ h hh => imagV_Wt n ψ h hh)
    (fun h hh => hessForm_coercive n U L hL hδ h hh) g hg μ y v hs ν x

/-- The energy of the actual form controls point values with a constant free of `N` and `L`. The hypotheses are
the two facts that are proved globally and, away from bad plaquettes, locally. -/
theorem hessForm_point_of (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n) (h : VF V' ℍ[ℝ])
    (hcurl : curlEnergy (covShift U) h - (192 * (1 / (1000 * (L : ℝ) ^ 2)) ^ 2 + 48 * (1 / (1000 * (L : ℝ) ^ 2))) *
      nsq h ≤ hessB n U h h)
    (hbd : ∀ μ ν, |⟪(covShift U μ).Dstar (h μ), (covShift U ν).Dstar (h ν)⟫ -
      ⟪(covShift U ν).D (h μ), (covShift U μ).D (h ν)⟫| ≤
        (2 * (1 / (1000 * (L : ℝ) ^ 2))) * ‖h μ‖ * ‖h ν‖)
    (hco : 1 / (16 * (L : ℝ) ^ 2) * nsq h ≤ hessForm n U L h h) (ν : Fin 4) (x : V') :
    ‖h ν x‖ ^ 2 ≤ 116 * hessForm n U L h h := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set z : ℝ := 1 / (L : ℝ) ^ 2 with hz
  have hz0 : 0 < z := by positivity
  have hz1 : z ≤ 1 := by
    rw [hz]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hL1)
  have eLz : (L : ℝ) ^ 2 * z = 1 := by
    rw [hz]
    field_simp
  have e1 : 1 / (1000 * (L : ℝ) ^ 2) = z / 1000 := by
    rw [hz]
    field_simp
  have e16 : 1 / (16 * (L : ℝ) ^ 2) = z / 16 := by
    rw [hz]
    field_simp
  have hκ : 0 ≤ 2 * (z / 1000) := by positivity
  rw [e1] at hcurl hbd
  rw [e16] at hco
  have hW := weitzenbock_of_cross (covShift U) _ hκ h hbd
  have hYa : hessForm n U L h h = hessB n U h h + ‖div (covShift U) h‖ ^ 2 +
      1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (h μ)‖ ^ 2 := by
    rw [hessForm_apply]
    simp only [real_inner_self_eq_norm_sq]
  have hp : 0 ≤ 1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (h μ)‖ ^ 2 := by positivity
  set Y := hessForm n U L h h with hYd
  have hnn : 0 ≤ nsq h := nsq_nonneg h
  have hzn : 0 ≤ z * nsq h := by positivity
  have hY0 : 0 ≤ Y := by
    have : z / 16 * nsq h = 1 / 16 * (z * nsq h) := by ring
    linarith only [hco, hzn, this]
  have hn : nsq h ≤ 16 * (L : ℝ) ^ 2 * Y := by
    have m := mul_le_mul_of_nonneg_left hco (by positivity : (0 : ℝ) ≤ 16 * (L : ℝ) ^ 2)
    have e : 16 * (L : ℝ) ^ 2 * (z / 16 * nsq h) = nsq h := by
      calc _ = ((L : ℝ) ^ 2 * z) * nsq h := by ring
        _ = _ := by rw [eLz, one_mul]
    rwa [e] at m
  have hg : ∑ μ, ∑ ρ, ‖(covShift U ρ).D (h μ)‖ ^ 2 ≤ 19 / 10 * Y := by
    have e : 4 * (2 * (z / 1000)) * ∑ μ, ‖h μ‖ ^ 2 = 1 / 125 * (z * nsq h) := by
      unfold nsq
      ring
    rw [e] at hW
    have e2 : (192 * (z / 1000) ^ 2 + 48 * (z / 1000)) * nsq h =
        (48 / 1000 + 192 / 1000000 * z) * (z * nsq h) := by ring
    rw [e2] at hcurl
    have h3 : (48 / 1000 + 192 / 1000000 * z) * (z * nsq h) ≤ (48 / 1000 + 192 / 1000000) * (z * nsq h) :=
      mul_le_mul_of_nonneg_right (by linarith only [hz1]) hzn
    nlinarith only [hW, hcurl, hYa, hp, hco, h3, hzn, hY0]
  have key := point_sq_le (covShift U) (fun μ g x => cov_iso U μ g x) h Y (19 / 10) 16 3 hY0
    (by norm_num) (by norm_num) hg L hL hLN hn ν x
  exact key.trans (mul_le_mul_of_nonneg_right (by norm_num) hY0)

/-- The curl hypothesis of `hessForm_point_of`, for imaginary fields at a background with small defects. -/
theorem hess_curl_of_small (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (h : VF V' ℍ[ℝ]) (hh : h ∈ imagV n) :
    curlEnergy (covShift U) h - (192 * δ ^ 2 + 48 * δ) * nsq h ≤ hessB n U h h := by
  have key := hessian_cov_lower n 1 (by norm_num) U (toX n h) δ hδ0 hδ
  rw [hess_eq] at key
  have hX := Xf_toX n h hh
  have hn : ∑ a, ∑ μ, ‖toX n h a μ‖ ^ 2 = nsq h := by
    rw [← Xh_norm n (toX n h)]
    change nsq (Xf n (toX n h)) = _
    rw [hX]
  have e1 : Xh n (toX n h) = h := hX
  rw [hn, e1] at key
  rw [hX] at key
  linarith only [key]

theorem hess_curl_of_avoid (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ) (h : VF V' ℍ[ℝ]) (hh : h ∈ imagV n)
    (ha : h ∈ avoidV n U δ) :
    curlEnergy (covShift U) h - (192 * δ ^ 2 + 48 * δ) * nsq h ≤ hessB n U h h := by
  have hX := Xf_toX n h hh
  have hav : Avoids n U δ (toX n h) := by
    intro l hl
    have := ha l hl
    have e : Xh n (toX n h) l.2 l.1 = h l.2 l.1 := by
      rw [show (Xh n (toX n h) : Fin 4 → QField (2 * n)) = h from hX]
    rw [← e] at this
    exact this
  have key := hessian_avoids n 1 (by norm_num) U (toX n h) δ hδ0 hav
  rw [hess_eq] at key
  have hn : ∑ a, ∑ μ, ‖toX n h a μ‖ ^ 2 = nsq h := by
    rw [← Xh_norm n (toX n h)]
    change nsq (Xf n (toX n h)) = _
    rw [hX]
  have e1 : Xh n (toX n h) = h := hX
  rw [hn, e1] at key
  rw [hX] at key
  linarith only [key]

/-- The energy-norm decay for the actual form. -/
theorem hessForm_decay_unif (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (P : VF V' ℍ[ℝ] → Prop) (hPi : ∀ h, P h → h ∈ imagV n)
    (hV : ∀ (ψ : V' → ℝ) h, P h → P (Wt ψ h))
    (hc : ∀ h, P h → 1 / (16 * (L : ℝ) ^ 2) * nsq h ≤ hessForm n U L h h)
    (hpt : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ 116 * hessForm n U L h h)
    (g : VF V' ℍ[ℝ]) (hg : P g) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f, P f → β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 232 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith only [hL1]
  set m : ℝ := 1 / (100 * L) with hm
  have hm0 : 0 ≤ m := by positivity
  have hn := hess_numbers L hL
  rw [← hm] at hn
  have hconj : ∀ h, P h → 1 / 2 * (β • hessForm n U L) h h ≤
      (β • hessForm n U L) (Wt (distW m y) h) (Wt (-distW m y) h) := by
    intro h hP
    have h1 := hc h hP
    have h2 := hessForm_conj n U (distW m y) m hm0 (fun μ x => distW_lip m hm0 y x μ) L hL h (hPi h hP)
    have h3 := mul_le_mul_of_nonneg_right hn (nsq_nonneg h)
    simp only [LinearMap.smul_apply, smul_eq_mul]
    have h4 : 1 / 2 * hessForm n U L h h ≤ hessForm n U L (Wt (distW m y) h) (Wt (-distW m y) h) := by
      have hnn := nsq_nonneg h
      set z : ℝ := 1 / (L : ℝ) ^ 2 with hz
      have hz0 : 0 < z := by positivity
      have e1 : 1 / (16 * (L : ℝ) ^ 2) = z / 16 := by
        rw [hz]
        field_simp
      have e2 : 1 / (32 * (L : ℝ) ^ 2) = z / 32 := by
        rw [hz]
        field_simp
      rw [e1, e2] at h3
      rw [e1] at h1
      have hzn := mul_nonneg hz0.le hnn
      nlinarith only [h1, h2, h3, hzn]
    have := mul_le_mul_of_nonneg_left h4 hβ.le
    linarith only [this]
  have hpt' : ∀ h, P h → ∀ ν x, ‖h ν x‖ ^ 2 ≤ 116 / β * (β • hessForm n U L) h h := by
    intro h hP ν x
    have e : 116 / β * (β • hessForm n U L) h h = 116 * hessForm n U L h h := by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      field_simp
    rw [e]
    exact hpt h hP ν x
  have key := green_energy (β • hessForm n U L) P (distW m y) (1 / 2) (116 / β) (by norm_num) (by positivity)
    hV hconj hpt' g hg μ y v
    (fun f hf => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      exact hs f hf) ν x
  rw [distW_diff] at key
  have e3 : m * (dist1 x y : ℝ) = (dist1 x y : ℝ) / (100 * L) := by
    rw [hm]
    ring
  rw [e3] at key
  have e4 : 232 / β = 2 * (116 / β) := by ring
  rw [e4]
  linarith only [key]

/-- **The diagonal of the covariance of the actual action is at most `116/β`.** No constant involves `L` or `N`. -/
theorem hess_point (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF V' ℍ[ℝ]) (hg : g ∈ imagV n) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ imagV n, β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 116 / β * ‖v‖ := by
  refine green_point (β • hessForm n U L) (· ∈ imagV n) (116 / β) (by positivity)
    (fun ψ h hh => imagV_Wt n ψ h hh) (fun h hh ν x => ?_) g hg μ y v
    (fun f hf => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      exact hs f hf) ν x
  have e : 116 / β * (β • hessForm n U L) h h = 116 * hessForm n U L h h := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [e]
  exact hessForm_point_of n U L hL hLN h
    (hess_curl_of_small n U _ (by positivity) hδ h hh)
    (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _)
    (hessForm_coercive n U L hL hδ h hh) ν x

/-- **Pointwise decay of the covariance of the actual action, with prefactor free of `L` and `N`.** The form and rate
are those of `hess_decay`. This improves on `hess_point` only past `dist > 69.4 L`, so `N > 34.7 L`. The uniform rate
comes from the added penalty. This is a linear statement at a fixed background, with no effective action. -/
theorem hess_decay_unif (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g : VF V' ℍ[ℝ]) (hg : g ∈ imagV n) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ imagV n, β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 232 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ :=
  hessForm_decay_unif n β hβ U L hL (· ∈ imagV n) (fun _ h => h) (fun ψ h hh => imagV_Wt n ψ h hh)
    (fun h hh => hessForm_coercive n U L hL hδ h hh)
    (fun h hh ν x => hessForm_point_of n U L hL hLN h
      (hess_curl_of_small n U _ (by positivity) hδ h hh)
      (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _)
      (hessForm_coercive n U L hL hδ h hh) ν x)
    g hg μ y v hs ν x

/-- **The covariance of the actual action on an `L²` source:** `‖g ν x‖² ≤ (1856 L²/β²) ‖s‖²`. For a source spread
over a box of side `L` with total mass one this gives `‖g ν x‖ ≤ 44/(β L)`. -/
theorem hess_point_source (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2))
    (g s : VF V' ℍ[ℝ]) (hg : g ∈ imagV n) (hs : ∀ f ∈ imagV n, β * hessForm n U L f g = ip f s) (ν : Fin 4)
    (x : V') : ‖g ν x‖ ^ 2 ≤ 1856 * (L : ℝ) ^ 2 / β ^ 2 * nsq s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have key := green_source (β • hessForm n U L) (· ∈ imagV n) (β * (1 / (16 * (L : ℝ) ^ 2))) (116 / β)
    (by positivity) (by positivity)
    (fun h hh => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hessForm_coercive n U L hL hδ h hh) hβ.le)
    (fun h hh ν x => by
      have e : 116 / β * (β • hessForm n U L) h h = 116 * hessForm n U L h h := by
        simp only [LinearMap.smul_apply, smul_eq_mul]
        field_simp
      rw [e]
      exact hessForm_point_of n U L hL hLN h
        (hess_curl_of_small n U _ (by positivity) hδ h hh)
        (fun μ ν => cross_error _ _ _ (cov_comm U _ (by positivity) hδ μ ν) _ _)
        (hessForm_coercive n U L hL hδ h hh) ν x)
    g s hg (fun f hf => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
      exact hs f hf) ν x
  have e : 1856 * (L : ℝ) ^ 2 / β ^ 2 * nsq s =
      (β * (1 / (16 * (L : ℝ) ^ 2)))⁻¹ * (116 / β * nsq s) := by
    field_simp
    ring
  rw [e, ← div_eq_inv_mul, le_div_iff₀ (by positivity), mul_comm]
  exact key

/-- The Lie-algebra directions that vanish on the links of bad plaquettes. -/
abbrev goodV (U : V' → Fin 4 → Q) (L : ℕ) : Submodule ℝ (VF V' ℍ[ℝ]) :=
  imagV n ⊓ avoidV n U (1 / (1000 * (L : ℝ) ^ 2))

/-- **Existence of the restricted covariance, for every field.** -/
theorem hess_exists_unique_avoid (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (s : VF V' ℍ[ℝ]) :
    ∃! g, g ∈ goodV n U L ∧ ∀ f ∈ goodV n U L, (β • hessForm n U L) f g = ip f s := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  refine exists_unique_solution _ (goodV n U L) (β * (1 / (16 * (L : ℝ) ^ 2))) (by positivity)
    (fun h hh => ?_) s
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hessForm_coercive_avoid n U L hL h hh.1 hh.2) hβ.le

/-- **Pointwise decay of the restricted covariance, for every field.** Nothing is assumed about `U`. Restrict
the actual fluctuation form to Lie-algebra directions vanishing on the links of plaquettes with defect above
`1/(1000 L²)`. Then the Dirichlet covariance has the same decay and prefactor as `hess_decay`. The statement
degenerates for rough `U`: `goodV` may be `{0}`, and `g = 0` when the source link is excluded. `measure_bad_density`
bounds the bad plaquettes per link by `(log cap(24β) + t)/(β δ²)` with `δ² = 10⁻⁶/L⁴`, and there are `3/2` plaquettes
per link, so the removed links are a small fraction only at `β` of order `10⁶ L⁴` times a logarithm. The excluded
directions are not controlled and the form can be negative on them. -/
theorem hess_decay_avoid (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (g : VF V' ℍ[ℝ]) (hg : g ∈ goodV n U L) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ goodV n U L, β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 32 * (L : ℝ) ^ 2 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ :=
  hessForm_decay n β hβ U L hL (· ∈ goodV n U L) (fun _ h => h.1)
    (fun ψ h hh => ⟨imagV_Wt n ψ h hh.1, avoidV_Wt n U _ ψ h hh.2⟩)
    (fun h hh => hessForm_coercive_avoid n U L hL h hh.1 hh.2) g hg μ y v hs ν x

/-- The energy controls point values on the good directions, for an arbitrary field. -/
theorem goodV_point (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L) (hLN : L ≤ 2 * n) (h : VF V' ℍ[ℝ])
    (hh : h ∈ goodV n U L) (ν : Fin 4) (x : V') : ‖h ν x‖ ^ 2 ≤ 116 * hessForm n U L h h :=
  hessForm_point_of n U L hL hLN h
    (hess_curl_of_avoid n U _ (by positivity) h hh.1 hh.2)
    (cross_avoidV n U _ (by positivity) h hh.2)
    (hessForm_coercive_avoid n U L hL h hh.1 hh.2) ν x

/-- **The restricted covariance has the same prefactor, for every field.** The caveats of `hess_decay_avoid` apply. -/
theorem hess_decay_avoid_unif (β : ℝ) (hβ : 0 < β) (U : V' → Fin 4 → Q) (L : ℕ) (hL : 1 ≤ L)
    (hLN : L ≤ 2 * n) (g : VF V' ℍ[ℝ]) (hg : g ∈ goodV n U L) (μ : Fin 4) (y : V') (v : ℍ[ℝ])
    (hs : ∀ f ∈ goodV n U L, β * hessForm n U L f g = ⟪f μ y, v⟫) (ν : Fin 4) (x : V') :
    ‖g ν x‖ ≤ 232 / β * Real.exp (-((dist1 x y : ℝ) / (100 * L))) * ‖v‖ :=
  hessForm_decay_unif n β hβ U L hL (· ∈ goodV n U L) (fun _ h => h.1)
    (fun ψ h hh => ⟨imagV_Wt n ψ h hh.1, avoidV_Wt n U _ ψ h hh.2⟩)
    (fun h hh => hessForm_coercive_avoid n U L hL h hh.1 hh.2)
    (fun h hh ν x => goodV_point n U L hL hLN h hh ν x) g hg μ y v hs ν x

/-- The covariance is symmetric. With `hessForm_coercive` it is positive on the imaginary fields. -/
theorem hess_green_symm (β : ℝ) (U : V' → Fin 4 → Q) (L : ℕ) (g g' s s' : VF V' ℍ[ℝ])
    (hg : g ∈ imagV n) (hg' : g' ∈ imagV n)
    (hs : ∀ f ∈ imagV n, (β • hessForm n U L) f g = ip f s)
    (hs' : ∀ f ∈ imagV n, (β • hessForm n U L) f g' = ip f s') : ip g' s = ip g s' :=
  green_symm (β • hessForm n U L) (· ∈ imagV n)
    (fun f g => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        hessForm_comm]) g g' s s' hg hg' hs hs'

end Hessian

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedCovarianceDecay
