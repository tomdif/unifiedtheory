/- Background-covariant fluctuation bound at the block scale. For a link field `U` whose plaquette
defects are at most `δ`, the second derivative of the action, the covariant divergence and a penalty on
`U`-covariant running averages of length `L` together bound the fluctuation norm below by `1/(16L²)`
once `δ ≤ 1/(1000 L²)`. Neither the constant nor the condition involves the lattice size, or the distance
from the flat field. It is a pointwise statement about the quadratic form at `U`, not a statement about
the measure, and it does not yet give any effective action. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField
import UnifiedTheory.Clay.YangMills.Twisted.BlockShifts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant
noncomputable section
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField BlockShifts
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion RealInnerProductSpace

/-! ### The adjoint action -/

/-- The adjoint action of a unit quaternion. -/
def Ad (u : Q) (v : ℍ[ℝ]) : ℍ[ℝ] := (u : ℍ[ℝ]) * v * ((u⁻¹ : Q) : ℍ[ℝ])

theorem Ad_add (u : Q) (a b : ℍ[ℝ]) : Ad u (a + b) = Ad u a + Ad u b := by
  simp only [Ad, mul_add, add_mul]

theorem Ad_smul (u : Q) (c : ℝ) (a : ℍ[ℝ]) : Ad u (c • a) = c • Ad u a := by
  simp only [Ad, mul_smul_comm, smul_mul_assoc]

theorem Ad_one (v : ℍ[ℝ]) : Ad 1 v = v := by
  have h : (((1 : Q)⁻¹ : Q) : ℍ[ℝ]) = 1 := by
    rw [inv_one]
    rfl
  unfold Ad
  rw [h]
  change (1 : ℍ[ℝ]) * v * 1 = v
  simp

theorem Ad_mul (g h : Q) (v : ℍ[ℝ]) : Ad (g * h) v = Ad g (Ad h v) := by
  unfold Ad
  rw [mul_inv_rev]
  change (g : ℍ[ℝ]) * (h : ℍ[ℝ]) * v * (((h⁻¹ : Q) : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ])) = _
  simp only [mul_assoc]

theorem norm_Ad (u : Q) (v : ℍ[ℝ]) : ‖Ad u v‖ = ‖v‖ := norm_conj u v

theorem Ad_inv_Ad (u : Q) (v : ℍ[ℝ]) : Ad u⁻¹ (Ad u v) = v := by
  rw [← Ad_mul, inv_mul_cancel, Ad_one]

theorem Ad_Ad_inv (u : Q) (v : ℍ[ℝ]) : Ad u (Ad u⁻¹ v) = v := by
  rw [← Ad_mul, mul_inv_cancel, Ad_one]

theorem Ad_inner (u : Q) (a b : ℍ[ℝ]) : ⟪Ad u a, b⟫ = ⟪a, Ad u⁻¹ b⟫ := by
  have hs : ((u⁻¹ : Q) : ℍ[ℝ]) = star (u : ℍ[ℝ]) := rfl
  have hi : (((u⁻¹)⁻¹ : Q) : ℍ[ℝ]) = u := by rw [inv_inv]
  rw [Quaternion.inner_def, Quaternion.inner_def]
  unfold Ad
  rw [hi, hs, star_mul, star_mul, star_star]
  rw [show (u : ℍ[ℝ]) * a * star (u : ℍ[ℝ]) * star b =
    (u : ℍ[ℝ]) * (a * star (u : ℍ[ℝ]) * star b) by simp only [mul_assoc]]
  rw [re_comm]
  simp only [mul_assoc]

/-- Close to a center element, the adjoint action is close to the identity. -/
theorem Ad_close (P : Q) (k : ℕ) (w : ℍ[ℝ]) : ‖Ad P w - w‖ ≤ 2 * d P (ω ^ k) * ‖w‖ := by
  have h := norm_conj_sub P (ω ^ k * 1) w
  rw [conj_center, mul_one] at h
  have e : ((1 : Q) : ℍ[ℝ]) * w * (((1 : Q)⁻¹ : Q) : ℍ[ℝ]) = w := Ad_one w
  rw [e] at h
  exact h

/-! ### The covariant shift -/

variable {N : ℕ} [NeZero N]

/-- Quaternion-valued fields on the lattice with their `L²` norm. -/
abbrev QField (N : ℕ) [NeZero N] := PiLp 2 (fun _ : Vertex N => ℍ[ℝ])

def covT (U : Vertex N → Fin 4 → Q) (μ : Fin 4) : QField N →ₗ[ℝ] QField N where
  toFun φ := WithLp.toLp 2 fun x => Ad (U x μ) (φ (step N x μ))
  map_add' a b := by
    ext x : 1
    exact Ad_add _ _ _
  map_smul' c a := by
    ext x : 1
    exact Ad_smul _ _ _

def covS (U : Vertex N → Fin 4 → Q) (μ : Fin 4) : QField N →ₗ[ℝ] QField N where
  toFun φ := WithLp.toLp 2 fun x => Ad (U (back x μ) μ)⁻¹ (φ (back x μ))
  map_add' a b := by
    ext x : 1
    exact Ad_add _ _ _
  map_smul' c a := by
    ext x : 1
    exact Ad_smul _ _ _

theorem covT_apply (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (φ : QField N) (x : Vertex N) :
    covT U μ φ x = Ad (U x μ) (φ (step N x μ)) := rfl

theorem covS_apply (U : Vertex N → Fin 4 → Q) (μ : Fin 4) (φ : QField N) (x : Vertex N) :
    covS U μ φ x = Ad (U (back x μ) μ)⁻¹ (φ (back x μ)) := rfl

/-- The `U`-covariant shift in direction `μ`. -/
def covShift (U : Vertex N → Fin 4 → Q) (μ : Fin 4) : Shift (QField N) where
  T := covT U μ
  S := covS U μ
  adj := by
    intro φ ψ
    rw [PiLp.inner_apply, PiLp.inner_apply,
      ← Equiv.sum_comp (stepEquiv (N := N) μ) (fun x => ⟪φ x, covS U μ ψ x⟫)]
    refine Finset.sum_congr rfl fun x _ => ?_
    change ⟪Ad (U x μ) (φ (step N x μ)), ψ x⟫ = ⟪φ (step N x μ), covS U μ ψ (step N x μ)⟫
    rw [covS_apply, back_step, Ad_inner]
  left := by
    intro φ
    ext x : 1
    rw [covS_apply, covT_apply, step_back, Ad_inv_Ad]
  right := by
    intro φ
    ext x : 1
    rw [covT_apply, covS_apply, back_step, Ad_Ad_inv]

theorem norm_sq_field (f : QField N) : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-- A pointwise bound through a reindexing gives a norm bound. -/
theorem norm_le_of_pointwise (f φ : QField N) (e : Vertex N ≃ Vertex N) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x, ‖f x‖ ≤ c * ‖φ (e x)‖) : ‖f‖ ≤ c * ‖φ‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [mul_pow, norm_sq_field f, norm_sq_field φ, ← Equiv.sum_comp e (fun x => ‖φ x‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2

/-- For `μ < ν`, the covariant shifts commute up to twice the defect. -/
theorem cov_comm_lt (U : Vertex N → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (μ ν : Fin 4) (h : μ < ν) (φ : QField N) :
    ‖covT U μ (covT U ν φ) - covT U ν (covT U μ φ)‖ ≤ 2 * δ * ‖φ‖ := by
  refine norm_le_of_pointwise _ φ ((stepEquiv (N := N) ν).trans (stepEquiv μ)) _ (by positivity) ?_
  intro x
  change ‖covT U μ (covT U ν φ) x - covT U ν (covT U μ φ) x‖ ≤ 2 * δ * ‖φ (step N (step N x ν) μ)‖
  rw [covT_apply, covT_apply, covT_apply, covT_apply, step_step_comm x μ ν, ← Ad_mul, ← Ad_mul]
  set a := U x μ
  set b := U (step N x μ) ν
  set c := U (step N x ν) μ
  set e := U x ν
  set v := φ (step N (step N x ν) μ)
  have hP : a * b = (a * b * c⁻¹ * e⁻¹) * (e * c) := by group
  rw [hP, Ad_mul]
  have hc := Ad_close (a * b * c⁻¹ * e⁻¹) (twistExp μ ν x) (Ad (e * c) v)
  rw [norm_Ad] at hc
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
  have := hδ x μ ν h
  have hd : d (a * b * c⁻¹ * e⁻¹) (ω ^ twistExp μ ν x) = defect U μ ν x := rfl
  rw [hd]
  linarith only [this]

theorem cov_comm (U : Vertex N → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (μ ν : Fin 4) (φ : QField N) :
    ‖(covShift U μ).T ((covShift U ν).T φ) - (covShift U ν).T ((covShift U μ).T φ)‖ ≤
      2 * δ * ‖φ‖ := by
  change ‖covT U μ (covT U ν φ) - covT U ν (covT U μ φ)‖ ≤ _
  rcases lt_trichotomy μ ν with h | h | h
  · exact cov_comm_lt U δ hδ0 hδ μ ν h φ
  · subst h
    rw [sub_self, norm_zero]
    positivity
  · rw [norm_sub_rev]
    exact cov_comm_lt U δ hδ0 hδ ν μ h φ

/-! ### The Hessian against the covariant curl -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The perturbation direction as a family of quaternion fields. -/
def Xh (X : Fin 3 → Fin 4 → Section (2 * n)) (μ : Fin 4) : QField (2 * n) :=
  WithLp.toLp 2 fun x => imag X μ x

theorem Xh_apply (X : Fin 3 → Fin 4 → Section (2 * n)) (μ : Fin 4) (x : V') :
    Xh n X μ x = imag X μ x := rfl

theorem Xh_norm (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∑ μ, ‖Xh n X μ‖ ^ 2 = ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := by
  have hn (c : Section (2 * n)) : ‖c‖ ^ 2 = ∑ x, c x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [norm_sq_field]
  simp only [Xh_apply, imag_normSq, hn]
  rw [Finset.sum_comm]

/-- The covariant curl at a point. -/
def covCurl (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (μ ν : Fin 4) (x : V') : ℍ[ℝ] :=
  curl (covShift U) (Xh n X) μ ν x

theorem covCurl_eq (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (μ ν : Fin 4) (x : V') :
    covCurl n U X μ ν x = (Ad (U x μ) (imag X ν (step (2 * n) x μ)) - imag X ν x) -
      (Ad (U x ν) (imag X μ (step (2 * n) x ν)) - imag X μ x) := rfl

theorem curl_field_norm (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (μ ν : Fin 4) :
    ‖curl (covShift U) (Xh n X) μ ν‖ ^ 2 = ∑ x, ‖covCurl n U X μ ν x‖ ^ 2 := norm_sq_field _

/-- The frame-transported sum differs from the covariant curl by the defect. -/
theorem Z_sub_curl (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖(plaqOf n U X x μ ν).Y₁ + (plaqOf n U X x μ ν).Y₂ + (plaqOf n U X x μ ν).Y₃ +
        (plaqOf n U X x μ ν).Y₄ - covCurl n U X μ ν x‖ ≤
      2 * defect U μ ν x * linkSum n X x μ ν := by
  rw [covCurl_eq]
  set a := U x μ
  set b := U (step (2 * n) x μ) ν
  set c := U (step (2 * n) x ν) μ
  set e := U x ν
  set P := a * b * c⁻¹ * e⁻¹ with hP
  set A := imag X μ x
  set B := imag X ν (step (2 * n) x μ)
  set C := imag X μ (step (2 * n) x ν)
  set E := imag X ν x
  have y1 : (plaqOf n U X x μ ν).Y₁ = A := rfl
  have y2 : (plaqOf n U X x μ ν).Y₂ = Ad a B := rfl
  have y3 : (plaqOf n U X x μ ν).Y₃ = -Ad (a * b * c⁻¹) C := rfl
  have y4 : (plaqOf n U X x μ ν).Y₄ = -Ad P E := rfl
  have hPe : a * b * c⁻¹ = P * e := by
    rw [hP]
    group
  rw [y1, y2, y3, y4, hPe, Ad_mul]
  have hD : d P (ω ^ twistExp μ ν x) = defect U μ ν x := rfl
  have h1 := Ad_close P (twistExp μ ν x) (Ad e C)
  have h2 := Ad_close P (twistExp μ ν x) E
  rw [norm_Ad, hD] at h1
  rw [hD] at h2
  have split : A + Ad a B + -Ad P (Ad e C) + -Ad P E - (Ad a B - E - (Ad e C - A)) =
      -(Ad P (Ad e C) - Ad e C) - (Ad P E - E) := by
    abel
  rw [split]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]
  have hd0 : 0 ≤ defect U μ ν x := defect_nonneg _ _ _ _
  have nA := norm_nonneg A
  have nB := norm_nonneg B
  unfold linkSum
  have m1 := mul_nonneg hd0 nA
  have m2 := mul_nonneg hd0 nB
  nlinarith only [h1, h2, m1, m2]

theorem plaqC_defect (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V')
    (μ ν : Fin 4) : ‖plaqC n U X x μ ν - 1‖ = defect U μ ν x := by
  have hd : d (plaqOf n U X x μ ν).P (ω ^ twistExp μ ν x) = defect U μ ν x := rfl
  unfold plaqC
  rw [← hd]
  rcases twistExp_cases n μ ν x with hc | hc
  · rw [hc, pow_zero]
    simp only [zero_ne_one, if_false, one_smul]
    rfl
  · rw [hc, pow_one]
    simp only [if_true, neg_smul, one_smul]
    have e : -(((plaqOf n U X x μ ν).P : Q) : ℍ[ℝ]) - 1 =
        -(((plaqOf n U X x μ ν).P : ℍ[ℝ]) - (-1 : ℍ[ℝ])) := by noncomm_ring
    rw [e, norm_neg]
    rfl

/-- One plaquette's second derivative against the covariant curl. -/
theorem plaq_cov_bound (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (x : V') (μ ν : Fin 4) (hd : defect U μ ν x ≤ δ) :
    ‖covCurl n U X μ ν x‖ ^ 2 - (32 * δ ^ 2 + 8 * δ) * linkSq n X x μ ν ≤
      -(2 * (secondCoeff (plaqOf n U X x μ ν).Y₁ (plaqOf n U X x μ ν).Y₂ (plaqOf n U X x μ ν).Y₃
        (plaqOf n U X x μ ν).Y₄ * plaqC n U X x μ ν).re) := by
  obtain ⟨h1, h2, h3, h4⟩ := Y_re n U X x μ ν
  have hT0 : 0 ≤ linkSum n X x μ ν := by
    unfold linkSum
    positivity
  have hρ : ‖(plaqOf n U X x μ ν).Y₁ + (plaqOf n U X x μ ν).Y₂ + (plaqOf n U X x μ ν).Y₃ +
      (plaqOf n U X x μ ν).Y₄ - covCurl n U X μ ν x‖ ≤ 2 * δ * linkSum n X x μ ν :=
    (Z_sub_curl n U X x μ ν).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hd]) hT0)
  have hc : ‖plaqC n U X x μ ν - 1‖ ≤ δ := (plaqC_defect n U X x μ ν).trans_le hd
  have key := second_lower _ _ _ _ (plaqC n U X x μ ν) (covCurl n U X μ ν x) h1 h2 h3 h4 δ
    (2 * δ * linkSum n X x μ ν) (by positivity) hc hρ
  rw [plaq_norms] at key
  have hS := linkSum_sq n X x μ ν
  have hcoef : 0 ≤ 8 * δ ^ 2 + 2 * δ := by positivity
  have hm := mul_le_mul_of_nonneg_left hS hcoef
  refine le_trans ?_ key
  nlinarith only [hm]

/-- **The Hessian in terms of the covariant curl.** Only the supremum of the plaquette defects enters. -/
theorem hessian_cov_lower (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) :
    β * (curlEnergy (covShift U) (Xh n X) - (192 * δ ^ 2 + 48 * δ) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 := by
  rw [second_derivative_field]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have hsum := Finset.sum_le_sum fun (p : PlaquetteIndex (2 * n)) (_ : p ∈ Finset.univ) =>
    plaq_cov_bound n U X δ hδ0 p.1 p.2.1.1 p.2.1.2 (hδ p.1 p.2.1.1 p.2.1.2 p.2.2)
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hl : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  have hc : ∑ p : PlaquetteIndex (2 * n), ‖covCurl n U X p.2.1.1 p.2.1.2 p.1‖ ^ 2 =
      curlEnergy (covShift U) (Xh n X) := by
    unfold curlEnergy
    simp only [curl_field_norm]
    rw [← plane_sum (fun μ ν => ∑ x, ‖covCurl n U X μ ν x‖ ^ 2), Fintype.sum_prod_type,
      Finset.sum_comm]
  rw [hl, hc]
  ring

/-- **Covariant block coercivity.** The fluctuation form at `U`: the second derivative of the action,
plus the covariant divergence, plus a penalty on covariant running averages over `L` sites. -/
theorem cov_block_lower (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ δ) (L : ℕ) (hL : 1 ≤ L) :
    β * ((1 / (8 * (L : ℝ) ^ 2) - 56 * δ - 192 * δ ^ 2) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 +
        β * (‖div (covShift U) (Xh n X)‖ ^ 2 +
          1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (Xh n X μ)‖ ^ 2) := by
  have h1 := hessian_cov_lower n β hβ U X δ hδ0 hδ
  have h2 := block_coercive (covShift U) L hL (2 * δ) (by positivity)
    (fun μ ν φ => cov_comm U δ hδ0 hδ μ ν φ) (Xh n X)
  rw [Xh_norm] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  nlinarith only [h1, h3]

/-- **The block-scale bound, uniform in the lattice size.** Once all plaquette defects are at most
`1/(1000 L²)`, the fluctuation form is at least `β/(16 L²)` times the norm. -/
theorem cov_block_coercive (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (L : ℕ) (hL : 1 ≤ L)
    (hδ : ∀ x μ ν, μ < ν → defect U μ ν x ≤ 1 / (1000 * (L : ℝ) ^ 2)) :
    β * (1 / (16 * (L : ℝ) ^ 2) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 +
        β * (‖div (covShift U) (Xh n X)‖ ^ 2 +
          1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (Xh n X μ)‖ ^ 2) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set y : ℝ := 1 / (L : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hL1)
  have e1 : 1 / (1000 * (L : ℝ) ^ 2) = y / 1000 := by
    rw [hy]
    field_simp
  have e2 : 1 / (8 * (L : ℝ) ^ 2) = y / 8 := by
    rw [hy]
    field_simp
  have e3 : 1 / (16 * (L : ℝ) ^ 2) = y / 16 := by
    rw [hy]
    field_simp
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hβ)
    (cov_block_lower n β hβ U X (y / 1000) (by positivity) (by simpa only [e1] using hδ) L hL)
  have hW : 0 ≤ ∑ a : Fin 3, ∑ μ : Fin 4, ‖X a μ‖ ^ 2 := by positivity
  rw [e2, e3]
  refine mul_le_mul_of_nonneg_right ?_ hW
  nlinarith only [hy0, hy1, mul_nonneg hy0.le (sub_nonneg.2 hy1)]

/-- All plaquette defects of a configuration are below `δ`. -/
def SmallDefects (δ : ℝ) (U : Configuration V' Q) : Prop :=
  ∀ x μ ν, μ < ν → defect (linkValue (2 * n) Q U) μ ν x ≤ δ

theorem defect_sq_le (L : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    defect L μ ν x ^ 2 ≤ actionL L := by
  unfold actionL
  let p : PlaquetteIndex (2 * n) := (x, ⟨(μ, ν), h⟩)
  have hp := Finset.single_le_sum
    (f := fun p : PlaquetteIndex (2 * n) => defect L p.2.1.1 p.2.1.2 p.1 ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  exact hp

/-- The global action tail controls all defects, but only at `β` growing like the volume. A local tail
bound uniform in the volume is not proved here. -/
theorem measure_smallDefects (β δ : ℝ) (hβ : 1 / 32 ≤ β) (hδ0 : 0 ≤ δ) :
    TwistedLocalization.twistedLaw n β {U | ¬ SmallDefects n δ U} ≤
      ENNReal.ofReal (Real.exp (-β * δ ^ 2) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  have hsub : {U | ¬ SmallDefects n δ U} ⊆ {U | δ ^ 2 ≤ actionOne n U} := by
    intro U hU
    by_contra hlt
    have hlt' : actionOne n U < δ ^ 2 := not_le.1 hlt
    refine hU fun x μ ν h => ?_
    have hs := defect_sq_le n (linkValue (2 * n) Q U) x μ ν h
    rw [← TwistedNearFlat.actionOne_eq] at hs
    exact (abs_le_of_sq_le_sq' (hs.trans hlt'.le) hδ0).2
  exact (MeasureTheory.measure_mono hsub).trans (action_tail n β (δ ^ 2) hβ)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant
