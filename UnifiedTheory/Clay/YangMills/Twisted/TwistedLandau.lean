/- Landau gauge around the flat twisted field. On each gauge orbit a minimizer of the squared
distance to `flatLink` exists by compactness. Its stationarity is exactly the vanishing of the
colour-bundle divergence of the imaginary part of `U · F⁻¹`. This is classical. It assumes
nothing about the measure, and gives no competitor showing a given orbit comes close. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat TwistedStability TwistedLocalization
open CommutingShifts TwistedHessian
open WilsonSingleLinkStaples (Q)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The gauge action on link fields. -/
def act {N : ℕ} (h : Vertex N → Q) (U : Vertex N → Fin 4 → Q) : Vertex N → Fin 4 → Q :=
  fun x μ => h x * U x μ * (h (step N x μ))⁻¹

theorem act_act {N : ℕ} (g h : Vertex N → Q) (U : Vertex N → Fin 4 → Q) :
    act g (act h U) = act (fun x => g x * h x) U := by
  funext x μ
  simp only [act, mul_inv_rev]
  group

/-- Gauge transformations preserve the defect, since the twist is central. -/
theorem defect_act {N : ℕ} (h : Vertex N → Q) (U : Vertex N → Fin 4 → Q) (μ ν : Fin 4)
    (x : Vertex N) : defect (act h U) μ ν x = defect U μ ν x := by
  unfold defect
  set P := U x μ * U (step N x μ) ν * (U (step N x ν) μ)⁻¹ * (U x ν)⁻¹ with hP
  have hc : step N (step N x ν) μ = step N (step N x μ) ν := by
    simp only [step]
    abel
  have hprod : act h U x μ * act h U (step N x μ) ν * (act h U (step N x ν) μ)⁻¹ *
      (act h U x ν)⁻¹ = h x * P * (h x)⁻¹ := by
    simp only [act, hP, hc]
    group
  rw [hprod]
  have hw : h x * ω ^ twistExp μ ν x * (h x)⁻¹ = ω ^ twistExp μ ν x := by
    rw [← ((ω_commute _).pow_left _).eq]
    group
  calc d (h x * P * (h x)⁻¹) (ω ^ twistExp μ ν x)
      = d (h x * P * (h x)⁻¹) (h x * ω ^ twistExp μ ν x * (h x)⁻¹) := by rw [hw]
    _ = _ := by rw [d_mul_right, d_mul_left]

/-- Total squared defect: the action of a link field. -/
def actionL {N : ℕ} [NeZero N] (U : Vertex N → Fin 4 → Q) : ℝ :=
  ∑ p : PlaquetteIndex N, defect U p.2.1.1 p.2.1.2 p.1 ^ 2

theorem actionL_act {N : ℕ} [NeZero N] (h : Vertex N → Q) (U : Vertex N → Fin 4 → Q) :
    actionL (act h U) = actionL U := by
  unfold actionL
  simp only [defect_act]

/-! ### A rotation by `t` about a colour axis -/

/-- `cos t + sin t · e_a`. -/
def rot (a : Fin 3) (t : ℝ) : Q :=
  ⟨((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • basis a, by
    rw [Unitary.mem_iff]
    have hc := Real.sin_sq_add_cos_sq t
    fin_cases a <;> constructor <;> ext <;> simp [basis] <;> nlinarith only [hc]⟩

theorem rot_coe (a : Fin 3) (t : ℝ) :
    ((rot a t : Q) : ℍ[ℝ]) = ((Real.cos t : ℝ) : ℍ[ℝ]) + Real.sin t • basis a := rfl

theorem rot_inv_coe (a : Fin 3) (t : ℝ) :
    (((rot a t)⁻¹ : Q) : ℍ[ℝ]) = ((Real.cos t : ℝ) : ℍ[ℝ]) - Real.sin t • basis a := by
  change star ((rot a t : Q) : ℍ[ℝ]) = _
  rw [rot_coe]
  fin_cases a <;> ext <;> simp [basis]

theorem rot_zero (a : Fin 3) : rot a 0 = 1 := by
  apply Subtype.ext
  rw [rot_coe]
  simp

/-- Real part used for distances. -/
def rePart (q b : Q) : ℝ := ((q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ])).re

theorem d_sq_eq (q b : Q) : d q b ^ 2 = 2 - 2 * rePart q b := by
  have e := d_mul_right b⁻¹ q b
  rw [mul_inv_cancel] at e
  rw [← e]
  unfold d rePart
  change ‖(q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ]) - ((1 : Q) : ℍ[ℝ])‖ ^ 2 = _
  have hn := unit_normSq (q * b⁻¹)
  change ((q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ])).re ^ 2 + ((q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ])).imI ^ 2 +
    ((q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ])).imJ ^ 2 + ((q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ])).imK ^ 2 = 1 at hn
  generalize (q : ℍ[ℝ]) * ((b⁻¹ : Q) : ℍ[ℝ]) = v at *
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  change (v - 1).re ^ 2 + (v - 1).imI ^ 2 + (v - 1).imJ ^ 2 + (v - 1).imK ^ 2 = _
  simp only [Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub, Quaternion.imK_sub,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
  linear_combination hn

/-- Left rotation splits the real part. -/
theorem rePart_rot_left (a : Fin 3) (t : ℝ) (U F : Q) :
    rePart (rot a t * U) F = Real.cos t * rePart U F +
      Real.sin t * (basis a * ((U : ℍ[ℝ]) * ((F⁻¹ : Q) : ℍ[ℝ]))).re := by
  unfold rePart
  change (((rot a t : Q) : ℍ[ℝ]) * U * ((F⁻¹ : Q) : ℍ[ℝ])).re = _
  rw [rot_coe, mul_assoc, add_mul, smul_mul_assoc]
  simp

/-- Right rotation splits the real part. -/
theorem rePart_rot_right (a : Fin 3) (t : ℝ) (U F : Q) :
    rePart (U * (rot a t)⁻¹) F = Real.cos t * rePart U F -
      Real.sin t * ((U : ℍ[ℝ]) * basis a * ((F⁻¹ : Q) : ℍ[ℝ])).re := by
  unfold rePart
  change ((U : ℍ[ℝ]) * (((rot a t)⁻¹ : Q) : ℍ[ℝ]) * ((F⁻¹ : Q) : ℍ[ℝ])).re = _
  rw [rot_inv_coe, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  simp [Quaternion.re_sub]
  ring_nf

/-! ### Stationarity at a gauge-orbit minimizer -/

variable {n}

/-- Squared distance to the flat field. -/
abbrev D (U : V' → Fin 4 → Q) : ℝ := distSq n U

theorem step_ne (x : V') (μ : Fin 4) : step (2 * n) x μ ≠ x := by
  intro h
  have h1 := congrFun h μ
  simp only [step, Pi.add_apply, Pi.single_eq_same, add_eq_left] at h1
  have hn := NeZero.pos n
  have : Fact (1 < 2 * n) := ⟨by omega⟩
  exact one_ne_zero h1

/-- The gauge transformation rotating only at `y`. -/
def spike (a : Fin 3) (y : V') (t : ℝ) : V' → Q := Function.update 1 y (rot a t)

theorem act_spike_value (a : Fin 3) (y : V') (t : ℝ) (U : V' → Fin 4 → Q) (x : V') (μ : Fin 4) :
    rePart (act (spike a y t) U x μ) (flatLink x μ) = rePart (U x μ) (flatLink x μ) +
      (if x = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) +
        Real.sin t * (basis a * ((U x μ : ℍ[ℝ]) * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ]))).re else 0) +
      (if step (2 * n) x μ = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) -
        Real.sin t * ((U x μ : ℍ[ℝ]) * basis a * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ])).re else 0) := by
  unfold act spike
  by_cases h1 : x = y
  · subst h1
    have h2 : step (2 * n) x μ ≠ x := step_ne x μ
    simp only [Function.update_self, Function.update_of_ne h2, Pi.one_apply, inv_one, mul_one, if_true,
      if_neg h2, add_zero]
    rw [rePart_rot_left]
    ring
  · by_cases h2 : step (2 * n) x μ = y
    · subst h2
      simp only [Function.update_of_ne h1, Function.update_self, Pi.one_apply, one_mul, if_neg h1,
        if_true, add_zero]
      rw [rePart_rot_right]
      ring
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2, Pi.one_apply, one_mul, inv_one,
        mul_one, if_neg h1, if_neg h2, add_zero]

/-- The closed form of the squared distance along a spike. -/
theorem D_spike (a : Fin 3) (y : V') (t : ℝ) (U : V' → Fin 4 → Q) :
    D (act (spike a y t) U) = D U + 2 * (1 - Real.cos t) * ∑ μ, (rePart (U y μ) (flatLink y μ) +
        rePart (U (back y μ) μ) (flatLink (back y μ) μ)) -
      2 * Real.sin t * ∑ μ, ((basis a * ((U y μ : ℍ[ℝ]) * (((flatLink y μ)⁻¹ : Q) : ℍ[ℝ]))).re -
        ((U (back y μ) μ : ℍ[ℝ]) * basis a * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])).re) := by
  have hμ (μ : Fin 4) : ∑ x, d (act (spike a y t) U x μ) (flatLink x μ) ^ 2 =
      ∑ x, d (U x μ) (flatLink x μ) ^ 2 + 2 * (1 - Real.cos t) *
        (rePart (U y μ) (flatLink y μ) + rePart (U (back y μ) μ) (flatLink (back y μ) μ)) -
      2 * Real.sin t * ((basis a * ((U y μ : ℍ[ℝ]) * (((flatLink y μ)⁻¹ : Q) : ℍ[ℝ]))).re -
        ((U (back y μ) μ : ℍ[ℝ]) * basis a * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])).re) := by
    simp only [d_sq_eq, act_spike_value]
    have hb (g : V' → ℝ) : (∑ x, if step (2 * n) x μ = y then g x else 0) = g (back y μ) := by
      have hc (x : V') : (step (2 * n) x μ = y) ↔ x = back y μ := by
        constructor
        · rintro rfl
          exact (back_step x μ).symm
        · rintro rfl
          exact step_back y μ
      simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e (x : V') : 2 - 2 * (rePart (U x μ) (flatLink x μ) +
        (if x = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) +
          Real.sin t * (basis a * ((U x μ : ℍ[ℝ]) * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ]))).re else 0) +
        (if step (2 * n) x μ = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) -
          Real.sin t * ((U x μ : ℍ[ℝ]) * basis a * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ])).re else 0)) =
        (2 - 2 * rePart (U x μ) (flatLink x μ)) +
        (-2) * (if x = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) +
          Real.sin t * (basis a * ((U x μ : ℍ[ℝ]) * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ]))).re else 0) +
        (-2) * (if step (2 * n) x μ = y then (Real.cos t - 1) * rePart (U x μ) (flatLink x μ) -
          Real.sin t * ((U x μ : ℍ[ℝ]) * basis a * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ])).re else 0) := by
      ring
    simp only [e]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hb,
      Finset.sum_ite_eq' Finset.univ y]
    simp only [Finset.mem_univ, if_true]
    ring
  unfold D distSq
  simp only [hμ]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Stationarity of a gauge-orbit minimizer, in real-part form. -/
theorem stationary (U : V' → Fin 4 → Q) (hmin : ∀ h : V' → Q, D U ≤ D (act h U)) (a : Fin 3) (y : V') :
    ∑ μ, ((basis a * ((U y μ : ℍ[ℝ]) * (((flatLink y μ)⁻¹ : Q) : ℍ[ℝ]))).re -
        ((U (back y μ) μ : ℍ[ℝ]) * basis a * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])).re) = 0 := by
  set A := ∑ μ, (rePart (U y μ) (flatLink y μ) + rePart (U (back y μ) μ) (flatLink (back y μ) μ))
  set B := ∑ μ, ((basis a * ((U y μ : ℍ[ℝ]) * (((flatLink y μ)⁻¹ : Q) : ℍ[ℝ]))).re -
        ((U (back y μ) μ : ℍ[ℝ]) * basis a * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])).re)
  let φ : ℝ → ℝ := fun t => 2 * (1 - Real.cos t) * A - 2 * Real.sin t * B
  have hφ : ∀ t, φ 0 ≤ φ t := by
    intro t
    have h := hmin (spike a y t)
    rw [D_spike] at h
    simp only [φ, Real.cos_zero, Real.sin_zero]
    linarith only [h]
  have hder : HasDerivAt φ (2 * (0 - (-Real.sin 0)) * A - 2 * Real.cos 0 * B) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * (1 - Real.cos t)) (2 * (0 - (-Real.sin 0))) 0 :=
      ((hasDerivAt_const _ _).sub (Real.hasDerivAt_cos 0)).const_mul 2
    have h2 : HasDerivAt (fun t : ℝ => 2 * Real.sin t) (2 * Real.cos 0) 0 :=
      (Real.hasDerivAt_sin 0).const_mul 2
    exact (h1.mul_const A).sub (h2.mul_const B)
  have hmin0 : IsLocalMin φ 0 := Filter.Eventually.of_forall hφ
  have := hmin0.hasDerivAt_eq_zero hder
  simp only [Real.sin_zero, Real.cos_zero] at this
  linarith only [this]

/-- Colour coordinate of a quaternion. -/
def coord (a : Fin 3) (q : ℍ[ℝ]) : ℝ := ![q.imI, q.imJ, q.imK] a

theorem re_basis_mul (a : Fin 3) (q : ℍ[ℝ]) : (basis a * q).re = -coord a q := by
  fin_cases a <;> simp [basis, coord]

theorem re_mul_basis (a : Fin 3) (q : ℍ[ℝ]) : (q * basis a).re = -coord a q := by
  fin_cases a <;> simp [basis, coord]

/-- The colour components of the imaginary part of `U · F⁻¹`. -/
def imPart (U : V' → Fin 4 → Q) (a : Fin 3) (μ : Fin 4) : Section (2 * n) :=
  WithLp.toLp 2 fun x => coord a ((U x μ : ℍ[ℝ]) * (((flatLink x μ)⁻¹ : Q) : ℍ[ℝ]))

/-- **Landau gauge.** At a minimizer, the colour divergence of the imaginary part vanishes. -/
theorem div_imPart (U : V' → Fin 4 → Q) (hmin : ∀ h : V' → Q, D U ≤ D (act h U)) (a : Fin 3) :
    div (shifts a) (imPart U a) = 0 := by
  ext y
  have hs := stationary U hmin a y
  have hterm (μ : Fin 4) : ((U (back y μ) μ : ℍ[ℝ]) * basis a *
      (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])).re =
      -(eta (bundle a).1 (bundle a).2 (back y μ) μ *
        coord a ((U (back y μ) μ : ℍ[ℝ]) * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ]))) := by
    set x := back y μ
    set F := flatLink x μ
    have hUF : (U x μ : ℍ[ℝ]) = ((U x μ : ℍ[ℝ]) * ((F⁻¹ : Q) : ℍ[ℝ])) * (F : ℍ[ℝ]) := by
      rw [mul_assoc]
      have : ((F⁻¹ : Q) : ℍ[ℝ]) * (F : ℍ[ℝ]) = 1 := congrArg Subtype.val (inv_mul_cancel F)
      rw [this, mul_one]
    have had := ad_flatLink (N := 2 * n) a x μ
    calc ((U x μ : ℍ[ℝ]) * basis a * ((F⁻¹ : Q) : ℍ[ℝ])).re
        = (((U x μ : ℍ[ℝ]) * ((F⁻¹ : Q) : ℍ[ℝ])) * ((F : ℍ[ℝ]) * basis a * ((F⁻¹ : Q) : ℍ[ℝ]))).re := by
          conv_lhs => rw [hUF]
          simp only [mul_assoc]
      _ = _ := by
          rw [had, mul_smul_comm, Quaternion.re_smul, re_mul_basis]
          simp only [smul_eq_mul]
          ring
  simp only [hterm, re_basis_mul] at hs
  simp only [div, Shift.Dstar, PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.zero_apply]
  have hS (μ : Fin 4) : ((shifts (N := 2 * n) a μ).S (imPart U a μ)) y =
      eta (bundle a).1 (bundle a).2 (back y μ) μ *
        coord a ((U (back y μ) μ : ℍ[ℝ]) * (((flatLink (back y μ) μ)⁻¹ : Q) : ℍ[ℝ])) := rfl
  have hI (μ : Fin 4) : (imPart U a μ) y =
      coord a ((U y μ : ℍ[ℝ]) * (((flatLink y μ)⁻¹ : Q) : ℍ[ℝ])) := rfl
  simp only [hS, hI]
  rw [← hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring

/-! ### The logarithm near the identity -/

/-- The rotation angle of a quaternion. -/
def angle (q : ℍ[ℝ]) : ℝ := Real.arccos q.re

/-- The factor taking the imaginary part to the logarithm. -/
def logFactor (q : ℍ[ℝ]) : ℝ := if Real.sin (angle q) = 0 then 1 else angle q / Real.sin (angle q)

theorem im_normSq (q : Q) :
    (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 = Real.sin (angle q) ^ 2 := by
  have hn := unit_normSq q
  have hre := abs_le.mp (TwistedFlat.re_le_one q)
  have hc : Real.cos (angle q) = (q : ℍ[ℝ]).re := Real.cos_arccos hre.1 hre.2
  have hs := Real.sin_sq_add_cos_sq (angle q)
  rw [hc] at hs
  linarith only [hn, hs]

/-- The logarithm has coordinates `logFactor · coord`. -/
def logQ (q : ℍ[ℝ]) : ℍ[ℝ] := ⟨0, logFactor q * q.imI, logFactor q * q.imJ, logFactor q * q.imK⟩

theorem angle_nonneg (q : ℍ[ℝ]) : 0 ≤ angle q := Real.arccos_nonneg _

theorem sin_angle_nonneg (q : ℍ[ℝ]) : 0 ≤ Real.sin (angle q) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg q) (Real.arccos_le_pi _)

theorem angle_zero_of_sin (q : ℍ[ℝ]) (hq : 0 < q.re) (hs : Real.sin (angle q) = 0) :
    angle q = 0 := by
  have hlt : angle q < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hq
  by_contra hne
  have hpos : 0 < angle q := lt_of_le_of_ne (angle_nonneg q) (Ne.symm hne)
  have := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith only [hlt, Real.pi_pos])
  linarith only [this, hs]

theorem logQ_normSq (q : Q) (hq : 0 < (q : ℍ[ℝ]).re) : ‖logQ q‖ ^ 2 = angle q ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp only [logQ]
  have h := im_normSq q
  by_cases hs : Real.sin (angle q) = 0
  · have hz : (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 = 0 := by
      rw [h, hs]
      ring
    rw [angle_zero_of_sin _ hq hs]
    linear_combination (logFactor (q : ℍ[ℝ])) ^ 2 * hz
  · have hf : logFactor (q : ℍ[ℝ]) = angle q / Real.sin (angle q) := by
      unfold logFactor
      rw [if_neg hs]
    rw [hf]
    field_simp
    linear_combination (angle (q : ℍ[ℝ])) ^ 2 * h

theorem logQ_norm (q : Q) (hq : 0 < (q : ℍ[ℝ]).re) : ‖logQ q‖ = angle q := by
  have := logQ_normSq q hq
  exact (sq_eq_sq₀ (norm_nonneg _) (angle_nonneg _)).mp this

theorem exp_logQ (q : Q) (hq : 0 < (q : ℍ[ℝ]).re) : NormedSpace.exp (logQ q) = (q : ℍ[ℝ]) := by
  have hre := abs_le.mp (TwistedFlat.re_le_one q)
  have hc : Real.cos (angle q) = (q : ℍ[ℝ]).re := Real.cos_arccos hre.1 hre.2
  have him := im_normSq q
  by_cases hs : Real.sin (angle q) = 0
  · have hθ := angle_zero_of_sin _ hq hs
    have hz : (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 = 0 := by
      rw [him, hs]
      ring
    have sI := sq_nonneg (q : ℍ[ℝ]).imI
    have sJ := sq_nonneg (q : ℍ[ℝ]).imJ
    have sK := sq_nonneg (q : ℍ[ℝ]).imK
    have h1 : (q : ℍ[ℝ]).imI = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp (by linarith only [hz, sI, sJ, sK])
    have h2 : (q : ℍ[ℝ]).imJ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp (by linarith only [hz, sI, sJ, sK])
    have h3 : (q : ℍ[ℝ]).imK = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp (by linarith only [hz, sI, sJ, sK])
    have hr1 : (q : ℍ[ℝ]).re = 1 := by
      rw [← hc, hθ, Real.cos_zero]
    have hl : logQ (q : ℍ[ℝ]) = 0 := by
      ext <;> simp [logQ, h1, h2, h3]
    rw [hl, NormedSpace.exp_zero]
    ext <;> simp [h1, h2, h3, hr1]
  · have hf : logFactor (q : ℍ[ℝ]) = angle q / Real.sin (angle q) := by
      unfold logFactor
      rw [if_neg hs]
    have hθ : angle (q : ℍ[ℝ]) ≠ 0 := by
      intro h0
      apply hs
      rw [h0, Real.sin_zero]
    rw [TwistedSmallField.exp_imag _ (by simp [logQ]), logQ_norm q hq, hc]
    ext
    · simp [logQ]
    · simp [logQ, hf]
      field_simp
    · simp [logQ, hf]
      field_simp
    · simp [logQ, hf]
      field_simp

/-- Chord bounds on the angle, for positive real part. -/
theorem chord_sq (q : Q) : ‖(q : ℍ[ℝ]) - 1‖ ^ 2 = 2 - 2 * Real.cos (angle q) := by
  have hre := abs_le.mp (TwistedFlat.re_le_one q)
  have hc : Real.cos (angle q) = (q : ℍ[ℝ]).re := Real.cos_arccos hre.1 hre.2
  rw [hc]
  exact (SU2GaussianMass.chord_square q).trans (by ring)

theorem chord_le_angle (q : Q) : ‖(q : ℍ[ℝ]) - 1‖ ≤ angle q := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := angle q)
  exact abs_le_of_sq_le_sq' (by rw [chord_sq]; linarith only [hc]) (angle_nonneg _) |>.2

theorem angle_le_chord (q : Q) : angle q ≤ 8 / 5 * ‖(q : ℍ[ℝ]) - 1‖ := by
  set θ := angle (q : ℍ[ℝ]) with hθ
  have h0 : 0 ≤ θ := angle_nonneg _
  have hπ : θ ≤ Real.pi := Real.arccos_le_pi _
  have hs := Real.mul_le_sin (x := θ / 2) (by positivity) (by linarith only [hπ])
  have hd : ‖(q : ℍ[ℝ]) - 1‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [chord_sq]
    have e : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this
      rw [this, Real.cos_sq']
      ring
    rw [← hθ, e]
    ring
  have hnn : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    linarith only [hπ, h0, Real.pi_pos]
  have hch : ‖(q : ℍ[ℝ]) - 1‖ = 2 * Real.sin (θ / 2) :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hd
  rw [hch]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have e2 : 2 / Real.pi * (θ / 2) = θ / Real.pi := by
    have := Real.pi_pos.ne'
    field_simp
  rw [e2] at hs
  have h3 : θ ≤ Real.pi * Real.sin (θ / 2) := by
    rw [div_le_iff₀ Real.pi_pos] at hs
    linarith only [hs]
  nlinarith only [h3, hnn, hpi]

/-! ### Divergence of a general form -/

theorem div_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Fin 4 → Shift E)
    (ω₁ ω₂ : Fin 4 → E) : div A (ω₁ - ω₂) = div A ω₁ - div A ω₂ := by
  unfold div
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Shift.Dstar, Pi.sub_apply, map_sub]
  abel

theorem norm_Dstar_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Shift E)
    (x : E) : ‖A.Dstar x‖ ≤ 2 * ‖x‖ := by
  rw [A.norm_Dstar]
  unfold Shift.D
  have := norm_sub_le (A.T x) x
  rw [A.norm_T] at this
  linarith only [this]

theorem norm_div_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Fin 4 → Shift E) (ω : Fin 4 → E) : ‖div A ω‖ ^ 2 ≤ 16 * ∑ μ, ‖ω μ‖ ^ 2 := by
  have h1 : ‖div A ω‖ ≤ ∑ μ, 2 * ‖ω μ‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => norm_Dstar_le (A μ) (ω μ))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ?_
  simp only [Fin.sum_univ_four]
  nlinarith only [sq_nonneg (‖ω 0‖ - ‖ω 1‖), sq_nonneg (‖ω 0‖ - ‖ω 2‖), sq_nonneg (‖ω 0‖ - ‖ω 3‖),
    sq_nonneg (‖ω 1‖ - ‖ω 2‖), sq_nonneg (‖ω 1‖ - ‖ω 3‖), sq_nonneg (‖ω 2‖ - ‖ω 3‖)]

/-! ### The logarithmic coordinates of a field near the flat field -/

/-- The relative rotation `U · F⁻¹`. -/
def rel (U : V' → Fin 4 → Q) (x : V') (μ : Fin 4) : Q := U x μ * (flatLink x μ)⁻¹

theorem rel_coord (U : V' → Fin 4 → Q) (a : Fin 3) (μ : Fin 4) (x : V') :
    (imPart U a μ) x = coord a (rel U x μ : ℍ[ℝ]) := rfl

theorem d_eq_chord (U : V' → Fin 4 → Q) (x : V') (μ : Fin 4) :
    d (U x μ) (flatLink x μ) = ‖(rel U x μ : ℍ[ℝ]) - 1‖ := by
  rw [← d_mul_right (flatLink x μ)⁻¹, mul_inv_cancel]
  rfl

/-- Logarithmic coordinates of the field. -/
def logForm (U : V' → Fin 4 → Q) (a : Fin 3) (μ : Fin 4) : Section (2 * n) :=
  WithLp.toLp 2 fun x => logFactor (rel U x μ : ℍ[ℝ]) * coord a (rel U x μ : ℍ[ℝ])

theorem imag_logForm (U : V' → Fin 4 → Q) (μ : Fin 4) (x : V') :
    TwistedActionJet.imag (logForm U) μ x = logQ (rel U x μ : ℍ[ℝ]) := by
  unfold TwistedActionJet.imag logForm logQ
  ext <;> simp [Fin.sum_univ_three, basis, coord]

theorem d_single (U : V' → Fin 4 → Q) (x : V') (μ : Fin 4) :
    d (U x μ) (flatLink x μ) ^ 2 ≤ D U := by
  have h1 : d (U x μ) (flatLink x μ) ^ 2 ≤ ∑ y, d (U y μ) (flatLink y μ) ^ 2 :=
    Finset.single_le_sum (f := fun y => d (U y μ) (flatLink y μ) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ x)
  have h2 : ∑ y, d (U y μ) (flatLink y μ) ^ 2 ≤ D U :=
    Finset.single_le_sum (f := fun ν => ∑ y, d (U y ν) (flatLink y ν) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  exact h1.trans h2

theorem logForm_norm (U : V' → Fin 4 → Q)
    (hre : ∀ x μ, 0 < (rel U x μ : ℍ[ℝ]).re) :
    ∑ a, ∑ μ, ‖logForm U a μ‖ ^ 2 = ∑ μ, ∑ x, angle (rel U x μ : ℍ[ℝ]) ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hn (a : Fin 3) : ‖logForm U a μ‖ ^ 2 = ∑ x, (logForm U a μ x) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  simp only [hn]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← logQ_normSq _ (hre x μ), ← imag_logForm, TwistedSmallField.imag_normSq]

theorem pertLink_logForm (U : V' → Fin 4 → Q) (hre : ∀ x μ, 0 < (rel U x μ : ℍ[ℝ]).re) :
    TwistedActionJet.pertLink (logForm U) 1 = U := by
  funext x μ
  apply Subtype.ext
  unfold TwistedActionJet.pertLink TwistedActionJet.expQ
  change NormedSpace.exp ((1 : ℝ) • TwistedActionJet.imag (logForm U) μ x) *
    ((flatLink x μ : Q) : ℍ[ℝ]) = _
  rw [one_smul, imag_logForm, exp_logQ _ (hre x μ)]
  change ((U x μ * (flatLink x μ)⁻¹ * flatLink x μ : Q) : ℍ[ℝ]) = _
  rw [inv_mul_cancel_right]

theorem action_logForm (U : V' → Fin 4 → Q) (hre : ∀ x μ, 0 < (rel U x μ : ℍ[ℝ]).re) :
    TwistedReflection.action n Q (TwistedReflection.spatialTwist n)
      WilsonSingleLinkStaples.character 1 2 (TwistedActionJet.pertConfig n (logForm U) 1) =
      actionL U := by
  unfold TwistedReflection.action actionL
  rw [one_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ _
  rw [term_eq_defect_sq, TwistedActionJet.pertConfig_link, pertLink_logForm U hre]

/-- **Quadratic growth at a Landau minimizer.** -/
theorem landau_quadratic (U : V' → Fin 4 → Q) (hmin : ∀ h : V' → Q, D U ≤ D (act h U))
    (hsmall : D U ≤ (1 / (32 * ((2 * n : ℕ) : ℝ))) ^ 2) :
    D U ≤ ((2 * n : ℕ) : ℝ) ^ 2 * actionL U := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hN : (1 : ℝ) ≤ N := by
    rw [hNd]
    exact_mod_cast NeZero.pos (2 * n)
  have hNpos : 0 < N := by linarith only [hN]
  set ρ := 1 / (32 * N) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 / 32 := by
    rw [hρ]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith only [hN]
  have hchord (x : V') (μ : Fin 4) : ‖(rel U x μ : ℍ[ℝ]) - 1‖ ≤ ρ := by
    rw [← d_eq_chord]
    exact abs_le_of_sq_le_sq' ((d_single U x μ).trans hsmall) hρ0 |>.2
  have hre (x : V') (μ : Fin 4) : 0 < (rel U x μ : ℍ[ℝ]).re := by
    have h := SU2GaussianMass.chord_square (rel U x μ)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hchord x μ) 2
    have h3 : ρ ^ 2 ≤ (1 / 32) ^ 2 := pow_le_pow_left₀ hρ0 hρ1 2
    rw [h] at h2
    nlinarith only [h2, h3]
  set r := 1 / (20 * N) with hr
  have hθr (x : V') (μ : Fin 4) : angle (rel U x μ : ℍ[ℝ]) ≤ r := by
    have h1 := angle_le_chord (rel U x μ)
    have h2 := hchord x μ
    have e : 8 / 5 * ρ = r := by
      rw [hρ, hr]
      field_simp
      norm_num
    linarith only [h1, h2, e]
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    linarith only [hN]
  set Ω := logForm U with hΩ
  have hsup : ∀ μ x, ‖TwistedActionJet.imag Ω μ x‖ ≤ r := by
    intro μ x
    rw [imag_logForm, logQ_norm _ (hre x μ)]
    exact hθr x μ
  have hcoer := TwistedSmallField.action_coercive n Ω r hr1 hsup
  rw [hΩ, action_logForm U hre, ← hΩ] at hcoer
  set W := ∑ a, ∑ μ, ‖Ω a μ‖ ^ 2 with hW
  have hWeq : W = ∑ μ, ∑ x, angle (rel U x μ : ℍ[ℝ]) ^ 2 := logForm_norm U hre
  have hW0 : 0 ≤ W := by positivity
  -- the error between logarithmic and imaginary coordinates
  have herr (μ : Fin 4) (x : V') :
      ∑ a, ((logForm U a μ - imPart U a μ) x) ^ 2 ≤ r ^ 4 / 16 * angle (rel U x μ : ℍ[ℝ]) ^ 2 := by
    set q := rel U x μ with hq
    set θ := angle (q : ℍ[ℝ]) with hθ
    have hθ0 : 0 ≤ θ := angle_nonneg _
    have hθ1 : θ ≤ 1 := (hθr x μ).trans hr1
    have him := im_normSq q
    have hval (a : Fin 3) : ((logForm U a μ - imPart U a μ) x) =
        (logFactor (q : ℍ[ℝ]) - 1) * coord a (q : ℍ[ℝ]) := by
      change logFactor (q : ℍ[ℝ]) * coord a (q : ℍ[ℝ]) - coord a (q : ℍ[ℝ]) = _
      ring
    simp only [hval, mul_pow, ← Finset.mul_sum]
    have hsum : ∑ a, coord a (q : ℍ[ℝ]) ^ 2 = Real.sin θ ^ 2 := by
      rw [← him]
      simp [Fin.sum_univ_three, coord]
    rw [hsum]
    have hfact : (logFactor (q : ℍ[ℝ]) - 1) ^ 2 * Real.sin θ ^ 2 = (θ - Real.sin θ) ^ 2 := by
      by_cases hs : Real.sin θ = 0
      · have h0 : θ = 0 := angle_zero_of_sin _ (hre x μ) hs
        rw [hs, h0]
        simp
      · have hf : logFactor (q : ℍ[ℝ]) = θ / Real.sin θ := by
          unfold logFactor
          rw [if_neg hs]
        rw [hf]
        field_simp
    rw [hfact]
    have hdiff0 : 0 ≤ θ - Real.sin θ := by linarith only [Real.sin_le hθ0]
    have hdiff : θ - Real.sin θ ≤ θ ^ 3 / 4 := by
      rcases hθ0.eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      · have := Real.sin_gt_sub_cube hpos hθ1
        linarith only [this]
    have hsq := pow_le_pow_left₀ hdiff0 hdiff 2
    have hθr' : θ ≤ r := hθr x μ
    have hθ4 : θ ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hθ0 hθr' 4
    have e : (θ ^ 3 / 4) ^ 2 = θ ^ 4 / 16 * θ ^ 2 := by ring
    rw [e] at hsq
    have := mul_le_mul_of_nonneg_right hθ4 (sq_nonneg θ)
    nlinarith only [hsq, this]
  -- the divergence is controlled by that error
  have hdivΩ (a : Fin 3) : div (shifts a) (Ω a) = div (shifts a) (logForm U a - imPart U a) := by
    rw [div_sub, div_imPart U hmin a, sub_zero]
  have hdivsum : ∑ a, ‖div (shifts a) (Ω a)‖ ^ 2 ≤ r ^ 4 * W := by
    have h1 : ∑ a, ‖div (shifts a) (Ω a)‖ ^ 2 ≤
        ∑ a, 16 * ∑ μ, ‖(logForm U a - imPart U a) μ‖ ^ 2 :=
      Finset.sum_le_sum fun a _ => by
        rw [hdivΩ a]
        exact norm_div_sq_le _ _
    refine h1.trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hμ (μ : Fin 4) : ∑ a, ‖(logForm U a - imPart U a) μ‖ ^ 2 ≤
        r ^ 4 / 16 * ∑ x, angle (rel U x μ : ℍ[ℝ]) ^ 2 := by
      have hn (a : Fin 3) : ‖(logForm U a - imPart U a) μ‖ ^ 2 =
          ∑ x, ((logForm U a μ - imPart U a μ) x) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp
      simp only [hn]
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => herr μ x
    have h3 := Finset.sum_le_sum (s := Finset.univ) fun μ _ => hμ μ
    rw [← Finset.mul_sum, ← hWeq] at h3
    linarith only [h3]
  -- assemble
  have hl := TwistedSmallField.lam_lower (2 * n)
  rw [← hNd] at hl
  have hS : W / N ^ 2 ≤ actionL U := by
    refine le_trans ?_ hcoer
    have hr4 : r ^ 4 ≤ r ^ 2 := by
      have : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
      nlinarith only [this, sq_nonneg r]
    have hr2 : r ^ 2 = 1 / 400 / N ^ 2 := by
      rw [hr]
      field_simp
      norm_num
    have hdiv2 : (∑ a, ‖div (shifts a) (Ω a)‖ ^ 2) / 2 ≤ r ^ 2 / 2 * W := by
      have : r ^ 4 * W ≤ r ^ 2 * W := mul_le_mul_of_nonneg_right hr4 hW0
      linarith only [hdivsum, this]
    have hcoef : 1 / N ^ 2 ≤ TwistedHessian.lam (2 * n) / 2 - 384 * r ^ 2 - r ^ 2 / 2 := by
      rw [hr2]
      have e1 : 4 / N ^ 2 / 2 = 2 / N ^ 2 := by ring
      have e2 : 2 / N ^ 2 - 384 * (1 / 400 / N ^ 2) - 1 / 400 / N ^ 2 / 2 =
          (2 - 384 / 400 - 1 / 800) * (1 / N ^ 2) := by ring
      have hpos : 0 ≤ 1 / N ^ 2 := by positivity
      nlinarith only [hl, e1, e2, hpos]
    have hm := mul_le_mul_of_nonneg_right hcoef hW0
    have e4 : W / N ^ 2 = 1 / N ^ 2 * W := by ring
    rw [e4]
    linarith only [hm, hdiv2]
  have hDW : D U ≤ W := by
    rw [hWeq]
    unfold D distSq
    refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun x _ => ?_
    rw [d_eq_chord]
    exact pow_le_pow_left₀ (norm_nonneg _) (chord_le_angle _) 2
  have hNsq : 0 < N ^ 2 := by positivity
  rw [div_le_iff₀ hNsq] at hS
  linarith only [hDW, hS, mul_comm (actionL U) (N ^ 2)]

/-- Continuity of the squared distance along the gauge orbit. -/
theorem continuous_D_act (L : V' → Fin 4 → Q) :
    Continuous fun g : V' → Q => D (act g L) := by
  unfold D distSq act d
  fun_prop

/-- The configuration with prescribed link values. -/
def ofLink (L : V' → Fin 4 → Q) : RegulatedGauge.Configuration V' Q :=
  fun e => L (PeriodicTimeReflection.edgeCoordinates (2 * n) e).1
    (PeriodicTimeReflection.edgeCoordinates (2 * n) e).2

/-- The action of a link field is at most `24` times its squared distance to the flat field. -/
theorem actionL_le (L : V' → Fin 4 → Q) : actionL L ≤ 24 * D L := by
  have h := actionOne_le n (ofLink L)
  have hL : PeriodicTimeReflection.linkValue (2 * n) Q (ofLink L) = L := rfl
  rw [hL] at h
  have he : actionOne n (ofLink L) = actionL L := by
    unfold actionOne TwistedReflection.action actionL
    rw [one_mul]
    refine Finset.sum_congr rfl ?_
    rintro ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ _
    rw [term_eq_defect_sq, hL]
  rwa [he] at h

/-- **Two-sided local quadratic bound on a gauge orbit.** If the orbit of `L` comes within
`1/(32 N)` of the flat field, its closest representative has
`dist² / N² ≤ S(L) ≤ 24 dist²`. -/
theorem orbit_quadratic (L : V' → Fin 4 → Q) (g : V' → Q)
    (hg : D (act g L) ≤ (1 / (32 * ((2 * n : ℕ) : ℝ))) ^ 2) :
    ∃ g' : V' → Q, D (act g' L) ≤ ((2 * n : ℕ) : ℝ) ^ 2 * actionL L ∧
      actionL L ≤ 24 * D (act g' L) ∧ D (act g' L) ≤ D (act g L) := by
  obtain ⟨g', -, hg'⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (continuous_D_act (n := n) L).continuousOn
  have hle : ∀ h : V' → Q, D (act g' L) ≤ D (act h L) := fun h => hg' (Set.mem_univ h)
  refine ⟨g', ?_, ?_, hle g⟩
  · have hq := landau_quadratic (act g' L) (fun h => by
      rw [act_act]
      exact hle _) ((hle g).trans hg)
    rwa [actionL_act] at hq
  · have := actionL_le (act g' L)
    rwa [actionL_act] at this

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau
