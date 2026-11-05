/- A spectral statement about the actual twisted transfer operator. The trial vector `holo · Ω` is
odd under a center flip and orthogonal to the vacuum, and the ground-state identity bounds its
Rayleigh quotient. For large coupling the flux-odd sector is nearly degenerate with the vacuum, so a
uniform gap can only hold in the neutral sector. This bounds a gap from above. It gives no lower
bound on any gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCollatz
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedVacuum TwistedSliceLift
open TwistedNormLower TwistedRectangle PeriodicLattice4 TwistedFlat TwistedStability
open WilsonPositiveGroundState (complexify realSmoothing realSmoothing_integral)
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "T" => TwistedTransfer.transfer n β

/-- The spatial weight of the twisted kernel. -/
def wt (u : Slice n) : ℝ := Real.exp (-(β / 2) * twistedPotential n u)

/-- The temporal average. -/
def avg (u v : Slice n) : ℝ :=
  ∫ h, Real.exp (-β * temporalAction character 2 u v h) ∂(temporalHaar (n := n) (G := Q))

theorem kernel_factor (u v : Slice n) : twistedKernel n β (u, v) = wt n β u * avg n β u v * wt n β v :=
  twistedKernel_eq n β u v

theorem temporal_nonneg (u v : Slice n) (h : SliceGauge n Q) :
    0 ≤ temporalAction character 2 u v h := by
  rw [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
  unfold kineticAction
  refine Finset.sum_nonneg fun e _ => ?_
  rw [kinetic_term]
  exact sq_nonneg _

theorem wt_pos (u : Slice n) : 0 < wt n β u := Real.exp_pos _

variable (hβ : 0 ≤ β)

include hβ

theorem wt_le_one (u : Slice n) : wt n β u ≤ 1 := by
  unfold wt
  apply Real.exp_le_one_iff.mpr
  have := potential_nonneg n u
  nlinarith only [this, hβ]

theorem exp_temporal_le (u v : Slice n) (h : SliceGauge n Q) :
    Real.exp (-β * temporalAction character 2 u v h) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have := temporal_nonneg n u v h
  nlinarith only [this, hβ]

theorem avg_nonneg (u v : Slice n) : 0 ≤ avg n β u v :=
  integral_nonneg fun _ => (Real.exp_pos _).le

theorem avg_integrable (u v : Slice n) : Integrable
    (fun h : SliceGauge n Q => Real.exp (-β * temporalAction character 2 u v h))
    (temporalHaar (n := n) (G := Q)) :=
  (Real.continuous_exp.comp (continuous_const.mul
    (temporal_continuous n u v))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem avg_le_one (u v : Slice n) : avg n β u v ≤ 1 := by
  have h := integral_mono (avg_integrable n β hβ u v) (integrable_const (1 : ℝ))
    (fun k => exp_temporal_le n β hβ u v k)
  simpa [avg] using h

omit hβ in
/-- The holonomy observable as a continuous function. -/
theorem run_lift_continuous (x : Vertex n) (m : ℕ) :
    Continuous fun u : Slice n => run (lift n u) 3 x m := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [run]
    refine ih.mul ?_
    exact continuous_apply ((sp n (walk 3 x m), (2 : Fin 3)))

omit hβ in
theorem holo_continuous : Continuous (holo n) := by
  unfold holo wind3
  exact Quaternion.continuous_re.comp (continuous_subtype_val.comp (run_lift_continuous n _ _))

/-- The odd trial observable. -/
def obs : C(Slice n, ℝ) := ⟨holo n, holo_continuous n⟩

/-- The main pointwise estimate: small kinetic cost means small change of the observable. -/
theorem kernel_diff (t : ℝ) (ht : 0 ≤ t) (u v : Slice n) :
    twistedKernel n β (u, v) * (holo n u - holo n v) ^ 2 ≤
      n * t * twistedKernel n β (u, v) + 4 * Real.exp (-β * t) * (wt n β u * wt n β v) := by
  set Δ := (holo n u - holo n v) ^ 2 with hΔ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΔ4 : Δ ≤ 4 := by
    have h1 := abs_le.mp (holo_abs_le n u)
    have h2 := abs_le.mp (holo_abs_le n v)
    rw [hΔ]
    nlinarith only [h1.1, h1.2, h2.1, h2.2]
  have hpt (h : SliceGauge n Q) :
      Real.exp (-β * temporalAction character 2 u v h) * Δ ≤
        n * t * Real.exp (-β * temporalAction character 2 u v h) + 4 * Real.exp (-β * t) := by
    set J := temporalAction character 2 u v h with hJ
    have hexp := Real.exp_pos (-β * J)
    have hexp2 := Real.exp_pos (-β * t)
    by_cases hc : J ≤ t
    · have hL : Δ ≤ n * J := by
        have h1 := holo_lipschitz n u (gaugeSlice h v)
        rw [holo_gauge] at h1
        rw [hJ, temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
        exact h1
      have : Δ ≤ n * t := hL.trans (mul_le_mul_of_nonneg_left hc hn0)
      nlinarith only [mul_le_mul_of_nonneg_left this hexp.le, hexp2]
    · push_neg at hc
      have hle : Real.exp (-β * J) ≤ Real.exp (-β * t) :=
        Real.exp_le_exp.mpr (by nlinarith only [hc, hβ])
      have h0 : 0 ≤ Δ := sq_nonneg _
      have h1 : Real.exp (-β * J) * Δ ≤ Real.exp (-β * t) * 4 :=
        mul_le_mul hle hΔ4 h0 hexp2.le
      have h2 : 0 ≤ n * t * Real.exp (-β * J) := by positivity
      linarith only [h1, h2]
  have hint := avg_integrable n β hβ u v
  have hB : Integrable (fun h : SliceGauge n Q => (n : ℝ) * t *
      Real.exp (-β * temporalAction character 2 u v h) + 4 * Real.exp (-β * t))
      (temporalHaar (n := n) (G := Q)) := (hint.const_mul _).add (integrable_const _)
  have hmono := integral_mono (hint.mul_const Δ) hB hpt
  have hR : ∫ h : SliceGauge n Q, ((n : ℝ) * t * Real.exp (-β * temporalAction character 2 u v h) +
      4 * Real.exp (-β * t)) ∂(temporalHaar (n := n) (G := Q)) =
      n * t * avg n β u v + 4 * Real.exp (-β * t) := by
    rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp [avg]
  rw [hR, integral_mul_const] at hmono
  change avg n β u v * Δ ≤ n * t * avg n β u v + 4 * Real.exp (-β * t) at hmono
  rw [kernel_factor]
  have hw := mul_pos (wt_pos n β u) (wt_pos n β v)
  have := mul_le_mul_of_nonneg_left hmono hw.le
  nlinarith only [this]

/-! ### The ground state -/

omit hβ in
/-- A positive top eigenfunction is invariant under every flip. -/
theorem top_flip (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (hlam : 0 < ‖T‖)
    (i : Fin 3) (c : ZMod n) (u : Slice n) : η (TwistedTransfer.flip n i c u) = η u := by
  obtain ⟨m, M, hm, hM, hb⟩ := kernel_bounds n β
  have hmp : MeasurePreserving (flipEquiv n i c) (μ') (μ') := flip_measurePreserving n i c
  let f : C(Slice n, ℂ) := ⟨fun w => (η (TwistedTransfer.flip n i c w) : ℂ),
    Complex.continuous_ofReal.comp (η.continuous.comp (flip_continuous n i c))⟩
  have hf (w : Slice n) : (∫ v, (twistedKernel n β (w, v) : ℂ) * f v ∂μ') = (‖T‖ : ℂ) * f w := by
    have h1 := heig (TwistedTransfer.flip n i c w)
    have h2 := hmp.integral_comp' (fun v => twistedKernel n β (TwistedTransfer.flip n i c w, v) * η v)
    have h3 : (∫ v, twistedKernel n β (w, v) * η (TwistedTransfer.flip n i c v) ∂μ') =
        ‖T‖ * η (TwistedTransfer.flip n i c w) := by
      rw [← h1, ← h2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      change _ = twistedKernel n β (TwistedTransfer.flip n i c w, TwistedTransfer.flip n i c v) *
        η (TwistedTransfer.flip n i c v)
      rw [twistedKernel_flip]
    change (∫ v, (twistedKernel n β (w, v) : ℂ) * (η (TwistedTransfer.flip n i c v) : ℂ) ∂μ') = _
    simp only [← Complex.ofReal_mul, integral_complex_ofReal, h3]
    simp [f]
  obtain ⟨z, hz⟩ := PositiveKernelRatio.complex_top_proportional (μ') (twistedKernel n β) η hη ‖T‖ m M
    hlam hm hM (fun a b => (hb a b).1) (fun a b => (hb a b).2) heig f hf
  have hval (w : Slice n) : (η (TwistedTransfer.flip n i c w) : ℂ) = z * (η w : ℂ) := hz w
  set r : ℝ := η (TwistedTransfer.flip n i c u) / η u with hr
  have hzr : z = (r : ℂ) := by
    have h0 := hval u
    have hne : (η u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hη u).ne'
    rw [hr]
    push_cast
    rw [h0]
    field_simp
  have hrpos : 0 < r := div_pos (hη _) (hη _)
  have hreal (w : Slice n) : η (TwistedTransfer.flip n i c w) = r * η w := by
    have := hval w
    rw [hzr] at this
    exact_mod_cast this
  have h1 := hreal u
  have h2 := hreal (TwistedTransfer.flip n i c u)
  rw [flip_flip, h1] at h2
  have hne := (hη u).ne'
  have hrr : r * r = 1 := by
    have : η u * (r * r - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith only [h]
  have hr1 : r = 1 := by nlinarith only [hrr, hrpos]
  rw [h1, hr1, one_mul]

omit hβ in
/-- Integrable because continuous on a compact space. -/
theorem ci {f : Slice n → ℝ} (hf : Continuous f) : Integrable f μ' :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit hβ in
theorem integral_three (a b c : Slice n → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (x y : ℝ) :
    ∫ v, (x * a v - y * b v + c v) ∂μ' = x * ∫ v, a v ∂μ' - y * ∫ v, b v ∂μ' + ∫ v, c v ∂μ' := by
  have h1 : Integrable (fun v => x * a v) μ' := ci n (continuous_const.mul ha)
  have h2 : Integrable (fun v => y * b v) μ' := ci n (continuous_const.mul hb)
  have h3 : Integrable (fun v => x * a v - y * b v) μ' := h1.sub h2
  rw [integral_add h3 (ci n hc), integral_sub h1 h2, integral_const_mul, integral_const_mul]

omit hβ in
theorem eta_mean_le (η : C(Slice n, ℝ)) (hnorm : ∫ u, η u ^ 2 ∂μ' = 1) : ∫ v, η v ∂μ' ≤ 1 := by
  have h : 0 ≤ ∫ v, (η v - 1) ^ 2 ∂μ' := integral_nonneg fun v => sq_nonneg _
  have e : ∀ v, (η v - 1) ^ 2 = 1 * η v ^ 2 - 2 * η v + 1 := fun v => by ring
  simp only [e] at h
  rw [integral_three n (fun v => η v ^ 2) (fun v => η v) (fun _ => 1) (η.continuous.pow 2) η.continuous
    continuous_const, hnorm] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith only [h]

omit hβ in
theorem wt_continuous : Continuous (wt n β) := by
  have hcd := defect_continuous n
  have hcp : Continuous (potential character 2 : Slice n → ℝ) := by
    have hc := WilsonSingleLinkStaples.character_continuous
    unfold potential spatialHolonomy
    fun_prop
  have hP : twistedPotential n = fun u => potential character 2 u + defect n u :=
    funext (twistedPotential_eq n)
  have hcP : Continuous (twistedPotential n) := by
    rw [hP]
    exact hcp.add hcd
  exact Real.continuous_exp.comp (continuous_const.mul hcP)

/-- The pointwise bound of the ground state by the spatial weight. -/
theorem eta_le (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u) (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (hlam : 0 < ‖T‖)
    (u : Slice n) : η u ≤ wt n β u / ‖T‖ := by
  have hηint : Integrable (fun v => η v) μ' := ci n η.continuous
  have hη1 := eta_mean_le n η hnorm
  have hker : Integrable (fun v => twistedKernel n β (u, v) * η v) μ' :=
    (((twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)).mul
      η.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : ∫ v, twistedKernel n β (u, v) * η v ∂μ' ≤ ∫ v, wt n β u * η v ∂μ' := by
    refine integral_mono hker (hηint.const_mul _) fun v => ?_
    dsimp only
    refine mul_le_mul_of_nonneg_right ?_ (hη v).le
    rw [kernel_factor]
    have h1 := avg_le_one n β hβ u v
    have h2 := avg_nonneg n β hβ u v
    have h3 := wt_le_one n β hβ v
    have h4 := (wt_pos n β v).le
    have h5 := (wt_pos n β u).le
    calc wt n β u * avg n β u v * wt n β v ≤ wt n β u * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 h5) h3 h4 (by positivity)
      _ = _ := by ring
  rw [heig, integral_const_mul] at hle
  have h6 : ‖T‖ * η u ≤ wt n β u := by
    refine hle.trans ?_
    have h7 := (wt_pos n β u).le
    nlinarith only [mul_le_mul_of_nonneg_left hη1 h7]
  rw [le_div_iff₀ hlam]
  linarith only [h6]

/-- Lower bound on the norm of the trial vector. -/
theorem norm_trial (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u) (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (hlam : 0 < ‖T‖) :
    1 / 2 - Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 / 2 ≤
      ∫ u, holo n u ^ 2 * η u ^ 2 ∂μ' := by
  set σ := 1 / (16 * (n : ℝ) ^ 4) with hσ
  have hpt (u : Slice n) : η u ^ 2 / 2 - Real.exp (-β * σ) / ‖T‖ ^ 2 / 2 ≤ holo n u ^ 2 * η u ^ 2 := by
    by_cases hc : twistedPotential n u < σ
    · have hh := holo_sq_of_small n u hc
      have hq := sq_nonneg (η u)
      have hp : 0 ≤ Real.exp (-β * σ) / ‖T‖ ^ 2 / 2 := by positivity
      nlinarith only [mul_le_mul_of_nonneg_right hh hq, hp]
    · push_neg at hc
      have h1 := eta_le n β hβ η hη hnorm heig hlam u
      have h2 : η u ^ 2 ≤ (wt n β u / ‖T‖) ^ 2 := pow_le_pow_left₀ (hη u).le h1 2
      have h3 : (wt n β u / ‖T‖) ^ 2 ≤ Real.exp (-β * σ) / ‖T‖ ^ 2 := by
        rw [div_pow]
        apply div_le_div_of_nonneg_right _ (by positivity)
        unfold wt
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hc hβ]
      have h4 : 0 ≤ holo n u ^ 2 * η u ^ 2 := by positivity
      linarith only [h2, h3, h4]
  have hc1 : Integrable (fun u => η u ^ 2 / 2 - Real.exp (-β * σ) / ‖T‖ ^ 2 / 2) μ' :=
    (((η.continuous.pow 2).div_const 2).sub continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc2 : Integrable (fun u => holo n u ^ 2 * η u ^ 2) μ' :=
    (((holo_continuous n).pow 2).mul (η.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm := integral_mono hc1 hc2 hpt
  have hsq : Integrable (fun v => η v ^ 2) μ' :=
    (η.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (hsq.div_const 2) (integrable_const _), integral_div, hnorm, integral_const] at hm
  simp only [probReal_univ, smul_eq_mul, one_mul] at hm
  exact hm

/-! ### The Rayleigh quotient -/

/-- The smoothing of a continuous function by the twisted kernel. -/
abbrev sm (f : C(Slice n, ℝ)) : C(Slice n, ℝ) := realSmoothing (μ') (twistedKernel n β) f

omit hβ in
theorem sm_apply (f : C(Slice n, ℝ)) (u : Slice n) :
    sm n β f u = ∫ v, twistedKernel n β (u, v) * f v ∂μ' := realSmoothing_integral _ _ _ _

/-- The inner estimate of the ground-state identity. -/
theorem inner_bound (η s f₁ f₂ : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u) (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (hsv : ∀ u, s u = holo n u) (hf₁ : ∀ u, f₁ u = s u * η u) (hf₂ : ∀ u, f₂ u = s u * s u * η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (t : ℝ) (ht : 0 ≤ t)
    (u : Slice n) :
    s u ^ 2 * (‖T‖ * η u) - 2 * s u * sm n β f₁ u + sm n β f₂ u ≤
      n * t * (‖T‖ * η u) + 4 * Real.exp (-β * t) * wt n β u := by
  have hk := kernel_diff n β hβ t ht u
  have hK : Continuous fun v => twistedKernel n β (u, v) :=
    (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
  have hw := wt_continuous n β
  have hexpand : ∫ v, twistedKernel n β (u, v) * η v * (s u - s v) ^ 2 ∂μ' =
      s u ^ 2 * (‖T‖ * η u) - 2 * s u * sm n β f₁ u + sm n β f₂ u := by
    rw [sm_apply, sm_apply, ← heig u]
    have e : ∀ v, twistedKernel n β (u, v) * η v * (s u - s v) ^ 2 =
        s u ^ 2 * (twistedKernel n β (u, v) * η v) -
          2 * s u * (twistedKernel n β (u, v) * f₁ v) + twistedKernel n β (u, v) * f₂ v := by
      intro v
      rw [hf₁, hf₂]
      ring
    simp only [e]
    exact integral_three n _ _ _ (hK.mul η.continuous) (hK.mul f₁.continuous)
      (hK.mul f₂.continuous) _ _
  rw [← hexpand]
  have hmono : ∫ v, twistedKernel n β (u, v) * η v * (s u - s v) ^ 2 ∂μ' ≤
      ∫ v, (n * t * (twistedKernel n β (u, v) * η v) -
        0 * η v + 4 * Real.exp (-β * t) * wt n β u * (wt n β v * η v)) ∂μ' := by
    refine integral_mono (ci n ((hK.mul η.continuous).mul
      ((continuous_const.sub s.continuous).pow 2))) (ci n (((continuous_const.mul
      (hK.mul η.continuous)).sub (continuous_const.mul η.continuous)).add
      (continuous_const.mul (hw.mul η.continuous)))) fun v => ?_
    dsimp only
    have h1 := mul_le_mul_of_nonneg_right (hk v) (hη v).le
    rw [hsv u, hsv v]
    nlinarith only [h1]
  refine hmono.trans ?_
  have hthree := integral_three n (fun v => twistedKernel n β (u, v) * η v) (fun v => η v)
    (fun v => 4 * Real.exp (-β * t) * wt n β u * (wt n β v * η v)) (hK.mul η.continuous) η.continuous
    (continuous_const.mul (hw.mul η.continuous)) (n * t) 0
  rw [hthree, integral_const_mul, heig]
  have hwη : ∫ v, wt n β v * η v ∂μ' ≤ 1 := by
    refine le_trans (integral_mono (ci n (hw.mul η.continuous)) (ci n η.continuous) fun v => ?_)
      (eta_mean_le n η hnorm)
    exact mul_le_of_le_one_left (hη v).le (wt_le_one n β hβ v)
  have hc0 : 0 ≤ 4 * Real.exp (-β * t) * wt n β u := by
    have := wt_pos n β u
    positivity
  nlinarith only [mul_le_mul_of_nonneg_left hwη hc0]

/-- **The ground-state Rayleigh estimate.** For the odd observable, with any scale `t ≥ 0`. -/
theorem rayleigh (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u) (hnorm : ∫ u, η u ^ 2 ∂μ' = 1)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (t : ℝ) (ht : 0 ≤ t) :
    ‖T‖ * (∫ u, holo n u ^ 2 * η u ^ 2 ∂μ') - (n * t * ‖T‖ + 4 * Real.exp (-β * t)) / 2 ≤
      ∫ u, (holo n u * η u) * (∫ v, twistedKernel n β (u, v) * (holo n v * η v) ∂μ') ∂μ' := by
  set s := obs n with hs
  have hsv (u : Slice n) : s u = holo n u := rfl
  let f₁ : C(Slice n, ℝ) := s * η
  let f₂ : C(Slice n, ℝ) := s * s * η
  have hf₁ (u : Slice n) : f₁ u = s u * η u := rfl
  have hf₂ (u : Slice n) : f₂ u = s u * s u * η u := rfl
  have hinner := inner_bound n β hβ η s f₁ f₂ hη hnorm hsv hf₁ hf₂ heig t ht
  have hw := wt_continuous n β
  set lam := ‖T‖ with hlam
  set X := ∫ u, holo n u ^ 2 * η u ^ 2 ∂μ' with hX
  set Q := ∫ u, (holo n u * η u) * (∫ v, twistedKernel n β (u, v) * (holo n v * η v) ∂μ') ∂μ' with hQ
  have hmono := integral_mono (f := fun u => lam * (s u ^ 2 * η u ^ 2) - 2 * (f₁ u * sm n β f₁ u) +
      sm n β f₂ u * η u) (g := fun u => n * t * lam * η u ^ 2 - 0 * η u +
      4 * Real.exp (-β * t) * (wt n β u * η u)) (μ := μ')
    (ci n (((continuous_const.mul ((s.continuous.pow 2).mul (η.continuous.pow 2))).sub
      (continuous_const.mul (f₁.continuous.mul (sm n β f₁).continuous))).add
      ((sm n β f₂).continuous.mul η.continuous)))
    (ci n (((continuous_const.mul (η.continuous.pow 2)).sub (continuous_const.mul η.continuous)).add
      (continuous_const.mul (hw.mul η.continuous)))) fun u => by
      have h1 := mul_le_mul_of_nonneg_right (hinner u) (hη u).le
      dsimp only
      rw [hf₁]
      nlinarith only [h1]
  have hL : ∫ u, (lam * (s u ^ 2 * η u ^ 2) - 2 * (f₁ u * sm n β f₁ u) + sm n β f₂ u * η u) ∂μ' =
      lam * X - 2 * Q + lam * X := by
    have hthree := integral_three n (fun u => s u ^ 2 * η u ^ 2) (fun u => f₁ u * sm n β f₁ u)
      (fun u => sm n β f₂ u * η u) ((s.continuous.pow 2).mul (η.continuous.pow 2))
      (f₁.continuous.mul (sm n β f₁).continuous) ((sm n β f₂).continuous.mul η.continuous) lam 2
    rw [hthree]
    have h1 : ∫ u, s u ^ 2 * η u ^ 2 ∂μ' = X := rfl
    have h2 : ∫ u, f₁ u * sm n β f₁ u ∂μ' = Q := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [sm_apply]
      rfl
    have h3 : ∫ u, sm n β f₂ u * η u ∂μ' = lam * X := by
      have hp := TwistedCollatz.pairing_symm n β f₂ η
      simp only [heig, ← sm_apply] at hp
      rw [hp, hX, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [hf₂]
      change _ = lam * (s u ^ 2 * η u ^ 2)
      ring
    rw [h1, h2, h3]
  have hR : ∫ u, (n * t * lam * η u ^ 2 - 0 * η u + 4 * Real.exp (-β * t) * (wt n β u * η u)) ∂μ' ≤
      n * t * lam + 4 * Real.exp (-β * t) := by
    have hthree := integral_three n (fun u => η u ^ 2) (fun u => η u)
      (fun u => 4 * Real.exp (-β * t) * (wt n β u * η u)) (η.continuous.pow 2) η.continuous
      (continuous_const.mul (hw.mul η.continuous)) (n * t * lam) 0
    rw [hthree, hnorm, integral_const_mul]
    have hwη : ∫ v, wt n β v * η v ∂μ' ≤ 1 := by
      refine le_trans (integral_mono (ci n (hw.mul η.continuous)) (ci n η.continuous) fun v => ?_)
        (eta_mean_le n η hnorm)
      exact mul_le_of_le_one_left (hη v).le (wt_le_one n β hβ v)
    have hE := (Real.exp_pos (-β * t))
    nlinarith only [hwη, hE]
  rw [hL] at hmono
  linarith only [hmono, hR]

/-! ### The spectral statement -/

omit hβ in
theorem inner_embed (f g : C(Slice n, ℝ)) :
    inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify f)) (ContinuousMap.toLp 2 (μ') ℂ (complexify g)) =
      ((∫ u, f u * g u ∂μ' : ℝ) : ℂ) := by
  rw [MeasureTheory.ContinuousMap.inner_toLp, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [complexify, mul_comm]

omit hβ in
/-- The operator on an embedded continuous function. -/
theorem transfer_embed (f : C(Slice n, ℝ)) :
    T (ContinuousMap.toLp 2 (μ') ℂ (complexify f)) =
      ContinuousMap.toLp 2 (μ') ℂ (complexify (sm n β f)) := by
  change ContinuousMap.toLp 2 (μ') ℂ (CompactKernelOperator.smoothing (μ') (twistedKernel n β)
    (ContinuousMap.toLp 2 (μ') ℂ (complexify f))) = _
  rw [WilsonPositiveGroundState.complexify_realSmoothing]

/-- **The flux-odd sector is nearly degenerate with the vacuum.** With `λ = ‖T‖`, for every `t ≥ 0`,
as long as the trial norm bound `A` is positive, there is a nonzero vector odd under the center flip
and orthogonal to the unit vacuum whose image has norm at least
`(1 - (n t + 4 e^{-β t} / λ) / (2A)) λ` times its own. -/
theorem flux_near_degenerate (t : ℝ) (ht : 0 ≤ t)
    (hA : 0 < 1 / 2 - Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 / 2) :
    ∃ Ω F : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ F ≠ 0 ∧ flipOp n 2 0 F = -F ∧ inner ℂ Ω F = 0 ∧
      (1 - (n * t + 4 * Real.exp (-β * t) / ‖T‖) /
        (2 * (1 / 2 - Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 / 2))) * ‖T‖ * ‖F‖ ≤ ‖T F‖ := by
  obtain ⟨η, hη, hnormL, heig⟩ := exists_positive_top n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  have hnorm : ∫ u, η u ^ 2 ∂μ' = 1 := by
    rw [← WilsonPositiveGroundState.real_embedding_norm_sq, hnormL, one_pow]
  set A := 1 / 2 - Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 / 2 with hAd
  set lam := ‖T‖ with hlamd
  have hmp := flip_measurePreserving n 2 0
  have hmp' : MeasurePreserving (flipEquiv n 2 0) (μ') (μ') := hmp
  have hflipη := top_flip n β η hη heig hlam 2 0
  let f : C(Slice n, ℝ) := obs n * η
  have hfv (u : Slice n) : f u = holo n u * η u := rfl
  set Ω := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ
  set F := ContinuousMap.toLp 2 (μ') ℂ (complexify f) with hF
  have hX := norm_trial n β hβ η hη hnorm heig hlam
  set X := ∫ u, holo n u ^ 2 * η u ^ 2 ∂μ' with hXd
  have hXA : A ≤ X := hX
  have hXpos : 0 < X := lt_of_lt_of_le hA hXA
  have hFsq : ‖F‖ ^ 2 = X := by
    rw [hF, WilsonPositiveGroundState.real_embedding_norm_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hfv]
    ring
  have hFpos : 0 < ‖F‖ := by
    by_contra hneg
    have h0 : ‖F‖ = 0 := le_antisymm (not_lt.mp hneg) (norm_nonneg _)
    rw [h0] at hFsq
    norm_num at hFsq
    linarith only [hFsq, hXpos]
  refine ⟨Ω, F, hnormL, ?_, norm_pos_iff.mp hFpos, ?_, ?_, ?_⟩
  · rw [hΩ, transfer_embed]
    have hs : sm n β η = lam • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · apply Lp.ext
    have h1 : (flipOp n 2 0 F : Slice n → ℂ) =ᵐ[μ'] ((F : Hilbert n) ∘ TwistedTransfer.flip n 2 0) :=
      Lp.coeFn_compMeasurePreserving _ hmp
    have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') (complexify f)
    have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
    have h4 : ((-F : Hilbert n) : Slice n → ℂ) =ᵐ[μ'] -(F : Slice n → ℂ) := Lp.coeFn_neg F
    have h5 : -(F : Slice n → ℂ) =ᵐ[μ'] -(complexify f : Slice n → ℂ) := h2.neg
    have hodd : ((complexify f : Slice n → ℂ) ∘ TwistedTransfer.flip n 2 0) =ᵐ[μ']
        -(complexify f : Slice n → ℂ) := by
      refine Filter.Eventually.of_forall fun u => ?_
      change ((f (TwistedTransfer.flip n 2 0 u) : ℝ) : ℂ) = -((f u : ℝ) : ℂ)
      rw [hfv, hfv, holo_flip, hflipη]
      push_cast
      ring
    exact h1.trans (h3.trans (hodd.trans (h4.trans h5).symm))
  · rw [hΩ, hF, inner_embed]
    have hzero : ∫ u, η u * f u ∂μ' = 0 := by
      have hodd := hmp'.integral_comp' (fun u => η u * f u)
      have hneg : (fun u => η ((flipEquiv n 2 0) u) * f ((flipEquiv n 2 0) u)) =
          fun u => -(η u * f u) := by
        funext u
        change η (TwistedTransfer.flip n 2 0 u) * f (TwistedTransfer.flip n 2 0 u) = _
        rw [hfv, hfv, holo_flip, hflipη]
        ring
      rw [hneg, integral_neg] at hodd
      linarith only [hodd]
    rw [hzero]
    simp
  · -- the Rayleigh quotient
    have hR := rayleigh n β hβ η hη hnorm heig t ht
    set Q := ∫ u, (holo n u * η u) * (∫ v, twistedKernel n β (u, v) * (holo n v * η v) ∂μ') ∂μ' with hQ
    have hinner : inner ℂ F (T F) = (Q : ℂ) := by
      rw [hF, transfer_embed, inner_embed]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      rw [sm_apply]
      rfl
    have hbound : Q ≤ ‖F‖ * ‖T F‖ := by
      have h1 := norm_inner_le_norm (𝕜 := ℂ) F (T F)
      rw [hinner, Complex.norm_real, Real.norm_eq_abs] at h1
      exact (le_abs_self _).trans h1
    set δ := (n * t + 4 * Real.exp (-β * t) / lam) / (2 * A) with hδ
    have hAne : 2 * A ≠ 0 := by positivity
    have hkey : lam * (1 - δ) * X ≤ Q := by
      have e1 : lam * δ = (n * t * lam + 4 * Real.exp (-β * t)) / (2 * A) := by
        rw [hδ]
        field_simp
      have hnum : 0 ≤ n * t * lam + 4 * Real.exp (-β * t) := by positivity
      have h2 : (n * t * lam + 4 * Real.exp (-β * t)) / 2 ≤ lam * δ * X := by
        rw [e1]
        have e2 : (n * t * lam + 4 * Real.exp (-β * t)) / (2 * A) * X =
            (n * t * lam + 4 * Real.exp (-β * t)) / 2 * (X / A) := by
          field_simp
        rw [e2]
        have hq : 1 ≤ X / A := (one_le_div hA).mpr hXA
        have hn2 : 0 ≤ (n * t * lam + 4 * Real.exp (-β * t)) / 2 := by positivity
        nlinarith only [mul_le_mul_of_nonneg_left hq hn2]
      nlinarith only [hR, h2]
    have hfin : lam * (1 - δ) * ‖F‖ ^ 2 ≤ ‖F‖ * ‖T F‖ := by
      rw [hFsq]
      exact hkey.trans hbound
    have hfin2 : (1 - δ) * lam * ‖F‖ * ‖F‖ ≤ ‖T F‖ * ‖F‖ := by
      nlinarith only [hfin]
    exact le_of_mul_le_mul_right hfin2 hFpos

/-- **Explicit form.** With `P = mass(24β)^{7n³}`, if `e^{-β/(16n⁴)} ≤ P²/2` and `e^{-βt} ≤ P t`, then
the odd vector loses at most the factor `1 - 2(n+4)t`. No gap in this sector can exceed that. -/
theorem flux_near_degenerate_explicit (t : ℝ) (ht : 0 ≤ t)
    (hσ : Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) ≤
      (SU2GaussianMass.mass (24 * β) ^ (2 * links n + sites n)) ^ 2 / 2)
    (hτ : Real.exp (-β * t) ≤ SU2GaussianMass.mass (24 * β) ^ (2 * links n + sites n) * t) :
    ∃ Ω F : Hilbert n, ‖Ω‖ = 1 ∧ T Ω = ‖T‖ • Ω ∧ F ≠ 0 ∧ flipOp n 2 0 F = -F ∧ inner ℂ Ω F = 0 ∧
      (1 - 2 * (n + 4) * t) * ‖T‖ * ‖F‖ ≤ ‖T F‖ := by
  set P := SU2GaussianMass.mass (24 * β) ^ (2 * links n + sites n) with hP
  have hPpos : 0 < P := pow_pos (SU2GaussianMass.mass_pos _) _
  have hle : P ≤ ‖T‖ := norm_lower' n β hβ
  have hlam : 0 < ‖T‖ := lt_of_lt_of_le hPpos hle
  have hsq : P ^ 2 ≤ ‖T‖ ^ 2 := pow_le_pow_left₀ hPpos.le hle 2
  have hratio : Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hσ, hsq]
  set A := 1 / 2 - Real.exp (-β * (1 / (16 * (n : ℝ) ^ 4))) / ‖T‖ ^ 2 / 2 with hAd
  have hA4 : 1 / 4 ≤ A := by
    rw [hAd]
    linarith only [hratio]
  have hA : 0 < A := by linarith only [hA4]
  obtain ⟨Ω, F, h1, h2, h3, h4, h5, h6⟩ := flux_near_degenerate n β hβ t ht hA
  refine ⟨Ω, F, h1, h2, h3, h4, h5, le_trans ?_ h6⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : 4 * Real.exp (-β * t) / ‖T‖ ≤ 4 * t := by
    rw [div_le_iff₀ hlam]
    have h7 : Real.exp (-β * t) ≤ ‖T‖ * t :=
      hτ.trans (mul_le_mul_of_nonneg_right hle ht)
    linarith only [h7]
  have hδ : (n * t + 4 * Real.exp (-β * t) / ‖T‖) / (2 * A) ≤ 2 * (n + 4) * t := by
    rw [div_le_iff₀ (by positivity)]
    have hnum : n * t + 4 * Real.exp (-β * t) / ‖T‖ ≤ (n + 4) * t := by linarith only [hexp]
    have hnn : 0 ≤ (n + 4 : ℝ) * t := by positivity
    nlinarith only [hnum, hA4, hnn, mul_le_mul_of_nonneg_left hA4 hnn]
  have hF := norm_nonneg F
  have hc : 0 ≤ ‖T‖ * ‖F‖ := by positivity
  have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_left hδ 1) hc
  nlinarith only [hmul]

/-! ### Non-vacuity: the limit `β → ∞` at fixed lattice size -/

omit hβ in
/-- A polynomial times a decaying exponential is eventually small. -/
theorem poly_exp_small (D : ℝ) (m : ℕ) (c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ b : ℝ in Filter.atTop, D * (b ^ m * Real.exp (-c * b)) ≤ a := by
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m
  have h2 : Filter.Tendsto (fun b : ℝ => c * b) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hc
  have h3 := (h1.comp h2).const_mul (D / c ^ m)
  rw [mul_zero] at h3
  have hc' : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
  have hEq : (fun b : ℝ => D / c ^ m * ((fun x => x ^ m * Real.exp (-x)) ∘ fun b => c * b) b) =
      fun b => D * (b ^ m * Real.exp (-c * b)) := by
    funext b
    simp only [Function.comp, mul_pow, neg_mul]
    field_simp
  rw [hEq] at h3
  exact (h3.eventually (Iio_mem_nhds ha)).mono fun _ h => (le_of_lt h)

omit hβ in
/-- The Gaussian mass is at least an inverse polynomial. -/
theorem mass_lower_poly (b : ℝ) (hb : 1 / 24 ≤ b) :
    (SU2GaussianMass.cap 1 * (24 * b) ^ 2)⁻¹ ≤ SU2GaussianMass.mass (24 * b) := by
  set s := 24 * b with hs
  have hs1 : 1 ≤ s := by rw [hs]; linarith only [hb]
  have hcapv : SU2GaussianMass.cap s = SU2GaussianMass.cap 1 * (s * Real.sqrt s) := by
    unfold SU2GaussianMass.cap
    simp only [Real.sqrt_one, mul_one]
    ring
  have hmc := SU2GaussianMass.mass_cap_lower s (by linarith only [hs1])
  have hK : 0 ≤ SU2GaussianMass.cap 1 := SU2GaussianMass.cap_nonneg 1 (by norm_num)
  have hsq : Real.sqrt s ≤ s := by
    rw [Real.sqrt_le_left (by linarith only [hs1])]
    nlinarith only [hs1]
  have hle : SU2GaussianMass.cap s ≤ SU2GaussianMass.cap 1 * s ^ 2 := by
    rw [hcapv, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by linarith only [hs1])) hK
  have hm := SU2GaussianMass.mass_pos s
  have hprod : 1 ≤ SU2GaussianMass.mass s * (SU2GaussianMass.cap 1 * s ^ 2) :=
    hmc.trans (mul_le_mul_of_nonneg_left hle hm.le)
  have hQ : 0 < SU2GaussianMass.cap 1 * s ^ 2 := by
    by_contra hneg
    push_neg at hneg
    nlinarith only [hprod, hm, mul_nonneg hm.le (neg_nonneg.mpr hneg)]
  rw [inv_le_iff_one_le_mul₀ hQ]
  linarith only [hprod]

omit hβ in
/-- **The flux gap vanishes at fixed lattice size.** For every `ε > 0` and all sufficiently large `β`,
the flux-odd sector contains a nonzero vector orthogonal to the vacuum and contracted by at most
`1 - ε`. So no uniform gap can hold outside the neutral sector. -/
theorem flux_gap_vanishes (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ b : ℝ in Filter.atTop, ∃ Ω F : Hilbert n, ‖Ω‖ = 1 ∧
      TwistedTransfer.transfer n b Ω = ‖TwistedTransfer.transfer n b‖ • Ω ∧ F ≠ 0 ∧
      flipOp n 2 0 F = -F ∧ inner ℂ Ω F = 0 ∧
      (1 - ε) * ‖TwistedTransfer.transfer n b‖ * ‖F‖ ≤ ‖TwistedTransfer.transfer n b F‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  set M := 2 * links n + sites n with hM
  set t := ε / (2 * (n + 4)) with ht
  have htpos : 0 < t := by positivity
  set c₁ := 1 / (16 * (n : ℝ) ^ 4) with hc₁
  have hc₁pos : 0 < c₁ := by positivity
  set K := SU2GaussianMass.cap 1 * 576 with hK
  have hcap0 : 0 ≤ SU2GaussianMass.cap 1 := SU2GaussianMass.cap_nonneg 1 (by norm_num)
  have hK0 : 0 ≤ K := by positivity
  -- The two exponential requirements, for all large `b`.
  have ev₁ := poly_exp_small (2 * K ^ (2 * M)) (2 * (2 * M)) c₁ 1 hc₁pos one_pos
  have ev₂ := poly_exp_small (K ^ M / t) (2 * M) t 1 htpos one_pos
  filter_upwards [ev₁, ev₂, Filter.eventually_ge_atTop (1 : ℝ)] with b hb₁ hb₂ hb1
  have hb0 : 0 ≤ b := by linarith only [hb1]
  have hbpos : 0 < b := by linarith only [hb1]
  set Q := K * b ^ 2 with hQ
  have hmass : Q⁻¹ ≤ SU2GaussianMass.mass (24 * b) := by
    have := mass_lower_poly b (by linarith only [hb1])
    have e : SU2GaussianMass.cap 1 * (24 * b) ^ 2 = Q := by
      rw [hQ, hK]
      ring
    rwa [e] at this
  have hmasspos := SU2GaussianMass.mass_pos (24 * b)
  have hQpos : 0 < Q := by
    by_contra hneg
    push_neg at hneg
    have hinv : Q⁻¹ ≤ 0 := inv_nonpos.mpr hneg
    have hcapm := SU2GaussianMass.mass_cap_lower (24 * b) (by linarith only [hb1])
    have hcapv : SU2GaussianMass.cap (24 * b) = SU2GaussianMass.cap 1 * ((24 * b) * Real.sqrt (24 * b)) := by
      unfold SU2GaussianMass.cap
      simp only [Real.sqrt_one, mul_one]
      ring
    have hKz : K = 0 ∨ 0 < K := hK0.eq_or_lt.imp (fun h => h.symm) id
    rcases hKz with h0 | hpos
    · have hc0 : SU2GaussianMass.cap 1 = 0 := by
        rw [hK] at h0
        linarith only [h0]
      rw [hcapv, hc0] at hcapm
      norm_num at hcapm
    · have : 0 < Q := by rw [hQ]; positivity
      linarith only [this, hneg]
  set P := SU2GaussianMass.mass (24 * b) ^ M with hP
  have hPlow : (Q ^ M)⁻¹ ≤ P := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hQpos.le) hmass M
  have hQM : 0 < Q ^ M := pow_pos hQpos _
  have hσ : Real.exp (-b * c₁) ≤ P ^ 2 / 2 := by
    have hQe : Q ^ M = K ^ M * b ^ (2 * M) := by
      rw [hQ, mul_pow, ← pow_mul]
    have h1 : 2 * (Q ^ M) ^ 2 * Real.exp (-c₁ * b) ≤ 1 := by
      have : (Q ^ M) ^ 2 = K ^ (2 * M) * b ^ (2 * (2 * M)) := by
        rw [hQe, mul_pow, ← pow_mul, ← pow_mul]
        ring_nf
      rw [this]
      calc _ = 2 * K ^ (2 * M) * (b ^ (2 * (2 * M)) * Real.exp (-c₁ * b)) := by ring
        _ ≤ 1 := hb₁
    have h2 : ((Q ^ M)⁻¹) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hQM.le) hPlow 2
    have h3 : Real.exp (-b * c₁) ≤ ((Q ^ M)⁻¹) ^ 2 / 2 := by
      rw [inv_pow, le_div_iff₀ (by norm_num), ← one_div, le_div_iff₀ (by positivity)]
      have e : -b * c₁ = -c₁ * b := by ring
      rw [e]
      linarith only [h1]
    linarith only [h2, h3]
  have hτ : Real.exp (-b * t) ≤ P * t := by
    have hQe : Q ^ M = K ^ M * b ^ (2 * M) := by
      rw [hQ, mul_pow, ← pow_mul]
    have h1 : (Q ^ M) / t * Real.exp (-t * b) ≤ 1 := by
      rw [hQe]
      calc _ = K ^ M / t * (b ^ (2 * M) * Real.exp (-t * b)) := by ring
        _ ≤ 1 := hb₂
    have h3 : Real.exp (-b * t) ≤ (Q ^ M)⁻¹ * t := by
      rw [← one_div, div_mul_eq_mul_div, one_mul, le_div_iff₀ hQM]
      have e : -b * t = -t * b := by ring
      rw [e]
      have h4 : Q ^ M * Real.exp (-t * b) ≤ t := by
        have := mul_le_mul_of_nonneg_right h1 htpos.le
        have e2 : Q ^ M / t * Real.exp (-t * b) * t = Q ^ M * Real.exp (-t * b) := by
          field_simp
        rw [e2, one_mul] at this
        exact this
      linarith only [h4, mul_comm (Q ^ M) (Real.exp (-t * b))]
    exact h3.trans (mul_le_mul_of_nonneg_right hPlow htpos.le)
  obtain ⟨Ω, F, h1, h2, h3, h4, h5, h6⟩ :=
    flux_near_degenerate_explicit n b hb0 t htpos.le hσ hτ
  refine ⟨Ω, F, h1, h2, h3, h4, h5, ?_⟩
  have e : 1 - 2 * ((n : ℝ) + 4) * t = 1 - ε := by
    rw [ht]
    field_simp
  rwa [e] at h6

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector
