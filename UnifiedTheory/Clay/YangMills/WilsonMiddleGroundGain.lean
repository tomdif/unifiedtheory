/- Finite-difference integration by parts controls the formerly unbounded
middle log-ground insertion. The new price uses l1 times l2 displacement;
it still carries square-root link-count loss for equal rotations. -/
import UnifiedTheory.Clay.YangMills.WilsonJointGroundLipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMiddleGroundGain
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonMiddleBridge WilsonMiddleEntropy WilsonJointGroundLipschitz
open WilsonVarianceProfile WilsonVarianceProfileCost CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def pairedGain (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) : C(Slice n, ℝ) :=
  ⟨fun u => WilsonJointEntropy.logGain n β hβ q u+WilsonJointEntropy.logGain n β hβ q⁻¹ u,
    (WilsonJointEntropy.logGain_continuous n β hβ q).add
      (WilsonJointEntropy.logGain_continuous n β hβ q⁻¹)⟩

def gainMean (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) : ℝ :=
  ∫ u, pairedGain n β hβ q u ∂law n β v w

/-- A second ground-log difference is a first-difference response of the middle density. -/
theorem gainMean_as_response (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) :
    gainMean n β hβ q v w =
      (∫ u, density n β v w u*WilsonJointEntropy.logGain n β hβ q u
        ∂WilsonSlabOperator.measure n) -
      (∫ u, density n β v w (q*u)*WilsonJointEntropy.logGain n β hβ q u
        ∂WilsonSlabOperator.measure n) := by
  have hp := density_continuous n β v w
  have hg := WilsonJointEntropy.logGain_continuous n β hβ q
  have hm := WilsonJointEntropy.logGain_continuous n β hβ q⁻¹
  have ht := WilsonJointEntropy.rotation_integral n q
    (fun u => density n β v w u*WilsonJointEntropy.logGain n β hβ q⁻¹ u)
  have he (u : Slice n) : WilsonJointEntropy.logGain n β hβ q⁻¹ (q*u) =
      -WilsonJointEntropy.logGain n β hβ q u := by
    unfold WilsonJointEntropy.logGain
    rw [inv_mul_cancel_left]
    ring
  simp_rw [he, mul_neg, integral_neg] at ht
  unfold gainMean
  rw [← density_integral]
  change (∫ u, density n β v w u*(WilsonJointEntropy.logGain n β hβ q u+
    WilsonJointEntropy.logGain n β hβ q⁻¹ u) ∂WilsonSlabOperator.measure n) = _
  simp_rw [mul_add]
  have ha := integral_add (continuous_integrable (WilsonSlabOperator.measure n) _ (hp.mul hg))
    (continuous_integrable (WilsonSlabOperator.measure n) _ (hp.mul hm))
  simp only [Pi.mul_apply] at ha
  rw [ha]
  linarith

/-- The middle entropy budget controls this actual insertion, uniformly in endpoints. -/
theorem gainMean_sq_bound (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) :
    (gainMean n β hβ q v w)^2 ≤
      5184*β^3*(length n q)^2*WilsonJointRotation.cost n q := by
  have hg := WilsonJointEntropy.logGain_continuous n β hβ q
  have h := response_sq_le_entropy (WilsonSlabOperator.measure n)
    (density n β v w) (fun u => density n β v w (q*u))
    (WilsonJointEntropy.logGain n β hβ q) (density_continuous n β v w)
    ((density_continuous n β v w).comp (f := fun u : Slice n => q*u)
      (continuous_const.mul continuous_id)) hg
    (density_pos n β v w) (fun u => density_pos n β v w (q*u))
    (density_mass n β v w) (rotated_mass n β q v w)
    (-(6*β*length n q)) (6*β*length n q)
    (fun u => abs_le.mp (log_gain_bound n β hβ q u))
  rw [← gainMean_as_response] at h
  have hb := mul_le_mul_of_nonneg_left (WilsonMiddleEntropy.bound n β hβ q v w)
    (sq_nonneg (6*β*length n q-(-(6*β*length n q))))
  have hh := h.trans hb
  convert hh using 1
  ring

def gainCap (β : ℝ) (q : Slice n) : ℝ :=
  72*β*length n q*Real.sqrt (β*WilsonJointRotation.cost n q)

theorem gainCap_nonneg (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) : 0 ≤ gainCap n β q :=
  mul_nonneg (mul_nonneg (by positivity) (length_nonneg n q)) (Real.sqrt_nonneg _)

theorem gainCap_sq (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    (gainCap n β q)^2 = 5184*β^3*(length n q)^2*WilsonJointRotation.cost n q := by
  unfold gainCap
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hβ (WilsonJointRotation.cost_nonneg n q))]
  ring

theorem gainMean_bound (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) :
    |gainMean n β hβ q v w| ≤ gainCap n β q := by
  apply (sq_le_sq₀ (abs_nonneg _) (gainCap_nonneg n β hβ q)).mp
  rw [sq_abs, gainCap_sq n β hβ]
  exact gainMean_sq_bound n β hβ q v w

/-- The certified insertion cap still has square-root link-count scaling in this direction. -/
theorem gainCap_constant_sq (β : ℝ) (hβ : 0 ≤ β) (a : Q) :
    (gainCap n β (fun _ => a))^2 = 5184*β^3*
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*
        (WilsonJointRotation.cost n (fun _ => a))^2 := by
  have he : (length n (fun _ => a))^2 =
      (Fintype.card (SpatialVertex n × Fin 3) : ℝ)*WilsonJointRotation.cost n (fun _ => a) := by
    simp only [length, WilsonJointRotation.cost, WilsonJointRotation.displacement,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [gainCap_sq n β hβ, he]
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonMiddleGroundGain
