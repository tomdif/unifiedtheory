/- A polynomial lower bound on the actual finite-cutoff ground-law variance
of a physical plaquette, with constants independent of spatial volume.
This is a local variance estimate, not survival of a continuum smeared field. -/
import UnifiedTheory.Clay.YangMills.QuaternionRotationFrame
import UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteVarianceFloor
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonSymmetricLinkChange WilsonGroundSmallRotation
open WilsonGroundVarianceBudget WilsonPlaquetteTransport CompactDensityEntropy

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

omit [NeZero n] in
theorem holonomy_shift_base (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j)
    (q : Q) (u : Slice n) :
    spatialHolonomy (shift n (x,i) q u) x i j = q*spatialHolonomy u x i j := by
  have h1 : (spatialStep n x i, j) ≠ (x, i) := by
    intro h
    exact hij (congrArg Prod.snd h).symm
  have h2 : (spatialStep n x j, i) ≠ (x, i) := by
    intro h
    exact spatialStep_ne n x j (congrArg Prod.fst h)
  have h3 : (x, j) ≠ (x, i) := by
    intro h
    exact hij (congrArg Prod.snd h).symm
  simp only [spatialHolonomy, shift_at, shift_away n (x,i) q u _ h1,
    shift_away n (x,i) q u _ h2, shift_away n (x,i) q u _ h3, mul_assoc]

omit [NeZero n] in
theorem pointwise_frame_lower (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j)
    (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) (u : Slice n) :
    8*t^4 ≤ ∑ a : Fin 3,
      ((plaquette n x i j (shift n (x,i) (QuaternionRotationFrame.rotation t a) u)-
        plaquette n x i j u)^2+
       (plaquette n x i j (shift n (x,i) (QuaternionRotationFrame.rotation (-t) a) u)-
        plaquette n x i j u)^2) := by
  simpa only [plaquette, ContinuousMap.coe_mk, holonomy_shift_base n x i j hij] using
    QuaternionRotationFrame.frame_lower t ht h1 (spatialHolonomy u x i j)

theorem energy_frame_lower (β : ℝ) (hβ : 0 ≤ β)
    (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    8*t^4 ≤ ∑ a : Fin 3,
      (responseEnergy n β hβ (x,i) (QuaternionRotationFrame.rotation t a) (plaquette n x i j)+
       responseEnergy n β hβ (x,i) (QuaternionRotationFrame.rotation (-t) a)
         (plaquette n x i j)) := by
  letI := groundLaw_probability n β hβ
  let f := plaquette n x i j
  have hi (q : Q) : Integrable (fun u => (f (shift n (x,i) q u)-f u)^2) (groundLaw n β hβ) :=
    continuous_integrable _ _ (((f.continuous.comp (shift_continuous n (x,i) q)).sub
      f.continuous).pow 2)
  have hI : Integrable (fun u => ∑ a : Fin 3,
      ((f (shift n (x,i) (QuaternionRotationFrame.rotation t a) u)-f u)^2+
       (f (shift n (x,i) (QuaternionRotationFrame.rotation (-t) a) u)-f u)^2))
        (groundLaw n β hβ) :=
    integrable_finset_sum _ (fun a _ => (hi _).add (hi _))
  have h := integral_mono (integrable_const (8*t^4)) hI
    (pointwise_frame_lower n x i j hij t ht h1)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have he := integral_finset_sum Finset.univ (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    (hi (QuaternionRotationFrame.rotation t a)).add (hi (QuaternionRotationFrame.rotation (-t) a)))
  simp only [Pi.add_apply] at he
  rw [he] at h
  have ha (a : Fin 3) := integral_add (hi (QuaternionRotationFrame.rotation t a))
    (hi (QuaternionRotationFrame.rotation (-t) a))
  simp_rw [ha] at h
  exact h

omit [Fact (1 < n)] in
theorem rotation_response_le (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (t : ℝ) (ht : 2 * β * |t| ≤ 1) (a : Fin 3) (f : C(Slice n, ℝ)) :
    responseEnergy n β hβ e (QuaternionRotationFrame.rotation t a) f ≤
      2*(Real.exp 36+1)*variance n β hβ f := by
  have hd := mul_le_mul_of_nonneg_left (QuaternionRotationFrame.distance_le t a) hβ
  have he : Real.exp (36*β*‖((QuaternionRotationFrame.rotation t a : Q) : Quaternion ℝ)-1‖) ≤
      Real.exp 36 := Real.exp_le_exp.mpr (by nlinarith)
  exact (response_le_variance n β hβ e _ f).trans
    (mul_le_mul_of_nonneg_right (by linarith :
      2*(Real.exp (36*β*‖((QuaternionRotationFrame.rotation t a : Q) : Quaternion ℝ)-1‖)+1) ≤
        2*(Real.exp 36+1)) (variance_nonneg n β hβ f))

omit [Fact (1 < n)] in
theorem energy_frame_upper (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (t : ℝ) (ht : 2 * β * |t| ≤ 1) (f : C(Slice n, ℝ)) :
    (∑ a : Fin 3,
      (responseEnergy n β hβ e (QuaternionRotationFrame.rotation t a) f+
       responseEnergy n β hβ e (QuaternionRotationFrame.rotation (-t) a) f)) ≤
      12*(Real.exp 36+1)*variance n β hβ f := by
  have hn : 2*β*|-t| ≤ 1 := by simpa only [abs_neg] using ht
  calc
    _ ≤ ∑ _a : Fin 3, 4*(Real.exp 36+1)*variance n β hβ f := by
      apply Finset.sum_le_sum
      intro a _
      have hp := rotation_response_le n β hβ e t ht a f
      have hm := rotation_response_le n β hβ e (-t) hn a f
      linarith
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit n [NeZero n] [Fact (1 < n)] in
def scale (β : ℝ) : ℝ := 1/(2*(β+1))

omit n [NeZero n] [Fact (1 < n)] in
theorem scale_pos (β : ℝ) (hβ : 0 ≤ β) : 0 < scale β := by unfold scale; positivity

omit n [NeZero n] [Fact (1 < n)] in
theorem scale_le_one (β : ℝ) (hβ : 0 ≤ β) : scale β ≤ 1 := by
  unfold scale
  apply (div_le_one (by positivity : 0 < 2*(β+1))).mpr
  linarith

omit n [NeZero n] [Fact (1 < n)] in
theorem scale_budget (β : ℝ) (hβ : 0 ≤ β) : 2*β*|scale β| ≤ 1 := by
  rw [abs_of_pos (scale_pos β hβ)]
  unfold scale
  rw [mul_one_div]
  apply (div_le_one (by positivity : 0 < 2*(β+1))).mpr
  linarith

/-- The actual physical plaquette variance has a volume-independent polynomial floor. -/
theorem variance_lower (β : ℝ) (hβ : 0 ≤ β)
    (x : SpatialVertex n) (i j : Fin 3) (hij : i ≠ j) :
    1/(24*(Real.exp 36+1)*(β+1)^4) ≤ variance n β hβ (plaquette n x i j) := by
  have h := (energy_frame_lower n β hβ x i j hij (scale β)
    (scale_pos β hβ).le (scale_le_one β hβ)).trans
      (energy_frame_upper n β hβ (x,i) (scale β) (scale_budget β hβ) (plaquette n x i j))
  have hs : 8*(scale β)^4 = 1/(2*(β+1)^4) := by
    unfold scale
    field_simp [show β+1 ≠ 0 by linarith]
    ring
  rw [hs] at h
  have hh := (div_le_iff₀ (by positivity : 0 < 2*(β+1)^4)).mp h
  apply (div_le_iff₀ (by positivity : 0 < 24*(Real.exp 36+1)*(β+1)^4)).mpr
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteVarianceFloor
