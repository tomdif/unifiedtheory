/- A finite block orbit is normalized with its actual coupled Wilson weight.
Only a Gaussian lower envelope factorizes under the reference Haar product. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeBlockTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGaugeBlock CompactDensityEntropy
open WilsonSingleLinkStaples (character character_continuous)
open WilsonGaugeOrbitTail (kinetic_continuous peakCap peakCap_nonneg)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def orbitMass (β : ℝ) (B : Finset (SpatialVertex n)) (u v : Slice n) : ℝ :=
  ∫ q, kineticWeight character β 2 u (rotate n B q v) ∂haar n B

theorem profile_continuous (β : ℝ) (B : Finset (SpatialVertex n)) (u v : Slice n) :
    Continuous (fun q : Parameters n B => kineticWeight character β 2 u (rotate n B q v)) :=
  (kinetic_continuous n β).comp
    (f := fun q : Parameters n B => (u,rotate n B q v))
    (continuous_const.prodMk ((rotate_continuous n B).comp
      (f := fun q : Parameters n B => (q,v)) (continuous_id.prodMk continuous_const)))

theorem orbitMass_continuous (β : ℝ) (B : Finset (SpatialVertex n)) :
    Continuous (fun z : Slice n × Slice n => orbitMass n β B z.1 z.2) := by
  unfold orbitMass
  apply GibbsMarginalTower.fiber_integral_continuous (haar n B)
    (fun z : (Slice n × Slice n) × Parameters n B => kineticWeight character β 2 z.1.1
      (rotate n B z.2 z.1.2))
  exact (kinetic_continuous n β).comp
    (f := fun z : (Slice n × Slice n) × Parameters n B => (z.1.1,rotate n B z.2 z.1.2))
    ((continuous_fst.comp continuous_fst).prodMk ((rotate_continuous n B).comp
      (f := fun z : (Slice n × Slice n) × Parameters n B => (z.2,z.1.2)) (by fun_prop)))

theorem orbitMass_pos (β : ℝ) (B : Finset (SpatialVertex n)) (u v : Slice n) :
    0 < orbitMass n β B u v := by
  unfold orbitMass kineticWeight
  apply integral_exp_pos
  exact continuous_integrable _ _ (profile_continuous n β B u v)

theorem orbitMass_rotate (β : ℝ) (B : Finset (SpatialVertex n))
    (q : Parameters n B) (u v : Slice n) :
    orbitMass n β B u (rotate n B q v) = orbitMass n β B u v := by
  unfold orbitMass
  simp_rw [rotate_mul]
  exact integral_mul_right_eq_self
    (fun r => kineticWeight character β 2 u (rotate n B r v)) q

omit [NeZero n] in
/-- The factored object is a reference Gaussian, not a Wilson conditional law. -/
theorem gaussian_mass (s : ℝ) (B : Finset (SpatialVertex n)) :
    (∫ q : Parameters n B, ∏ y : B, SU2GaussianMass.weight s (q y) ∂haar n B) =
      (SU2GaussianMass.mass s)^B.card := by
  have h := integral_fintype_prod_eq_pow (ι := B) (μ := RegulatedGauge.compactHaar Q)
    (SU2GaussianMass.weight s)
  simpa only [Fintype.card_coe] using h

/-- Block normalization is charged only to the number of block vertices. -/
theorem gaussian_lower (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n))
    (u v : Slice n) :
    (SU2GaussianMass.mass (36*β^2))^B.card*kineticWeight character β 2 u v ≤
      (Real.exp 1)^B.card*orbitMass n β B u v := by
  have hp (q : Parameters n B) :
      (∏ y : B, SU2GaussianMass.weight (36*β^2) (q y)) =
        Real.exp (-(36*β^2)*∑ y : B, ‖(q y : ℍ)-1‖^2) := by
    simp only [SU2GaussianMass.weight, ← Real.exp_sum, ← Finset.mul_sum]
  have he : (Real.exp 1)^B.card = Real.exp (B.card : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  have hpoint (q : Parameters n B) :
      (∏ y : B, SU2GaussianMass.weight (36*β^2) (q y))*kineticWeight character β 2 u v ≤
        (Real.exp 1)^B.card*kineticWeight character β 2 u (rotate n B q v) := by
    have hs : 12*β*(∑ y : B, ‖(q y : ℍ)-1‖) ≤
        (B.card : ℝ)+36*β^2*(∑ y : B, ‖(q y : ℍ)-1‖^2) := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun (y : B) _ =>
        show 12*β*‖(q y : ℍ)-1‖ ≤ 1+36*β^2*‖(q y : ℍ)-1‖^2 by
          nlinarith [sq_nonneg (6*β*‖(q y : ℍ)-1‖-1)])
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] using h
    rw [hp, he, kineticWeight, kineticWeight, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left
      (abs_le.mp (kinetic_difference n B q u v)).2 hβ
    nlinarith
  have hc : Continuous (fun q : Parameters n B =>
      ∏ y : B, SU2GaussianMass.weight (36*β^2) (q y)) := by
    have hw := SU2GaussianMass.weight_continuous (36*β^2)
    fun_prop
  have hi := integral_mono
    ((continuous_integrable (haar n B) _ hc).mul_const (kineticWeight character β 2 u v))
    ((continuous_integrable (haar n B) _ (profile_continuous n β B u v)).const_mul
      ((Real.exp 1)^B.card)) hpoint
  simpa only [integral_mul_const, integral_const_mul, gaussian_mass, orbitMass] using hi

theorem orbit_density_le (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n))
    (u v : Slice n) (q : Parameters n B) :
    kineticWeight character β 2 u (rotate n B q v) ≤
      (peakCap β)^B.card*orbitMass n β B u v := by
  have h := gaussian_lower n β hβ B u (rotate n B q v)
  rw [orbitMass_rotate] at h
  have hm := pow_le_pow_left₀ (SU2GaussianMass.mass_pos (36*(β+1)^2)).le
    (SU2GaussianMass.mass_antitone (show 36*β^2 ≤ 36*(β+1)^2 by nlinarith)) B.card
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
    (SU2GaussianMass.mass_cap_lower (36*(β+1)^2) (by nlinarith [sq_nonneg β])) B.card
  rw [one_pow, mul_pow] at hc
  have h1 := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ kineticWeight character β 2 u (rotate n B q v) from (Real.exp_pos _).le)
  have h2 := mul_le_mul_of_nonneg_left (h1.trans h)
    (pow_nonneg (SU2GaussianMass.cap_nonneg (36*(β+1)^2) (by positivity)) B.card)
  have h3 := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ kineticWeight character β 2 u (rotate n B q v) from (Real.exp_pos _).le)
  unfold WilsonGaugeOrbitTail.peakCap
  rw [mul_pow]
  nlinarith

/-- The witness may change all vertices in B simultaneously, including adjacent ones. -/
def bad (B : Finset (SpatialVertex n)) (t : ℝ) : Set (Slice n × Slice n) :=
  {z | ∃ q : Parameters n B, t < kineticAction character 2 z.1 z.2-
    kineticAction character 2 z.1 (rotate n B q z.2)}

theorem bad_open (B : Finset (SpatialVertex n)) (t : ℝ) : IsOpen (bad n B t) := by
  have hc (q : Parameters n B) : Continuous (fun z : Slice n × Slice n =>
      kineticAction character 2 z.1 z.2-kineticAction character 2 z.1 (rotate n B q z.2)) := by
    have hchar := character_continuous
    have hr := (rotate_continuous n B).comp
      (f := fun z : Slice n × Slice n => (q,z.2)) (continuous_const.prodMk continuous_snd)
    unfold kineticAction
    fun_prop
  have he : bad n B t = ⋃ q : Parameters n B,
      {z | t < kineticAction character 2 z.1 z.2-
        kineticAction character 2 z.1 (rotate n B q z.2)} := by ext z; simp [bad]
  rw [he]
  exact isOpen_iUnion (fun q => isOpen_lt continuous_const (hc q))

theorem bad_density_le (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n))
    (t : ℝ) (u v : Slice n) (hbad : (u, v) ∈ bad n B t) :
    kineticWeight character β 2 u v ≤
      Real.exp (-β*t)*(peakCap β)^B.card*orbitMass n β B u v := by
  obtain ⟨q,hq⟩ := hbad
  have he : kineticWeight character β 2 u v ≤
      Real.exp (-β*t)*kineticWeight character β 2 u (rotate n B q v) := by
    unfold kineticWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hq.le hβ]
  exact he.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (orbit_density_le n β hβ B u v q) (Real.exp_pos (-β*t)).le)

theorem orbit_pairing (β : ℝ) (B : Finset (SpatialVertex n)) (u : Slice n)
    (S : C(Slice n, ℝ)) (hS : ∀ q v, S (rotate n B q v) = S v) :
    (∫ v, orbitMass n β B u v*S v ∂WilsonSlabOperator.measure n) =
      ∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n := by
  have hc : Continuous (fun z : Slice n × Parameters n B =>
      kineticWeight character β 2 u (rotate n B z.2 z.1)*S z.1) :=
    ((kinetic_continuous n β).comp
      (f := fun z : Slice n × Parameters n B => (u,rotate n B z.2 z.1))
      (continuous_const.prodMk ((rotate_continuous n B).comp
        (f := fun z : Slice n × Parameters n B => (z.2,z.1))
        (continuous_snd.prodMk continuous_fst)))).mul (S.continuous.comp continuous_fst)
  simp only [orbitMass, ← integral_mul_const]
  rw [integral_integral_swap
    (f := fun v q => kineticWeight character β 2 u (rotate n B q v)*S v)
    (continuous_integrable ((WilsonSlabOperator.measure n).prod (haar n B)) _ hc)]
  have he (q : Parameters n B) : (∫ v, kineticWeight character β 2 u (rotate n B q v)*S v
      ∂WilsonSlabOperator.measure n) =
      ∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n := by
    simpa only [hS] using rotate_integral n B q
      (fun v => kineticWeight character β 2 u v*S v)
  simp_rw [he]
  simp

theorem weighted_tail (β : ℝ) (hβ : 0 ≤ β) (B : Finset (SpatialVertex n)) (t : ℝ)
    (u : Slice n) (S : C(Slice n, ℝ)) (hS : ∀ q v, S (rotate n B q v) = S v)
    (hS0 : ∀ v, 0 ≤ S v) :
    (∫ v in {v | (u, v) ∈ bad n B t}, kineticWeight character β 2 u v*S v
      ∂WilsonSlabOperator.measure n) ≤ Real.exp (-β*t)*(peakCap β)^B.card*
        (∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n) := by
  let E := {v : Slice n | (u, v) ∈ bad n B t}
  have hE : MeasurableSet E := (bad_open n B t).measurableSet.preimage
    (measurable_const.prodMk measurable_id)
  have hK := (kinetic_continuous n β).comp
    (f := fun v : Slice n => (u, v)) (continuous_const.prodMk continuous_id)
  have hM := (orbitMass_continuous n β B).comp
    (f := fun v : Slice n => (u, v)) (continuous_const.prodMk continuous_id)
  have hi := integral_mono
    ((continuous_integrable (WilsonSlabOperator.measure n) _ (hK.mul S.continuous)).indicator hE)
    ((continuous_integrable (WilsonSlabOperator.measure n) _ (hM.mul S.continuous)).const_mul
      (Real.exp (-β*t)*(peakCap β)^B.card)) (fun v => by
      by_cases hv : v ∈ E
      · rw [Set.indicator_of_mem hv]
        have h := mul_le_mul_of_nonneg_right (bad_density_le n β hβ B t u v hv) (hS0 v)
        simpa only [mul_assoc] using h
      · rw [Set.indicator_of_notMem hv]
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (peakCap_nonneg β) B.card))
          (mul_nonneg (orbitMass_pos n β B u v).le (hS0 v)))
  rw [integral_indicator hE, integral_const_mul] at hi
  simp only [Pi.mul_apply, Function.comp_apply] at hi
  rw [orbit_pairing n β B u S hS] at hi
  exact hi

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeBlockTail
