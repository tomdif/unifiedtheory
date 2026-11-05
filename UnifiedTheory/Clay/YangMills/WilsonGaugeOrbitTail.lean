/- Local normalization and concentration along a one-vertex gauge orbit.
The bound is polynomial in coupling and independent of the spatial volume. -/
import UnifiedTheory.Clay.YangMills.WilsonSiteGauge
import UnifiedTheory.Clay.YangMills.SU2GaussianMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSiteGauge
open WilsonSingleLinkStaples (character character_continuous)
open CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem kinetic_continuous (β : ℝ) :
    Continuous (fun z : Slice n × Slice n => kineticWeight character β 2 z.1 z.2) := by
  have hc := character_continuous
  unfold kineticWeight kineticAction
  fun_prop

def orbitMass (β : ℝ) (x : SpatialVertex n) (u v : Slice n) : ℝ :=
  ∫ q, kineticWeight character β 2 u (rotate n x q v) ∂RegulatedGauge.compactHaar Q

theorem profile_continuous (β : ℝ) (x : SpatialVertex n) (u v : Slice n) :
    Continuous (fun q : Q => kineticWeight character β 2 u (rotate n x q v)) :=
  (kinetic_continuous n β).comp
    (f := fun q : Q => (u,rotate n x q v))
    (continuous_const.prodMk ((rotate_continuous n x).comp
      (f := fun q : Q => (q,v)) (continuous_id.prodMk continuous_const)))

theorem orbitMass_continuous (β : ℝ) (x : SpatialVertex n) :
    Continuous (fun z : Slice n × Slice n => orbitMass n β x z.1 z.2) := by
  unfold orbitMass
  apply GibbsMarginalTower.fiber_integral_continuous (RegulatedGauge.compactHaar Q)
    (fun z : (Slice n × Slice n) × Q => kineticWeight character β 2 z.1.1
      (rotate n x z.2 z.1.2))
  exact (kinetic_continuous n β).comp
    (f := fun z : (Slice n × Slice n) × Q => (z.1.1,rotate n x z.2 z.1.2))
    ((continuous_fst.comp continuous_fst).prodMk ((rotate_continuous n x).comp
      (f := fun z : (Slice n × Slice n) × Q => (z.2,z.1.2)) (by fun_prop)))

theorem orbitMass_pos (β : ℝ) (x : SpatialVertex n) (u v : Slice n) :
    0 < orbitMass n β x u v := by
  unfold orbitMass kineticWeight
  apply integral_exp_pos
  exact continuous_integrable _ _ (profile_continuous n β x u v)

theorem orbitMass_rotate (β : ℝ) (x : SpatialVertex n) (q : Q) (u v : Slice n) :
    orbitMass n β x u (rotate n x q v) = orbitMass n β x u v := by
  unfold orbitMass
  simp_rw [rotate_mul]
  exact integral_mul_right_eq_self
    (fun r => kineticWeight character β 2 u (rotate n x r v)) q

/-- A quadratic envelope of the local Lipschitz cost gives a Haar mass lower bound. -/
theorem gaussian_lower (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (u v : Slice n) :
    SU2GaussianMass.mass (36*β^2)*kineticWeight character β 2 u v ≤
      Real.exp 1*orbitMass n β x u v := by
  have hc := profile_continuous n β x u v
  have hi := integral_mono
    ((continuous_integrable (RegulatedGauge.compactHaar Q) _
      (SU2GaussianMass.weight_continuous (36*β^2))).mul_const
        (kineticWeight character β 2 u v))
    ((continuous_integrable (RegulatedGauge.compactHaar Q) _ hc).const_mul (Real.exp 1))
    (fun q => by
      unfold SU2GaussianMass.weight kineticWeight
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (abs_le.mp (WilsonSiteGauge.kinetic_difference n x q u v)).2 hβ
      nlinarith [sq_nonneg (6*β*‖(q : ℍ)-1‖-1)])
  simpa only [integral_mul_const, integral_const_mul, SU2GaussianMass.mass, orbitMass] using hi

omit n [NeZero n] in
def peakCap (β : ℝ) : ℝ := Real.exp 1*SU2GaussianMass.cap (36*(β+1)^2)

omit n [NeZero n] in
theorem peakCap_nonneg (β : ℝ) : 0 ≤ peakCap β :=
  mul_nonneg (Real.exp_pos _).le (SU2GaussianMass.cap_nonneg _ (by positivity))

omit n [NeZero n] in
theorem peakCap_formula (β : ℝ) (hβ : 0 ≤ β) :
    peakCap β = Real.exp 1*SU2GaussianMass.cap 36*(β+1)^3 := by
  unfold peakCap SU2GaussianMass.cap
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36), Real.sqrt_sq (by linarith : 0 ≤ β+1)]
  ring

/-- Every point of the same local orbit is dominated by its own normalizer. -/
theorem orbit_density_le (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n)
    (u v : Slice n) (q : Q) :
    kineticWeight character β 2 u (rotate n x q v) ≤ peakCap β*orbitMass n β x u v := by
  have h := gaussian_lower n β hβ x u (rotate n x q v)
  rw [orbitMass_rotate] at h
  have hm := SU2GaussianMass.mass_antitone (show 36*β^2 ≤ 36*(β+1)^2 by nlinarith)
  have hs : 3 / 4 ≤ 36*(β+1)^2 := by nlinarith [sq_nonneg β]
  have hc := SU2GaussianMass.mass_cap_lower (36*(β+1)^2) hs
  have h1 := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ kineticWeight character β 2 u (rotate n x q v) from (Real.exp_pos _).le)
  have h2 := mul_le_mul_of_nonneg_left (h1.trans h)
    (SU2GaussianMass.cap_nonneg (36*(β+1)^2) (by positivity))
  have h3 := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ kineticWeight character β 2 u (rotate n x q v) from (Real.exp_pos _).le)
  unfold peakCap
  nlinarith

/-- Bad means that some gauge rotation at this vertex lowers the temporal
action by more than t. This is not a condition on spatial plaquette defects. -/
def bad (x : SpatialVertex n) (t : ℝ) : Set (Slice n × Slice n) :=
  {z | ∃ q : Q, t < kineticAction character 2 z.1 z.2-
    kineticAction character 2 z.1 (rotate n x q z.2)}

theorem bad_open (x : SpatialVertex n) (t : ℝ) : IsOpen (bad n x t) := by
  have hc (q : Q) : Continuous (fun z : Slice n × Slice n =>
      kineticAction character 2 z.1 z.2-kineticAction character 2 z.1 (rotate n x q z.2)) := by
    have hchar := character_continuous
    have hr := (rotate_continuous n x).comp
      (f := fun z : Slice n × Slice n => (q,z.2)) (continuous_const.prodMk continuous_snd)
    unfold kineticAction
    fun_prop
  have he : bad n x t = ⋃ q : Q, {z | t < kineticAction character 2 z.1 z.2-
      kineticAction character 2 z.1 (rotate n x q z.2)} := by ext z; simp [bad]
  rw [he]
  exact isOpen_iUnion (fun q => isOpen_lt continuous_const (hc q))

theorem bad_density_le (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n)
    (t : ℝ) (u v : Slice n) (hbad : (u, v) ∈ bad n x t) :
    kineticWeight character β 2 u v ≤ Real.exp (-β*t)*peakCap β*orbitMass n β x u v := by
  obtain ⟨q,hq⟩ := hbad
  have he : kineticWeight character β 2 u v ≤
      Real.exp (-β*t)*kineticWeight character β 2 u (rotate n x q v) := by
    unfold kineticWeight
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hq.le hβ]
  exact he.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (orbit_density_le n β hβ x u v q) (Real.exp_pos (-β*t)).le)

/-- Haar invariance cancels the local normalizer against every invariant source. -/
theorem orbit_pairing (β : ℝ) (x : SpatialVertex n) (u : Slice n)
    (S : C(Slice n, ℝ)) (hS : ∀ q v, S (rotate n x q v) = S v) :
    (∫ v, orbitMass n β x u v*S v ∂WilsonSlabOperator.measure n) =
      ∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n := by
  have hc : Continuous (fun z : Slice n × Q =>
      kineticWeight character β 2 u (rotate n x z.2 z.1)*S z.1) :=
    ((kinetic_continuous n β).comp (continuous_const.prodMk ((rotate_continuous n x).comp
      (continuous_snd.prodMk continuous_fst)))).mul (S.continuous.comp continuous_fst)
  simp only [orbitMass, ← integral_mul_const]
  rw [integral_integral_swap
    (f := fun v q => kineticWeight character β 2 u (rotate n x q v)*S v) (continuous_integrable
    ((WilsonSlabOperator.measure n).prod (RegulatedGauge.compactHaar Q)) _ hc)]
  have he (q : Q) : (∫ v, kineticWeight character β 2 u (rotate n x q v)*S v
      ∂WilsonSlabOperator.measure n) =
      ∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n := by
    simpa only [hS] using rotate_integral n x q
      (fun v => kineticWeight character β 2 u v*S v)
  simp_rw [he]
  simp

theorem weighted_tail (β : ℝ) (hβ : 0 ≤ β) (x : SpatialVertex n) (t : ℝ)
    (u : Slice n) (S : C(Slice n, ℝ)) (hS : ∀ q v, S (rotate n x q v) = S v)
    (hS0 : ∀ v, 0 ≤ S v) :
    (∫ v in {v | (u, v) ∈ bad n x t}, kineticWeight character β 2 u v*S v
      ∂WilsonSlabOperator.measure n) ≤ Real.exp (-β*t)*peakCap β*
        (∫ v, kineticWeight character β 2 u v*S v ∂WilsonSlabOperator.measure n) := by
  let B := {v : Slice n | (u, v) ∈ bad n x t}
  have hB : MeasurableSet B := (bad_open n x t).measurableSet.preimage
    (measurable_const.prodMk measurable_id)
  have hK := (kinetic_continuous n β).comp
    (f := fun v : Slice n => (u, v)) (continuous_const.prodMk continuous_id)
  have hM := (orbitMass_continuous n β x).comp
    (f := fun v : Slice n => (u, v)) (continuous_const.prodMk continuous_id)
  have hi := integral_mono
    ((continuous_integrable (WilsonSlabOperator.measure n) _ (hK.mul S.continuous)).indicator hB)
    ((continuous_integrable (WilsonSlabOperator.measure n) _ (hM.mul S.continuous)).const_mul
      (Real.exp (-β*t)*peakCap β)) (fun v => by
      by_cases hv : v ∈ B
      · rw [Set.indicator_of_mem hv]
        have h := mul_le_mul_of_nonneg_right (bad_density_le n β hβ x t u v hv) (hS0 v)
        simpa only [mul_assoc] using h
      · rw [Set.indicator_of_notMem hv]
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (peakCap_nonneg β))
          (mul_nonneg (orbitMass_pos n β x u v).le (hS0 v)))
  rw [integral_indicator hB, integral_const_mul] at hi
  simp only [Pi.mul_apply, Function.comp_apply] at hi
  rw [orbit_pairing n β x u S hS] at hi
  exact hi

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitTail
