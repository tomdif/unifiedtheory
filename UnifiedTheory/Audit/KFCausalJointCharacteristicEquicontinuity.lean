/- Uniform local frequency control and local time Lipschitz estimates
produce equicontinuity in time and frequency jointly. -/
import UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalJointCharacteristicEquicontinuity
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness

theorem joint_equicontinuity (F : ℕ → ℝ × ℝ → ℂ) (s : ℝ)
    (hf : ∀ T η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ t v w : ℝ, |t-s| ≤ T → |v-w| ≤ ρ → ‖F n (t,v)-F n (t,w)‖ < η)
    (ht : ∀ T v : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ t u : ℝ, |t-s| ≤ T → |u-s| ≤ T → ‖F n (t,v)-F n (u,v)‖ ≤ C*|t-u|) :
    EventuallyLocallyEquicontinuous F := by
  intro x η hη
  let T := |x.1-s|+1
  obtain ⟨ρ,hρ,N,hN⟩ := hf T (η/2) (by positivity)
  obtain ⟨C,hC,he⟩ := ht T x.2
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  let δ := min ρ (min 1 (η/(2*(C+1))))
  have hδ : 0 < δ := lt_min hρ (lt_min zero_lt_one (by positivity))
  refine ⟨δ,hδ,max N M,?_⟩
  intro n hn y hy
  have hyNorm : ‖y-x‖ < δ := by simpa only [dist_eq_norm] using hy
  have htime : |y.1-x.1| < δ := (norm_fst_le (y-x)).trans_lt hyNorm
  have hfreq : |y.2-x.2| < δ := (norm_snd_le (y-x)).trans_lt hyNorm
  have htime1 : |y.1-x.1| < 1 := htime.trans_le ((min_le_right ρ _).trans (min_le_left _ _))
  have hyT : |y.1-s| ≤ T := by
    have htri := abs_sub_le y.1 x.1 s
    dsimp [T]
    linarith
  have hxT : |x.1-s| ≤ T := by dsimp [T]; linarith
  have hfreqρ : |y.2-x.2| ≤ ρ := hfreq.le.trans (min_le_left _ _)
  have hfreqbound := hN n ((le_max_left N M).trans hn) y.1 y.2 x.2 hyT hfreqρ
  have htimebound := hM n ((le_max_right N M).trans hn) y.1 x.1 hyT hxT
  have hd : |y.1-x.1| < η/(2*(C+1)) := htime.trans_le
    ((min_le_right ρ _).trans (min_le_right _ _))
  have hmul : (C+1)*|y.1-x.1| < η/2 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp hd
    nlinarith
  have hsmall : C*|y.1-x.1| < η/2 := by nlinarith [abs_nonneg (y.1-x.1)]
  rw [dist_eq_norm]
  exact (norm_sub_le_norm_sub_add_norm_sub (F n y) (F n (y.1,x.2)) (F n x)).trans_lt
    ((add_le_add hfreqbound.le htimebound).trans_lt (by linarith))

#print axioms joint_equicontinuity
end
end UnifiedTheory.Audit.KFCausalJointCharacteristicEquicontinuity
