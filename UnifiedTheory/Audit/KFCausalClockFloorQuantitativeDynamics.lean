/- A concrete rate for the actual regulated quantum propagator and
observable cutoffs whose norms grow with the approximation parameter. -/
import UnifiedTheory.Audit.KFCausalClockFloorYosidaErrorRate
import UnifiedTheory.Audit.KFCausalPureMomentumCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantitativeDynamics
noncomputable section

theorem balanced_cost (B N K T : ℝ) (hB : 0 ≤ B) (hN : 0 < N) :
    2*Real.sqrt (B/(4*N^2))+
      (Real.sqrt (B/N^2)+K*(2*N^2*Real.sqrt (B/(4*N^6))))*T =
      Real.sqrt B*(1+(1+K)*T)/N := by
  have hs2 : Real.sqrt (4*N^2) = 2*N := by
    rw [show 4*N^2 = (2*N)^2 by ring,Real.sqrt_sq (by positivity)]
  have hs6 : Real.sqrt (4*N^6) = 2*N^3 := by
    rw [show 4*N^6 = (2*N^3)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [Real.sqrt_div hB,Real.sqrt_div hB,Real.sqrt_div hB,hs2,hs6,Real.sqrt_sq hN.le]
  field_simp

theorem pairing_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) (u v : H) :
    ‖inner ℂ u (O u)-inner ℂ v (O v)‖ ≤ ‖O‖*‖u-v‖*(‖u‖+‖v‖) := by
  have he : inner ℂ u (O u)-inner ℂ v (O v) =
      inner ℂ (u-v) (O u)+inner ℂ v (O (u-v)) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [he]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (u-v) (O u)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) v (O (u-v))
  have h3 := mul_le_mul_of_nonneg_left (O.le_opNorm u) (norm_nonneg (u-v))
  have h4 := mul_le_mul_of_nonneg_left (O.le_opNorm (u-v)) (norm_nonneg v)
  have hs := norm_add_le (inner ℂ (u-v) (O u)) (inner ℂ v (O (u-v)))
  nlinarith only [h1,h2,h3,h4,hs]

theorem scaled_pairing_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) (u v : H) (N C M : ℝ) (hN : 0 < N) (hO : ‖O‖ ≤ N)
    (hu : ‖u‖ = M) (hv : ‖v‖ = M) (he : ‖u-v‖ ≤ C/N^2) :
    ‖inner ℂ u (O u)-inner ℂ v (O v)‖ ≤ 2*M*C/N := by
  have hM : 0 ≤ M := hu ▸ norm_nonneg u
  have hp := pairing_error O u v
  rw [hu,hv] at hp
  calc
    _ ≤ ‖O‖*‖u-v‖*(M+M) := hp
    _ ≤ N*(C/N^2)*(M+M) := mul_le_mul_of_nonneg_right
      (mul_le_mul hO he (norm_nonneg _) hN.le) (by positivity)
    _ = 2*M*C/N := by field_simp; ring

open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorYosidaErrorRate
open UnifiedTheory.Audit.KFCausalPureMomentumCutoff

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "U" => evolution ε hε h hne hh m g k
local notation "D" => dynamics ε hε h hne hh m g k
local notation "B" => budget ε hε h hne hh m g k

def windowConstant (s T : ℝ) (w : V) : ℝ :=
  Real.sqrt (B s T w)*(1+(1+|1/h|)*T)

theorem windowConstant_nonneg (s T : ℝ) (hT : 0 ≤ T) (w : V) :
    0 ≤ windowConstant ε hε h hne hh m g k s T w := by
  unfold windowConstant
  positivity

theorem balanced_error (N : ℝ) (hN : 0 < N)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t-s| ≤ T) (w : V) :
    ‖D (N^6) (pow_pos hN _) s t (J w)-U s t (J w)‖ ≤
      windowConstant ε hε h hne hh m g k s T w/N := by
  have he := two_scale_error ε hε h hne hh m g k (N^6) (N^2)
    (pow_pos hN _) (pow_pos hN _) s T t hT ht w
  have hB : 0 ≤ B s T w := mul_nonneg (Real.exp_pos _).le
    (timeEnergy_nonneg ε hε h hne hh m g k s w)
  rw [balanced_cost (B s T w) N |1/h| T hB hN] at he
  exact he

theorem growing_observable_error (N : ℝ) (hN : 0 < N)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t-s| ≤ T) (w : V)
    (O : Hilbert →L[ℂ] Hilbert) (hO : ‖O‖ ≤ N) :
    ‖inner ℂ (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w))
        (O (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w)))-
      inner ℂ (U s t (J w)) (O (U s t (J w)))‖ ≤
      2*‖J w‖*windowConstant ε hε h hne hh m g k s T w/N := by
  exact scaled_pairing_error O (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w))
    (U s t (J w)) N (windowConstant ε hε h hne hh m g k s T w) ‖J w‖ hN hO
    (dynamics_norm ε hε h hne hh m g k ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w))
    (evolution_norm ε hε h hne hh m g k s t (J w))
    (balanced_error ε hε h hne hh m g k (N^2) (pow_pos hN _) s T t hT ht w)

theorem momentum_cutoff_error (N : ℝ) (hN : 0 < N)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t-s| ≤ T) (w : V) :
    ‖inner ℂ (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w))
        (momentumCutoff ε hε h N⁻¹ (inv_pos.mpr hN)
          (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w)))-
      inner ℂ (U s t (J w))
        (momentumCutoff ε hε h N⁻¹ (inv_pos.mpr hN) (U s t (J w)))‖ ≤
      2*‖J w‖*windowConstant ε hε h hne hh m g k s T w/N := by
  apply growing_observable_error ε hε h hne hh m g k N hN s T t hT ht w
  simpa only [inv_inv] using operator_opNorm _ _ _ N⁻¹ (inv_pos.mpr hN)

theorem absolute_cutoff_error (N : ℝ) (hN : 0 < N)
    (s T t : ℝ) (hT : 0 ≤ T) (ht : |t-s| ≤ T) (w : V) :
    ‖inner ℂ (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w))
        (absoluteCutoff ε hε h N⁻¹ (inv_pos.mpr hN)
          (D ((N^2)^6) (pow_pos (pow_pos hN _) _) s t (J w)))-
      inner ℂ (U s t (J w))
        (absoluteCutoff ε hε h N⁻¹ (inv_pos.mpr hN) (U s t (J w)))‖ ≤
      2*‖J w‖*windowConstant ε hε h hne hh m g k s T w/N := by
  apply growing_observable_error ε hε h hne hh m g k N hN s T t hT ht w
  simpa only [inv_inv] using operator_opNorm _ _ _ N⁻¹ (inv_pos.mpr hN)

#print axioms balanced_cost
#print axioms pairing_error
#print axioms scaled_pairing_error
#print axioms windowConstant_nonneg
#print axioms balanced_error
#print axioms growing_observable_error
#print axioms momentum_cutoff_error
#print axioms absolute_cutoff_error
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantitativeDynamics
