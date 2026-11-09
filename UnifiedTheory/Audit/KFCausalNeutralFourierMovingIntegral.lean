/- Differentiation of the actual neutral marginal under moving charged
coefficients and clock geometry. All local domination is constructed
from the packet family; no response bound is included as a hypothesis. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierMovingJet
import UnifiedTheory.Audit.KFCausalNeutralFourierMovingEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierMovingIntegral
noncomputable section
open MeasureTheory
open scoped ComplexConjugate Topology
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralFourierResponseSplit (slope response frequencyResponse)
open KFCausalNeutralFourierMovingEnvelope (moving_envelope real_local_bound)
open KFCausalNeutralLinePackets (step)
open KFCausalNeutralFourierEnergy (frequencyMoment)
open KFCausalNeutralFourierMovingJet (chargedSlope)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)

variable (n : ℕ) (β : ℝ) (hβ : 0 < β) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

theorem field_continuous (c : Fin n → ℂ) (j : ℕ) (a y : ℝ) :
    Continuous (fieldLine n β b c P j a y) :=
  Differentiable.continuous (fun x => (KFCausalNeutralFourierMomentum.fieldLine_derivative n β b c P j a y x).differentiableAt)

theorem slope_continuous (c cd : Fin n → ℂ) (j : ℕ) (a y ad yd : ℝ) :
    Continuous (slope n β b c cd P j a y ad yd) :=
  ((field_continuous n β b P cd j a y).add
    (continuous_const.mul (field_continuous n β b P c (j-1) a y))).add
    (continuous_const.mul (field_continuous n β b (fun i => step β (b i) (P i)) c j a y))

include hβ

theorem value_slope_envelope (j : ℕ) (C Cd : ℝ → Fin n → ℂ) (a y ad yd : ℝ → ℝ)
    (hC : ∀ i, Continuous (fun t => C t i)) (hCd : ∀ i, Continuous (fun t => Cd t i))
    (ha : Continuous a) (hy : Continuous y) (had : Continuous ad) (hyd : Continuous yd) (s : ℝ) :
    ∃ D : ℝ → ℝ, Continuous D ∧ MemLp D 2 volume ∧ (∀ x, 0 ≤ D x) ∧
      ∀ t ∈ Set.Icc (s-1) (s+1), ∀ x,
        ‖fieldLine n β b (C t) P j (a t) (y t) x‖ ≤ D x ∧
        ‖slope n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x‖ ≤ D x := by
  obtain ⟨D₀,h₀,h₀₂,h₀₀,hb₀⟩ := moving_envelope n β hβ b P j C a y hC ha hy s
  obtain ⟨D₁,h₁,h₁₂,h₁₀,hb₁⟩ := moving_envelope n β hβ b P j Cd a y hCd ha hy s
  obtain ⟨D₂,h₂,h₂₂,h₂₀,hb₂⟩ := moving_envelope n β hβ b P (j-1) C a y hC ha hy s
  obtain ⟨D₃,h₃,h₃₂,h₃₀,hb₃⟩ := moving_envelope n β hβ b (fun i => step β (b i) (P i)) j C a y hC ha hy s
  obtain ⟨M,hM,hm⟩ := real_local_bound ad had s
  obtain ⟨N,hN,hn⟩ := real_local_bound yd hyd s
  let J : ℝ := ‖(j:ℂ)‖
  have hJ : 0 ≤ J := norm_nonneg _
  refine ⟨fun x => D₀ x+D₁ x+J*M*D₂ x+N*D₃ x,
    ((h₀.add h₁).add (continuous_const.mul h₂)).add (continuous_const.mul h₃),
    ((h₀₂.add h₁₂).add (h₂₂.const_mul (J*M))).add (h₃₂.const_mul N),
    fun x => add_nonneg (add_nonneg (add_nonneg (h₀₀ x) (h₁₀ x))
      (mul_nonneg (mul_nonneg hJ hM) (h₂₀ x))) (mul_nonneg hN (h₃₀ x)),?_⟩
  intro t ht x
  have hp : ‖(j:ℂ)*(ad t:ℂ)*fieldLine n β b (C t) P (j-1) (a t) (y t) x‖ ≤ J*M*D₂ x := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hm t ht) hJ) (hb₂ t ht x)
      (norm_nonneg _) (mul_nonneg hJ hM)
  have hs : ‖(Complex.I*(yd t:ℂ))*fieldLine n β b (C t) (fun i => step β (b i) (P i)) j (a t) (y t) x‖ ≤ N*D₃ x := by
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (hn t ht) (hb₃ t ht x) (norm_nonneg _) hN
  constructor
  · exact (hb₀ t ht x).trans (by nlinarith [h₁₀ x,h₂₀ x,h₃₀ x,mul_nonneg (mul_nonneg hJ hM) (h₂₀ x),mul_nonneg hN (h₃₀ x)])
  · unfold KFCausalNeutralFourierResponseSplit.slope
    have hh := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hb₁ t ht x) hp)) hs)
    exact hh.trans (by linarith [h₀₀ x])

theorem energy_derivative (j : ℕ) (C Cd : ℝ → Fin n → ℂ) (a y ad yd : ℝ → ℝ)
    (hC : ∀ i, Continuous (fun t => C t i)) (hCd : ∀ i, Continuous (fun t => Cd t i))
    (ha : Continuous a) (hy : Continuous y) (had : Continuous ad) (hyd : Continuous yd)
    (hCd' : ∀ t i, HasDerivAt (fun v => C v i) (Cd t i) t)
    (ha' : ∀ t, HasDerivAt a (ad t) t) (hy' : ∀ t, HasDerivAt y (yd t) t) (s : ℝ) :
    HasDerivAt (fun t => ∫ x, ‖fieldLine n β b (C t) P j (a t) (y t) x‖^2)
      (∫ x, response n β b (C s) (Cd s) P j (a s) (y s) (ad s) (yd s) x) s := by
  obtain ⟨D,_,hD,hD₀,hb⟩ := value_slope_envelope n β hβ b P j C Cd a y ad yd hC hCd ha hy had hyd s
  have hB : Integrable (fun x => 2*(D x*D x)) := (hD.integrable_mul hD).const_mul 2
  have hi := KFCausalNeutralFourierEnergy.fieldLine_square_integrable n β b (C s) P hβ j (a s) (y s)
  have hv (t : ℝ) : Continuous (fun x => ‖fieldLine n β b (C t) P j (a t) (y t) x‖^2) :=
    (field_continuous n β b P (C t) j (a t) (y t)).norm.pow 2
  have hg : Continuous (fun x => response n β b (C s) (Cd s) P j (a s) (y s) (ad s) (yd s) x) :=
    continuous_const.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp
      (field_continuous n β b P (C s) j (a s) (y s))).mul
      (slope_continuous n β b P (C s) (Cd s) j (a s) (y s) (ad s) (yd s))))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => ‖fieldLine n β b (C t) P j (a t) (y t) x‖^2)
    (F' := fun t x => response n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x)
    (bound := fun x => 2*(D x*D x))
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t => (hv t).aestronglyMeasurable)) hi hg.aestronglyMeasurable
    ?_ hB (Filter.Eventually.of_forall (fun x t _ =>
      KFCausalNeutralFourierMovingJet.square_derivative n β b P C (Cd t) a y (ad t) (yd t) t x j
        (hCd' t) (ha' t) (hy' t)))
  · exact hd.2
  · exact Filter.Eventually.of_forall (fun x t ht => by
      unfold response
      calc
        ‖2*(conj (fieldLine n β b (C t) P j (a t) (y t) x)*
          slope n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x).re‖
            = 2*|(conj (fieldLine n β b (C t) P j (a t) (y t) x)*
              slope n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x).re| := by
                rw [Real.norm_eq_abs,abs_mul]; norm_num
        _ ≤ 2*‖conj (fieldLine n β b (C t) P j (a t) (y t) x)*
              slope n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
        _ = 2*(‖fieldLine n β b (C t) P j (a t) (y t) x‖*
              ‖slope n β b (C t) (Cd t) P j (a t) (y t) (ad t) (yd t) x‖) := by
            rw [norm_mul,Complex.norm_conj]
        _ ≤ 2*(D x*D x) := mul_le_mul_of_nonneg_left
            (mul_le_mul (hb t ht x).1 (hb t ht x).2 (norm_nonneg _) (hD₀ x)) (by norm_num))

theorem frequency_energy_derivative (j : ℕ) (C Cd : ℝ → Fin n → ℂ) (a y ad yd : ℝ → ℝ)
    (hC : ∀ i, Continuous (fun t => C t i)) (hCd : ∀ i, Continuous (fun t => Cd t i))
    (ha : Continuous a) (hy : Continuous y) (had : Continuous ad) (hyd : Continuous yd)
    (hCd' : ∀ t i, HasDerivAt (fun v => C v i) (Cd t i) t)
    (ha' : ∀ t, HasDerivAt a (ad t) t) (hy' : ∀ t, HasDerivAt y (yd t) t) (s : ℝ) :
    HasDerivAt (fun t => ∫ k, frequencyMoment n β b (C t) P j (a t) (y t) k)
      (∫ k, frequencyResponse n β b (C s) (Cd s) P j (a s) (y s) (ad s) (yd s) k) s := by
  have hd := energy_derivative n β hβ b P j C Cd a y ad yd hC hCd ha hy had hyd hCd' ha' hy' s
  simp_rw [KFCausalNeutralFourierEnergy.field_plancherel n β b _ P hβ,
    KFCausalNeutralFourierResponseSplit.response_frequency_integral n β b _ _ P hβ] at hd
  exact hd

theorem actual_frequency_energy_derivative (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r rd : ℝ → ℂ) (hr : Continuous r) (hrd : Continuous rd)
    (hr' : ∀ t, HasDerivAt r (rd t) t) (s u v Y : ℝ) (j : ℕ) :
    HasDerivAt (fun t => ∫ k, frequencyMoment n β b
      (coefficients n w c (chart α (r t) (u^2+v^2) Y)) P j (fieldSlope (r t)*v) (2*(r t).im*v) k)
      (∫ k, frequencyResponse n β b (coefficients n w c (chart α (r s) (u^2+v^2) Y))
        (chargedSlope n α w c (r s) (rd s) u v Y) P j
        (fieldSlope (r s)*v) (2*(r s).im*v) (-2*(rd s).re*v) (2*(rd s).im*v) k) s := by
  apply frequency_energy_derivative n β hβ b P j
    (fun t => coefficients n w c (chart α (r t) (u^2+v^2) Y))
    (fun t => chargedSlope n α w c (r t) (rd t) u v Y)
    (fun t => fieldSlope (r t)*v) (fun t => 2*(r t).im*v)
    (fun t => -2*(rd t).re*v) (fun t => 2*(rd t).im*v)
  · intro i
    unfold coefficients chart KFCausalReciprocalWedgeGeometry.gamma
    fun_prop
  · intro i
    unfold chargedSlope KFCausalClusteredClockFactors.Zd coefficients chart KFCausalReciprocalWedgeGeometry.gamma
    fun_prop
  · unfold fieldSlope
    fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro t i
    exact KFCausalNeutralFourierMovingJet.actual_coefficients_derivative n α w c r (rd t) t u v Y (hr' t) i
  · intro t
    exact KFCausalNeutralFourierMovingJet.actual_field_derivative r (rd t) t v (hr' t)
  · intro t
    exact KFCausalNeutralFourierMovingJet.actual_translation_derivative r (rd t) t v (hr' t)

#print axioms field_continuous
#print axioms slope_continuous
#print axioms value_slope_envelope
#print axioms energy_derivative
#print axioms frequency_energy_derivative
#print axioms actual_frequency_energy_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralFourierMovingIntegral
