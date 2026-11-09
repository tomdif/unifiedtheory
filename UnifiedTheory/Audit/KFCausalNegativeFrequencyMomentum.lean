/- The actual pure-clock-momentum output grows at least linearly with
clock frequency on a fixed nonzero sourced Gaussian. The coefficient is
the norm of its inverse-clock multiple, proved strictly positive. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNegativeFrequencyMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state state_coe)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse clockInverse_coe)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers (coefficient)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart)
open UnifiedTheory.Audit.KFCausalOriginalPureClockOutput (preOutput preOutput_coe profile_differential)
open UnifiedTheory.Audit.KFCausalSourcedMomentumFactors (pureOutput)

theorem clockInverse_ne_zero (ε : ℝ) (hε : 0 < ε) (f : Hilbert) (hf : f ≠ 0) :
    clockInverse ε hε f ≠ 0 := by
  intro hz
  apply hf
  apply Lp.ext
  filter_upwards [clockInverse_coe ε hε f,Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)]
    with x hx h0
  rw [hz,h0] at hx
  have hc : (clock ε x.1:ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (clock_positive ε x.1 hε.le).ne')
  simpa only [h0] using (mul_eq_zero.mp hx.symm).resolve_left hc

theorem coefficient_lower (ε a p s : ℝ) :
    |p| *‖(clock ε s:ℂ)⁻¹‖ ≤
      ‖coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ)‖ := by
  have him : (coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ)).im = p*(clock ε s)⁻¹ := by
    simp [coefficient,← Complex.ofReal_inv,Complex.mul_im,Complex.mul_re]
  have hi := Complex.abs_im_le_norm (coefficient ε p s-2*(a:ℂ)*(chart ε s:ℂ))
  rw [him,abs_mul] at hi
  simpa only [← Complex.ofReal_inv,Complex.norm_real,Real.norm_eq_abs] using hi

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p q : ℝ) (b : Fin 5 → ℂ)

theorem inverse_norm_frequency :
    ‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C p b)‖ =
      ‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C q b)‖ := by
  have he : ∀ᵐ x ∂volume,
      ‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C p b) x‖ =
      ‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C q b) x‖ := by
    filter_upwards [clockInverse_coe ε hε (state ε a α β hε ha hα hβ hw C p b),
      clockInverse_coe ε hε (state ε a α β hε ha hα hβ hw C q b),
      state_coe ε a α β hε ha hα hβ hw C p b,
      state_coe ε a α β hε ha hα hβ hw C q b] with x hp hq hsp hsq
    rw [hp,hq,hsp,hsq,norm_mul,norm_mul,
      KFCausalNegativeFrequencyEnergy.profile_norm_frequency C p q]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

theorem preOutput_lower :
    |p| *‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C 0 b)‖ ≤
      ‖preOutput ε a hε ha C p α β hα hβ hw b‖ := by
  rw [← inverse_norm_frequency ε a α β hε ha hα hβ hw C p 0 b,
    ← norm_smul_of_nonneg (abs_nonneg p)]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_smul (|p|:ℝ)
      (clockInverse ε hε (state ε a α β hε ha hα hβ hw C p b)),
    clockInverse_coe ε hε (state ε a α β hε ha hα hβ hw C p b),
    state_coe ε a α β hε ha hα hβ hw C p b,
    preOutput_coe ε a hε ha C p α β hα hβ hw b] with x hs hi hf ho
  rw [hs,ho,profile_differential ε a hε C p α β b x]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_abs,hi,hf,norm_mul]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (coefficient_lower ε a p x.1) (norm_nonneg _)

theorem pureOutput_lower (h : ℝ) :
    |h| *|p| *‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C 0 b)‖ ≤
      ‖pureOutput ε a α β hε ha hα hβ hw C p b h‖ := by
  change _ ≤ ‖(-Complex.I*(h:ℂ)) • preOutput ε a hε ha C p α β hα hβ hw b‖
  simp only [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (preOutput_lower ε a α β hε ha hα hβ hw C p b) (abs_nonneg h)

theorem negative_frequency_unbounded (h : ℝ) (hh : h ≠ 0)
    (hf : state ε a α β hε ha hα hβ hw C 0 b ≠ 0) (M : ℝ) :
    ∃ n : ℕ, M < ‖pureOutput ε a α β hε ha hα hβ hw C (-(n:ℝ)) b h‖ := by
  let d := |h| *‖clockInverse ε hε (state ε a α β hε ha hα hβ hw C 0 b)‖
  have hd : 0 < d := mul_pos (abs_pos.mpr hh)
    (norm_pos_iff.mpr (clockInverse_ne_zero ε hε _ hf))
  obtain ⟨n,hn⟩ := exists_nat_gt (M/d)
  refine ⟨n,lt_of_lt_of_le ((div_lt_iff₀ hd).mp hn) ?_⟩
  have hb := pureOutput_lower ε a α β hε ha hα hβ hw C (-(n:ℝ)) b h
  simpa only [abs_neg,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)),d,mul_assoc,mul_left_comm,mul_comm] using hb

#print axioms clockInverse_ne_zero
#print axioms coefficient_lower
#print axioms inverse_norm_frequency
#print axioms preOutput_lower
#print axioms pureOutput_lower
#print axioms negative_frequency_unbounded
end
end UnifiedTheory.Audit.KFCausalNegativeFrequencyMomentum
