/- The full eight-factor response estimate for finite reciprocal sums.
The potential estimate is identified with actual L2 pairings, then
combined with the clock and kinetic operator inequalities at unit couplings. -/
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionFactors
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionClockResponse
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalSuperpositionEnergy
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalSuperpositionFactors
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalGaussianVacuumSquare (original_strip)

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "u" => output n ε h a w c hε ha hh hw hb
local notation "v" => momentumOutput n ε h a w c hε ha hh hw hb
local notation "E" => factorEnergy n ε h a w c hε ha hh hw hb
local notation "R" => factorRate n ε h a w c hε ha hh hw hb
local notation "F" => KFCausalReciprocalCrossPhysical.factorSum n ε h a w c
local notation "V" => KFCausalReciprocalCrossPhysical.momentumFactorSum n ε h a w c

def potentialEnergy : ℝ := E 7+E 5/2+E 6/4
def potentialResponse : ℝ := R 7+R 5/2+R 6/4
def clockKineticEnergy (t : ℝ) : ℝ := (E 0+E 1+E 2)/2+Real.exp (2*t)*(E 3+E 4)/2
def clockKineticResponse (t : ℝ) : ℝ := (R 0+R 1+R 2)/2+Real.exp (2*t)*(R 3+R 4)/2
def fullEnergy (t : ℝ) : ℝ := ∑ j : Fin 8, ‖energyWeight 1 1 1 t j‖^2*E j
def fullResponse (t : ℝ) : ℝ := ∑ j : Fin 8, ‖energyWeight 1 1 1 t j‖^2*R j

theorem factorEnergy_integral (k : Fin 3) : E (index k) = ∫ x, ‖F k x‖^2 := by
  rw [factorEnergy,KFCausalAveragedEnergyGraph.l2_norm_square volume]
  apply integral_congr_ae
  filter_upwards [output_coe n ε h a w c hε ha hh hw hb k] with x hx
  rw [hx]

theorem factorPair_integral (k : Fin 3) :
    inner ℂ (u (index k)) (v (index k)) = ∫ x, conj (F k x)*V k x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [output_coe n ε h a w c hε ha hh hw hb k,
    momentumOutput_coe n ε h a w c hε ha hh hw hb k] with x hx hy
  simp only [hx,hy,RCLike.inner_apply]
  ring

theorem potentialEnergy_integral :
    potentialEnergy n ε h a w c hε ha hh hw hb =
      ∫ x, KFCausalReciprocalCrossPhysical.energyDensity n ε h a w c x := by
  have hi (k : Fin 3) :=
    (KFCausalReciprocalCrossPhysical.factorSum_memLp n ε h a w c hε ha hh hw hb k).integrable_norm_pow
      (by norm_num : (2:ℕ) ≠ 0)
  have h01 : Integrable (fun x => ‖F 0 x‖^2+‖F 1 x‖^2/2) := (hi 0).add ((hi 1).div_const 2)
  have h0 := factorEnergy_integral n ε h a w c hε ha hh hw hb 0
  have h1 := factorEnergy_integral n ε h a w c hε ha hh hw hb 1
  have h2 := factorEnergy_integral n ε h a w c hε ha hh hw hb 2
  change E 7 = _ at h0
  change E 5 = _ at h1
  change E 6 = _ at h2
  unfold potentialEnergy KFCausalReciprocalCrossPhysical.energyDensity
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div,h0,h1,h2]

theorem potentialPair_integral :
    (∫ x, KFCausalReciprocalCrossPhysical.potentialPair n ε h a w c x) =
      inner ℂ (u 7) (v 7)+inner ℂ (u 5) (v 5)/2+inner ℂ (u 6) (v 6)/4 := by
  have hi (k : Fin 3) : Integrable (fun x => conj (F k x)*V k x) := by
    simpa only [Complex.star_def] using
      (KFCausalReciprocalCrossPhysical.factorSum_memLp n ε h a w c hε ha hh hw hb k).star.integrable_mul
        (KFCausalReciprocalCrossPhysical.momentumFactorSum_memLp n ε h a w c hε ha hh hw hb k)
  have h01 : Integrable (fun x => conj (F 0 x)*V 0 x+conj (F 1 x)*V 1 x/2) :=
    (hi 0).add ((hi 1).div_const 2)
  have h0 := factorPair_integral n ε h a w c hε ha hh hw hb 0
  have h1 := factorPair_integral n ε h a w c hε ha hh hw hb 1
  have h2 := factorPair_integral n ε h a w c hε ha hh hw hb 2
  change inner ℂ (u 7) (v 7) = _ at h0
  change inner ℂ (u 5) (v 5) = _ at h1
  change inner ℂ (u 6) (v 6) = _ at h2
  unfold KFCausalReciprocalCrossPhysical.potentialPair
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem potentialResponse_integral :
    potentialResponse n ε h a w c hε ha hh hw hb =
      (-2/h)*(∫ x, KFCausalReciprocalCrossPhysical.potentialPair n ε h a w c x).im := by
  rw [potentialPair_integral n ε h a w c hε ha hh hw hb]
  unfold potentialResponse factorRate
  norm_num [Complex.add_im,Complex.div_im]
  ring

theorem unit_weights (t : ℝ) (r : Fin 8 → ℝ) :
    (∑ j : Fin 8, ‖energyWeight 1 1 1 t j‖^2*r j) =
      (r 0+r 1+r 2)/2+Real.exp (2*t)*(r 3+r 4)/2+Real.exp (2*t)*(r 7+r 5/2+r 6/4) := by
  simp_rw [KFCausalPhysicalEnergyFactors.energyWeight_norm_square 1 1 1 t
    (by norm_num) (by norm_num) (by norm_num)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring!

theorem fullEnergy_decomposition (t : ℝ) : fullEnergy n ε h a w c hε ha hh hw hb t =
    clockKineticEnergy n ε h a w c hε ha hh hw hb t+
      Real.exp (2*t)*potentialEnergy n ε h a w c hε ha hh hw hb := unit_weights t E

theorem fullResponse_decomposition (t : ℝ) : fullResponse n ε h a w c hε ha hh hw hb t =
    clockKineticResponse n ε h a w c hε ha hh hw hb t+
      Real.exp (2*t)*potentialResponse n ε h a w c hε ha hh hw hb := unit_weights t R

theorem clockKinetic_lower (t : ℝ) :
    -(1/(4*ε))*clockKineticEnergy n ε h a w c hε ha hh hw hb t ≤
      clockKineticResponse n ε h a w c hε ha hh hw hb t := by
  have h0 := (clock_energy_bounds n ε h a w c hε ha hh hw hb).1
  have h1 := (kinetic_bounds n ε h a w c hε ha hh hw hb 0).1
  have h2 := (kinetic_bounds n ε h a w c hε ha hh hw hb 1).1
  have h3 := (kinetic_bounds n ε h a w c hε ha hh hw hb 2).1
  have h4 := (kinetic_bounds n ε h a w c hε ha hh hw hb 3).1
  change 0 ≤ R 1 at h1
  change 0 ≤ R 2 at h2
  change 0 ≤ R 3 at h3
  change 0 ≤ R 4 at h4
  have hc : 0 ≤ 1/(4*ε) := by positivity
  have he : E 0/2 ≤ clockKineticEnergy n ε h a w c hε ha hh hw hb t := by
    have hs : 0 ≤ (E 1+E 2)/2 := by unfold factorEnergy; positivity
    have hg : 0 ≤ Real.exp (2*t)*(E 3+E 4)/2 := by unfold factorEnergy; positivity
    unfold clockKineticEnergy
    linarith
  have hr : -(1/(4*ε))*(E 0/2) ≤ clockKineticResponse n ε h a w c hε ha hh hw hb t := by
    have hg := mul_nonneg (Real.exp_pos (2*t)).le (add_nonneg h3 h4)
    unfold clockKineticResponse
    linarith
  exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hc)).trans hr

theorem exists_uniform_full_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*fullEnergy n ε h a w c hε ha hh hw (original_strip ε h hε hb) t ≤
        fullResponse n ε h a w c hε ha hh hw (original_strip ε h hε hb) t := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionClockResponse.exists_uniform_potential_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb t
  have hp := hbound n ε h a w c hε ha hh hw hb
  rw [← potentialEnergy_integral n ε h a w c hε ha hh hw (original_strip ε h hε hb),
    ← potentialResponse_integral n ε h a w c hε ha hh hw (original_strip ε h hε hb)] at hp
  have hc := clockKinetic_lower n ε h a w c hε ha hh hw (original_strip ε h hε hb) t
  have he : 0 ≤ clockKineticEnergy n ε h a w c hε ha hh hw (original_strip ε h hε hb) t := by
    unfold clockKineticEnergy factorEnergy
    positivity
  have hκ : 1/(4*ε) ≤ (C+2)/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hk := (mul_le_mul_of_nonneg_right (neg_le_neg hκ) he).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [fullEnergy_decomposition,fullResponse_decomposition]
  convert hs using 1
  ring

#print axioms factorEnergy_integral
#print axioms factorPair_integral
#print axioms potentialEnergy_integral
#print axioms potentialPair_integral
#print axioms potentialResponse_integral
#print axioms unit_weights
#print axioms fullEnergy_decomposition
#print axioms fullResponse_decomposition
#print axioms clockKinetic_lower
#print axioms exists_uniform_full_response
end
end UnifiedTheory.Audit.KFCausalReciprocalSuperpositionEnergy
