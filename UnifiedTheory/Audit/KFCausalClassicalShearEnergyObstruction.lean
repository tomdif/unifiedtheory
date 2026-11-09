/- Probability laws on actual classical states have uniformly bounded
mean energy and arbitrarily large mean signed shear force. Therefore no
global affine energy bound holds for this classical force. No transfer to
the fixed-hbar quantum operator or its evolution is asserted. -/
import UnifiedTheory.Audit.KFCausalClassicalShearEnergyWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClassicalShearEnergyObstruction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClassicalShearEnergyWitness
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean_eq)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

abbrev State := Phase × (ℝ × ℝ)
def sample (r : ℝ) : State := (phase r,(clockPoint,clockMomentum r))
def baseline : State := (0,(clockPoint,0))
def energy (m g : ℝ) (x : State) : ℝ := hamiltonian (1/2) m g 1 0 x.1 x.2.1 x.2.2
def rate (m g : ℝ) (x : State) : ℝ := longitudinalRate (1/2) m g 1 0 x.1 x.2.1 x.2.2
def signedShear (m g : ℝ) (x : State) : ℝ :=
  response (1/2) x.2.1*amplitude (1/2) 0 x.2.1 x.2.2*
    weightedTilt m g 1 (clock (1/2) x.2.1) x.1/(clock (1/2) x.2.1)^2

def mixingWeight (r : ℝ) : ℝ := 1/(1+r^2)

theorem mixingWeight_bounds (r : ℝ) : 0 ≤ mixingWeight r ∧ mixingWeight r ≤ 1 := by
  unfold mixingWeight
  constructor
  · positivity
  · exact (div_le_one (by positivity : 0 < 1+r^2)).mpr (by nlinarith [sq_nonneg r])

def law (r : ℝ) : Measure State :=
  ENNReal.ofReal (mixingWeight r) • Measure.dirac (sample r)+
    ENNReal.ofReal (1-mixingWeight r) • Measure.dirac baseline

instance law_probability (r : ℝ) : IsProbabilityMeasure (law r) where
  measure_univ := by
    simp only [law,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_add (mixingWeight_bounds r).1 (by linarith [(mixingWeight_bounds r).2])]
    norm_num

theorem law_integrable (r : ℝ) (F : State → ℝ) : Integrable F (law r) := by
  have h0 : Integrable F (Measure.dirac (sample r)) := integrable_dirac (by finiteness)
  have h1 : Integrable F (Measure.dirac baseline) := integrable_dirac (by finiteness)
  exact (h0.smul_measure (by finiteness)).add_measure (h1.smul_measure (by finiteness))

theorem law_integral (r : ℝ) (F : State → ℝ) :
    (∫ x, F x ∂law r) = mixingWeight r*F (sample r)+(1-mixingWeight r)*F baseline := by
  have h0 : Integrable F (Measure.dirac (sample r)) := integrable_dirac (by finiteness)
  have h1 : Integrable F (Measure.dirac baseline) := integrable_dirac (by finiteness)
  rw [law,integral_add_measure (h0.smul_measure (by finiteness)) (h1.smul_measure (by finiteness))]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (mixingWeight_bounds r).1,
    ENNReal.toReal_ofReal (show 0 ≤ 1-mixingWeight r by linarith [(mixingWeight_bounds r).2]),smul_eq_mul]

theorem baseline_energy (m g : ℝ) : energy m g baseline = 3/2 := by
  change hamiltonian (1/2) m g 1 0 0 clockPoint 0 = 3/2
  rw [hamiltonian,clock_at_point]
  norm_num [kineticMean_eq,amplitude,
    weightedMean,potential,fieldValue_rotate,shear_rotate,diagonalPairing,crossPairing,mean_const]

theorem baseline_rate (m g : ℝ) : rate m g baseline = 1/4 := by
  change longitudinalRate (1/2) m g 1 0 0 clockPoint 0 = 1/4
  rw [longitudinalRate,response_at_point,clock_at_point]
  norm_num [kineticMean_eq,
    amplitude,weightedMean,weightedTilt,potential,fieldValue_rotate,shear_rotate,
    diagonalPairing,crossPairing,mean_const]

theorem baseline_shear (m g : ℝ) : signedShear m g baseline = 0 := by
  simp [signedShear,baseline,weightedTilt,shear_rotate,diagonalPairing,crossPairing,mean_const]

theorem sample_shear (m g r : ℝ) (hr : r ≠ 0) : signedShear m g (sample r) = shearRate r := by
  change response (1/2) clockPoint*amplitude (1/2) 0 clockPoint (clockMomentum r)*
    weightedTilt m g 1 (clock (1/2) clockPoint) (phase r)/(clock (1/2) clockPoint)^2 = _
  rw [response_at_point,clock_at_point,amplitude_at_point r hr,phase_tilt]
  simp only [one_pow,div_one,shearRate]

theorem law_energy (m g r : ℝ) (hr : r ≠ 0) :
    (∫ x, energy m g x ∂law r) = 7/2-3*mixingWeight r := by
  rw [law_integral,baseline_energy]
  change mixingWeight r*hamiltonian (1/2) m g 1 0 (phase r) clockPoint (clockMomentum r)+
    (1-mixingWeight r)*(3/2) = _
  rw [witness_energy m g r hr]
  unfold mixingWeight
  have hn : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem law_energy_bounds (m g r : ℝ) (hr : r ≠ 0) :
    0 ≤ (∫ x, energy m g x ∂law r) ∧ (∫ x, energy m g x ∂law r) ≤ 7/2 := by
  rw [law_energy m g r hr]
  constructor <;> linarith [(mixingWeight_bounds r).1,(mixingWeight_bounds r).2]

theorem scaled_quartic_lower (r : ℝ) (hr : 1 ≤ r^2) : r^2/32 ≤ mixingWeight r*(r^4/16) := by
  unfold mixingWeight
  have hn : 0 < 1+r^2 := by positivity
  have hx : r^2/32 ≤ r^4/(16*(1+r^2)) :=
    (le_div_iff₀ (show 0 < 16*(1+r^2) by positivity)).mpr
      (by nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hr)])
  exact hx.trans_eq (by field_simp)

theorem law_shear_lower (m g r : ℝ) (hr : 480 ≤ r^2) :
    r^2/32 ≤ ∫ x, signedShear m g x ∂law r := by
  have hn : r ≠ 0 := by intro hz; norm_num [hz] at hr
  rw [law_integral,baseline_shear,mul_zero,add_zero,sample_shear m g r hn]
  exact (scaled_quartic_lower r (by linarith)).trans
    (mul_le_mul_of_nonneg_left (shearRate_lower r hr) (mixingWeight_bounds r).1)

theorem law_rate_lower (m g r : ℝ) (hr : 480 ≤ r^2) :
    r^2/32 ≤ ∫ x, rate m g x ∂law r := by
  rw [law_integral,baseline_rate]
  have h := mul_le_mul_of_nonneg_left (witness_rate_lower m g r hr) (mixingWeight_bounds r).1
  have hw : 0 ≤ (1-mixingWeight r)*(1/4:ℝ) :=
    mul_nonneg (sub_nonneg.mpr (mixingWeight_bounds r).2) (by norm_num)
  change _ ≤ mixingWeight r*longitudinalRate (1/2) m g 1 0 (phase r) clockPoint (clockMomentum r)+_
  linarith [scaled_quartic_lower r (by linarith)]

theorem exists_bounded_energy_large_shear (m g M : ℝ) :
    ∃ r : ℝ, r ≠ 0 ∧ 0 ≤ (∫ x, energy m g x ∂law r) ∧
      (∫ x, energy m g x ∂law r) ≤ 7/2 ∧ M < (∫ x, signedShear m g x ∂law r) := by
  let r : ℝ := 32*(|M|+481)
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg M]
  have hrs : r ≤ r^2 := by nlinarith [mul_nonneg (show 0 ≤ r by linarith) (sub_nonneg.mpr hr1)]
  have hr : 480 ≤ r^2 := by dsimp [r] at *; nlinarith [abs_nonneg M]
  have hn : r ≠ 0 := ne_of_gt (by linarith)
  have hM : M < r^2/32 := by dsimp [r] at hrs; linarith [le_abs_self M]
  exact ⟨r,hn,(law_energy_bounds m g r hn).1,(law_energy_bounds m g r hn).2,
    hM.trans_le (law_shear_lower m g r hr)⟩

theorem no_affine_energy_bound (m g : ℝ) :
    ¬ ∃ A B : ℝ, ∀ x : State, signedShear m g x ≤ A*energy m g x+B := by
  rintro ⟨A,B,h⟩
  obtain ⟨r,hn,hE0,hE,hS⟩ := exists_bounded_energy_large_shear m g (|A| * (7/2)+B)
  have hi := integral_mono_ae (law_integrable r (signedShear m g))
    (law_integrable r (fun x => A*energy m g x+B)) (Filter.Eventually.of_forall h)
  have he := integral_add ((law_integrable r (energy m g)).const_mul A) (integrable_const B)
  rw [he,integral_const_mul,integral_const,probReal_univ,one_smul] at hi
  have hb := (mul_le_mul_of_nonneg_right (le_abs_self A) hE0).trans
    (mul_le_mul_of_nonneg_left hE (abs_nonneg A))
  linarith

#print axioms mixingWeight_bounds
#print axioms law_probability
#print axioms law_integrable
#print axioms law_integral
#print axioms baseline_energy
#print axioms baseline_rate
#print axioms baseline_shear
#print axioms sample_shear
#print axioms law_energy
#print axioms law_energy_bounds
#print axioms scaled_quartic_lower
#print axioms law_shear_lower
#print axioms law_rate_lower
#print axioms exists_bounded_energy_large_shear
#print axioms no_affine_energy_bound
end
end UnifiedTheory.Audit.KFCausalClassicalShearEnergyObstruction
