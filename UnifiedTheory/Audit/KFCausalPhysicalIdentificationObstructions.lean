/- Exact obstructions to identifying the physical charged character with Watson
by simple regrading, and to obtaining a broken-symmetry Higgs identification
from the present positive square-root energy weights alone. -/
import UnifiedTheory.Audit.KFCausalPhysicalChargedCharacter
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
import UnifiedTheory.LayerA.IdentificationChain

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalIdentificationObstructions
noncomputable section
open PowerSeries UnifiedTheory.QSeries.Watson
open KFCausalPhysicalChargedCharacter

private theorem inverse_FP_low (a b n j : ℕ) (ha : 0 < a) (hj : j < a) :
    coeff j (Ring.inverse (FP 1 a b n)) = coeff j (1 : PowerSeries ℤ) := by
  have he := coeff_mul_of_dvd_sub_one
    (f := Ring.inverse (FP 1 a b n)) (FP_sub_one_dvd 1 a b n) hj
  rw [Ring.inverse_mul_cancel _ (isUnit_FP 1 ha b n)] at he
  exact he.symm

theorem chi_second : coeff 2 chiA = 1 := by
  rw [chiA,coeff_osum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 3) (by
    intro n hn
    apply Finset.mem_range.mpr
    by_contra hh
    have he : coeff 2 (X^n*Ring.inverse (FP 1 (n+1) 1 n)) = 0 := by
      rw [coeff_X_pow_mul',if_neg (by omega)]
    exact hn he)]
  norm_num [Finset.sum_range_succ,coeff_X_pow_mul',FP_zero,Ring.inverse_one,
    inverse_FP_low]

def characterReal : PowerSeries ℝ := map (Int.castRingHom ℝ) character
def chiReal : PowerSeries ℝ := map (Int.castRingHom ℝ) chiA

theorem character_ne_rescaled_chi (a : ℝ) : characterReal ≠ rescale a chiReal := by
  intro he
  have h1 := congrArg (coeff 1) he
  have h2 := congrArg (coeff 2) he
  norm_num [characterReal,chiReal,coeff_map,coefficient,chi_first] at h1
  norm_num [characterReal,chiReal,coeff_map,coefficient,chi_second,h1.symm] at h2

theorem character_ne_dilated_rescaled_chi (a : ℝ) (d : ℕ) (hd : d ≠ 0) (hd1 : d ≠ 1) :
    characterReal ≠ rescale a (expand d hd chiReal) := by
  intro he
  have h1 := congrArg (coeff 1) he
  have hn : ¬ d ∣ 1 := by simpa only [Nat.dvd_one] using hd1
  rw [coeff_rescale,coeff_expand_of_not_dvd d hd chiReal hn] at h1
  norm_num [characterReal,coeff_map,coefficient] at h1

open KFCausalPhysicalEnergyFactors (energyWeight)

/-- Lean's real square root clips a nonpositive quadratic coupling to zero. -/
theorem negative_mass_weight_vanishes (m g k t : ℝ) (hm : m ≤ 0) :
    energyWeight m g k t 5 = 0 := by
  simp [energyWeight,Real.sqrt_eq_zero_of_nonpos (show m/2 ≤ 0 by linarith)]

theorem nonpositive_mass_same_weights (m g k t : ℝ) (hm : m ≤ 0) :
    energyWeight m g k t = energyWeight 0 g k t := by
  funext i
  fin_cases i <;>
    simp [energyWeight,Real.sqrt_eq_zero_of_nonpos (show m/2 ≤ 0 by linarith)]

/-- With nonnegative quadratic coefficient and positive quartic coefficient,
the polynomial stationary equation has only the zero solution. -/
theorem positive_quartic_stationary_iff (m g v : ℝ) (hm : 0 ≤ m) (hg : 0 < g) :
    m*v+g*v^3 = 0 ↔ v = 0 := by
  constructor
  · intro he
    by_contra hv
    have hv2 : 0 < v^2 := sq_pos_of_ne_zero hv
    have hpos : 0 < m+g*v^2 := by positivity
    have hf : v*(m+g*v^2) = 0 := by nlinarith [he]
    exact (mul_ne_zero hv hpos.ne') hf
  · intro hv
    simp [hv]

/-- At a nonzero stationary point the mass parameter must be negative;
the curvature is then twice the quartic coefficient times the squared VEV. -/
theorem broken_stationary_curvature (m g v : ℝ) (hg : 0 < g) (hv : v ≠ 0)
    (hs : m*v+g*v^3 = 0) : m < 0 ∧ m+3*g*v^2 = 2*g*v^2 := by
  have hf : v*(m+g*v^2) = 0 := by nlinarith [hs]
  have hm := (mul_eq_zero.mp hf).resolve_left hv
  have hp : 0 < g*v^2 := mul_pos hg (sq_pos_of_ne_zero hv)
  constructor <;> nlinarith

/-- A constructive scalar repair: put the negative quadratic coefficient inside
a shifted square, instead of taking its real square root as a separate row. -/
theorem signed_quartic_square_completion (m g k x : ℝ) (hg : g ≠ 0) :
    k+m*x^2/2+g*x^4/4 =
      (g/4)*(x^2+m/g)^2+(k-m^2/(4*g)) := by
  field_simp [hg]
  ring

theorem broken_square_identity (g v x : ℝ) :
    g*v^4/4+(-g*v^2)*x^2/2+g*x^4/4 = (g/4)*(x^2-v^2)^2 := by ring

theorem broken_square_nonnegative (g v x : ℝ) (hg : 0 ≤ g) :
    0 ≤ g*v^4/4+(-g*v^2)*x^2/2+g*x^4/4 := by
  rw [broken_square_identity]
  positivity

theorem broken_square_minima (g v x : ℝ) (hg : 0 < g) :
    g*v^4/4+(-g*v^2)*x^2/2+g*x^4/4 = 0 ↔ x = v ∨ x = -v := by
  rw [broken_square_identity]
  have hn : g/4 ≠ 0 := (div_pos hg (by norm_num)).ne'
  rw [mul_eq_zero]
  simp only [hn,false_or,pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0),sub_eq_zero]
  exact sq_eq_sq_iff_eq_or_eq_neg

/-- The usual mass relation admits every positive mass-to-VEV ratio. -/
theorem arbitrary_positive_ratio (r v : ℝ) (hr : 0 < r) (hv : 0 < v) :
    0 < r^2/2 ∧ 0 < r*v ∧ (r*v)^2 = 2*(r^2/2)*v^2 ∧ (r*v)/v = r := by
  refine ⟨by positivity,mul_pos hr hv,by ring,?_⟩
  exact mul_div_cancel_right₀ r hv.ne'

/-- A concrete countermodel to deducing the proposed coupling from that relation. -/
theorem standard_mass_relation_not_identification :
    ∃ lam mH v : ℝ, 0 < lam ∧ 0 < mH ∧ 0 < v ∧ mH^2 = 2*lam*v^2 ∧
      lam ≠ UnifiedTheory.LayerA.IdentificationChain.lambda_predicted := by
  refine ⟨1/2,1,1,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  exact ne_of_gt UnifiedTheory.LayerA.IdentificationChain.lambda_lt_half

theorem watson_compatible_countermodel : chiA = 2*F0w-P0w ∧
    ∃ lam mH v : ℝ, 0 < lam ∧ 0 < mH ∧ 0 < v ∧ mH^2 = 2*lam*v^2 ∧
      lam ≠ UnifiedTheory.LayerA.IdentificationChain.lambda_predicted :=
  ⟨UnifiedTheory.LayerA.WatsonSeriesBridge.chi0_R1,standard_mass_relation_not_identification⟩

#print axioms chi_second
#print axioms character_ne_rescaled_chi
#print axioms character_ne_dilated_rescaled_chi
#print axioms negative_mass_weight_vanishes
#print axioms nonpositive_mass_same_weights
#print axioms positive_quartic_stationary_iff
#print axioms broken_stationary_curvature
#print axioms signed_quartic_square_completion
#print axioms broken_square_identity
#print axioms broken_square_nonnegative
#print axioms broken_square_minima
#print axioms arbitrary_positive_ratio
#print axioms standard_mass_relation_not_identification
#print axioms watson_compatible_countermodel
end
end UnifiedTheory.Audit.KFCausalPhysicalIdentificationObstructions
