/- The positive joint integral is the actual ordered potential energy
of a finite joint state, including independent clock widths/frequencies.
The clock integral is justified by the actual L2 cross-pairing domains. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralActualPositive
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPairing
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveEnergy
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity pairing)
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalReciprocalNeutralSuperposition (output)
open KFCausalNeutralFinitePairing (sum_inner_pairs)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (c b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "F" => fun i => exponentialProfile (b i) 1 (P i)

def coefficients (s : ℝ) (i : Fin n) : ℂ := c i*clockAmplitude ε (a i) (p i) (-h/2) s

def clockPairing (s : ℝ) : ℂ :=
  pairing n α β w (scale ε (-h/2) s) (coefficients n ε h a p c s) (coefficients n ε h a p c s) F

def positiveSlice (s : ℝ) : ℝ :=
  Real.pi/4*∫ z, positiveDensity n α β w (scale ε (-h/2) s) (coefficients n ε h a p c s) F z ∂jointMeasure

theorem clockPairing_sum (s : ℝ) :
    clockPairing n ε h a w p c b P s =
      ∑ i, ∑ j, KFCausalReciprocalNeutralPhysicalPair.clockKernel ε h (a i) (a j)
        (w i) (w j) (p i) (p j) (c i) (c j) (b i) (b j) (P i) (P j) s := by
  unfold clockPairing pairing
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he (d : ℂ) (Q : Polynomial ℂ) :
      exponentialProfile d 1 Q = KFCausalReciprocalNeutralPhysicalPair.neutralProfile d Q := by
    funext z
    simp [exponentialProfile,KFCausalReciprocalNeutralPhysicalPair.neutralProfile]
  simp only [KFCausalReciprocalNeutralPhysicalPair.clockKernel,
    KFCausalReciprocalNeutralPhysicalPair.coefficient,coefficients,
    he]

variable (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "u" => output n ε h a w p c b P hε ha hh hw hb

include hε hh hw hb in
theorem clockPairing_positive (s : ℝ) :
    clockPairing n ε h a w p c b P s = (positiveSlice n ε h a w p c b P s:ℂ) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact KFCausalReciprocalNeutralActualPositive.pairing_positive_integral n α β ε (-h/2) s w b
    (coefficients n ε h a p c s) P (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy hw

include hε ha hh hw hb in
theorem clockPairing_integrable : Integrable (clockPairing n ε h a w p c b P) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      KFCausalReciprocalNeutralPairing.clockKernel_integrable ε h (a i) (a j)
        (w i) (w j) (p i) (p j) (c i) (c j) (b i) (b j) (P i) (P j)
        hε (ha i) (ha j) hh (hw i) (hw j) hb))
  exact hi.congr (Filter.Eventually.of_forall (fun s => (clockPairing_sum n ε h a w p c b P s).symm))

include hε ha hh hw hb in
theorem positiveSlice_integrable : Integrable (positiveSlice n ε h a w p c b P) := by
  apply (clockPairing_integrable n ε h a w p c b P hε ha hh hw hb).re.congr
  filter_upwards [] with s
  rw [clockPairing_positive n ε h a w p c b P hε hh hw hb]
  rfl

theorem positiveSlice_nonnegative (s : ℝ) : 0 ≤ positiveSlice n ε h a w p c b P s :=
  mul_nonneg (by positivity)
    (integral_nonneg (KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg n α β w _ _ F))

def potentialEnergy : ℝ := ‖u 7‖^2+‖u 5‖^2/2+‖u 6‖^2/4

theorem potentialEnergy_clockPairing :
    (potentialEnergy n ε h a w p c b P hε ha hh hw hb:ℂ) =
      ∫ s, clockPairing n ε h a w p c b P s := by
  have hi (i j : Fin n) := KFCausalReciprocalNeutralPairing.clockKernel_integrable ε h (a i) (a j)
    (w i) (w j) (p i) (p j) (c i) (c j) (b i) (b j) (P i) (P j)
    hε (ha i) (ha j) hh (hw i) (hw j) hb
  simp_rw [clockPairing_sum]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),
    ← KFCausalReciprocalNeutralPairing.ordered_pair_clock_kernel ε h _ _ _ _ _ _ _ _ _ _ _ _
      hε (ha _) (ha _) hh (hw _) (hw _) hb]
  simp only [Finset.sum_add_distrib,← Finset.sum_div]
  rw [sum_inner_pairs,sum_inner_pairs,sum_inner_pairs]
  simp only [inner_self_eq_norm_sq_to_K]
  unfold potentialEnergy output
  push_cast
  rfl

theorem potentialEnergy_positive_integral :
    potentialEnergy n ε h a w p c b P hε ha hh hw hb =
      ∫ s, positiveSlice n ε h a w p c b P s := by
  have he := potentialEnergy_clockPairing n ε h a w p c b P hε ha hh hw hb
  simp_rw [clockPairing_positive n ε h a w p c b P hε hh hw hb] at he
  rw [integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

#print axioms clockPairing_sum
#print axioms clockPairing_positive
#print axioms clockPairing_integrable
#print axioms positiveSlice_integrable
#print axioms positiveSlice_nonnegative
#print axioms potentialEnergy_clockPairing
#print axioms potentialEnergy_positive_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveEnergy
