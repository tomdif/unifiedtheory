/- Identify the differentiated complete transverse integral with the
existing neutral/reciprocal Gram kernel and actual positive clock slice. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralPositiveForm (pairing)
open KFCausalReciprocalNeutralKernel (density kernel)
open KFCausalReciprocalNeutralSliceIntegrability (factor density_decomposition)
open KFCausalReciprocalNeutralClockEnvelope (curve)
open KFCausalReciprocalNeutralClockDerivative
open KFCausalTransverseClockDifferentiation (energy)

theorem norm_sum_expansion (n : ℕ) (c f : Fin n → ℂ) :
    ((‖∑ i, c i*f i‖^2:ℝ):ℂ) = ∑ i, ∑ j, (conj (c i)*c j)*(conj (f i)*f j) := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (n : ℕ) (ε y α β : ℝ) (w : Fin n → ℝ) (b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (c : ℝ → Fin n → ℂ)
local notation "F" => finiteCurve n ε y α β w b P c
local notation "profiles" => fun i => exponentialProfile (b i) 1 (P i)

theorem density_expansion (s : ℝ) (q : Transverse) :
    ((‖F 0 s q‖^2+‖F 1 s q‖^2/2+‖F 2 s q‖^2/4:ℝ):ℂ) =
      ∑ i, ∑ j, (conj (c s i)*c s j)*
        density α β (w i) (w j) (scale ε y s) (profiles i) (profiles j) q := by
  simp only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_ofNat,
    finiteCurve,norm_sum_expansion,density_decomposition,curve,
    mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div]

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i)

include hε hy hα hβ hwidth hw in
theorem finite_memLp (k : ℕ) (s : ℝ) : MemLp (F k s) 2 volume :=
  memLp_finset_sum _ (fun i _ =>
    (KFCausalReciprocalNeutralSliceIntegrability.factor_memLp α β ε y s (w i)
      hα hβ hwidth hε hy (hw i) (b i) (P i) k).const_mul (c s i))

include hε hy hα hβ hwidth hw in
theorem pairing_totalEnergy (s : ℝ) :
    pairing n α β w (scale ε y s) (c s) (c s) profiles =
      (totalEnergy n ε y α β w b P c s:ℂ) := by
  have hi (i j : Fin n) : Integrable (fun q => (conj (c s i)*c s j)*
      density α β (w i) (w j) (scale ε y s) (profiles i) (profiles j) q) :=
    (KFCausalReciprocalNeutralSliceIntegrability.density_integrable α β ε y s (w i) (w j)
      hα hβ hwidth hε hy (hw i) (hw j) (b i) (b j) (P i) (P j)).const_mul _
  have hn (k : ℕ) : Integrable (fun q => ‖F k s q‖^2) := by
    have hm := finite_memLp n ε y α β w b P c hε hy hα hβ hwidth hw k s
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have he : (∫ q, ((‖F 0 s q‖^2+‖F 1 s q‖^2/2+‖F 2 s q‖^2/4:ℝ):ℂ)) =
      pairing n α β w (scale ε y s) (c s) (c s) profiles := by
    simp_rw [density_expansion]
    rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
    simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),integral_const_mul]
    rfl
  have hsum := integral_add ((hn 0).add ((hn 1).div_const 2)) ((hn 2).div_const 4)
  simp only [Pi.add_apply] at hsum
  rw [← he,integral_complex_ofReal,hsum,
    integral_add (hn 0) ((hn 1).div_const 2),integral_div,integral_div]
  rfl

include hε hy hα hβ hwidth hw in
theorem pairing_derivative (hc : ∀ i, ContDiff ℝ 1 (fun s => c s i)) (s : ℝ) :
    HasDerivAt (fun t => (pairing n α β w (scale ε y t) (c t) (c t) profiles).re)
      (totalResponse n ε y α β w b P c s) s := by
  have he : (fun t => (pairing n α β w (scale ε y t) (c t) (c t) profiles).re) =
      totalEnergy n ε y α β w b P c := by
    funext t
    rw [pairing_totalEnergy n ε y α β w b P c hε hy hα hβ hwidth hw,Complex.ofReal_re]
  rw [he]
  exact total_derivative n ε y α β w b P c hε hy hα hβ hwidth hw hc s

include hε hy hα hβ hwidth hw in
theorem fixed_pairing_derivative (C : Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fun t => (pairing n α β w (scale ε y t) C C profiles).re)
      (totalResponse n ε y α β w b P (fun _ => C) s) s :=
  pairing_derivative n ε y α β w b P (fun _ => C) hε hy hα hβ hwidth hw
    (fun _ => contDiff_const) s

include hε hy hα hβ hwidth hw in
theorem pairing_contDiff (hc : ∀ i, ContDiff ℝ 1 (fun s => c s i)) :
    ContDiff ℝ 1 (fun t => (pairing n α β w (scale ε y t) (c t) (c t) profiles).re) := by
  have he : (fun t => (pairing n α β w (scale ε y t) (c t) (c t) profiles).re) =
      totalEnergy n ε y α β w b P c := by
    funext t
    rw [pairing_totalEnergy n ε y α β w b P c hε hy hα hβ hwidth hw,Complex.ofReal_re]
  rw [he]
  exact total_contDiff n ε y α β w b P c hε hy hα hβ hwidth hw hc

theorem actual_clockPairing_derivative (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ)
    (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (fun t => (KFCausalReciprocalNeutralPositiveEnergy.clockPairing N ε h a w p C b P t).re)
      (totalResponse N ε (-h/2) (KFCausalChargeGaussianGeometry.groundWidth h)
        (KFCausalClockFloorInvariantTrial.neutralWidth h) w b P
        (KFCausalReciprocalNeutralPositiveEnergy.coefficients N ε h a p C) s) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact pairing_derivative N ε (-h/2) _ _ w b P _ hε hy
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hw
    (actual_coefficients_smooth N ε h a p C hε hb) s

theorem actual_positiveSlice_derivative (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ)
    (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (KFCausalReciprocalNeutralPositiveEnergy.positiveSlice N ε h a w p C b P)
      (totalResponse N ε (-h/2) (KFCausalChargeGaussianGeometry.groundWidth h)
        (KFCausalClockFloorInvariantTrial.neutralWidth h) w b P
        (KFCausalReciprocalNeutralPositiveEnergy.coefficients N ε h a p C) s) s := by
  have he : KFCausalReciprocalNeutralPositiveEnergy.positiveSlice N ε h a w p C b P =
      fun t => (KFCausalReciprocalNeutralPositiveEnergy.clockPairing N ε h a w p C b P t).re := by
    funext t
    rw [KFCausalReciprocalNeutralPositiveEnergy.clockPairing_positive N ε h a w p C b P hε hh hw hb,
      Complex.ofReal_re]
  rw [he]
  exact actual_clockPairing_derivative N ε h a w p C b P hε hh hw hb s

theorem actual_positiveSlice_contDiff (N : ℕ) (ε h : ℝ) (a w p : Fin N → ℝ)
    (C b : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ContDiff ℝ 1 (KFCausalReciprocalNeutralPositiveEnergy.positiveSlice N ε h a w p C b P) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have he : KFCausalReciprocalNeutralPositiveEnergy.positiveSlice N ε h a w p C b P =
      fun t => (KFCausalReciprocalNeutralPositiveEnergy.clockPairing N ε h a w p C b P t).re := by
    funext t
    rw [KFCausalReciprocalNeutralPositiveEnergy.clockPairing_positive N ε h a w p C b P hε hh hw hb,
      Complex.ofReal_re]
  rw [he]
  exact pairing_contDiff N ε (-h/2) _ _ w b P _ hε hy
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hw
    (actual_coefficients_smooth N ε h a p C hε hb)

#print axioms norm_sum_expansion
#print axioms density_expansion
#print axioms finite_memLp
#print axioms pairing_totalEnergy
#print axioms pairing_derivative
#print axioms fixed_pairing_derivative
#print axioms pairing_contDiff
#print axioms actual_clockPairing_derivative
#print axioms actual_positiveSlice_derivative
#print axioms actual_positiveSlice_contDiff
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralKernelDerivative
