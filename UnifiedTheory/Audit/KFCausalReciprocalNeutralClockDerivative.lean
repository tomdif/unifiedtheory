/- Differentiation through the complete transverse energy integral for
finite reciprocal neutral families, with arbitrary C1 clock coefficients.
The actual clock amplitudes are instantiated without extra regularity premises. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralClockEnvelope
import UnifiedTheory.Audit.KFCausalTransverseClockDifferentiation
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralClockDerivative
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPolynomialOrbitEnvelope (clockSlope)
open KFCausalReciprocalNeutralClockEnvelope (curve slope)
open KFCausalTransverseClockDifferentiation
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)

theorem clockSlope_continuous (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (clockSlope ε y) := by
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy
  unfold clockSlope KFCausalClockResponseTransport.clock
  fun_prop

theorem curve_regular (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (n : ℕ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hw : 1 ≤ w) :
    Regular (curve ε y α β w b P n) (slope ε y α β w b P n) := by
  have hw₀ : 0 < w := by linarith
  refine ⟨KFCausalReciprocalNeutralClockEnvelope.curve_continuous ε y α β w b P n hε hy hw₀,
    KFCausalReciprocalNeutralClockEnvelope.slope_continuous ε y α β w b P n hε hy hw₀,
    fun s q => KFCausalReciprocalNeutralClockEnvelope.curve_derivative ε y α β w b P n s q hε hy hw₀, ?_⟩
  intro s₀
  obtain ⟨D,hD,hD₂,hD₀,hb⟩ := KFCausalReciprocalNeutralClockEnvelope.common_envelope
    ε y α β w b P n hε hy hα hβ hwidth hw
  obtain ⟨M,hM,hm⟩ := continuous_local_bound (clockSlope ε y) (clockSlope_continuous ε y hε hy) s₀
  refine ⟨fun q => (1+M)*D q, continuous_const.mul hD, hD₂.const_mul _,
    fun q => mul_nonneg (by linarith) (hD₀ q), ?_⟩
  intro s hs q
  constructor
  · exact (hb s q).1.trans (by nlinarith [hD₀ q])
  · exact (hb s q).2.trans ((mul_le_mul_of_nonneg_right (hm s hs) (hD₀ q)).trans
      (by nlinarith [hD₀ q]))

def finiteCurve (N : ℕ) (ε y α β : ℝ) (w : Fin N → ℝ) (b : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (c : ℝ → Fin N → ℂ) (k : ℕ) (s : ℝ) (q : Transverse) : ℂ :=
  ∑ i, c s i*curve ε y α β (w i) (b i) (P i) k s q

def finiteSlope (N : ℕ) (ε y α β : ℝ) (w : Fin N → ℝ) (b : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (c : ℝ → Fin N → ℂ) (k : ℕ) (s : ℝ) (q : Transverse) : ℂ :=
  ∑ i, (deriv (fun t => c t i) s*curve ε y α β (w i) (b i) (P i) k s q+
    c s i*slope ε y α β (w i) (b i) (P i) k s q)

variable (N : ℕ) (ε y α β : ℝ) (w : Fin N → ℝ) (b : Fin N → ℂ)
  (P : Fin N → Polynomial ℂ) (c : ℝ → Fin N → ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : ∀ i, 1 ≤ w i) (hc : ∀ i, ContDiff ℝ 1 (fun s => c s i))
local notation "F" => finiteCurve N ε y α β w b P c
local notation "G" => finiteSlope N ε y α β w b P c

include hε hy hα hβ hwidth hw hc in
theorem finite_regular (k : ℕ) : Regular (F k) (G k) :=
  regular_sum N _ _ (fun i => regular_mul _ _
    (curve_regular ε y α β (w i) (b i) (P i) k hε hy hα hβ hwidth (hw i))
    (fun s => c s i) (deriv (fun s => c s i)) (hc i).continuous (hc i).continuous_deriv_one
    (fun s => ((hc i).differentiable (by norm_num)).differentiableAt.hasDerivAt))

include hε hy hα hβ hwidth hw hc in
theorem finite_energy_derivative (k : ℕ) (s : ℝ) :
    Integrable (fun q => 2*(star (F k s q)*G k s q).re) ∧
      HasDerivAt (energy (F k)) (response (F k) (G k) s) s :=
  energy_derivative _ _ (finite_regular N ε y α β w b P c hε hy hα hβ hwidth hw hc k) s

def totalEnergy (s : ℝ) : ℝ := energy (F 0) s+energy (F 1) s/2+energy (F 2) s/4
def totalResponse (s : ℝ) : ℝ := response (F 0) (G 0) s+
  response (F 1) (G 1) s/2+response (F 2) (G 2) s/4

include hε hy hα hβ hwidth hw hc in
theorem total_derivative (s : ℝ) :
    HasDerivAt (totalEnergy N ε y α β w b P c) (totalResponse N ε y α β w b P c s) s :=
  (((finite_energy_derivative N ε y α β w b P c hε hy hα hβ hwidth hw hc 0 s).2.add
    ((finite_energy_derivative N ε y α β w b P c hε hy hα hβ hwidth hw hc 1 s).2.div_const 2)).add
    ((finite_energy_derivative N ε y α β w b P c hε hy hα hβ hwidth hw hc 2 s).2.div_const 4))

include hε hy hα hβ hwidth hw hc in
theorem total_contDiff : ContDiff ℝ 1 (totalEnergy N ε y α β w b P c) := by
  have he (k : ℕ) := energy_contDiff _ _
    (finite_regular N ε y α β w b P c hε hy hα hβ hwidth hw hc k)
  exact ((he 0).add ((he 1).div_const 2)).add ((he 2).div_const 4)

theorem actual_coefficients_smooth (n : ℕ) (ε h : ℝ) (a p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (i : Fin n) :
    ContDiff ℝ 1 (fun s => KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C s i) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact contDiff_const.mul (clockAmplitude_smooth ε (a i) (p i) (-h/2) hε hy)

theorem actual_total_derivative (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ)
    (C b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (hh : h ≠ 0)
    (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (totalEnergy n ε (-h/2) (KFCausalChargeGaussianGeometry.groundWidth h)
      (KFCausalClockFloorInvariantTrial.neutralWidth h) w b P
      (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C))
      (totalResponse n ε (-h/2) (KFCausalChargeGaussianGeometry.groundWidth h)
        (KFCausalClockFloorInvariantTrial.neutralWidth h) w b P
        (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C) s) s := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  exact total_derivative n ε (-h/2) _ _ w b P _ hε hy
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hw
    (actual_coefficients_smooth n ε h a p C hε hb) s

#print axioms clockSlope_continuous
#print axioms curve_regular
#print axioms finite_regular
#print axioms finite_energy_derivative
#print axioms total_derivative
#print axioms total_contDiff
#print axioms actual_coefficients_smooth
#print axioms actual_total_derivative
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralClockDerivative
