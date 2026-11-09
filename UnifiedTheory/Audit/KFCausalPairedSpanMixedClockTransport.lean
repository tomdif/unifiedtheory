/- Independent Gaussian clock widths and frequencies in the centered/paired
kernel. The clock coefficients are differentiated, and their derivatives
cancel exactly against the physical weak slopes. No cross term is removed. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMovingCoefficients
import UnifiedTheory.Audit.KFCausalMovingKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockTransport
noncomputable section
open MeasureTheory
open KFCausalPairedSpanMoments (Coefficients value)
open KFCausalPairedSpanGrowth (rate)
open KFCausalPairedSpanCoefficientDifferential
open KFCausalPairedSpanMovingCoefficients
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedGaussianLongitudinalDifferential
  (amplitudeSlope clockAmplitude_derivative inverseClock)
open KFCausalClockResponseTransport (clock coefficient weakSlope slope_decomposition)
open KFCausalClockFloorTransportDerivative (amplitudeLogSlope)

def clockCoefficients (ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : Coefficients :=
  (c.1*clockAmplitude ε a p y s,c.2*clockAmplitude ε b q y s)
def clockDerivative (ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : Coefficients :=
  (c.1*(amplitudeSlope ε a p y s*clockAmplitude ε a p y s),
    c.2*(amplitudeSlope ε b q y s*clockAmplitude ε b q y s))
def weakCoefficients (ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : Coefficients :=
  (c.1*(weakSlope ε a p y s*clockAmplitude ε a p y s),
    c.2*(weakSlope ε b q y s*clockAmplitude ε b q y s))
def correction (ε y s : ℝ) : ℂ :=
  (inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2)/2+
    (amplitudeLogSlope ε s:ℂ)/(clock ε s:ℂ)
def energy (α β ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : ℝ :=
  value α β (scale ε y s) (clockCoefficients ε a b p q y c s)
def geometry (α β ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : ℝ :=
  rate α β ε y s (clockCoefficients ε a b p q y c s)
def response (α β ε a b p q y : ℝ) (c : Coefficients) (s : ℝ) : ℝ :=
  coefficientRate α β (scale ε y s) (clockCoefficients ε a b p q y c s)
    (weakCoefficients ε a b p q y c s)

theorem clockCoefficients_derivative (ε a b p q y : ℝ) (c : Coefficients) (s : ℝ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (clockCoefficients ε a b p q y c)
      (clockDerivative ε a b p q y c s) s :=
  ((clockAmplitude_derivative ε a p y s hε hy).const_mul c.1).prodMk
    ((clockAmplitude_derivative ε b q y s hε hy).const_mul c.2)

theorem clockCoefficients_continuous (ε a b p q y : ℝ) (c : Coefficients)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (clockCoefficients ε a b p q y c) :=
  (continuous_const.mul (clockAmplitude_smooth ε a p y hε hy).continuous).prodMk
    (continuous_const.mul (clockAmplitude_smooth ε b q y hε hy).continuous)

theorem weakCoefficients_decomposition (ε a b p q y : ℝ) (c : Coefficients) (s : ℝ)
    (hε : 0 < ε) :
    weakCoefficients ε a b p q y c s =
      (1/clock ε s:ℝ) • clockDerivative ε a b p q y c s+
        (-correction ε y s) • clockCoefficients ε a b p q y c s := by
  ext <;> simp only [weakCoefficients,clockDerivative,clockCoefficients,correction,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_one,slope_decomposition ε a p y s hε,
    slope_decomposition ε b q y s hε] <;> ring

theorem correction_identity (ε y s : ℝ) (hε : 0 < ε) :
    -2*(correction ε y s).re =
      coefficient ε y s-Real.exp s/(clock ε s)^2 := by
  have hc : clock ε s ≠ 0 := by unfold clock; positivity
  simp only [correction,Complex.add_re,Complex.div_ofNat_re,Complex.div_ofReal_re,
    Complex.ofReal_re,coefficient]
  unfold amplitudeLogSlope clock at *
  field_simp
  ring

theorem response_split (α β ε a b p q y : ℝ) (c : Coefficients) (s : ℝ)
    (hε : 0 < ε) :
    response α β ε a b p q y c s =
      coefficientRate α β (scale ε y s) (clockCoefficients ε a b p q y c s)
        (clockDerivative ε a b p q y c s)/clock ε s+
      (coefficient ε y s-Real.exp s/(clock ε s)^2)*energy α β ε a b p q y c s := by
  unfold response
  rw [weakCoefficients_decomposition ε a b p q y c s hε,coefficientRate_add,
    coefficientRate_real_smul,coefficientRate_radial,Complex.neg_re]
  have he := correction_identity ε y s hε
  unfold energy
  rw [← he]
  ring

variable (α β ε a b p q y : ℝ) (c : Coefficients)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)

include hα hβ hw hε hy in
theorem energy_derivative (s : ℝ) :
    HasDerivAt (energy α β ε a b p q y c)
      (geometry α β ε a b p q y c s+
        coefficientRate α β (scale ε y s) (clockCoefficients ε a b p q y c s)
          (clockDerivative ε a b p q y c s)) s :=
  moving_derivative α β ε y hα hβ hw hε hy _ _ s
    (clockCoefficients_derivative ε a b p q y c s hε hy)

include hα hβ hw hε hy in
theorem boundary_derivative (s : ℝ) :
    HasDerivAt (KFCausalMovingKernelClockResponse.boundary ε (energy α β ε a b p q y c))
      (response α β ε a b p q y c s-
        KFCausalMovingKernelClockResponse.reduced ε y (energy α β ε a b p q y c)
          (geometry α β ε a b p q y c) s) s := by
  have hc : clock ε s ≠ 0 := by unfold clock; positivity
  have hd := (energy_derivative α β ε a b p q y c hα hβ hw hε hy s).div
    ((Real.hasDerivAt_exp s).add_const ε) hc
  convert hd using 1
  rw [response_split α β ε a b p q y c s hε]
  unfold KFCausalMovingKernelClockResponse.reduced
  change _ = (_*clock ε s-_*Real.exp s)/(clock ε s)^2
  field_simp
  ring

include hα hβ hw hε hy in
theorem energy_nonnegative (s : ℝ) : 0 ≤ energy α β ε a b p q y c s :=
  value_nonnegative α β ε y hα hβ hw hε hy s _

include hα hβ hw hε hy in
theorem energy_continuous : Continuous (energy α β ε a b p q y c) :=
  moving_continuous α β ε y hα hβ hw hε hy _
    (clockCoefficients_continuous ε a b p q y c hε hy)

include hα hβ hw hε hy in
theorem geometry_continuous : Continuous (geometry α β ε a b p q y c) :=
  rate_continuous α β ε y hα hβ hw hε hy _
    (clockCoefficients_continuous ε a b p q y c hε hy)

theorem exists_uniform_integrable_response_bound (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a b p q y : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 →
      ∀ c : Coefficients,
        Integrable (energy α β ε a b p q y c) volume →
        Integrable (response α β ε a b p q y c) volume →
        (∫ s, response α β ε a b p q y c s) =
          ∫ s, KFCausalMovingKernelClockResponse.reduced ε y
            (energy α β ε a b p q y c) (geometry α β ε a b p q y c) s ∧
        -((C+2)/ε)*(∫ s, energy α β ε a b p q y c s) ≤
          ∫ s, response α β ε a b p q y c s := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_rate_bound α β hα hβ hw
  refine ⟨C,hC,?_⟩
  intro ε a b p q y hε hy c hE hW
  exact KFCausalMovingKernelClockResponse.full_clock_identity_and_bound ε y C
    (energy α β ε a b p q y c) (geometry α β ε a b p q y c) (response α β ε a b p q y c)
    hε hy hC (energy_continuous α β ε a b p q y c hα hβ hw hε hy)
    (geometry_continuous α β ε a b p q y c hα hβ hw hε hy)
    (energy_nonnegative α β ε a b p q y c hα hβ hw hε hy)
    (fun s => hbound ε y hε hy _ s)
    (boundary_derivative α β ε a b p q y c hα hβ hw hε hy) hE hW

#print axioms clockCoefficients_derivative
#print axioms clockCoefficients_continuous
#print axioms weakCoefficients_decomposition
#print axioms correction_identity
#print axioms response_split
#print axioms energy_derivative
#print axioms boundary_derivative
#print axioms energy_nonnegative
#print axioms energy_continuous
#print axioms geometry_continuous
#print axioms exists_uniform_integrable_response_bound
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockTransport
