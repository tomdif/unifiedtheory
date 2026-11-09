/- Differentiate the transverse cross kernel integrated over two
independent charge parameters. A common Gaussian envelope derives all
domination; no integral derivative is supplied as a premise. -/
import UnifiedTheory.Audit.KFCausalPolynomialKernelJointContinuity
import UnifiedTheory.Audit.KFCausalChargeResponseFubini
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialLocalKernel
noncomputable section
open MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)

abbrev Domain := (ℝ × ℝ) × Transverse
def measure : Measure Domain := angles.prod volume

variable (ε y α β : ℝ) (b c : ℝ → Fin 5 → ℂ) (C D : ℝ → ℂ)
  (P Q : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : ℕ)

def value (s : ℝ) (z : Domain) : ℂ :=
  star (factor ε y α β (b z.1.1) (C z.1.1) P l n z.2 s)*
    factor ε y α β (c z.1.2) (D z.1.2) Q l n z.2 s

def derivative (s : ℝ) (z : Domain) : ℂ :=
  star (factorDerivative ε y α β (b z.1.1) (C z.1.1) P l n z.2 s)*
      factor ε y α β (c z.1.2) (D z.1.2) Q l n z.2 s+
    star (factor ε y α β (b z.1.1) (C z.1.1) P l n z.2 s)*
      factorDerivative ε y α β (c z.1.2) (D z.1.2) Q l n z.2 s

def integralValue (s : ℝ) : ℂ := ∫ z, value ε y α β b c C D P Q l n s z ∂measure
def integralDerivative (s : ℝ) : ℂ := ∫ z, derivative ε y α β b c C D P Q l n s z ∂measure

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hb : Continuous b) (hc : Continuous c) (hC : Continuous C) (hD : Continuous D)

include hε hy in
theorem value_derivative (s : ℝ) (z : Domain) :
    HasDerivAt (fun t => value ε y α β b c C D P Q l n t z)
      (derivative ε y α β b c C D P Q l n s z) s :=
  (factor_derivative ε y α β (b z.1.1) (C z.1.1) P l n z.2 s hε hy).star.mul
    (factor_derivative ε y α β (c z.1.2) (D z.1.2) Q l n z.2 s hε hy)

include hε hy hb hc hC hD in
theorem value_continuous (s : ℝ) : Continuous (value ε y α β b c C D P Q l n s) := by
  have h1 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => b z.1.1)
    (fun z : Domain => C z.1.1) continuous_const continuous_snd
    (hb.comp continuous_fst.fst) (hC.comp continuous_fst.fst) P l n
  have h2 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => c z.1.2)
    (fun z : Domain => D z.1.2) continuous_const continuous_snd
    (hc.comp continuous_fst.snd) (hD.comp continuous_fst.snd) Q l n
  exact h1.star.mul h2

include hε hy hb hc hC hD in
theorem derivative_continuous (s : ℝ) : Continuous (derivative ε y α β b c C D P Q l n s) := by
  have h1 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => b z.1.1)
    (fun z : Domain => C z.1.1) continuous_const continuous_snd
    (hb.comp continuous_fst.fst) (hC.comp continuous_fst.fst) P l n
  have h2 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => c z.1.2)
    (fun z : Domain => D z.1.2) continuous_const continuous_snd
    (hc.comp continuous_fst.snd) (hD.comp continuous_fst.snd) Q l n
  have h1d := KFCausalPolynomialKernelJointContinuity.factorDerivative_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => b z.1.1)
    (fun z : Domain => C z.1.1) continuous_const continuous_snd
    (hb.comp continuous_fst.fst) (hC.comp continuous_fst.fst) P l n
  have h2d := KFCausalPolynomialKernelJointContinuity.factorDerivative_continuous ε y α β hε hy
    (fun _ : Domain => s) (fun z : Domain => z.2) (fun z : Domain => c z.1.2)
    (fun z : Domain => D z.1.2) continuous_const continuous_snd
    (hc.comp continuous_fst.snd) (hD.comp continuous_fst.snd) Q l n
  exact (h1d.star.mul h2).add (h1.star.mul h2d)

variable (b₀ c₀ : Fin 5 → ℂ)
local notation "EnvP" => amplitudeEnvelope ε y α β b₀ P l n
local notation "EnvQ" => amplitudeEnvelope ε y α β c₀ Q l n
local notation "CorrP" => correctionEnvelope ε y α β b₀ P l n
local notation "CorrQ" => correctionEnvelope ε y α β c₀ Q l n

def valueBound (z : Domain) : ℝ := EnvP z.2*EnvQ z.2
def derivativeBound (z : Domain) : ℝ := CorrP z.2*EnvQ z.2+EnvP z.2*CorrQ z.2

theorem valueBound_nonnegative (z : Domain) : 0 ≤ valueBound ε y α β P Q l n b₀ c₀ z :=
  mul_nonneg (amplitudeEnvelope_nonnegative ε y α β b₀ P l n z.2)
    (amplitudeEnvelope_nonnegative ε y α β c₀ Q l n z.2)

theorem derivativeBound_nonnegative (z : Domain) : 0 ≤ derivativeBound ε y α β P Q l n b₀ c₀ z :=
  add_nonneg (mul_nonneg (correctionEnvelope_nonnegative ε y α β b₀ P l n z.2)
    (amplitudeEnvelope_nonnegative ε y α β c₀ Q l n z.2))
    (mul_nonneg (amplitudeEnvelope_nonnegative ε y α β b₀ P l n z.2)
      (correctionEnvelope_nonnegative ε y α β c₀ Q l n z.2))

theorem valueBound_integrable (hα : 0 < α) (hβ : 0 < β) :
    Integrable (valueBound ε y α β P Q l n b₀ c₀) measure :=
  ((amplitudeEnvelope_memLp ε y α β hα hβ b₀ P l n).integrable_mul
    (amplitudeEnvelope_memLp ε y α β hα hβ c₀ Q l n)).comp_snd angles

theorem derivativeBound_integrable (hα : 0 < α) (hβ : 0 < β) :
    Integrable (derivativeBound ε y α β P Q l n b₀ c₀) measure :=
  (((correctionEnvelope_memLp ε y α β hα hβ b₀ P l n).integrable_mul
    (amplitudeEnvelope_memLp ε y α β hα hβ c₀ Q l n)).add
      ((amplitudeEnvelope_memLp ε y α β hα hβ b₀ P l n).integrable_mul
        (correctionEnvelope_memLp ε y α β hα hβ c₀ Q l n))).comp_snd angles

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hb₀ : ∀ θ, sourceSize (b θ) ≤ sourceSize b₀) (hc₀ : ∀ θ, sourceSize (c θ) ≤ sourceSize c₀)
  (hCb : ∀ θ, ‖C θ‖ ≤ 1) (hDb : ∀ θ, ‖D θ‖ ≤ 1)

include hε hy hα hβ hw hb₀ hc₀ hCb hDb in
theorem value_bound (s : ℝ) (z : Domain) :
    ‖value ε y α β b c C D P Q l n s z‖ ≤ valueBound ε y α β P Q l n b₀ c₀ z := by
  rw [value,norm_mul,norm_star]
  exact mul_le_mul (factor_bound ε y α β hε hy hα hβ hw (b z.1.1) b₀ (hb₀ _) (C z.1.1) (hCb _) P l n z.2 s)
    (factor_bound ε y α β hε hy hα hβ hw (c z.1.2) c₀ (hc₀ _) (D z.1.2) (hDb _) Q l n z.2 s)
    (norm_nonneg _) (amplitudeEnvelope_nonnegative ε y α β b₀ P l n z.2)

include hε hy hα hβ hw hb₀ hc₀ hCb hDb in
theorem derivative_bound (s : ℝ) (z : Domain) :
    ‖derivative ε y α β b c C D P Q l n s z‖ ≤
      ‖clockSlope ε y s‖*derivativeBound ε y α β P Q l n b₀ c₀ z := by
  have h1 := factor_bound ε y α β hε hy hα hβ hw (b z.1.1) b₀ (hb₀ _) (C z.1.1) (hCb _) P l n z.2 s
  have h2 := factor_bound ε y α β hε hy hα hβ hw (c z.1.2) c₀ (hc₀ _) (D z.1.2) (hDb _) Q l n z.2 s
  have h1d := factorDerivative_bound ε y α β hε hy hα hβ hw (b z.1.1) b₀ (hb₀ _) (C z.1.1) (hCb _) P l n z.2 s
  have h2d := factorDerivative_bound ε y α β hε hy hα hβ hw (c z.1.2) c₀ (hc₀ _) (D z.1.2) (hDb _) Q l n z.2 s
  unfold derivative
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_star]
  have hi := add_le_add
    (mul_le_mul h1d h2 (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (correctionEnvelope_nonnegative ε y α β b₀ P l n z.2)))
    (mul_le_mul h1 h2d (norm_nonneg _) (amplitudeEnvelope_nonnegative ε y α β b₀ P l n z.2))
  convert hi using 1
  unfold derivativeBound
  ring

include hε hy hb hc hC hD hα hβ hw hb₀ hc₀ hCb hDb in
theorem value_integrable (s : ℝ) : Integrable (value ε y α β b c C D P Q l n s) measure :=
  (valueBound_integrable ε y α β P Q l n b₀ c₀ hα hβ).mono'
    (value_continuous ε y α β b c C D P Q l n hε hy hb hc hC hD s).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (value_bound ε y α β b c C D P Q l n hε hy b₀ c₀ hα hβ hw hb₀ hc₀ hCb hDb s))

include hε hy hb hc hC hD hα hβ hw hb₀ hc₀ hCb hDb in
theorem derivative_integrable (s : ℝ) : Integrable (derivative ε y α β b c C D P Q l n s) measure :=
  ((derivativeBound_integrable ε y α β P Q l n b₀ c₀ hα hβ).const_mul ‖clockSlope ε y s‖).mono'
    (derivative_continuous ε y α β b c C D P Q l n hε hy hb hc hC hD s).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (derivative_bound ε y α β b c C D P Q l n hε hy b₀ c₀ hα hβ hw hb₀ hc₀ hCb hDb s))

include hε hy hb hc hC hD hα hβ hw hb₀ hc₀ hCb hDb in
theorem integral_derivative (s : ℝ) :
    HasDerivAt (integralValue ε y α β b c C D P Q l n)
      (integralDerivative ε y α β b c C D P Q l n s) s := by
  have hi := KFCausalShiftedGaussianLongitudinalDifferential.inverseClock_continuous ε y hε hy
  have hd : Continuous (clockSlope ε y) := by
    unfold clockSlope KFCausalClockResponseTransport.clock
    fun_prop
  obtain ⟨M,hM⟩ := (isCompact_closedBall s (1:ℝ)).exists_bound_of_continuousOn hd.continuousOn
  have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := measure)
    (F := value ε y α β b c C D P Q l n) (F' := derivative ε y α β b c C D P Q l n)
    (x₀ := s) (s := Metric.ball s 1) (bound := fun z => M*derivativeBound ε y α β P Q l n b₀ c₀ z)
    (Metric.ball_mem_nhds s (by norm_num))
    (Filter.Eventually.of_forall (fun t =>
      (value_continuous ε y α β b c C D P Q l n hε hy hb hc hC hD t).aestronglyMeasurable))
    (value_integrable ε y α β b c C D P Q l n hε hy hb hc hC hD b₀ c₀ hα hβ hw hb₀ hc₀ hCb hDb s)
    (derivative_continuous ε y α β b c C D P Q l n hε hy hb hc hC hD s).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z t ht =>
      (derivative_bound ε y α β b c C D P Q l n hε hy b₀ c₀ hα hβ hw hb₀ hc₀ hCb hDb t z).trans
        (mul_le_mul_of_nonneg_right (hM t (Metric.ball_subset_closedBall ht))
          (derivativeBound_nonnegative ε y α β P Q l n b₀ c₀ z))))
    ((derivativeBound_integrable ε y α β P Q l n b₀ c₀ hα hβ).const_mul M)
    (Filter.Eventually.of_forall (fun z t _ => value_derivative ε y α β b c C D P Q l n hε hy t z))
  exact he.2

#print axioms value_derivative
#print axioms value_continuous
#print axioms derivative_continuous
#print axioms valueBound_nonnegative
#print axioms derivativeBound_nonnegative
#print axioms valueBound_integrable
#print axioms derivativeBound_integrable
#print axioms value_bound
#print axioms derivative_bound
#print axioms value_integrable
#print axioms derivative_integrable
#print axioms integral_derivative
end
end UnifiedTheory.Audit.KFCausalPolynomialLocalKernel
