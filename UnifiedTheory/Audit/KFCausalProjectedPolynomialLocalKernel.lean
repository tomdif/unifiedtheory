/- The local transverse kernel of actual displaced polynomial charge
orbits is differentiable in clock position. Source caps, integrability
and domination are derived from the orbit and the physical widths. -/
import UnifiedTheory.Audit.KFCausalPolynomialLocalKernel
import UnifiedTheory.Audit.KFCausalPolynomialProjectedClockResponse
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (source amplitude clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialLocalKernel (Domain measure)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient pair)

def sourceCurve (h : ℝ) (q k : Joint 2 4) (θ : ℝ) : Fin 5 → ℂ :=
  source h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)

def amplitudeCurve (h : ℝ) (q k : Joint 2 4) (θ : ℝ) : ℂ :=
  amplitude h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)

theorem sourceCurve_continuous (h : ℝ) (q k : Joint 2 4) : Continuous (sourceCurve h q k) :=
  (KFCausalClockFloorDisplacedParameterBounds.source_curve_continuous h q k).comp
    (continuous_const.mul continuous_id)

theorem amplitudeCurve_continuous (h : ℝ) (q k : Joint 2 4) : Continuous (amplitudeCurve h q k) :=
  (KFCausalClockFloorDisplacedParameterBounds.amplitude_curve_continuous h q k).comp
    (continuous_const.mul continuous_id)

theorem sourceCurve_cap (h : ℝ) (q k : Joint 2 4) :
    ∃ b₀ : Fin 5 → ℂ, ∀ θ, sourceSize (sourceCurve h q k θ) ≤ sourceSize b₀ := by
  obtain ⟨B,hB⟩ := KFCausalClockFloorDisplacedParameterBounds.source_orbit_bound h q k
  obtain ⟨b₀,hb₀⟩ := KFCausalBoundedShearSourceContinuity.source_cap B
  exact ⟨b₀,fun θ => (hB (2*Real.pi*θ)).trans hb₀⟩

theorem amplitudeCurve_bound (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (θ : ℝ) :
    ‖amplitudeCurve h q k θ‖ ≤ 1 :=
  KFCausalClockFloorDisplacedSources.amplitude_norm_le_one h hh _ _

variable (ε h : ℝ) (q k : Joint 2 4) (P Q : Polynomial ℂ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "b" => sourceCurve h q k
local notation "C" => amplitudeCurve h q k

def value (s : ℝ) (z : Domain) : ℂ :=
  KFCausalPolynomialLocalKernel.value ε (-h/2) α β b b C C P Q pointField n s z
def derivative (s : ℝ) (z : Domain) : ℂ :=
  KFCausalPolynomialLocalKernel.derivative ε (-h/2) α β b b C C P Q pointField n s z
def localKernel (s : ℝ) : ℂ := ∫ z, value ε h q k P Q n s z ∂measure
def localDerivative (s : ℝ) : ℂ := ∫ z, derivative ε h q k P Q n s z ∂measure
def reducedValue (s : ℝ) (z : Domain) : ℂ :=
  (coefficient ε (-h/2) s:ℂ)*value ε h q k P Q n s z-
    derivative ε h q k P Q n s z/(clock ε s:ℂ)

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hb in
theorem value_integrable (s : ℝ) : Integrable (value ε h q k P Q n s) measure := by
  obtain ⟨b₀,hb₀⟩ := sourceCurve_cap h q k
  exact KFCausalPolynomialLocalKernel.value_integrable ε (-h/2) α β b b C C P Q pointField n
    hε (shift_bound ε h hb) (sourceCurve_continuous h q k) (sourceCurve_continuous h q k)
    (amplitudeCurve_continuous h q k) (amplitudeCurve_continuous h q k) b₀ b₀
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (by unfold neutralWidth; linarith)
    hb₀ hb₀ (amplitudeCurve_bound h hh q k) (amplitudeCurve_bound h hh q k) s

include hε hh hb in
theorem derivative_integrable (s : ℝ) : Integrable (derivative ε h q k P Q n s) measure := by
  obtain ⟨b₀,hb₀⟩ := sourceCurve_cap h q k
  exact KFCausalPolynomialLocalKernel.derivative_integrable ε (-h/2) α β b b C C P Q pointField n
    hε (shift_bound ε h hb) (sourceCurve_continuous h q k) (sourceCurve_continuous h q k)
    (amplitudeCurve_continuous h q k) (amplitudeCurve_continuous h q k) b₀ b₀
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (by unfold neutralWidth; linarith)
    hb₀ hb₀ (amplitudeCurve_bound h hh q k) (amplitudeCurve_bound h hh q k) s

include hε hh hb in
theorem localKernel_derivative (s : ℝ) :
    HasDerivAt (localKernel ε h q k P Q n) (localDerivative ε h q k P Q n s) s := by
  obtain ⟨b₀,hb₀⟩ := sourceCurve_cap h q k
  exact KFCausalPolynomialLocalKernel.integral_derivative ε (-h/2) α β b b C C P Q pointField n
    hε (shift_bound ε h hb) (sourceCurve_continuous h q k) (sourceCurve_continuous h q k)
    (amplitudeCurve_continuous h q k) (amplitudeCurve_continuous h q k) b₀ b₀
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (by unfold neutralWidth; linarith)
    hb₀ hb₀ (amplitudeCurve_bound h hh q k) (amplitudeCurve_bound h hh q k) s

theorem value_formula (s : ℝ) (z : Domain) :
    value ε h q k P Q n s z = (pointField z.2:ℂ)^(2*n.val)*
      KFCausalPolynomialKernelResponse.kernel ε (-h/2) α β α β
        (b z.1.1) (b z.1.2) (C z.1.1) (C z.1.2) P Q z.2 s := by
  simp only [value,KFCausalPolynomialLocalKernel.value,KFCausalPolynomialOrbitEnvelope.factor,
    KFCausalPolynomialKernelResponse.kernel,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  ring

theorem derivative_formula (s : ℝ) (z : Domain) :
    derivative ε h q k P Q n s z = (pointField z.2:ℂ)^(2*n.val)*
      KFCausalPolynomialKernelResponse.kernelDerivative ε (-h/2) α β α β
        (b z.1.1) (b z.1.2) (C z.1.1) (C z.1.2) P Q z.2 s := by
  simp only [derivative,KFCausalPolynomialLocalKernel.derivative,
    KFCausalPolynomialOrbitEnvelope.factor,KFCausalPolynomialOrbitEnvelope.factorDerivative,
    KFCausalPolynomialKernelResponse.kernelDerivative,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  ring

include hε hh hb in
theorem reducedValue_integrable (s : ℝ) : Integrable (reducedValue ε h q k P Q n s) measure :=
  ((value_integrable ε h q k P Q n hε hh hb s).const_mul _).sub
    ((derivative_integrable ε h q k P Q n hε hh hb s).div_const _)

include hε hh hb in
theorem reducedValue_integral (s : ℝ) :
    (∫ z, reducedValue ε h q k P Q n s z ∂measure) =
      (coefficient ε (-h/2) s:ℂ)*localKernel ε h q k P Q n s-
        localDerivative ε h q k P Q n s/(clock ε s:ℂ) := by
  unfold reducedValue
  rw [integral_sub ((value_integrable ε h q k P Q n hε hh hb s).const_mul _)
    ((derivative_integrable ε h q k P Q n hε hh hb s).div_const _),
    integral_const_mul,integral_div]
  rfl

theorem response_density_formula (a s : ℝ) (z : Domain) :
    KFCausalPolynomialProjectedClockResponse.reducedDensity ε a h q k P Q n z.1 (s,z.2) =
      pair ε a a (clockFrequency h k) (clockFrequency h k) (-h/2) s*
        reducedValue ε h q k P Q n s z := by
  unfold reducedValue
  rw [value_formula,derivative_formula]
  change (pointField z.2:ℂ)^(2*n.val)*
    (pair ε a a (clockFrequency h k) (clockFrequency h k) (-h/2) s*_) = _
  unfold sourceCurve amplitudeCurve
  ring

include hε hh hb in
theorem response_slice_integral (a s : ℝ) :
    (∫ z : Domain, KFCausalPolynomialProjectedClockResponse.reducedDensity
      ε a h q k P Q n z.1 (s,z.2) ∂measure) =
      pair ε a a (clockFrequency h k) (clockFrequency h k) (-h/2) s*
        ((coefficient ε (-h/2) s:ℂ)*localKernel ε h q k P Q n s-
          localDerivative ε h q k P Q n s/(clock ε s:ℂ)) := by
  simp_rw [response_density_formula]
  rw [integral_const_mul,reducedValue_integral ε h q k P Q n hε hh hb]

#print axioms sourceCurve_continuous
#print axioms amplitudeCurve_continuous
#print axioms sourceCurve_cap
#print axioms amplitudeCurve_bound
#print axioms value_integrable
#print axioms derivative_integrable
#print axioms localKernel_derivative
#print axioms value_formula
#print axioms derivative_formula
#print axioms reducedValue_integrable
#print axioms reducedValue_integral
#print axioms response_density_formula
#print axioms response_slice_integral
end
end UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
