/- Absolute joint integrability and Fubini for the actual projected
polynomial local response. The clock derivative and both charge angles
are retained; bounds here may depend on the polynomial degree. -/
import UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalChargeResponseFubini (angles)
open UnifiedTheory.Audit.KFCausalPolynomialLocalKernel (Domain measure valueBound derivativeBound)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient pair)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (clockFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (clockSlope)
open UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
  (relativeInverse relativeInverse_bound coefficient_bound coefficient_continuous)

local instance : SFinite measure := by
  unfold KFCausalPolynomialLocalKernel.measure
  infer_instance

variable (ε a h : ℝ) (q k : Joint 2 4) (P Q : Polynomial ℂ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "b" => sourceCurve h q k
local notation "C" => amplitudeCurve h q k
local notation "p" => clockFrequency h k

def density (t : ℝ × Domain) : ℂ :=
  pair ε a a p p (-h/2) t.1*reducedValue ε h q k P Q n t.1 t.2

def response (s : ℝ) : ℂ :=
  pair ε a a p p (-h/2) s*
    ((coefficient ε (-h/2) s:ℂ)*localKernel ε h q k P Q n s-
      localDerivative ε h q k P Q n s/(clock ε s:ℂ))

variable (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hb in
theorem response_eq_deriv (s : ℝ) :
    response ε a h q k P Q n s =
      pair ε a a p p (-h/2) s*
        ((coefficient ε (-h/2) s:ℂ)*localKernel ε h q k P Q n s-
          deriv (localKernel ε h q k P Q n) s/(clock ε s:ℂ)) := by
  rw [(localKernel_derivative ε h q k P Q n hε hh hb s).deriv]
  rfl

include hε hb in
private theorem kernel_continuity :
    Continuous (fun t : ℝ × Domain => value ε h q k P Q n t.1 t.2) ∧
    Continuous (fun t : ℝ × Domain => derivative ε h q k P Q n t.1 t.2) := by
  have hs := sourceCurve_continuous h q k
  have hc := amplitudeCurve_continuous h q k
  have h1 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε (-h/2) α β
    hε (shift_bound ε h hb) (fun t : ℝ × Domain => t.1) (fun t : ℝ × Domain => t.2.2)
    (fun t : ℝ × Domain => b t.2.1.1) (fun t : ℝ × Domain => C t.2.1.1)
    continuous_fst continuous_snd.snd (hs.comp continuous_snd.fst.fst)
    (hc.comp continuous_snd.fst.fst) P pointField n
  have h2 := KFCausalPolynomialKernelJointContinuity.factor_continuous ε (-h/2) α β
    hε (shift_bound ε h hb) (fun t : ℝ × Domain => t.1) (fun t : ℝ × Domain => t.2.2)
    (fun t : ℝ × Domain => b t.2.1.2) (fun t : ℝ × Domain => C t.2.1.2)
    continuous_fst continuous_snd.snd (hs.comp continuous_snd.fst.snd)
    (hc.comp continuous_snd.fst.snd) Q pointField n
  have h1d := KFCausalPolynomialKernelJointContinuity.factorDerivative_continuous ε (-h/2) α β
    hε (shift_bound ε h hb) (fun t : ℝ × Domain => t.1) (fun t : ℝ × Domain => t.2.2)
    (fun t : ℝ × Domain => b t.2.1.1) (fun t : ℝ × Domain => C t.2.1.1)
    continuous_fst continuous_snd.snd (hs.comp continuous_snd.fst.fst)
    (hc.comp continuous_snd.fst.fst) P pointField n
  have h2d := KFCausalPolynomialKernelJointContinuity.factorDerivative_continuous ε (-h/2) α β
    hε (shift_bound ε h hb) (fun t : ℝ × Domain => t.1) (fun t : ℝ × Domain => t.2.2)
    (fun t : ℝ × Domain => b t.2.1.2) (fun t : ℝ × Domain => C t.2.1.2)
    continuous_fst continuous_snd.snd (hs.comp continuous_snd.fst.snd)
    (hc.comp continuous_snd.fst.snd) Q pointField n
  exact ⟨h1.star.mul h2,(h1d.star.mul h2).add (h1.star.mul h2d)⟩

include hε hb in
theorem density_continuous : Continuous (density ε a h q k P Q n) := by
  obtain ⟨hv,hd⟩ := kernel_continuity ε h q k P Q n hε hb
  have hc := (coefficient_continuous ε (-h/2) hε (shift_bound ε h hb)).comp
    (continuous_fst : Continuous (fun t : ℝ × Domain => t.1))
  have ht : Continuous (fun t : ℝ × Domain => (clock ε t.1:ℂ)) := by
    unfold clock
    fun_prop
  have hn (t : ℝ × Domain) : (clock ε t.1:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold clock
    positivity
  have hg := (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth
    ε a p (-h/2) hε (shift_bound ε h hb)).continuous.comp
      (continuous_fst : Continuous (fun t : ℝ × Domain => t.1))
  exact (hg.star.mul hg).mul (((Complex.continuous_ofReal.comp hc).mul hv).sub (hd.div ht hn))

include hε hh hb in
theorem reducedValue_bound (b₀ : Fin 5 → ℂ)
    (hcap : ∀ θ, sourceSize (b θ) ≤ sourceSize b₀) (s : ℝ) (z : Domain) :
    ‖reducedValue ε h q k P Q n s z‖ ≤
      (4/ε)*valueBound ε (-h/2) α β P Q pointField n b₀ b₀ z+
        (2/ε)*derivativeBound ε (-h/2) α β P Q pointField n b₀ b₀ z := by
  have hy := shift_bound ε h hb
  have hw : 32*β ≤ α := by unfold neutralWidth; linarith
  have hv := KFCausalPolynomialLocalKernel.value_bound ε (-h/2) α β b b C C P Q pointField n
    hε hy b₀ b₀ (groundWidth_positive h hh) (neutralWidth_positive h hh) hw
    hcap hcap (amplitudeCurve_bound h hh q k) (amplitudeCurve_bound h hh q k) s z
  have hd := KFCausalPolynomialLocalKernel.derivative_bound ε (-h/2) α β b b C C P Q pointField n
    hε hy b₀ b₀ (groundWidth_positive h hh) (neutralWidth_positive h hh) hw
    hcap hcap (amplitudeCurve_bound h hh q k) (amplitudeCurve_bound h hh q k) s z
  have hc : (clock ε s:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold clock
    positivity
  have he : clockSlope ε (-h/2) s/(clock ε s:ℂ) = relativeInverse ε (-h/2) s := by
    unfold clockSlope relativeInverse
    field_simp
  have hd' : ‖derivative ε h q k P Q n s z/(clock ε s:ℂ)‖ ≤
      (2/ε)*derivativeBound ε (-h/2) α β P Q pointField n b₀ b₀ z := by
    calc
      _ ≤ (‖clockSlope ε (-h/2) s‖*
          derivativeBound ε (-h/2) α β P Q pointField n b₀ b₀ z)/‖(clock ε s:ℂ)‖ := by
        rw [norm_div]
        exact div_le_div_of_nonneg_right hd (norm_nonneg _)
      _ = ‖clockSlope ε (-h/2) s/(clock ε s:ℂ)‖*
          derivativeBound ε (-h/2) α β P Q pointField n b₀ b₀ z := by rw [norm_div]; ring
      _ = ‖relativeInverse ε (-h/2) s‖*
          derivativeBound ε (-h/2) α β P Q pointField n b₀ b₀ z := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right (relativeInverse_bound ε (-h/2) s hε hy)
        (KFCausalPolynomialLocalKernel.derivativeBound_nonnegative ε (-h/2) α β P Q pointField n b₀ b₀ z)
  apply (norm_sub_le _ _).trans
  apply add_le_add _ hd'
  rw [norm_mul]
  exact mul_le_mul (coefficient_bound ε (-h/2) s hε hy) hv (norm_nonneg _)
    (by positivity)

include hε ha hh hb in
theorem density_integrable : Integrable (density ε a h q k P Q n) (volume.prod measure) := by
  obtain ⟨b₀,hcap⟩ := sourceCurve_cap h q k
  have hv := KFCausalPolynomialLocalKernel.valueBound_integrable ε (-h/2) α β P Q pointField n b₀ b₀
    (groundWidth_positive h hh) (neutralWidth_positive h hh)
  have hd := KFCausalPolynomialLocalKernel.derivativeBound_integrable ε (-h/2) α β P Q pointField n b₀ b₀
    (groundWidth_positive h hh) (neutralWidth_positive h hh)
  have hg := KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p (-h/2) hε ha (shift_bound ε h hb)
  have hp : Integrable (fun s => ‖pair ε a a p p (-h/2) s‖) volume :=
    (hg.star.integrable_mul hg).norm
  apply (hp.mul_prod ((hv.const_mul (4/ε)).add (hd.const_mul (2/ε)))).mono'
    (density_continuous ε a h q k P Q n hε hb).aestronglyMeasurable
  filter_upwards [] with t
  rw [density,norm_mul]
  exact mul_le_mul_of_nonneg_left (reducedValue_bound ε h q k P Q n hε hh hb b₀ hcap t.1 t.2)
    (norm_nonneg _)

include hε hh hb in
theorem slice_integral (s : ℝ) :
    (∫ z, density ε a h q k P Q n (s,z) ∂measure) = response ε a h q k P Q n s := by
  unfold density
  dsimp only
  rw [integral_const_mul,reducedValue_integral ε h q k P Q n hε hh hb]
  rfl

include hε ha hh hb in
theorem response_integrable : Integrable (response ε a h q k P Q n) volume :=
  (density_integrable ε a h q k P Q n hε ha hh hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (slice_integral ε a h q k P Q n hε hh hb))

include hε ha hh hb in
theorem response_integral_reordered :
    (∫ s, response ε a h q k P Q n s) =
      ∫ t : ℝ × ℝ, ∫ x : Configuration,
        KFCausalPolynomialProjectedClockResponse.reducedDensity ε a h q k P Q n t x ∂volume ∂angles := by
  let f := density ε a h q k P Q n
  have hf := density_integrable ε a h q k P Q n hε ha hh hb
  have hassoc : Integrable (fun z : (ℝ × (ℝ × ℝ)) × Transverse => f (z.1.1,(z.1.2,z.2)))
      ((volume.prod angles).prod volume) :=
    (measurePreserving_prodAssoc (volume : Measure ℝ) angles (volume : Measure Transverse)).integrable_comp_of_integrable hf
  have hinner := hassoc.integral_prod_left
  calc
    _ = ∫ s : ℝ, ∫ z : Domain, f (s,z) ∂measure := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun s => (slice_integral ε a h q k P Q n hε hh hb s).symm))
    _ = ∫ s : ℝ, ∫ t : ℝ × ℝ, ∫ x : Transverse, f (s,(t,x)) ∂volume ∂angles := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact integral_prod _ ((reducedValue_integrable ε h q k P Q n hε hh hb s).const_mul
        (pair ε a a p p (-h/2) s))
    _ = ∫ t : ℝ × ℝ, ∫ s : ℝ, ∫ x : Transverse, f (s,(t,x)) ∂volume ∂volume ∂angles :=
      integral_integral_swap hinner
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hi := KFCausalPolynomialResponseIntegrability.reducedDensity_integrable ε a a h
        (clockFrequency h (KFCausalChargeModulationFlow.parameter (2*Real.pi*t.1) k))
        (clockFrequency h (KFCausalChargeModulationFlow.parameter (2*Real.pi*t.2) k))
        (b t.1) (b t.2) (C t.1) (C t.2) P Q pointField n hε ha ha hh hb
      change _ = ∫ x : Configuration,
        KFCausalPolynomialProjectedClockResponse.reducedDensity ε a h q k P Q n t x
      change Integrable (KFCausalPolynomialProjectedClockResponse.reducedDensity ε a h q k P Q n t)
        ((volume : Measure ℝ).prod (volume : Measure Transverse)) at hi
      rw [show (volume : Measure Configuration) =
        (volume : Measure ℝ).prod (volume : Measure Transverse) from rfl,integral_prod _ hi]
      apply integral_congr_ae
      filter_upwards [] with s
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        (response_density_formula ε h q k P Q n a s (t,x)).symm)

include hε ha hh hb in
omit Q in
theorem response_integral_factorRate :
    (∫ s, response ε a h q k P P n s) =
      (KFCausalDisplacedPolynomialProjectedResponse.factorRate ε a h hε ha hh hb q k P
        (KFCausalSourcedResponseFactorBridge.index n):ℂ) := by
  rw [response_integral_reordered ε a h q k P P n hε ha hh hb]
  exact KFCausalPolynomialProjectedClockResponse.factorRate_integral ε a h hε ha hh hb q k P n

#print axioms response_eq_deriv
#print axioms density_continuous
#print axioms reducedValue_bound
#print axioms density_integrable
#print axioms slice_integral
#print axioms response_integrable
#print axioms response_integral_reordered
#print axioms response_integral_factorRate
end
end UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalResponse
