/- Exact longitudinal exponential graphs for every canonical momentum boost
of the physical trial. The complex Gaussian source retains the neutral
shear. No uniform small-hbar estimate or averaged-domain claim is made. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw
import UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration (dot)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chartIso)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalComplexClockInverse (complexInverse_real)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (coherentPacket)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase line trial)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (source_real_flow)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (longitudinalExponential)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)

def imaginarySource (p : Transverse) : Fin 5 → ℂ := fun i => Complex.I*(p i:ℂ)

theorem phase_source (p : Configuration) (s : ℝ) (x : Transverse) :
    scalar (positionFrequency p.1 p.2 (s,x)) =
      clockPhase p.1 (s:ℂ)*Complex.exp (linearSource (imaginarySource p.2) x) := by
  rw [scalar,clockPhase,← Complex.exp_add]
  congr 1
  simp only [positionFrequency,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,
    dot,linearSource,imaginarySource,Complex.ofReal_add,Complex.ofReal_mul,
    Complex.ofReal_sum,mul_add,Finset.mul_sum,mul_assoc]
  ring

theorem positionFrequency_smul (c : ℝ) (p : Configuration) :
    positionFrequency (c • p).1 (c • p).2 = c • positionFrequency p.1 p.2 := by
  apply ContinuousLinearMap.ext
  intro x
  change (c*p.1)*x.1+(∑ i, (c*p.2 i)*x.2 i) = c*(p.1*x.1+∑ i, p.2 i*x.2 i)
  simp only [mul_add,Finset.mul_sum,mul_assoc]

def modulatedProfile (ε a h : ℝ) (p : Configuration) (x : Configuration) : ℂ :=
  scalar (positionFrequency p.1 p.2 x)*dampedProfile ε a h x

theorem inverse_modulatedProfile (ε a h : ℝ) (hε : 0 < ε) (p : Configuration)
    (z : ℝ × Grouped) :
    inverseFunction ε hε (modulatedProfile ε a h p) (grouping.symm z) =
      line ε a (groundWidth h) (neutralWidth h) p.1 (imaginarySource p.2) 0 z := by
  have he : inverseFunction ε hε (modulatedProfile ε a h p) (grouping.symm z) =
      scalar (positionFrequency p.1 p.2 ((coordinateHomeomorph ε hε).symm (grouping.symm z)))*
        inverseFunction ε hε (dampedProfile ε a h) (grouping.symm z) := by
    simp only [inverseFunction,modulatedProfile]
    ring
  rw [he,KFCausalClockFloorTrialUnitary.inverse_dampedProfile_grouping,
    KFCausalClockFloorChargeTrialBridge.dressedTrial_eq,grouping_symm_apply]
  change scalar (positionFrequency p.1 p.2
    ((chartIso ε hε).symm z.1,flow ((chartIso ε hε).symm z.1)
      ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))* _ = _
  rw [phase_source]
  simp only [line,trial,KFCausalClockFloorFullGaussian.line,KFCausalClockFloorFullGaussian.trial,
    Complex.ofReal_zero,zero_mul,add_zero,complexInverse_real ε hε,coherentPacket,source_real_flow]
  ring

theorem inverse_modulatedState_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (p : Configuration) :
    (coordinates ε hε).symm (modulation (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh))
      =ᵐ[volume] inverseFunction ε hε (modulatedProfile ε a h p) := by
  have hm : modulation (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh) =ᵐ[volume]
      modulatedProfile ε a h p := by
    filter_upwards [modulation_coe (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh),
      dampedState_coe ε a h hε ha hh] with x hx hy
    exact hx.trans (congrArg (fun t : ℂ => scalar (positionFrequency p.1 p.2 x)*t) hy)
  filter_upwards [coordinates_inverse_coe ε hε
      (modulation (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh)),
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae hm] with x hx hy
  rw [hx]
  unfold inverseFunction
  rw [hy]

theorem modulatedDamped_eq (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (p : Configuration) :
    modulation (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh) =
      gaussianState ε a (groundWidth h) (neutralWidth h) p.1 (imaginarySource p.2) 0
        hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
        (neutralWidth_bound h) (by simp; positivity) := by
  apply (coordinates ε hε).symm.injective
  unfold gaussianState
  rw [LinearIsometryEquiv.symm_apply_apply]
  apply Lp.ext
  filter_upwards [inverse_modulatedState_coe ε a h hε ha hh p,
    (configurationLine_memLp ε a (groundWidth h) (neutralWidth h) p.1 (imaginarySource p.2) 0
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (neutralWidth_bound h) (by simp; positivity)).coeFn_toLp] with x hx hy
  rw [hx,hy]
  have he := inverse_modulatedProfile ε a h hε p (grouping x)
  rw [MeasurableEquiv.symm_apply_apply] at he
  exact he

def spectralOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : Hilbert :=
  gaussianState ε a (groundWidth h) (neutralWidth h) p.1 (imaginarySource p.2) (-h/2)
    hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (shift_bound ε h hb)

theorem modulatedDamped_exponential_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (modulation (positionFrequency p.1 p.2) (dampedState ε a h hε ha hh),
      spectralOutput ε a h hε ha hh hb p) ∈ (longitudinalExponential ε hε h (1/2)).graph := by
  rw [modulatedDamped_eq]
  exact gaussianState_exponential_graph ε a (groundWidth h) (neutralWidth h) p.1
    (imaginarySource p.2) h hε ha (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hb

theorem modulatedTrial_ordered_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (modulation (positionFrequency p.1 p.2) (trialState ε a h hε ha hh),
      spectralOutput ε a h hε ha hh hb p) ∈ (orderedExponential ε hε h).graph := by
  apply (composition_graph _ _ _ _).mpr
  refine ⟨_,?_,modulatedDamped_exponential_graph ε a h hε ha hh hb p⟩
  apply (KFCausalClockFloorBoundedInverse.inverseL_graph ε hε _ _).mpr
  rw [KFCausalClockFloorKineticModulation.inverseL_modulation]
  rfl

def boostedExponentialOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹:ℝ) • spectralOutput ε a h hε ha hh hb (h⁻¹ • p)

theorem boostedExponential_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),
      boostedExponentialOutput ε a h hε ha hh hb p) ∈ (orderedExponential ε hε h).graph := by
  have he := ((orderedExponential ε hε h).graph.restrictScalars ℝ).smul_mem
    (‖trialState ε a h hε ha hh‖⁻¹) (modulatedTrial_ordered_graph ε a h hε ha hh hb (h⁻¹ • p))
  change ((‖trialState ε a h hε ha hh‖⁻¹:ℝ) •
    modulation (positionFrequency (h⁻¹ • p).1 (h⁻¹ • p).2) (trialState ε a h hε ha hh),_) ∈ _ at he
  rw [positionFrequency_smul] at he
  change ((‖trialState ε a h hε ha hh‖⁻¹:ℝ) •
    modulation (h⁻¹ • positionFrequency p.1 p.2) (trialState ε a h hε ha hh),
    boostedExponentialOutput ε a h hε ha hh hb p) ∈ (orderedExponential ε hε h).graph at he
  change (((modulation (h⁻¹ • positionFrequency p.1 p.2) : Hilbert →L[ℂ] Hilbert)
    ((‖trialState ε a h hε ha hh‖⁻¹:ℝ) • trialState ε a h hε ha hh)),_) ∈ _
  rw [ContinuousLinearMap.map_smul_of_tower]
  exact he

#print axioms phase_source
#print axioms positionFrequency_smul
#print axioms inverse_modulatedProfile
#print axioms inverse_modulatedState_coe
#print axioms modulatedDamped_eq
#print axioms modulatedDamped_exponential_graph
#print axioms modulatedTrial_ordered_graph
#print axioms boostedExponential_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
