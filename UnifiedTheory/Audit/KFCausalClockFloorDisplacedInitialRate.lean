/- Initial derivatives of actual quantum clock expectations for every
canonical momentum boost. All three potential outputs are retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialRate
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest (evolvingOutput classicalRate)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (transfer_inverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit (jointOutput_eq formVector_orbit_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain (factorOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedDomain (orbitLift)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput (classicalOutput)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed (weighted_classical_pairing)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ boostK)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral (driftPair)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral (boostedFieldOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral (boostedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow (rate_error_window rateConstant)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (p : Configuration)
local notation "q" => boostQ h (h⁻¹ • p)
local notation "k" => boostK (h⁻¹ • p)
local notation "w" => referenceState ε a h hε ha hh hb m g κ s p
local notation "out" => evolvingOutput ε hε h hh hb m g κ s s w
local notation "F" => fun θ => WithLp.toLp 2 (fun i => energyWeight m g κ s i •
  factorOutput ε a h hε ha hh hb (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k) modelDirections pointField i)

theorem initial_output_coe : out =ᵐ[angleMeasure] F := by
  let D := KFCausalClockFloorFormHamiltonian.formData ε hε h
    (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb) m g κ s
  let A := KFCausalClosedGraphForm.energyOutput D
  have he : out = A.compLp (orbitLift ε a h hε ha hh hb m g κ s q k rfl) := by
    let v := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g κ s
      (KFCausalClockFloorDisplacedAveragedDomain.averagedVector ε a h hε ha hh hb m g κ s q k rfl)
    have hf := formFlow_initial ε hε h hh hb m g κ s w
    have ht : KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hb m g κ 0 s w = v :=
      transfer_inverse ε hε h hh hb m g κ s 0 v
    exact congrArg (KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g κ s)
      ((congrArg (KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hb m g κ 0 s) hf).trans ht)
  rw [he]
  filter_upwards [A.coeFn_compLp (orbitLift ε a h hε ha hh hb m g κ s q k rfl),
    (formVector_orbit_memLp ε a h hε ha hh hb q k rfl m g κ s).coeFn_toLp] with θ hA hθ
  change orbitLift ε a h hε ha hh hb m g κ s q k rfl θ = _ at hθ
  rw [hA,hθ]
  exact jointOutput_eq ε a h hε ha hh hb _ _ ((parameter_clock (2*Real.pi*θ) q).trans rfl)
    modelDirections pointField m g κ s

theorem initial_output_pairing (B : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert) :
    (inner ℂ out (B.compLp out)).re = ∫ θ, (inner ℂ (F θ) (B (F θ))).re ∂angleMeasure := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) out (B.compLp out))
  change (∫ θ, (inner ℂ (out θ) (B.compLp out θ)).re ∂angleMeasure) =
    (∫ θ, inner ℂ (out θ) (B.compLp out θ) ∂angleMeasure).re at he
  rw [L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [B.coeFn_compLp out,initial_output_coe ε a h hε ha hh hb m g κ s p] with θ hB hθ
  rw [hB,hθ]

theorem initial_comparisonRate (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    comparisonRate ε a h hε ha hh hb m g κ s p s = Real.exp (2*s)*
      (m/2*averagedFieldDrift ε a h hε ha hh hb p pointField 0+
        g/4*averagedFieldDrift ε a h hε ha hh hb p pointField 1+
        κ*averagedDrift ε a h hε ha hh hb p) := by
  rw [comparisonRate,classicalRate,initial_output_pairing]
  simp_rw [weighted_classical_pairing ε hε m g κ s hm hg hκ]
  change (∫ θ, Real.exp (2*s)*(m/2*driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p (2*Real.pi*θ) pointField 0)+
    g/4*driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p (2*Real.pi*θ) pointField 1)+
    κ*driftPair ε hε (boostedOutput ε a h hε ha hh hb p (2*Real.pi*θ))) ∂angleMeasure) = _
  have h5 := (boostedFieldDrift_integrable ε a h hε ha hh hb p pointField 0).const_mul (m/2)
  have h6 := (boostedFieldDrift_integrable ε a h hε ha hh hb p pointField 1).const_mul (g/4)
  have h7 := (boostedDrift_integrable ε a h hε ha hh hb p).const_mul κ
  have hadd := integral_add (h5.add h6) h7
  simp only [Pi.add_apply] at hadd
  rw [integral_const_mul,hadd,integral_add h5 h6]
  simp only [integral_const_mul]
  rfl

omit h hh hb in
def initialRateLimit : ℝ := Real.exp (2*s)*
  (m/2*averagedFieldDriftLimit ε a p pointField 0+g/4*averagedFieldDriftLimit ε a p pointField 1+
    κ*averagedDriftLimit ε a p)

omit h hh hb in
theorem initial_comparisonRate_tendsto (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => comparisonRate ε a (h n) hε ha (hh n) (hb n) m g κ s p s) atTop
      (𝓝 (initialRateLimit ε a m g κ s p)) := by
  simp_rw [initial_comparisonRate ε a _ hε ha _ _ m g κ s p hm hg hκ]
  exact (((averagedFieldDrift_tendsto ε a hε ha p pointField 0 h hh hb hz).const_mul (m/2)).add
    ((averagedFieldDrift_tendsto ε a hε ha p pointField 1 h hh hb hz).const_mul (g/4))).add
      ((averagedDrift_tendsto ε a hε ha p h hh hb hz).const_mul κ) |>.const_mul (Real.exp (2*s))

omit h hh hb in
theorem initial_clockRate_tendsto (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p s) atTop
      (𝓝 (initialRateLimit ε a m g κ s p)) := by
  have herr : Tendsto (fun n => clockRate ε a (h n) hε ha (hh n) (hb n) m g κ s p s-
      comparisonRate ε a (h n) hε ha (hh n) (hb n) m g κ s p s) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [rate_error_window ε a hε ha m g κ s p hm hg hκ h hh hb hz 0] with n hn
      simpa only [Real.norm_eq_abs] using hn s (by simp)
    · simpa only [abs_zero,mul_zero] using hz.abs.const_mul (rateConstant ε a m g κ s 0 p)
  have ht := herr.add (initial_comparisonRate_tendsto ε a hε ha m g κ s p hm hg hκ h hh hb hz)
  simpa only [sub_add_cancel,zero_add] using ht

omit h hh hb in
theorem initial_derivative_tendsto (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => deriv (clockExpectation ε a (h n) hε ha (hh n) (hb n) m g κ s p) s) atTop
      (𝓝 (initialRateLimit ε a m g κ s p)) := by
  simp_rw [(clockExpectation_derivative ε a _ hε ha _ _ m g κ s p s).deriv]
  exact initial_clockRate_tendsto ε a hε ha m g κ s p hm hg hκ h hh hb hz

#print axioms initial_output_coe
#print axioms initial_output_pairing
#print axioms initial_comparisonRate
#print axioms initial_comparisonRate_tendsto
#print axioms initial_clockRate_tendsto
#print axioms initial_derivative_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedInitialRate
