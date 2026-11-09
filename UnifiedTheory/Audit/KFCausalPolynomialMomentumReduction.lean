/- The actual momentum and all its energy-factor outputs for polynomial
packets reduce to the same bounded clock maps at widths a and a/2.
This identifies the constructed graph outputs without differentiating
an unproved pointwise representative of an L2 integral. -/
import UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumReduction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain
open UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)

def originalMap (p : ℝ) : Hilbert × Hilbert →L[ℂ] Hilbert :=
  (-Complex.I*(h:ℂ)) •
    ((KFCausalPureClockOutputMultipliers.boundedPart ε hε p).comp (ContinuousLinearMap.fst ℂ Hilbert Hilbert)-
      (2*(a:ℂ)) • (KFCausalShiftedClockMomentOperator.momentOperator ε a 0 ha).comp
        (ContinuousLinearMap.snd ℂ Hilbert Hilbert))

def reducedMap (hb : |h| ≤ 2*Real.pi*ε/3) (p : ℝ) : Hilbert × Hilbert →L[ℂ] Hilbert :=
  (-Complex.I*(h:ℂ)) •
    ((((p:ℂ)*Complex.I-1) • KFCausalShiftedClockMomentOperator.inverseOperator ε (-h/2) hε
      (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)).comp (ContinuousLinearMap.fst ℂ Hilbert Hilbert)-
      (2*(a:ℂ)) • (KFCausalShiftedClockMomentOperator.momentOperator ε a (-h/2) ha).comp
        (ContinuousLinearMap.snd ℂ Hilbert Hilbert))-
    (KFCausalClockFloorOrderedMomentumCommutator.correction ε hε h hb).comp
      (ContinuousLinearMap.fst ℂ Hilbert Hilbert)

theorem originalMap_apply (p : ℝ) (f g : Hilbert) :
    originalMap ε a h hε ha p (f,g) =
      KFCausalPureClockOutputMultipliers.outputMap ε a h hε ha p f g := rfl

theorem reducedMap_apply (hb : |h| ≤ 2*Real.pi*ε/3) (p : ℝ) (f g : Hilbert) :
    reducedMap ε a h hε ha hb p (f,g) =
      KFCausalCoherentMomentumOutputReduction.reducedOutput ε a h hε ha hb p f g := rfl

def factorMap (hb : |h| ≤ 2*Real.pi*ε/3) (p : ℝ) (j : Fin 8) : Hilbert × Hilbert →L[ℂ] Hilbert :=
  if j.val < 5 then originalMap ε a h hε ha p else reducedMap ε a h hε ha hb p

theorem factorMap_apply (hb : |h| ≤ 2*Real.pi*ε/3) (p : ℝ) (j : Fin 8) (f g : Hilbert) :
    factorMap ε a h hε ha hb p j (f,g) =
      if j.val < 5 then KFCausalPureClockOutputMultipliers.outputMap ε a h hε ha p f g
      else KFCausalCoherentMomentumOutputReduction.reducedOutput ε a h hε ha hb p f g := by
  unfold factorMap
  split_ifs <;> rfl

omit ε a h hε ha in
theorem coefficient_pair (L : Hilbert × Hilbert →L[ℂ] Hilbert) (c : ℂ)
    (f g : ℝ → Hilbert) (hf : Continuous f) (hg : Continuous g) :
    c • (∫ θ, L (f θ,g θ) ∂angleMeasure) =
      L (c • (∫ θ, f θ ∂angleMeasure),c • (∫ θ, g θ ∂angleMeasure)) := by
  have hfi := (continuous_angle_memLp f hf).integrable (by norm_num)
  have hgi := (continuous_angle_memLp g hg).integrable (by norm_num)
  rw [L.integral_comp_comm (hfi.prodMk hgi),integral_pair hfi hgi]
  exact (L.map_smul c _).symm

variable (hh : h ≠ 0) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5) (C : ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem power_momentum_reduction (n : ℕ) :
    powerMomentum ε a h hε ha hh p b i C n = originalMap ε a h hε ha p
      (powerInput ε a h hε ha hh C p b i n,
        powerInput ε (a/2) h hε (by positivity) hh C p b i n) := by
  rw [powerInput_coefficient ε a h hε ha hh C p b i n,
    powerInput_coefficient ε (a/2) h hε (by positivity) hh C p b i n]
  exact coefficient_pair (originalMap ε a h hε ha p) (C*normalization n) _ _
    (KFCausalSourcedCurveDomain.state_continuous ε a h hε ha hh
      (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i))
    (KFCausalSourcedCurveDomain.state_continuous ε (a/2) h hε (by positivity) hh
      (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (circleSource_bound b i))

theorem power_factor_reduction (hb : |h| ≤ 2*Real.pi*ε/3) (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    powerMomentumFactor ε a h hε ha hh p b i C hb n v l j = factorMap ε a h hε ha hb p j
      (powerOutput ε a h hε ha hh C p b i hb n v l j,
        powerOutput ε (a/2) h hε (by positivity) hh C p b i hb n v l j) := by
  let f : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) h hb v l j
  let g : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε (a/2) α β hε (by positivity) hα hβ hw (weight n θ) p (circleSource b i θ) h hb v l j
  have he (θ : ℝ) : factorCurve ε a h hε ha hh p b i hb n v l j θ =
      factorMap ε a h hε ha hb p j (f θ,g θ) := (factorMap_apply ε a h hε ha hb p j _ _).symm
  change (C*normalization n) • (∫ θ, factorCurve ε a h hε ha hh p b i hb n v l j θ ∂angleMeasure) = _
  rw [show factorCurve ε a h hε ha hh p b i hb n v l j =
    (fun θ => factorMap ε a h hε ha hb p j (f θ,g θ)) from funext he]
  exact coefficient_pair (factorMap ε a h hε ha hb p j) (C*normalization n) f g
    (KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j)
    (KFCausalSourcedCurveDomain.factor_continuous ε (a/2) h hε (by positivity) hh hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i) v l j)

theorem momentum_reduction (P : Polynomial ℂ) :
    momentum ε a h hε ha hh p b i C P = originalMap ε a h hε ha p
      (input ε a h hε ha hh C p b i P,input ε (a/2) h hε (by positivity) hh C p b i P) := by
  have hs := map_sum (originalMap ε a h hε ha p)
    (fun n => P.coeff n • (powerInput ε a h hε ha hh C p b i n,
      powerInput ε (a/2) h hε (by positivity) hh C p b i n)) P.support
  simp only [map_smul] at hs
  simpa only [input,momentum,power_momentum_reduction,Prod.smul_mk,← prod_mk_sum] using hs.symm

theorem factor_reduction (hb : |h| ≤ 2*Real.pi*ε/3) (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    momentumFactor ε a h hε ha hh p b i C hb P v l j = factorMap ε a h hε ha hb p j
      (output ε a h hε ha hh C p b i hb P v l j,
        output ε (a/2) h hε (by positivity) hh C p b i hb P v l j) := by
  have hs := map_sum (factorMap ε a h hε ha hb p j)
    (fun n => P.coeff n • (powerOutput ε a h hε ha hh C p b i hb n v l j,
      powerOutput ε (a/2) h hε (by positivity) hh C p b i hb n v l j)) P.support
  simp only [map_smul] at hs
  simpa only [output,momentumFactor,power_factor_reduction,Prod.smul_mk,← prod_mk_sum] using hs.symm

#print axioms originalMap_apply
#print axioms reducedMap_apply
#print axioms factorMap_apply
#print axioms coefficient_pair
#print axioms power_momentum_reduction
#print axioms power_factor_reduction
#print axioms momentum_reduction
#print axioms factor_reduction
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumReduction
