/- A strictly nonzero actual potential-factor pairing between centered
and paired Gaussian states, including the whole clock integral and
unit vacuum/mass/quartic weights. Charge averaging and the remaining
kinetic factors are separate obligations. -/
import UnifiedTheory.Audit.KFCausalChargedPairOrderedOutputs
import UnifiedTheory.Audit.KFCausalChargedPairLocalCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairPotentialCoupling
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalChargedPairOrderedOutputs (pairedShifted)
open KFCausalChargedPairLocalCertificate (orderedDensity)

def baseAmplitude (ε a h : ℝ) (n : Fin 3) : Configuration → ℂ :=
  amplitude ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 0 1 pointField n

def factorDensity (ε a h : ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  conj (baseAmplitude ε a h n x)*pairedShifted ε a h pointField n x

def crossDensity (ε a h : ℝ) (x : Configuration) : ℂ :=
  factorDensity ε a h 0 x+(1/2:ℂ)*factorDensity ε a h 1 x+
    (1/4:ℂ)*factorDensity ε a h 2 x

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

def baseState : Hilbert :=
  KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw 1 0 0

def baseOutput (n : Fin 3) : Hilbert :=
  KFCausalClockFloorSourcedCommonDomain.factorOutput ε a α β hε ha hα hβ hw
    1 0 0 h hb modelDirections pointField (index n)

def pairedOutput (n : Fin 3) : Hilbert :=
  KFCausalChargedPairDomain.output ε a h hε ha hh hb modelDirections pointField (index n)

def potentialPairing : ℂ :=
  inner ℂ (baseOutput ε a h hε ha hh hb 0) (pairedOutput ε a h hε ha hh hb 0)+
    (1/2:ℂ)*inner ℂ (baseOutput ε a h hε ha hh hb 1) (pairedOutput ε a h hε ha hh hb 1)+
    (1/4:ℂ)*inner ℂ (baseOutput ε a h hε ha hh hb 2) (pairedOutput ε a h hε ha hh hb 2)

theorem baseOutput_graph (n : Fin 3) :
    (baseState ε a h hε ha hh,baseOutput ε a h hε ha hh hb n) ∈
      (energyFactor ε hε h modelDirections pointField (index n)).graph :=
  KFCausalClockFloorSourcedCommonDomain.factorOutput_graph ε a α β hε ha hα hβ hw
    1 0 0 h hb modelDirections pointField (index n)

theorem baseOutput_coe (n : Fin 3) :
    baseOutput ε a h hε ha hh hb n =ᵐ[volume] baseAmplitude ε a h n :=
  KFCausalSourcedResponseFactorBridge.input_factor_density ε a α β hε ha hα hβ hw
    1 0 0 h hb modelDirections pointField n

include hε ha hh hb in
theorem factorDensity_integrable (n : Fin 3) : Integrable (factorDensity ε a h n) volume := by
  have hA := (Lp.memLp (baseOutput ε a h hε ha hh hb n)).ae_eq
    (baseOutput_coe ε a h hε ha hh hb n)
  have hB := KFCausalChargedPairOrderedOutputs.pairedShifted_memLp
    ε a h hε ha hh hb modelDirections pointField n
  exact hA.star.integrable_mul hB

theorem factor_pairing (n : Fin 3) :
    inner ℂ (baseOutput ε a h hε ha hh hb n) (pairedOutput ε a h hε ha hh hb n) =
      ∫ x, factorDensity ε a h n x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [baseOutput_coe ε a h hε ha hh hb n,
    KFCausalChargedPairOrderedOutputs.output_coe ε a h hε ha hh hb modelDirections pointField n]
    with x hx hy
  change inner ℂ ((baseOutput ε a h hε ha hh hb n) x)
    ((KFCausalChargedPairDomain.output ε a h hε ha hh hb modelDirections pointField (index n)) x) = _
  rw [hx,hy]
  simp only [factorDensity,RCLike.inner_apply]
  ring

include hε ha hh hb in
theorem crossDensity_integrable : Integrable (crossDensity ε a h) volume :=
  ((factorDensity_integrable ε a h hε ha hh hb 0).add
    ((factorDensity_integrable ε a h hε ha hh hb 1).const_mul (1/2:ℂ))).add
      ((factorDensity_integrable ε a h hε ha hh hb 2).const_mul (1/4:ℂ))

theorem potential_integral :
    potentialPairing ε a h hε ha hh hb = ∫ x, crossDensity ε a h x := by
  simp only [potentialPairing,factor_pairing,crossDensity]
  have h1 : Integrable (fun x => (1/2:ℂ)*factorDensity ε a h 1 x) volume :=
    (factorDensity_integrable ε a h hε ha hh hb 1).const_mul _
  have h2 : Integrable (fun x => (1/4:ℂ)*factorDensity ε a h 2 x) volume :=
    (factorDensity_integrable ε a h hε ha hh hb 2).const_mul _
  have h01 : Integrable (fun x => factorDensity ε a h 0 x+(1/2:ℂ)*factorDensity ε a h 1 x) volume :=
    (factorDensity_integrable ε a h hε ha hh hb 0).add h1
  rw [integral_add h01 h2,
    integral_add (factorDensity_integrable ε a h hε ha hh hb 0) h1,
    integral_const_mul,integral_const_mul]

omit hε ha hh hb in
theorem crossDensity_factorization (x : Configuration) :
    crossDensity ε a h x = (‖clockAmplitude ε a 0 (-h/2) x.1‖^2:ℝ) *
      orderedDensity α β (scale ε (-h/2) x.1) x.2 := by
  rw [KFCausalChargedPairLocalCertificate.orderedDensity_identity]
  unfold crossDensity factorDensity baseAmplitude pairedShifted amplitude
    KFCausalRelativeGaussianDifferential.profile
    KFCausalChargedPairTransverseCoupling.transverseDensity
    KFCausalQuarticPlaneDomination.potential
  simp only [show (0:Fin 3).val=0 from rfl,show (1:Fin 3).val=1 from rfl,
    show (2:Fin 3).val=2 from rfl,pow_zero,pow_one,one_mul,map_mul,map_pow,
    Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_ofNat]
  rw [← Complex.conj_mul' (clockAmplitude ε a 0 (-h/2) x.1),
    ← Complex.conj_mul' (Complex.exp (KFCausalRelativeGaussianDifferential.exponent
      α β 0 (scale ε (-h/2) x.1) x.2))]
  ring

omit ha hh hb in
include hε in
theorem clockAmplitude_ne_zero (s : ℝ) : clockAmplitude ε a 0 (-h/2) s ≠ 0 := by
  unfold clockAmplitude KFCausalClockFloorCoherentStrip.clockPhase
    KFCausalClockFloorFullGaussian.clockFactor
  exact mul_ne_zero (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (KFCausalClockFloorChargeTrialBridge.amplitude_positive ε s hε).ne')
    (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)

omit hε ha hh hb in
theorem slice_integral_re (s : ℝ) :
    (∫ q : Transverse, crossDensity ε a h (s,q)).re =
      ‖clockAmplitude ε a 0 (-h/2) s‖^2 *
        (∫ q, orderedDensity α β (scale ε (-h/2) s) q).re := by
  simp_rw [crossDensity_factorization]
  rw [integral_const_mul]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

omit ha in
include hε hh hb in
theorem slice_integral_re_negative (s : ℝ) :
    (∫ q : Transverse, crossDensity ε a h (s,q)).re < 0 := by
  rw [slice_integral_re]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (clockAmplitude_ne_zero ε a h hε s)))
    (KFCausalChargedPairLocalCertificate.physical_integral_re_negative ε h s hε hh hb)

private theorem integral_strict_negative (f : ℝ → ℝ) (hf : Integrable f volume)
    (hn : ∀ x, f x < 0) : (∫ x, f x) < 0 := by
  have hp : 0 < ∫ x, -f x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (neg_pos.mpr (hn x)).le) hf.neg]
    have hs : Function.support (fun x => -f x) = Set.univ := by
      ext x
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (neg_pos.mpr (hn x)).ne'
    rw [hs]
    simp
  rw [integral_neg] at hp
  linarith

theorem potentialPairing_re_negative : (potentialPairing ε a h hε ha hh hb).re < 0 := by
  have hi := crossDensity_integrable ε a h hε ha hh hb
  have hs : Integrable (fun s : ℝ => ∫ q : Transverse, crossDensity ε a h (s,q)) volume :=
    hi.integral_prod_left
  rw [potential_integral]
  change (∫ x : ℝ × Transverse, crossDensity ε a h x ∂volume.prod volume).re < 0
  rw [integral_prod _ hi]
  change RCLike.re (∫ s : ℝ, ∫ q : Transverse, crossDensity ε a h (s,q)) < 0
  rw [← integral_re hs]
  exact integral_strict_negative _ hs.re (slice_integral_re_negative ε a h hε hh hb)

theorem potentialPairing_ne_zero : potentialPairing ε a h hε ha hh hb ≠ 0 := by
  intro hz
  have hn := potentialPairing_re_negative ε a h hε ha hh hb
  rw [hz,Complex.zero_re] at hn
  exact (lt_irrefl 0) hn

#print axioms baseOutput_graph
#print axioms baseOutput_coe
#print axioms factorDensity_integrable
#print axioms factor_pairing
#print axioms crossDensity_integrable
#print axioms potential_integral
#print axioms crossDensity_factorization
#print axioms clockAmplitude_ne_zero
#print axioms slice_integral_re
#print axioms slice_integral_re_negative
#print axioms potentialPairing_re_negative
#print axioms potentialPairing_ne_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairPotentialCoupling
