/- Reciprocal charged Gaussians with arbitrary neutral exponential-
polynomial profiles and real clock frequencies. Squeeze transport gives
actual graphs for the state, its pure-clock momentum, and all eight
energy factors of both. No uniform response inequality is asserted. -/
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialMomentum
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum
import UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorCoherentDerivative (physicalProfile)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound profile_squeeze)
open KFCausalReciprocalGaussianStates (configurationDensity)
open KFCausalReciprocalSqueezeFlow (squeeze)
open KFCausalReciprocalSqueezeTransport (transport transport_coe squeezeFlow squeezeFlow_apply squeezeFlow_quasiMeasurePreserving)
open KFCausalReciprocalSqueezeEnergy (factorScale factor_graph)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

def rescaledPolynomial (t : ℝ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (Polynomial.C (Real.exp (-t):ℂ)*Polynomial.X)

theorem neutral_source_profile (C : ℂ) (p α β : ℝ) (b : ℂ) (g : ℝ → ℂ) (x : Configuration) :
    physicalProfile C p α β (neutralSource b) g x =
      (C*clockPhase p (x.1:ℂ)*Complex.exp (b*(x.2 4:ℂ)))*physicalProfile 1 0 α β 0 g x := by
  simp only [physicalProfile,KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentMoments.sourcedPacket,KFCausalClockFloorCoherentSources.linearSource,
    neutralSource,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Pi.zero_apply,zero_mul,add_zero,zero_add,clockPhase,
    Complex.ofReal_zero,Complex.exp_zero,one_mul,mul_one]
  simp only [show ((Fin.succ 0).succ.succ.succ : Fin 5) = 4 from rfl]
  ring

theorem neutral_rescale (t : ℝ) (q : Transverse) :
    (Real.exp (-t):ℂ)*(squeeze t q 4:ℂ) = (q 4:ℂ) := by
  change (Real.exp (-t):ℂ)*((Real.exp t*q 4:ℝ):ℂ) = _
  rw [Complex.ofReal_mul,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

theorem polynomial_rescale (t : ℝ) (P : Polynomial ℂ) (q : Transverse) :
    (rescaledPolynomial t P).eval (squeeze t q 4:ℂ) = P.eval (q 4:ℂ) := by
  simp only [rescaledPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,neutral_rescale]

theorem profile_transport (α β t : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (g : ℝ → ℂ) (x : Configuration) :
    (rescaledPolynomial t P).eval (squeeze t x.2 4:ℂ)*
      physicalProfile C p α (β*Real.exp (-2*t))
        (neutralSource ((Real.exp (-t):ℂ)*b)) g (x.1,squeeze t x.2) =
      (C*clockPhase p (x.1:ℂ)*Complex.exp (b*(x.2 4:ℂ))*P.eval (x.2 4:ℂ))*
        configurationDensity α β (Real.exp (2*t)) g x := by
  rw [polynomial_rescale,neutral_source_profile,profile_squeeze]
  have he : ((Real.exp (-t):ℂ)*b)*(squeeze t x.2 4:ℂ) = b*(x.2 4:ℂ) := by
    rw [mul_assoc,mul_comm b,← mul_assoc,neutral_rescale]
    ring
  dsimp only
  rw [he]
  ring

def profile (ε a h w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Configuration) : ℂ :=
  (C*clockPhase p (x.1:ℂ)*Complex.exp (b*(x.2 4:ℂ))*P.eval (x.2 4:ℂ))*
    configurationDensity (groundWidth h) (neutralWidth h) w (clockFunction ε a) x

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
local notation "τ" => Real.log w/2
local notation "hτ" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h τ
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh τ
local notation "hwidth" => baseWidth_bound h hh τ hτ
local notation "d" => neutralSource ((Real.exp (-τ):ℂ)*b)
local notation "Q" => rescaledPolynomial τ P
local notation "k" => (Real.exp (-τ/2):ℂ)

def state : Hilbert := k • transport (-τ)
  (KFCausalVariableWidthPolynomialDomain.input ε a α β hε ha hα hβ hwidth C p d 4 Q)

theorem state_coe : state ε a h w hε ha hh hw C p b P =ᵐ[volume] profile ε a h w C p b P := by
  let f := KFCausalVariableWidthPolynomialDomain.input ε a α β hε ha hα hβ hwidth C p d 4 Q
  have he : Real.exp (2*τ) = w := by
    rw [show 2*τ=Real.log w by ring,Real.exp_log (by linarith)]
  filter_upwards [Lp.coeFn_smul k (transport (-τ) f),transport_coe (-τ) f,
    (squeezeFlow_quasiMeasurePreserving (-τ)).ae
      (KFCausalVariableWidthPolynomialDomain.input_coe ε a α β hε ha hα hβ hwidth C p d 4 Q)]
    with x hc ht hf
  change f (squeezeFlow (-τ) x) = _ at hf
  change (k • transport (-τ) f) x = _
  rw [hc,Pi.smul_apply,smul_eq_mul,ht]
  change k*((Real.exp (-(-τ)/2):ℂ)*f (squeezeFlow (-τ) x)) = _
  rw [hf]
  simp only [squeezeFlow_apply,neg_neg,baseWidth]
  rw [profile_transport,he,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,
    show -τ/2+τ/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]
  rfl

def momentum : Hilbert := k • transport (-τ)
  (KFCausalVariableWidthPolynomialMomentum.momentum ε a α β hε ha hα hβ hwidth h p d 4 C Q)

theorem momentum_graph :
    (state ε a h w hε ha hh hw C p b P,momentum ε a h w hε ha hh hw C p b P) ∈
      (pureMomentum ε hε h).graph :=
  (pureMomentum ε hε h).graph.smul_mem k
    (KFCausalReciprocalGaussianMomentum.pure_graph_transport ε hε h hh (-τ) _ _
      (KFCausalVariableWidthPolynomialMomentum.momentum_graph ε a α β hε ha hα hβ hwidth h hh p d 4 C Q))

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (j : Fin 8) : Hilbert := k • (factorScale (-τ) j • transport (-τ)
  (KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth h C p d 4 hb Q modelDirections pointField j))

def momentumOutput (j : Fin 8) : Hilbert := k • (factorScale (-τ) j • transport (-τ)
  (KFCausalVariableWidthPolynomialMomentum.momentumFactor ε a α β hε ha hα hβ hwidth h p d 4 C hb Q modelDirections pointField j))

theorem output_graph (j : Fin 8) :
    (state ε a h w hε ha hh hw C p b P,output ε a h w hε ha hh hw C p b P hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.smul_mem k
    (factor_graph ε hε h (-τ) j _ _
      (KFCausalVariableWidthPolynomialDomain.output_graph ε a α β hε ha hα hβ hwidth h C p d 4 hb Q modelDirections pointField j))

theorem momentumOutput_graph (j : Fin 8) :
    (momentum ε a h w hε ha hh hw C p b P,momentumOutput ε a h w hε ha hh hw C p b P hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph :=
  (energyFactor ε hε h modelDirections pointField j).graph.smul_mem k
    (factor_graph ε hε h (-τ) j _ _
      (KFCausalVariableWidthPolynomialMomentum.momentumFactor_graph ε a α β hε ha hα hβ hwidth h hh p d 4 C hb Q modelDirections pointField j))

#print axioms neutral_source_profile
#print axioms neutral_rescale
#print axioms polynomial_rescale
#print axioms profile_transport
#print axioms state_coe
#print axioms momentum_graph
#print axioms output_graph
#print axioms momentumOutput_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
