/- The full clock multiplication, including the actual clock-momentum
state, has a constructed L2 output. This supplies the second clock graph. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalGaussianClockSquare
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous realClock)
open KFCausalClockFloorTrialClockEnergy (clock_exponential_moment halfClockFunction halfClockFunction_memLp)
open KFCausalClockFloorSourcedClockMomentum (profileState profileState_coe clockOutput)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_graph halfWeight)
open KFCausalClockFloorCoherentDerivative (physicalProfile clockMultiplier)
open KFCausalSourcedMomentumFactors (pureOutput factorOutput factorOutput_graph)
open KFCausalPureClockOutputMultipliers (outputMap outputMap_half_graph)

def fullClockFunction (ε a s : ℝ) : ℂ := (Real.exp s+ε:ℝ)*clockFunction ε a s

theorem fullClockFunction_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (fullClockFunction ε a) 2 volume := by
  have hc : Continuous (fullClockFunction ε a) :=
    (by fun_prop : Continuous (fun s => ((Real.exp s+ε:ℝ):ℂ))).mul (clockFunction_continuous ε a)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := ((clock_exponential_moment ε a 2 hε ha).add
    ((clock_exponential_moment ε a 1 hε ha).const_mul (2*ε))).add
    ((clock_exponential_moment ε a 0 hε ha).const_mul (ε^2))
  convert hi using 1
  funext s
  have he : Real.exp (2*s) = (Real.exp s)^2 := by
    rw [show 2*s=s+s by ring,Real.exp_add,pow_two]
  simp only [fullClockFunction,clockFunction,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,Pi.add_apply,one_mul,zero_mul,Real.exp_zero,he]
  ring

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)

def output : Hilbert := profileState α β hα hβ hw C p b
  (fullClockFunction ε a) (fullClockFunction_memLp ε a hε ha)

theorem second_graph :
    (clockOutput ε a α β hε ha hα hβ hw C p b,
      output ε a α β hε ha hα hβ hw C p b) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [profileState_coe α β hα hβ hw C p b
    (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha),
    profileState_coe α β hα hβ hw C p b
      (fullClockFunction ε a) (fullClockFunction_memLp ε a hε ha)] with x hx hy
  change output ε a α β hε ha hα hβ hw C p b x = _ at hy
  change clockOutput ε a α β hε ha hα hβ hw C p b x = _ at hx
  rw [hy,hx]
  have hs : (Real.sqrt (Real.exp x.1+ε):ℂ)^2 = ((Real.exp x.1+ε:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ Real.exp x.1+ε by positivity)
  simp only [physicalProfile,clockMultiplier,fullClockFunction,halfClockFunction,halfWeight]
  calc
    _ = (Real.sqrt (Real.exp x.1+ε):ℂ)^2 *
      (C*KFCausalClockFloorCoherentStrip.clockPhase p (x.1:ℂ)*clockFunction ε a x.1*
        KFCausalClockFloorCoherentMoments.sourcedPacket α β b x.2) := by rw [hs]; ring
    _ = _ := by ring

def momentumOutput (h : ℝ) : Hilbert := outputMap ε a h hε ha p
  (output ε a α β hε ha hα hβ hw C p b)
  (output ε (a/2) α β hε (by positivity) hα hβ hw C p b)

theorem momentum_second_graph (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → KFCausalTransverseDilationFlow.Transverse)
    (l : KFCausalTransverseDilationFlow.Transverse →L[ℝ] ℝ) :
    (factorOutput ε a α β hε ha hα hβ hw C p b h hb v l 0,
      momentumOutput ε a α β hε ha hα hβ hw C p b h) ∈ (clockHalf ε).graph := by
  exact outputMap_half_graph ε a h hε ha p _ _ _ _
    (second_graph ε a α β hε ha hα hβ hw C p b)
    (second_graph ε (a/2) α β hε (by positivity) hα hβ hw C p b)

#print axioms fullClockFunction_memLp
#print axioms second_graph
#print axioms momentum_second_graph
end
end UnifiedTheory.Audit.KFCausalGaussianClockSquare
