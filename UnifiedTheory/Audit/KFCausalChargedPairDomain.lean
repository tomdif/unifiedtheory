/- The paired quadratic excitation is an explicit nonzero physical
Hilbert state in all eight natural energy-factor domains. These are
unprojected domains; no charge or completed averaged-form claim is made. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianDomain
import UnifiedTheory.Audit.KFCausalChargedPairCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalChargedPairDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous neutralWidth)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalDirectionalGaussianStates (linearForm)

def directions : Fin 4 → Transverse :=
  ![![1,1,0,0,0],![1,-1,0,0,0],![0,0,1,1,0],![0,0,1,-1,0]]

def combine {E : Type*} [AddCommGroup E] [Module ℂ E] (f : Fin 4 → E) : E :=
  (1/4:ℂ) • (f 0-f 1-f 2+f 3)

theorem polarization (q : Transverse) :
    combine (fun i => (linearForm (directions i) q:ℂ)^2) = (pairPolynomial q:ℂ) := by
  have h0 : linearForm (directions 0) q = q 0+q 1 := by
    simp [linearForm,directions,Fin.sum_univ_succ]
  have h1 : linearForm (directions 1) q = q 0-q 1 := by
    simp [linearForm,directions,Fin.sum_univ_succ,sub_eq_add_neg]
  have h2 : linearForm (directions 2) q = q 2+q 3 := by
    simp [linearForm,directions,Fin.sum_univ_succ]
  have h3 : linearForm (directions 3) q = q 2-q 3 := by
    simp [linearForm,directions,Fin.sum_univ_succ,sub_eq_add_neg]
  simp only [combine,smul_eq_mul,h0,h1,h2,h3,pairPolynomial]
  push_cast
  ring

theorem combine_coe (f : Fin 4 → Hilbert) (F : Fin 4 → Configuration → ℂ)
    (hF : ∀ i, f i =ᵐ[volume] F i) :
    (combine f : Hilbert) =ᵐ[volume] fun x => combine (fun i => F i x) := by
  filter_upwards [Lp.coeFn_smul (1/4:ℂ) (f 0-f 1-f 2+f 3),
    Lp.coeFn_add (f 0-f 1-f 2) (f 3),Lp.coeFn_sub (f 0-f 1) (f 2),
    Lp.coeFn_sub (f 0) (f 1),hF 0,hF 1,hF 2,hF 3] with x h0 h1 h2 h3 h4 h5 h6 h7
  change ((1/4:ℂ) • (f 0-f 1-f 2+f 3)) x = _
  rw [h0,Pi.smul_apply,smul_eq_mul,h1,Pi.add_apply,h2,Pi.sub_apply,h3,Pi.sub_apply,
    h4,h5,h6,h7]
  rfl

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def state : Hilbert :=
  combine (fun i => KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 0 (directions i) 2)

def output (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) : Hilbert :=
  combine (fun i =>
    KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 0 (directions i) 2 hb v l j)

def pairedProfile (x : Configuration) : ℂ :=
  (pairPolynomial x.2:ℂ)*clockFunction ε a x.1*physicalGaussian (groundWidth h) (neutralWidth h) x.2

theorem state_coe : state ε a h hε ha hh =ᵐ[volume] pairedProfile ε a h := by
  have he := combine_coe
    (fun i => KFCausalDirectionalGaussianDomain.input ε a h hε ha hh 1 0 (directions i) 2)
    (fun i => KFCausalDirectionalGaussianStates.profile 1 0 (groundWidth h) (neutralWidth h)
      (clockFunction ε a) (directions i) 2)
    (fun i => KFCausalDirectionalGaussianDomain.input_coe ε a h hε ha hh 1 0 (directions i) 2)
  filter_upwards [he] with x hx
  change (combine _ : Hilbert) x = _
  rw [hx]
  have hp := polarization x.2
  simp only [KFCausalDirectionalGaussianStates.profile,
    KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,
    KFCausalClockFloorCoherentStrip.clockPhase,Pi.zero_apply,Complex.ofReal_zero,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul,combine,smul_eq_mul] at hp ⊢
  unfold pairedProfile
  rw [← hp]
  ring

theorem output_graph (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (j : Fin 8) :
    (state ε a h hε ha hh,output ε a h hε ha hh hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hg (i : Fin 4) := KFCausalDirectionalGaussianDomain.output_graph
    ε a h hε ha hh 1 0 (directions i) 2 hb v l j
  exact (energyFactor ε hε h v l j).graph.smul_mem (1/4:ℂ)
    ((energyFactor ε hε h v l j).graph.add_mem
      ((energyFactor ε hε h v l j).graph.sub_mem
        ((energyFactor ε hε h v l j).graph.sub_mem (hg 0) (hg 1)) (hg 2)) (hg 3))

theorem state_commonEnergyDomain (hb : |h| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    state ε a h hε ha hh ∈ commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro j
  exact LinearPMap.mem_domain_of_mem_graph (output_graph ε a h hε ha hh hb v l j)

theorem pairedProfile_continuous : Continuous (pairedProfile ε a h) := by
  have hc := clockFunction_continuous ε a
  have hg := KFCausalPhysicalGaussianMoments.physicalGaussian_continuous (groundWidth h) (neutralWidth h)
  unfold pairedProfile pairPolynomial
  fun_prop

theorem state_ne_zero : state ε a h hε ha hh ≠ 0 := by
  intro hz
  have he : pairedProfile ε a h =ᵐ[volume] (fun _ => (0:ℂ)) := by
    filter_upwards [state_coe ε a h hε ha hh,Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)] with x hx h0
    rw [hz] at hx
    exact hx.symm.trans h0
  have heq := Measure.eq_of_ae_eq he (pairedProfile_continuous ε a h) continuous_const
  let x : Configuration := (0,![1,1,0,0,0])
  have hP : pairPolynomial x.2 = 1 := by
    change (1:ℝ)*1-0*0 = 1
    norm_num
  have hC : clockFunction ε a x.1 ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (show 0 < KFCausalClockFloorInvariantTrial.realClock ε a x.1 by
      unfold KFCausalClockFloorInvariantTrial.realClock
      positivity).ne'
  have hG : physicalGaussian (groundWidth h) (neutralWidth h) x.2 ≠ 0 := Complex.exp_ne_zero _
  have hn : pairedProfile ε a h x ≠ 0 := by
    unfold pairedProfile
    rw [hP,Complex.ofReal_one,one_mul]
    exact mul_ne_zero hC hG
  exact hn (congrFun heq x)

#print axioms polarization
#print axioms combine_coe
#print axioms state_coe
#print axioms output_graph
#print axioms state_commonEnergyDomain
#print axioms pairedProfile_continuous
#print axioms state_ne_zero
end
end UnifiedTheory.Audit.KFCausalChargedPairDomain
