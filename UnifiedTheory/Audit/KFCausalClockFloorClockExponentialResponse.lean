/- The clock/exponential commutator has the actual response rho/2 as
its leading coefficient. The L2 remainder is controlled by hbar^2/epsilon
times the squared-defect-weighted output. All natural energy factors
inherit this estimate on their proved common clock composition domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor
import UnifiedTheory.Audit.KFCausalClockFloorClockExponentialCommutator
import UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator
import UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockExponentialResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect response defect_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftTaylor
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator (commonDomain)
open UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator (factorDifference)

def firstOrderRemainder (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) : Hilbert →L[ℂ] Hilbert :=
  differenceOperator ε hε h hh-(Complex.I*(h:ℂ)/2) • responseOperator ε hε

theorem firstOrderRemainder_coe (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    firstOrderRemainder ε hε h hh f =ᵐ[volume]
      fun x => (difference ε h x-(Complex.I*(h:ℂ)/2)*(response ε x.1:ℂ))*f x := by
  let Δ := differenceOperator ε hε h hh
  let Q := responseOperator ε hε
  let c : ℂ := Complex.I*(h:ℂ)/2
  change Δ f-c • Q f =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (Δ f) (c • Q f),Lp.coeFn_smul c (Q f),
    differenceOperator_coe ε hε h hh f,responseOperator_coe ε hε f] with x hs hc hd hq
  change Δ f x = _ at hd
  change Q f x = _ at hq
  rw [hs]
  simp only [Pi.sub_apply,hc,Pi.smul_apply,smul_eq_mul,hd,hq]
  dsimp [c]
  ring

theorem firstOrderRemainder_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert) :
    ‖firstOrderRemainder ε hε h hh f‖ ≤
      (h^2/ε)*‖defectOperator ε hε (defectOperator ε hε f)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [firstOrderRemainder_coe ε hε h hh f,
    defectOperator_coe ε hε (defectOperator ε hε f),defectOperator_coe ε hε f] with x hr h2 h1
  have hn : ‖defectOperator ε hε (defectOperator ε hε f) x‖ = (defect ε x.1)^2*‖f x‖ := by
    rw [h2,h1,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (defect_positive ε x.1 hε)]
    ring
  rw [hr,norm_mul,hn]
  exact (mul_le_mul_of_nonneg_right (difference_first_order_bound ε hε h hh x)
    (norm_nonneg _)).trans_eq (by ring)

theorem exponential_first_order (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f cf ef ecf cef : Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph)
    (he : (f,ef) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hec : (cf,ecf) ∈ (longitudinalExponential ε hε h (1/2)).graph)
    (hce : (ef,cef) ∈ (clockOperator ε hε).graph) :
    ‖cef-ecf-(Complex.I*(h:ℂ)/2) • responseOperator ε hε ef‖ ≤
      (h^2/ε)*‖defectOperator ε hε (defectOperator ε hε ef)‖ := by
  rw [(KFCausalClockFloorClockExponentialCommutator.commutator_graph ε hε h hh
    f cf ef ecf cef hc he hec hce).1]
  exact firstOrderRemainder_norm ε hε h hh ef

theorem ordered_commonDomain_dense (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) : Dense (commonDomain ε hε (orderedExponential ε hε h)) := by
  apply KFCausalClockFloorClockShiftCommutator.commonDomain_dense
  exact KFCausalClockFloorCommonDensity.energyFactor_domain_dense ε h hε
    (by nlinarith [abs_nonneg h]) (fun _ => 0) 0 7

theorem ordered_commonDomain_graphs (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (f : Hilbert)
    (hf : f ∈ commonDomain ε hε (orderedExponential ε hε h)) :
    ∃ cf tf tcf ctf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧
      (f,tf) ∈ (orderedExponential ε hε h).graph ∧
      (cf,tcf) ∈ (orderedExponential ε hε h).graph ∧
      (tf,ctf) ∈ (clockOperator ε hε).graph ∧
      ctf-tcf = differenceOperator ε hε h hh tf ∧
      ‖ctf-tcf-(Complex.I*(h:ℂ)/2) • responseOperator ε hε tf‖ ≤
        (h^2/ε)*‖defectOperator ε hε (defectOperator ε hε tf)‖ := by
  obtain ⟨cf,tf,tcf,ctf,hc,ht,htc,hct,he,_⟩ :=
    KFCausalClockFloorClockShiftCommutator.commonDomain_graphs ε hε h hh _
      (KFCausalClockFloorOrderedDefectFullDomain.ordered_graph_defect ε hε h hh) f hf
  refine ⟨cf,tf,tcf,ctf,hc,ht,htc,hct,he,?_⟩
  rw [he]
  exact firstOrderRemainder_norm ε hε h hh tf

def factorResponse (ε : ℝ) (hε : 0 < ε) (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val < 5 then 0 else responseOperator ε hε

theorem energy_first_order_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (f cf : Hilbert) (tf tcf ctf : Fin 8 → Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph)
    (ht : ∀ i, (f,tf i) ∈ (energyFactor ε hε h v l i).graph)
    (htc : ∀ i, (cf,tcf i) ∈ (energyFactor ε hε h v l i).graph)
    (hct : ∀ i, (tf i,ctf i) ∈ (clockOperator ε hε).graph) :
    ∀ i, ‖ctf i-tcf i-(Complex.I*(h:ℂ)/2) • factorResponse ε hε i (tf i)‖ ≤
      (h^2/ε)*‖defectOperator ε hε (defectOperator ε hε (tf i))‖ := by
  have hcom := KFCausalClockFloorClockEnergyCommutator.commutator_graph ε hε h hh v l
    f cf tf tcf ctf hc ht htc hct
  intro i
  rw [(hcom i).1]
  by_cases hi : i.val < 5
  · simp only [factorDifference,factorResponse,hi,if_true,ContinuousLinearMap.zero_apply,
      smul_zero,sub_zero,norm_zero]
    positivity
  · simp only [factorDifference,factorResponse,hi,if_false]
    exact firstOrderRemainder_norm ε hε h hh (tf i)

#print axioms firstOrderRemainder_coe
#print axioms firstOrderRemainder_norm
#print axioms exponential_first_order
#print axioms ordered_commonDomain_dense
#print axioms ordered_commonDomain_graphs
#print axioms energy_first_order_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorClockExponentialResponse
