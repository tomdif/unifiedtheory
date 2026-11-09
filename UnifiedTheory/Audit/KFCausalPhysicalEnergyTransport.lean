/- Exact time transport of the full natural eight-factor energy graph
and its closure. Zero mass, quartic and vacuum coefficients are included. -/
import UnifiedTheory.Audit.KFCausalJointGraphRescaling
import UnifiedTheory.Audit.KFCausalPhysicalJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
open UnifiedTheory.Audit.KFCausalJointGraphRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
open UnifiedTheory.Audit.KFCausalPhysicalJointEnergy

def timeScale (s t : ℝ) (i : Fin 8) : ℂ := if i.val<3 then 1 else (Real.exp (t-s):ℂ)
def timeOutput (s t : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert := diagonal (timeScale s t)
def staticOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert := selected (fun i : Fin 8 => i.val<3)
def growingOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert := selected (fun i : Fin 8 => ¬ i.val<3)

theorem timeOutput_apply (s t : ℝ) (y : Output (Fin 8) Hilbert) (i : Fin 8) :
    timeOutput s t y i=if i.val<3 then y i else (Real.exp (t-s):ℂ) • y i :=
  splitScaled_apply (fun i : Fin 8 => i.val<3) (Real.exp (t-s)) y i

theorem weight_transition (mass2 quartic vacuum s t : ℝ) (i : Fin 8) :
    energyWeight mass2 quartic vacuum t i=timeScale s t i*energyWeight mass2 quartic vacuum s i := by
  have he : (Real.exp (t-s):ℂ)*(Real.exp s:ℂ)=(Real.exp t:ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add,sub_add_cancel]
  fin_cases i <;> norm_num only [energyWeight,timeScale,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.val_mk]
    <;> simp only [if_true,if_false,one_mul,Complex.ofReal_mul,← mul_assoc,he]

theorem norm_timeOutput_sq (s t : ℝ) (y : Output (Fin 8) Hilbert) :
    ‖timeOutput s t y‖^2=‖staticOutput y‖^2+Real.exp (2*(t-s))*‖growingOutput y‖^2 := by
  have h := splitScaled_norm_sq (fun i : Fin 8 => i.val<3) (Real.exp (t-s)) y
  change ‖timeOutput s t y‖^2=‖staticOutput y‖^2+(Real.exp (t-s))^2*‖growingOutput y‖^2 at h
  rwa [show (Real.exp (t-s))^2=Real.exp (2*(t-s)) by rw [← Real.exp_nat_mul]; norm_num] at h

theorem timeOutput_inner (s t : ℝ) (x y : Output (Fin 8) Hilbert) :
    inner ℂ (timeOutput s t x) (timeOutput s t y)=inner ℂ (staticOutput x) (staticOutput y)+
      (Real.exp (2*(t-s)):ℂ)*inner ℂ (growingOutput x) (growingOutput y) := by
  have h := splitScaled_inner (fun i : Fin 8 => i.val<3) (Real.exp (t-s)) x y
  change inner ℂ (timeOutput s t x) (timeOutput s t y)=inner ℂ (staticOutput x) (staticOutput y)+
    (Real.exp (t-s):ℂ)^2*inner ℂ (growingOutput x) (growingOutput y) at h
  rw [← Complex.ofReal_pow,show (Real.exp (t-s))^2=Real.exp (2*(t-s)) by rw [← Real.exp_nat_mul]; norm_num] at h
  exact h

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum s t : ℝ)

theorem initialEnergy_graph_transport (z : Hilbert × Output (Fin 8) Hilbert)
    (hz : z ∈ (initialEnergy ε hε hbar v l mass2 quartic vacuum s).graph) :
    (z.1,timeOutput s t z.2) ∈ (initialEnergy ε hε hbar v l mass2 quartic vacuum t).graph :=
  initial_graph_rescale _ _ _ _ (weight_transition mass2 quartic vacuum s t) z hz

theorem initialEnergy_domain_independent :
    (initialEnergy ε hε hbar v l mass2 quartic vacuum s).domain=
      (initialEnergy ε hε hbar v l mass2 quartic vacuum t).domain :=
  initial_domain_eq _ _ _ _ _ (weight_transition mass2 quartic vacuum s t)
    (weight_transition mass2 quartic vacuum t s)

theorem closedEnergy_graph_transport (hh : |hbar| ≤ Real.pi*ε)
    (z : Hilbert × Output (Fin 8) Hilbert)
    (hz : z ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum s).graph) :
    (z.1,timeOutput s t z.2) ∈ (closedEnergy ε hε hbar v l mass2 quartic vacuum t).graph :=
  closed_graph_rescale _ _ _ _ (energyFactor_closable ε hbar hε hh v l)
    (weight_transition mass2 quartic vacuum s t) z hz

theorem common_form_domain (hh : |hbar| ≤ Real.pi*ε) :
    (closedEnergy ε hε hbar v l mass2 quartic vacuum s).domain=
      (closedEnergy ε hε hbar v l mass2 quartic vacuum t).domain :=
  closed_domain_eq _ _ _ _ _ (energyFactor_closable ε hbar hε hh v l)
    (weight_transition mass2 quartic vacuum s t) (weight_transition mass2 quartic vacuum t s)

#print axioms timeOutput_apply
#print axioms weight_transition
#print axioms norm_timeOutput_sq
#print axioms timeOutput_inner
#print axioms initialEnergy_graph_transport
#print axioms initialEnergy_domain_independent
#print axioms closedEnergy_graph_transport
#print axioms common_form_domain

end
end UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
