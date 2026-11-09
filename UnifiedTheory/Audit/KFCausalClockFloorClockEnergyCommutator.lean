/- The actual clock has a dense simultaneous composition domain with all
eight natural energy factors. Clock and kinetic factors commute there;
both matter factors and the ordered exponential have the bounded shift
correction. This is not a domain theorem for the completed Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator
import UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
import UnifiedTheory.Audit.KFCausalClockFloorCommonDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator (clock_shifted_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCommonDensity
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

def factorDifference (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val < 5 then 0 else differenceOperator ε hε h hh

theorem factorDifference_norm (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (i : Fin 8) (g : Hilbert) :
    ‖factorDifference ε hε h hh i g‖ ≤ |h| * ‖g‖ := by
  unfold factorDifference
  split
  · simp only [ContinuousLinearMap.zero_apply,norm_zero]
    positivity
  · exact differenceOperator_norm ε hε h hh g

theorem clock_factorAction_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (i : Fin 8) (g : Hilbert) :
    (factorAction ε hε h hh i g,(ε:ℂ) • g+
      factorDifference ε hε h hh i (factorAction ε hε h hh i g)) ∈ (clockOperator ε hε).graph := by
  by_cases hi : i.val < 5
  · simpa only [factorAction,factorDifference,hi,if_true,ContinuousLinearMap.zero_apply,add_zero]
      using clock_defect_graph ε hε g
  · simpa only [factorAction,factorDifference,hi,if_false] using clock_shifted_graph ε hε h hh g

def commonClockDomain (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Set Hilbert :=
  defectOperator ε hε '' (commonEnergyDomain ε hε h v l : Set Hilbert)

theorem commonClockDomain_dense (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense (commonClockDomain ε hε h v l) :=
  (defectOperator_denseRange ε hε).dense_image (defectOperator ε hε).continuous
    (commonEnergyDomain_dense ε h hε (by nlinarith [abs_nonneg h]) v l)

/-- Precisely the intersection of all Dom(T_i C), with one actual clock output. -/
theorem commonClockDomain_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (f : Hilbert) :
    f ∈ commonClockDomain ε hε h v l ↔ ∃ cf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧ cf ∈ commonEnergyDomain ε hε h v l := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(ε:ℂ) • u,clock_defect_graph ε hε u,(commonEnergyDomain ε hε h v l).smul_mem _ hu⟩
  · rintro ⟨cf,hc,ht⟩
    refine ⟨(ε:ℂ)⁻¹ • cf,(commonEnergyDomain ε hε h v l).smul_mem _ ht,?_⟩
    rw [map_smul,defect_clock ε hε f cf hc,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]

theorem commonClockDomain_graphs (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (f : Hilbert) (hf : f ∈ commonClockDomain ε hε h v l) :
    ∃ (cf : Hilbert) (tf tcf ctf : Fin 8 → Hilbert),
      (f,cf) ∈ (clockOperator ε hε).graph ∧ ∀ i : Fin 8,
      (f,tf i) ∈ (energyFactor ε hε h v l i).graph ∧
      (cf,tcf i) ∈ (energyFactor ε hε h v l i).graph ∧
      (tf i,ctf i) ∈ (clockOperator ε hε).graph ∧
      ctf i-tcf i = factorDifference ε hε h hh i (tf i) ∧
      ‖ctf i-tcf i‖ ≤ |h| * ‖tf i‖ := by
  rcases hf with ⟨u,hu,rfl⟩
  let g (i : Fin 8) := energyFactor ε hε h v l i
    ⟨u,(commonEnergyDomain_iff ε hε h v l u).mp hu i⟩
  have hg (i : Fin 8) : (u,g i) ∈ (energyFactor ε hε h v l i).graph :=
    (energyFactor ε hε h v l i).mem_graph ⟨u,(commonEnergyDomain_iff ε hε h v l u).mp hu i⟩
  let b (i : Fin 8) := factorAction ε hε h hh i (g i)
  refine ⟨(ε:ℂ) • u,b,(fun i => (ε:ℂ) • g i),
    (fun i => (ε:ℂ) • g i+factorDifference ε hε h hh i (b i)),clock_defect_graph ε hε u,?_⟩
  intro i
  refine ⟨energyFactor_graph_defect ε hε h hh v l i u (g i) (hg i),
    (energyFactor ε hε h v l i).graph.smul_mem (ε:ℂ) (hg i),
    clock_factorAction_graph ε hε h hh i (g i),?_,?_⟩
  · simp only [add_sub_cancel_left]
  · simpa only [add_sub_cancel_left] using factorDifference_norm ε hε h hh i (b i)

/-- The identities apply to any actual outputs on the simultaneous domain. -/
theorem commutator_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (f cf : Hilbert) (tf tcf ctf : Fin 8 → Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph)
    (ht : ∀ i, (f,tf i) ∈ (energyFactor ε hε h v l i).graph)
    (htc : ∀ i, (cf,tcf i) ∈ (energyFactor ε hε h v l i).graph)
    (hct : ∀ i, (tf i,ctf i) ∈ (clockOperator ε hε).graph) :
    ∀ i, ctf i-tcf i = factorDifference ε hε h hh i (tf i) ∧
      ‖ctf i-tcf i‖ ≤ |h| * ‖tf i‖ := by
  have hf := (commonClockDomain_iff ε hε h v l f).mpr
    ⟨cf,hc,(commonEnergyDomain_iff ε hε h v l cf).mpr
      (fun i => LinearPMap.mem_domain_of_mem_graph (htc i))⟩
  obtain ⟨cf',tf',tcf',ctf',hc',hall⟩ := commonClockDomain_graphs ε hε h hh v l f hf
  have ec : cf' = cf := (clockOperator ε hε).mem_graph_snd_inj' hc' hc rfl
  subst cf'
  intro i
  obtain ⟨ht',htc',hct',he,hb⟩ := hall i
  have et : tf' i = tf i := (energyFactor ε hε h v l i).mem_graph_snd_inj' ht' (ht i) rfl
  have etc : tcf' i = tcf i := (energyFactor ε hε h v l i).mem_graph_snd_inj' htc' (htc i) rfl
  have ect : ctf' i = ctf i := (clockOperator ε hε).mem_graph_snd_inj' hct' (hct i) et
  simpa only [et,etc,ect] using And.intro he hb

/-- Arbitrary complex energy weights preserve the relative L2 output bound. -/
theorem weighted_output_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (w : Fin 8 → ℂ) (g : Fin 8 → Hilbert) :
    ‖(WithLp.toLp 2 (fun i => w i • factorDifference ε hε h hh i (g i)) : Output (Fin 8) Hilbert)‖ ≤
      |h| * ‖(WithLp.toLp 2 (fun i => w i • g i) : Output (Fin 8) Hilbert)‖ := by
  let a : Output (Fin 8) Hilbert := WithLp.toLp 2 (fun i => w i • factorDifference ε hε h hh i (g i))
  let b : Output (Fin 8) Hilbert := WithLp.toLp 2 (fun i => w i • g i)
  have hp (i : Fin 8) : ‖a i‖ ≤ |h| * ‖b i‖ := by
    change ‖w i • factorDifference ε hε h hh i (g i)‖ ≤ |h| * ‖w i • g i‖
    rw [norm_smul,norm_smul]
    calc
      _ ≤ ‖w i‖*(|h| * ‖g i‖) :=
        mul_le_mul_of_nonneg_left (factorDifference_norm ε hε h hh i (g i)) (norm_nonneg _)
      _ = _ := by ring
  have hs : ‖a‖^2 ≤ (|h| * ‖b‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hp i) 2
  change ‖a‖ ≤ |h| * ‖b‖
  exact (sq_le_sq₀ (norm_nonneg a) (mul_nonneg (abs_nonneg h) (norm_nonneg b))).mp hs

#print axioms factorDifference_norm
#print axioms clock_factorAction_graph
#print axioms commonClockDomain_dense
#print axioms commonClockDomain_iff
#print axioms commonClockDomain_graphs
#print axioms commutator_graph
#print axioms weighted_output_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator
