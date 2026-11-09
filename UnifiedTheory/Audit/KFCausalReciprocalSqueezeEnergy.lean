/- Exact reciprocal-squeeze law on all eight natural factors and their
simultaneously closed energy graph. The output norm records both kinetic
pairs and both matter terms. Charge averaging and a dynamical virial
identity still require additional proofs. -/
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeMatter
import UnifiedTheory.Audit.KFCausalReciprocalSqueezeKinetic
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalReciprocalSqueezeEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeTransport (transport transport_reverse)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeKinetic (kineticScale model_kinetic_graph half_graph)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeMatter (linear_matter_graph quadratic_matter_graph)
open UnifiedTheory.Audit.KFCausalReciprocalSqueezeExponential (ordered_graph_squeeze)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

def degree : Fin 8 → ℝ := ![0,1,-1,-1,1,1,2,0]
def factorScale (a : ℝ) (i : Fin 8) : ℂ := Real.exp (degree i*a)

theorem factor_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ)
    (i : Fin 8) (f g : Hilbert)
    (hfg : (f,g) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
    (transport a f,factorScale a i • transport a g) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  fin_cases i
  · simpa [factorScale,degree] using half_graph ε a f g hfg
  · simpa [factorScale,degree,kineticScale] using model_kinetic_graph ε h a 0 f g hfg
  · simpa [factorScale,degree,kineticScale] using model_kinetic_graph ε h a 1 f g hfg
  · simpa [factorScale,degree,kineticScale] using model_kinetic_graph ε h a 2 f g hfg
  · simpa [factorScale,degree,kineticScale] using model_kinetic_graph ε h a 3 f g hfg
  · simpa [factorScale,degree] using linear_matter_graph ε hε h a f g hfg
  · exact quadratic_matter_graph ε hε h a f g hfg
  · simpa [factorScale,degree] using ordered_graph_squeeze ε hε h a f g hfg

theorem common_domain (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (f : Hilbert) :
    transport a f ∈ commonEnergyDomain ε hε h modelDirections pointField ↔
      f ∈ commonEnergyDomain ε hε h modelDirections pointField := by
  have forward (b : ℝ) (v : Hilbert)
      (hv : v ∈ commonEnergyDomain ε hε h modelDirections pointField) :
      transport b v ∈ commonEnergyDomain ε hε h modelDirections pointField := by
    apply (commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr
    intro i
    exact LinearPMap.mem_domain_of_mem_graph (factor_graph ε hε h b i v _
      ((energyFactor ε hε h modelDirections pointField i).mem_graph
        ⟨v,(commonEnergyDomain_iff ε hε h modelDirections pointField v).mp hv i⟩))
  constructor
  · intro hf
    simpa only [transport_reverse] using forward (-a) _ hf
  · exact forward a f

def outputAction (a : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => factorScale a i • transport a (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add,smul_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
    exact smul_comm _ _ _
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => ((transport a).continuous.comp
      (PiLp.continuous_apply 2 _ i)).const_smul (factorScale a i)))

theorem outputAction_apply (a : ℝ) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    outputAction a g i = factorScale a i • transport a (g i) := rfl

theorem outputAction_norm_square (a : ℝ) (g : Output (Fin 8) Hilbert) :
    ‖outputAction a g‖^2 = ∑ i : Fin 8, Real.exp (2*degree i*a)*‖g i‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  simp only [outputAction_apply,norm_smul,LinearIsometryEquiv.norm_map,factorScale,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
  congr 2
  ring

theorem outputAction_norm_derivative (a : ℝ) (g : Output (Fin 8) Hilbert) :
    HasDerivAt (fun b => ‖outputAction b g‖^2)
      (∑ i : Fin 8, Real.exp (2*degree i*a)*(2*degree i)*‖g i‖^2) a := by
  have hi (i : Fin 8) :
      HasDerivAt (fun b => Real.exp (2*degree i*b)*‖g i‖^2)
        (Real.exp (2*degree i*a)*(2*degree i)*‖g i‖^2) a := by
    simpa only [id_eq,mul_one] using
      (((hasDerivAt_id a).const_mul (2*degree i)).exp.mul_const (‖g i‖^2))
  simpa only [outputAction_norm_square] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i))

theorem outputAction_norm_derivative_zero (g : Output (Fin 8) Hilbert) :
    HasDerivAt (fun b => ‖outputAction b g‖^2)
      (2*(‖g 1‖^2-‖g 2‖^2-‖g 3‖^2+‖g 4‖^2+‖g 5‖^2+2*‖g 6‖^2)) 0 := by
  convert outputAction_norm_derivative 0 g using 1
  simp [degree,Fin.sum_univ_succ]
  ring

theorem joint_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (c : Fin 8 → ℂ)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ jointGraph (energyFactor ε hε h modelDirections pointField) c) :
    (transport a f,outputAction a g) ∈
      jointGraph (energyFactor ε hε h modelDirections pointField) c := by
  intro i
  have he := factor_graph ε hε h a i (c i • f) (g i) (hfg i)
  simpa only [map_smul,outputAction_apply] using he

theorem closed_joint_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (c : Fin 8 → ℂ)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure) :
    (transport a f,outputAction a g) ∈
      (jointGraph (energyFactor ε hε h modelDirections pointField) c).topologicalClosure := by
  let K := jointGraph (energyFactor ε hε h modelDirections pointField) c
  let P := (transport a : Hilbert →L[ℂ] Hilbert).prodMap (outputAction a)
  have hK : K ≤ K.topologicalClosure.comap P.toLinearMap := by
    rintro ⟨x,y⟩ hxy
    exact K.le_topologicalClosure (joint_graph ε hε h a c x y hxy)
  exact K.topologicalClosure_minimal hK (K.isClosed_topologicalClosure.preimage P.continuous) hfg

theorem closed_energy_graph (ε : ℝ) (hε : 0 < ε) (h a : ℝ)
    (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ)
    (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h modelDirections pointField m q k t).graph) :
    (transport a f,outputAction a g) ∈
      (closedEnergy ε hε h modelDirections pointField m q k t).graph := by
  rw [closedEnergy_graph ε hε h modelDirections pointField m q k t hb] at hfg ⊢
  exact closed_joint_graph ε hε h a _ f g hfg

theorem closed_energy_domain (ε : ℝ) (hε : 0 < ε) (h a : ℝ)
    (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ) (f : Hilbert) :
    transport a f ∈ (closedEnergy ε hε h modelDirections pointField m q k t).domain ↔
      f ∈ (closedEnergy ε hε h modelDirections pointField m q k t).domain := by
  constructor
  · intro hf
    have hg := closed_energy_graph ε hε h (-a) hb m q k t _ _
      ((closedEnergy ε hε h modelDirections pointField m q k t).mem_graph ⟨_,hf⟩)
    rw [transport_reverse] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg
  · intro hf
    exact LinearPMap.mem_domain_of_mem_graph (closed_energy_graph ε hε h a hb m q k t f _
      ((closedEnergy ε hε h modelDirections pointField m q k t).mem_graph ⟨f,hf⟩))

theorem closed_energy_output (ε : ℝ) (hε : 0 < ε) (h a : ℝ)
    (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ)
    (f : Hilbert) (g z : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h modelDirections pointField m q k t).graph)
    (hfz : (transport a f,z) ∈
      (closedEnergy ε hε h modelDirections pointField m q k t).graph) :
    z = outputAction a g := by
  exact (closedEnergy ε hε h modelDirections pointField m q k t).mem_graph_snd_inj'
    hfz (closed_energy_graph ε hε h a hb m q k t f g hfg) rfl

#print axioms factor_graph
#print axioms common_domain
#print axioms outputAction_apply
#print axioms outputAction_norm_square
#print axioms outputAction_norm_derivative
#print axioms outputAction_norm_derivative_zero
#print axioms joint_graph
#print axioms closed_joint_graph
#print axioms closed_energy_graph
#print axioms closed_energy_domain
#print axioms closed_energy_output

end
end UnifiedTheory.Audit.KFCausalReciprocalSqueezeEnergy
