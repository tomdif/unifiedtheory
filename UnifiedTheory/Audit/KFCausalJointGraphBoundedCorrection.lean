/- Bounded input, output and state-correction maps pass a factorwise
product rule through the actual simultaneous weighted graph closure.
Zero weights impose no artificial domain conditions. -/
import UnifiedTheory.Audit.KFCausalFiniteJointGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
noncomputable section
open UnifiedTheory.Audit.KFCausalFiniteJointGraph

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype ι]

def outputMap (B : ι → H →L[ℂ] H) : Output ι H →L[ℂ] Output ι H where
  toFun y := WithLp.toLp 2 (fun i => B i (y i))
  map_add' f g := by ext i; simp only [PiLp.add_apply,map_add]
  map_smul' a f := by ext i; simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (B i).continuous.comp (PiLp.continuous_apply 2 _ i)))

def correctionMap (C : ι → H →L[ℂ] H) (c : ι → ℂ) : H →L[ℂ] Output ι H where
  toFun f := WithLp.toLp 2 (fun i => c i • C i f)
  map_add' f g := by ext i; simp only [PiLp.add_apply,map_add,smul_add]
  map_smul' a f := by ext i; simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]; exact smul_comm _ _ _
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => continuous_const.smul (C i).continuous))

def pairMap (M : H →L[ℂ] H) (B C : ι → H →L[ℂ] H) (c : ι → ℂ) :
    (H × Output ι H) →L[ℂ] (H × Output ι H) :=
  (M.comp (ContinuousLinearMap.fst ℂ H (Output ι H))).prod
    ((outputMap B).comp (ContinuousLinearMap.snd ℂ H (Output ι H))+
      (correctionMap C c).comp (ContinuousLinearMap.fst ℂ H (Output ι H)))

variable (T : ι → H →ₗ.[ℂ] H) (M : H →L[ℂ] H) (B C : ι → H →L[ℂ] H)
  (hA : ∀ i f g, (f,g) ∈ (T i).graph → (M f,B i g+C i f) ∈ (T i).graph)

include hA in
theorem joint_graph (c : ι → ℂ) (f : H) (g : Output ι H)
    (hfg : (f,g) ∈ jointGraph T c) :
    (M f,outputMap B g+correctionMap C c f) ∈ jointGraph T c := by
  intro i
  have he := hA i (c i • f) (g i) (hfg i)
  change (c i • M f,B i (g i)+c i • C i f) ∈ (T i).graph
  simpa only [map_smul] using he

include hA in
theorem joint_closure (c : ι → ℂ) (f : H) (g : Output ι H)
    (hfg : (f,g) ∈ (jointGraph T c).topologicalClosure) :
    (M f,outputMap B g+correctionMap C c f) ∈ (jointGraph T c).topologicalClosure := by
  let S := jointGraph T c
  let P := pairMap M B C c
  have hS : S ≤ S.topologicalClosure.comap P.toLinearMap := by
    rintro ⟨x,y⟩ hxy
    exact S.le_topologicalClosure (joint_graph T M B C hA c x y hxy)
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage P.continuous) hfg

theorem outputMap_norm (R : ℝ) (hR : 0 ≤ R) (hB : ∀ i f, ‖B i f‖ ≤ R*‖f‖) (g : Output ι H) :
    ‖outputMap B g‖ ≤ R*‖g‖ := by
  have hs : ‖outputMap B g‖^2 ≤ (R*‖g‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (pow_le_pow_left₀ (norm_nonneg _) (hB i (g i)) 2).trans_eq (by rw [mul_pow])
  nlinarith [norm_nonneg (outputMap B g),mul_nonneg hR (norm_nonneg g)]

#print axioms joint_graph
#print axioms joint_closure
#print axioms outputMap_norm

end
end UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection
