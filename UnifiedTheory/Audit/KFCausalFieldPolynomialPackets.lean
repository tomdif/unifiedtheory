/- Exact dilation/shear decomposition of every transverse linear field,
and Schwartz packets multiplied by its two polynomial coefficients. -/
import UnifiedTheory.Audit.KFCausalTransversePositionMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
noncomputable section
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalSchwartzTransversePacket

def constantPart : Transverse →L[ℝ] Transverse where
  toFun x i := if i=4 then x 4-2*(x 2+x 3) else 0
  map_add' := by intro x y; funext i; by_cases hi : i=4 <;> simp [hi]; ring
  map_smul' := by intro c x; funext i; by_cases hi : i=4 <;> simp [hi,smul_eq_mul]; ring
  cont := by apply continuous_pi; intro i; by_cases hi : i=4 <;> simp only [hi,ite_true,ite_false] <;> fun_prop

def scalePart : Transverse →L[ℝ] Transverse where
  toFun x i := if i=4 then 2*(x 2+x 3) else x i
  map_add' := by intro x y; funext i; by_cases hi : i=4 <;> simp [hi]; ring
  map_smul' := by intro c x; funext i; by_cases hi : i=4 <;> simp [hi,smul_eq_mul]; ring
  cont := by apply continuous_pi; intro i; by_cases hi : i=4 <;> simp only [hi,ite_true,ite_false] <;> fun_prop

theorem flow_decomposition (t : ℝ) (x : Transverse) :
    flow t x=constantPart x+scale t • scalePart x := by
  funext i
  by_cases hi : i=4 <;> simp [flow,constantPart,scalePart,hi]; ring

def constantField (l : Transverse →L[ℝ] ℝ) : TailSpace →L[ℝ] ℝ :=
  l.comp (constantPart.comp transverseLinearEquiv.symm.toContinuousLinearMap)
def scaleField (l : Transverse →L[ℝ] ℝ) : TailSpace →L[ℝ] ℝ :=
  l.comp (scalePart.comp transverseLinearEquiv.symm.toContinuousLinearMap)

theorem field_flow_decomposition (l : Transverse →L[ℝ] ℝ) (t : ℝ) (x : Transverse) :
    l (flow t x)=constantField l (transverseCoordinates x)+scale t*scaleField l (transverseCoordinates x) := by
  rw [flow_decomposition,map_add,map_smul]
  rfl

def polynomialPacket (l : Transverse →L[ℝ] ℝ) (i j : ℕ) (ψ : SchwartzMap TailSpace ℂ) :
    SchwartzMap TailSpace ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (constantField l x:ℂ)^i*(scaleField l x:ℂ)^j) ψ

theorem polynomialPacket_apply (l : Transverse →L[ℝ] ℝ) (i j : ℕ)
    (ψ : SchwartzMap TailSpace ℂ) (x : TailSpace) :
    polynomialPacket l i j ψ x=(constantField l x:ℂ)^i*(scaleField l x:ℂ)^j*ψ x := by
  have hc : (fun x => (constantField l x:ℂ)).HasTemperateGrowth :=
    (Complex.ofRealCLM.comp (constantField l)).hasTemperateGrowth
  have hs : (fun x => (scaleField l x:ℂ)).HasTemperateGrowth :=
    (Complex.ofRealCLM.comp (scaleField l)).hasTemperateGrowth
  have hp := (hc.pow i).mul (hs.pow j)
  simpa only [polynomialPacket,smul_eq_mul] using SchwartzMap.smulLeftCLM_apply_apply hp ψ x

#print axioms flow_decomposition
#print axioms field_flow_decomposition
#print axioms polynomialPacket_apply

end
end UnifiedTheory.Audit.KFCausalFieldPolynomialPackets
