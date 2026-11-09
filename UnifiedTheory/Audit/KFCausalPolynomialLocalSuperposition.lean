/- Finite complex superpositions in the actual projected local kernel.
The double sums retain cross terms. Derivative superposition follows
from uniqueness of the already proved derivative under the integral. -/
import UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPolynomialLocalSuperposition
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalPolynomialLocalKernel (Domain measure)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalResponse (response)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor)

variable {I J : Type*} (S : Finset I) (T : Finset J)
  (U : I → Polynomial ℂ) (V : J → Polynomial ℂ) (c : I → ℂ) (d : J → ℂ)

def combination : Polynomial ℂ := ∑ i ∈ S, c i • U i

theorem factor_combination (ε y α β : ℝ) (b : Fin 5 → ℂ) (C : ℂ)
    (l : Transverse →L[ℝ] ℝ) (n : ℕ) (x : Transverse) (s : ℝ) :
    factor ε y α β b C (combination S U c) l n x s =
      ∑ i ∈ S, c i*factor ε y α β b C (U i) l n x s := by
  simp only [combination,factor,KFCausalPolynomialKernelResponse.transverse,
    KFCausalPolynomialKernelResponse.weight,Polynomial.eval_finset_sum,Polynomial.eval_smul,
    smul_eq_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc,mul_left_comm]

variable (ε h : ℝ) (q k : Joint 2 4) (n : Fin 3)

theorem value_combination (s : ℝ) (z : Domain) :
    value ε h q k (combination S U c) (combination T V d) n s z =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*value ε h q k (U i) (V j) n s z := by
  unfold value KFCausalPolynomialLocalKernel.value
  rw [factor_combination,factor_combination]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [Finset.sum_comm]

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hb in
theorem localKernel_combination (s : ℝ) :
    localKernel ε h q k (combination S U c) (combination T V d) n s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*localKernel ε h q k (U i) (V j) n s := by
  have hi (i : I) (j : J) := (value_integrable ε h q k (U i) (V j) n hε hh hb s).const_mul (star (c i)*d j)
  unfold localKernel
  simp_rw [value_combination S T U V c d]
  rw [integral_finset_sum S (fun i _ => integrable_finset_sum T (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum T (fun j _ => hi i j)]
  simp only [integral_const_mul]

include hε hh hb in
theorem localDerivative_combination (s : ℝ) :
    localDerivative ε h q k (combination S U c) (combination T V d) n s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*localDerivative ε h q k (U i) (V j) n s := by
  have he : localKernel ε h q k (combination S U c) (combination T V d) n =
      fun t => ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*localKernel ε h q k (U i) (V j) n t :=
    funext (localKernel_combination S T U V c d ε h q k n hε hh hb)
  have hi := localKernel_derivative ε h q k (combination S U c) (combination T V d) n hε hh hb s
  rw [he] at hi
  exact hi.unique (HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ =>
    (localKernel_derivative ε h q k (U i) (V j) n hε hh hb s).const_mul (star (c i)*d j))))

include hε hh hb in
theorem response_combination (a s : ℝ) :
    response ε a h q k (combination S U c) (combination T V d) n s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*response ε a h q k (U i) (V j) n s := by
  unfold response
  rw [localKernel_combination S T U V c d ε h q k n hε hh hb,
    localDerivative_combination S T U V c d ε h q k n hε hh hb]
  simp only [Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms factor_combination
#print axioms value_combination
#print axioms localKernel_combination
#print axioms localDerivative_combination
#print axioms response_combination
end
end UnifiedTheory.Audit.KFCausalPolynomialLocalSuperposition
