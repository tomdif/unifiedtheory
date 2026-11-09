/- The weighted ordered potential kernel and its exact response.
The physical weights are vacuum, mass squared/2 and quartic/4. All
finite polynomial cross terms and the actual clock derivative survive. -/
import UnifiedTheory.Audit.KFCausalPolynomialLocalSuperposition
import UnifiedTheory.Audit.KFCausalPolynomialLocalGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalPolynomialLocalSuperposition (combination)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient pair)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (clockFrequency)

def physicalWeights (mass2 quartic vacuum : ℝ) : Fin 3 → ℝ := ![vacuum,mass2/2,quartic/4]

variable (ε h : ℝ) (q k : Joint 2 4) (w : Fin 3 → ℝ) (P Q : Polynomial ℂ)

def kernel (s : ℝ) : ℂ := ∑ n : Fin 3, (w n:ℂ)*localKernel ε h q k P Q n s
def kernelDerivative (s : ℝ) : ℂ := ∑ n : Fin 3, (w n:ℂ)*localDerivative ε h q k P Q n s
def reducedResponse (s : ℝ) : ℂ :=
  (coefficient ε (-h/2) s:ℂ)*kernel ε h q k w P Q s-
    kernelDerivative ε h q k w P Q s/(clock ε s:ℂ)
def response (a s : ℝ) : ℂ :=
  pair ε a a (clockFrequency h k) (clockFrequency h k) (-h/2) s*
    reducedResponse ε h q k w P Q s

theorem physical_kernel (mass2 quartic vacuum s : ℝ) :
    kernel ε h q k (physicalWeights mass2 quartic vacuum) P Q s =
      (vacuum:ℂ)*localKernel ε h q k P Q 0 s+
        ((mass2/2:ℝ):ℂ)*localKernel ε h q k P Q 1 s+
          ((quartic/4:ℝ):ℂ)*localKernel ε h q k P Q 2 s := by
  simp only [kernel,physicalWeights,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero,Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  ring

theorem response_sum (a s : ℝ) :
    response ε h q k w P Q a s =
      ∑ n : Fin 3, (w n:ℂ)*KFCausalProjectedPolynomialLocalResponse.response ε a h q k P Q n s := by
  unfold response reducedResponse kernel kernelDerivative KFCausalProjectedPolynomialLocalResponse.response
  simp only [Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hb in
theorem kernel_derivative (s : ℝ) :
    HasDerivAt (kernel ε h q k w P Q) (kernelDerivative ε h q k w P Q s) s :=
  HasDerivAt.fun_sum (fun n _ => (localKernel_derivative ε h q k P Q n hε hh hb s).const_mul (w n:ℂ))

include hε hh hb in
theorem reducedResponse_eq_deriv (s : ℝ) :
    reducedResponse ε h q k w P Q s =
      (coefficient ε (-h/2) s:ℂ)*kernel ε h q k w P Q s-
        deriv (kernel ε h q k w P Q) s/(clock ε s:ℂ) := by
  rw [(kernel_derivative ε h q k w P Q hε hh hb s).deriv]
  rfl

include hε hh hb in
theorem kernel_conj (s : ℝ) :
    star (kernel ε h q k w P Q s) = kernel ε h q k w Q P s := by
  unfold kernel
  simp only [star_sum,star_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Complex.star_def,KFCausalPolynomialLocalGram.localKernel_conj ε h q k P Q n hε hh hb]
  ring

include hε hh hb in
omit Q in
theorem kernel_self_nonnegative (hw : ∀ n, 0 ≤ w n) (s : ℝ) :
    0 ≤ (kernel ε h q k w P P s).re := by
  simp only [kernel,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (hw n)
    (KFCausalPolynomialLocalGram.localKernel_self_nonnegative ε h q k P n hε hh hb s))

include hε hh hb in
theorem kernelDerivative_conj (s : ℝ) :
    star (kernelDerivative ε h q k w P Q s) = kernelDerivative ε h q k w Q P s := by
  have hi := (kernel_derivative ε h q k w P Q hε hh hb s).star
  have he : (fun t => star (kernel ε h q k w P Q t)) = kernel ε h q k w Q P :=
    funext (kernel_conj ε h q k w P Q hε hh hb)
  rw [he] at hi
  exact hi.unique (kernel_derivative ε h q k w Q P hε hh hb s)

include hε hh hb in
theorem reducedResponse_conj (s : ℝ) :
    star (reducedResponse ε h q k w P Q s) = reducedResponse ε h q k w Q P s := by
  unfold reducedResponse
  simp only [star_sub,star_mul,star_div₀,Complex.star_def,Complex.conj_ofReal]
  rw [← Complex.star_def,kernel_conj ε h q k w P Q hε hh hb,
    kernelDerivative_conj ε h q k w P Q hε hh hb]
  ring

include hε hh hb in
theorem response_integrable (a : ℝ) (ha : 0 < a) : Integrable (response ε h q k w P Q a) volume := by
  have hi := integrable_finset_sum Finset.univ (fun n _ =>
    (KFCausalProjectedPolynomialLocalResponse.response_integrable ε a h q k P Q n hε ha hh hb).const_mul (w n:ℂ))
  exact hi.congr (Filter.Eventually.of_forall (fun s => (response_sum ε h q k w P Q a s).symm))

include hε hh hb in
omit Q in
theorem response_integral (a : ℝ) (ha : 0 < a) :
    (∫ s, response ε h q k w P P a s) =
      ∑ n : Fin 3, (w n:ℂ)*
        (KFCausalDisplacedPolynomialProjectedResponse.factorRate ε a h hε ha hh hb q k P
          (KFCausalSourcedResponseFactorBridge.index n):ℂ) := by
  simp_rw [response_sum ε h q k w P P a]
  rw [integral_finset_sum Finset.univ (fun n _ =>
    (KFCausalProjectedPolynomialLocalResponse.response_integrable ε a h q k P P n hε ha hh hb).const_mul (w n:ℂ))]
  simp_rw [integral_const_mul,
    KFCausalProjectedPolynomialLocalResponse.response_integral_factorRate ε a h q k P _ hε ha hh hb]

variable {I J : Type*} (S : Finset I) (T : Finset J)
  (U : I → Polynomial ℂ) (V : J → Polynomial ℂ) (c : I → ℂ) (d : J → ℂ)

include hε hh hb in
omit P Q in
theorem kernel_combination (s : ℝ) :
    kernel ε h q k w (combination S U c) (combination T V d) s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*kernel ε h q k w (U i) (V j) s := by
  unfold kernel
  simp_rw [KFCausalPolynomialLocalSuperposition.localKernel_combination S T U V c d ε h q k _ hε hh hb]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro n _
  ring

include hε hh hb in
omit P Q in
theorem kernelDerivative_combination (s : ℝ) :
    kernelDerivative ε h q k w (combination S U c) (combination T V d) s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*kernelDerivative ε h q k w (U i) (V j) s := by
  have he : kernel ε h q k w (combination S U c) (combination T V d) =
      fun t => ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*kernel ε h q k w (U i) (V j) t :=
    funext (kernel_combination ε h q k w hε hh hb S T U V c d)
  have hi := kernel_derivative ε h q k w (combination S U c) (combination T V d) hε hh hb s
  rw [he] at hi
  exact hi.unique (HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ =>
    (kernel_derivative ε h q k w (U i) (V j) hε hh hb s).const_mul (star (c i)*d j))))

include hε hh hb in
omit P Q in
theorem reducedResponse_combination (s : ℝ) :
    reducedResponse ε h q k w (combination S U c) (combination T V d) s =
      ∑ i ∈ S, ∑ j ∈ T, (star (c i)*d j)*reducedResponse ε h q k w (U i) (V j) s := by
  unfold reducedResponse
  rw [kernel_combination ε h q k w hε hh hb S T U V c d,
    kernelDerivative_combination ε h q k w hε hh hb S T U V c d]
  simp only [Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms physical_kernel
#print axioms response_sum
#print axioms kernel_derivative
#print axioms reducedResponse_eq_deriv
#print axioms kernel_conj
#print axioms kernel_self_nonnegative
#print axioms kernelDerivative_conj
#print axioms reducedResponse_conj
#print axioms response_integrable
#print axioms response_integral
#print axioms kernel_combination
#print axioms kernelDerivative_combination
#print axioms reducedResponse_combination
end
end UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse
