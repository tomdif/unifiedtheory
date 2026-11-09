/- Actual field-weighted Gaussian boundaries vanish in transverse L1.
The finite-clock weak/reduced response difference also vanishes in L1,
before and after transverse integration. Packet constants are not uniform
over states, and no Hamiltonian evolution or response lower bound follows. -/
import UnifiedTheory.Audit.KFCausalGaussianSliceEnvelope
import UnifiedTheory.Audit.KFCausalClockBoundaryDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalIntegratedGaussianBoundary
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalGaussianSliceEnvelope
  (slice slice_memLp slice_square_bound squareConstant squareConstant_nonnegative)
open UnifiedTheory.Audit.KFCausalGaussianKernelResponse (kernel kernelDerivative actual_kernel_interval)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock pair weakPair reduced)

variable (ε y α β α' β' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)

def weightedKernel (s : ℝ) (q : Transverse) : ℂ :=
  star (slice ε y α β b C l n s q)*slice ε y α' β' c D l n s q

def cost : ℝ := (squareConstant ε y α β b C l+squareConstant ε y α' β' c D l)/2

def boundary (a a' p p' s : ℝ) (q : Transverse) : ℂ :=
  weightedKernel ε y α β α' β' b c C D l n s q*
    KFCausalClockBoundaryDecay.boundary ε a a' p p' y s

def intervalDifference (a a' p p' R : ℝ) (q : Transverse) : ℂ :=
  (l q:ℂ)^(2*n.val)*
    ((∫ s in -R..R, kernel ε y α β α' β' b c C D q s*weakPair ε a a' p p' y s)-
     ∫ s in -R..R, reduced ε a a' p p' y
       (kernel ε y α β α' β' b c C D q) (kernelDerivative ε y α β α' β' b c C D q) s)

theorem cost_nonnegative : 0 ≤ cost ε y α β α' β' b c C D l := by
  unfold cost
  linarith [squareConstant_nonnegative ε y α β b C l,
    squareConstant_nonnegative ε y α' β' c D l]

theorem weightedKernel_eq (s : ℝ) (q : Transverse) :
    weightedKernel ε y α β α' β' b c C D l n s q =
      (l q:ℂ)^(2*n.val)*kernel ε y α β α' β' b c C D q s := by
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  simp only [weightedKernel,slice,kernel,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
  ring

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hα' : 0 < α') (hβ' : 0 < β') (hw' : 32*β' ≤ α')

include hε hy hα hβ hw hα' hβ' hw' in
theorem weightedKernel_integrable (s : ℝ) :
    Integrable (weightedKernel ε y α β α' β' b c C D l n s) volume :=
  (slice_memLp ε y α β b C l n s hε hy hα hβ hw).star.integrable_mul
    (slice_memLp ε y α' β' c D l n s hε hy hα' hβ' hw')

include hε hy hα hβ hw hα' hβ' hw' in
theorem weightedKernel_norm_bound (s : ℝ) :
    (∫ q, ‖weightedKernel ε y α β α' β' b c C D l n s q‖) ≤
      cost ε y α β α' β' b c C D l := by
  have hu := slice_memLp ε y α β b C l n s hε hy hα hβ hw
  have hv := slice_memLp ε y α' β' c D l n s hε hy hα' hβ' hw'
  have hi := (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  have hj := (memLp_two_iff_integrable_sq_norm hv.1).mp hv
  have hk := weightedKernel_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' s
  calc
    _ ≤ ∫ q, (‖slice ε y α β b C l n s q‖^2+‖slice ε y α' β' c D l n s q‖^2)/2 :=
      integral_mono hk.norm ((hi.add hj).div_const 2) (fun q => by
        simp only [weightedKernel,norm_mul,norm_star]
        nlinarith [sq_nonneg (‖slice ε y α β b C l n s q‖-‖slice ε y α' β' c D l n s q‖)])
    _ = ((∫ q, ‖slice ε y α β b C l n s q‖^2)+
      ∫ q, ‖slice ε y α' β' c D l n s q‖^2)/2 := by
      rw [integral_div,integral_add hi hj]
    _ ≤ _ := by
      unfold cost
      linarith [slice_square_bound ε y α β b C l n s hε hy hα hβ hw,
        slice_square_bound ε y α' β' c D l n s hε hy hα' hβ' hw']

include hε hy hα hβ hw hα' hβ' hw' in
theorem boundary_integrable (a a' p p' s : ℝ) :
    Integrable (boundary ε y α β α' β' b c C D l n a a' p p' s) volume :=
  (weightedKernel_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' s).mul_const _

include hε hy hα hβ hw hα' hβ' hw' in
theorem boundary_norm_bound (a a' p p' s : ℝ) :
    (∫ q, ‖boundary ε y α β α' β' b c C D l n a a' p p' s q‖) ≤
      cost ε y α β α' β' b c C D l*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ := by
  simp only [boundary,norm_mul]
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right
    (weightedKernel_norm_bound ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' s) (norm_nonneg _)

include hε hy hα hβ hw hα' hβ' hw' in
theorem boundary_gaussian_bound (a a' p p' s : ℝ) (ha : 0 < a+a') :
    (∫ q, ‖boundary ε y α β α' β' b c C D l n a a' p p' s q‖) ≤
      (cost ε y α β α' β' b c C D l*KFCausalClockBoundaryDecay.constant ε a a' p p' y)*
        Real.exp (-KFCausalClockBoundaryDecay.decay ε a a'*s^2) := by
  calc
    _ ≤ _ := boundary_norm_bound ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' s
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (KFCausalClockBoundaryDecay.boundary_bound ε a a' p p' y s hε ha hy)
        (cost_nonnegative ε y α β α' β' b c C D l)

include hε hy hα hβ hw hα' hβ' hw' in
private theorem boundary_norm_limit (a a' p p' : ℝ) (f : Filter ℝ)
    (hb : Tendsto (KFCausalClockBoundaryDecay.boundary ε a a' p p' y) f (𝓝 0)) :
    Tendsto (fun s => ∫ q, ‖boundary ε y α β α' β' b c C D l n a a' p p' s q‖) f (𝓝 0) := by
  apply squeeze_zero (fun s => integral_nonneg (fun q => norm_nonneg _))
    (boundary_norm_bound ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p')
  simpa using hb.norm.const_mul (cost ε y α β α' β' b c C D l)

include hε hy hα hβ hw hα' hβ' hw' in
theorem boundary_norm_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun s => ∫ q, ‖boundary ε y α β α' β' b c C D l n a a' p p' s q‖) atTop (𝓝 0) :=
  boundary_norm_limit ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' atTop
    (KFCausalClockBoundaryDecay.boundary_atTop ε a a' p p' y hε ha hy)

include hε hy hα hβ hw hα' hβ' hw' in
theorem boundary_norm_atBot (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun s => ∫ q, ‖boundary ε y α β α' β' b c C D l n a a' p p' s q‖) atBot (𝓝 0) :=
  boundary_norm_limit ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' atBot
    (KFCausalClockBoundaryDecay.boundary_atBot ε a a' p p' y hε ha hy)

include hε hy in
theorem intervalDifference_eq (a a' p p' R : ℝ) (q : Transverse) :
    intervalDifference ε y α β α' β' b c C D l n a a' p p' R q =
      boundary ε y α β α' β' b c C D l n a a' p p' R q-
      boundary ε y α β α' β' b c C D l n a a' p p' (-R) q := by
  unfold intervalDifference
  rw [actual_kernel_interval ε y a a' p p' α β α' β' b c C D q hε hy (-R) R]
  simp only [boundary,weightedKernel_eq,KFCausalClockBoundaryDecay.boundary,add_sub_cancel_right]
  ring

include hε hy hα hβ hw hα' hβ' hw' in
theorem intervalDifference_integrable (a a' p p' R : ℝ) :
    Integrable (intervalDifference ε y α β α' β' b c C D l n a a' p p' R) volume := by
  change Integrable (fun q => intervalDifference ε y α β α' β' b c C D l n a a' p p' R q) volume
  simp_rw [intervalDifference_eq ε y α β α' β' b c C D l n hε hy]
  exact (boundary_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' R).sub
    (boundary_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' (-R))

include hε hy hα hβ hw hα' hβ' hw' in
theorem intervalDifference_norm_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R => ∫ q, ‖intervalDifference ε y α β α' β' b c C D l n a a' p p' R q‖)
      atTop (𝓝 0) := by
  have ht := (boundary_norm_atTop ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha).add
    ((boundary_norm_atBot ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha).comp
      tendsto_neg_atTop_atBot)
  simp only [add_zero] at ht
  apply squeeze_zero (fun R => integral_nonneg (fun q => norm_nonneg _)) _ ht
  intro R
  have hi := boundary_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' R
  have hj := boundary_integrable ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' (-R)
  simp_rw [intervalDifference_eq ε y α β α' β' b c C D l n hε hy]
  exact (integral_mono (hi.sub hj).norm (hi.norm.add hj.norm) (fun q => norm_sub_le _ _)).trans_eq
    (integral_add hi.norm hj.norm)

include hε hy hα hβ hw hα' hβ' hw' in
theorem integrated_difference_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R => ∫ q, intervalDifference ε y α β α' β' b c C D l n a a' p p' R q)
      atTop (𝓝 0) :=
  squeeze_zero_norm (fun _ => norm_integral_le_integral_norm _)
    (intervalDifference_norm_atTop ε y α β α' β' b c C D l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha)

#print axioms cost_nonnegative
#print axioms weightedKernel_eq
#print axioms weightedKernel_integrable
#print axioms weightedKernel_norm_bound
#print axioms boundary_integrable
#print axioms boundary_norm_bound
#print axioms boundary_gaussian_bound
#print axioms boundary_norm_atTop
#print axioms boundary_norm_atBot
#print axioms intervalDifference_eq
#print axioms intervalDifference_integrable
#print axioms intervalDifference_norm_atTop
#print axioms integrated_difference_atTop
end
end UnifiedTheory.Audit.KFCausalIntegratedGaussianBoundary
