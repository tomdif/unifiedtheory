/- The explicit cross kernel is the actual Gram form of arbitrary finite
complex superpositions. Its Hermitian symmetry and positivity follow
from the integral, including coincident widths and exact cancellation.
No uniform response bound is inferred from the diagonal entries. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalCrossGram
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalGaussianCoordinates (exponent area)
open KFCausalReciprocalCrossKernel (density kernel)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalMatterOrderedDomain (pointField)
open scoped ComplexConjugate

theorem density_conj (α β w v : ℝ) (r : ℂ) (q : Transverse) :
    conj (density α β w v r q) = density α β v w r q := by
  simp only [density,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]
  ring

theorem kernel_conj (α β w v : ℝ) (r : ℂ) :
    conj (kernel α β w v r) = kernel α β v w r := by
  rw [kernel,← integral_conj]
  simp_rw [density_conj]
  rfl

theorem density_diagonal (α β w : ℝ) (r : ℂ) (q : Transverse) :
    density α β w w r q = (KFCausalReciprocalGaussianKernel.physicalDensity α β w r q:ℂ) := by
  simp only [density,KFCausalReciprocalGaussianKernel.physicalDensity,
    Complex.conj_mul',Complex.ofReal_mul,Complex.ofReal_pow]

theorem kernel_diagonal (α β w : ℝ) (r : ℂ) :
    kernel α β w w r = (KFCausalReciprocalGaussianKernel.kernel α β w r:ℂ) := by
  simp only [kernel,density_diagonal,integral_complex_ofReal,KFCausalReciprocalGaussianKernel.kernel]

def packetSum (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c : Fin n → ℂ)
    (q : Transverse) : ℂ := ∑ i, c i*Complex.exp (exponent α β (w i) r q)
def pairDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c d : Fin n → ℂ)
    (q : Transverse) : ℂ :=
  (potential (pointField q):ℂ)*(conj (packetSum n α β w r c q)*packetSum n α β w r d q)
def pairing (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (c d : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, (conj (c i)*d j)*kernel α β (w i) (w j) r

theorem pairDensity_expansion (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c d : Fin n → ℂ) (q : Transverse) :
    pairDensity n α β w r c d q =
      ∑ i, ∑ j, (conj (c i)*d j)*density α β (w i) (w j) r q := by
  unfold pairDensity packetSum
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold density
  ring

theorem pairDensity_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c d : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    Integrable (pairDensity n α β w r c d) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (KFCausalReciprocalCrossKernel.density_integrable α β (w i) (w j) r
        (hw i) (hw j) hA hC hβ).const_mul (conj (c i)*d j)))
  exact hi.congr (Filter.Eventually.of_forall (fun q => (pairDensity_expansion n α β w r c d q).symm))

theorem pairing_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c d : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    pairing n α β w r c d = ∫ q, pairDensity n α β w r c d q := by
  simp_rw [pairDensity_expansion]
  have hi := fun i j =>
    (KFCausalReciprocalCrossKernel.density_integrable α β (w i) (w j) r
      (hw i) (hw j) hA hC hβ).const_mul (conj (c i)*d j)
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j),integral_const_mul]
  rfl

theorem pairing_norm_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    pairing n α β w r c c =
      (∫ q, potential (pointField q)*‖packetSum n α β w r c q‖^2:ℝ) := by
  rw [pairing_integral n α β w r c c hw hA hC hβ]
  simp only [pairDensity,Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_mul,
    integral_complex_ofReal]

theorem pairing_nonneg (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    0 ≤ (pairing n α β w r c c).re := by
  rw [pairing_norm_integral n α β w r c hw hA hC hβ,Complex.ofReal_re]
  apply integral_nonneg
  intro q
  unfold potential
  positivity

theorem pairing_real (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (hw : ∀ i, 1 ≤ w i)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    (pairing n α β w r c c).im = 0 := by
  rw [pairing_norm_integral n α β w r c hw hA hC hβ,Complex.ofReal_im]

#print axioms density_conj
#print axioms kernel_conj
#print axioms density_diagonal
#print axioms kernel_diagonal
#print axioms pairDensity_expansion
#print axioms pairDensity_integrable
#print axioms pairing_integral
#print axioms pairing_norm_integral
#print axioms pairing_nonneg
#print axioms pairing_real
end
end UnifiedTheory.Audit.KFCausalReciprocalCrossGram
