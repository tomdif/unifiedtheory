/- Full charged-variable differentiation for finite sums of the actual
dilated exponential-polynomial packets. All local integrable domination
is derived from their Gaussian/Laplace widths and polynomial prefactors. -/
import UnifiedTheory.Audit.KFCausalCorrelatedDilationPolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedDilationDifferentiation
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalCorrelatedDilationPolynomials

variable (m : ℕ) (degree : Fin m → ℕ) (j : ℕ) (α : Fin m → ℝ) (β ell : ℝ)
  (r : ℂ) (b c : Fin m → ℂ) (P : Fin m → Polynomial ℂ)

def value (t : ℝ) (p : Joint) : ℂ :=
  ∑ i, c i*packet (degree i) j (α i) β ell r (b i) (P i) t p

def slope (t : ℝ) (p : Joint) : ℂ :=
  ∑ i, c i*packetSlope (degree i) j (α i) β ell r (b i) (P i) t p

def response (t : ℝ) (p : Joint) : ℝ :=
  2*(conj (value m degree j α β ell r b c P t p)*slope m degree j α β ell r b c P t p).re

theorem value_derivative (t : ℝ) (p : Joint) :
    HasDerivAt (fun s => value m degree j α β ell r b c P s p)
      (slope m degree j α β ell r b c P t p) t :=
  HasDerivAt.fun_sum (fun i _ => (packet_derivative (degree i) j (α i) β ell r (b i) (P i) t p).const_mul (c i))

theorem value_continuous (t : ℝ) : Continuous (value m degree j α β ell r b c P t) := by
  unfold value packet prefactor field KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Z
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.G
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem slope_continuous (t : ℝ) : Continuous (slope m degree j α β ell r b c P t) := by
  unfold slope packetSlope prefactorSlope field fieldVelocity KFCausalClusteredClockFactors.E
    KFCausalClusteredClockFactors.Ed KFCausalClusteredClockFactors.Z KFCausalClusteredClockFactors.Zd
    KFCausalClusteredClockFactors.N KFCausalClusteredClockFactors.Nd KFCausalClusteredClockFactors.G
    KFCausalClusteredClockFactors.Gd KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem response_continuous (t : ℝ) : Continuous (response m degree j α β ell r b c P t) :=
  continuous_const.mul (Complex.continuous_re.comp
    ((Complex.continuous_conj.comp (value_continuous m degree j α β ell r b c P t)).mul
      (slope_continuous m degree j α β ell r b c P t)))

theorem density_pointwise_derivative (t : ℝ) (p : Joint) :
    HasDerivAt (fun s => ‖value m degree j α β ell r b c P s p‖^2)
      (response m degree j α β ell r b c P t p) t :=
  KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun s => value m degree j α β ell r b c P s p)
    (fun s => slope m degree j α β ell r b c P s p) t
    (value_derivative m degree j α β ell r b c P t p)

variable (hβ : 0 < β) (hA : ∀ i, 0 < α i*area r) (hC : ∀ i, 0 < α i*area r-8*β*r.im^2)
include hβ hA hC

theorem finite_envelope :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ t ∈ Set.Icc (-1:ℝ) 1, ∀ p, 0 ≤ p.2 →
        ‖value m degree j α β ell r b c P t p‖^2+
          ‖slope m degree j α β ell r b c P t p‖^2 ≤ D p := by
  choose D hDi hD0 hD using fun i => packet_pair_envelope (degree i) j (α i) β ell r (b i) (P i) hβ (hA i) (hC i)
  refine ⟨fun p => (m:ℝ)*∑ i, ‖c i‖^2*D i p,
    (integrable_finset_sum Finset.univ (fun i _ => (hDi i).const_mul _)).const_mul _,?_,?_⟩
  · intro p
    exact mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hD0 i p)))
  · intro t ht p hp
    exact KFCausalCorrelatedClusteredBounds.sum_pair_bound m c _ _ _ (fun i => hD i t ht p hp)

theorem density_integrable (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Integrable (fun p => ‖value m degree j α β ell r b c P t p‖^2) jointMeasure := by
  obtain ⟨D,hDi,_,hD⟩ := finite_envelope m degree j α β ell r b c P hβ hA hC
  apply hDi.mono' ((value_continuous m degree j α β ell r b c P t).norm.pow 2).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (le_add_of_nonneg_right (sq_nonneg _)).trans (hD t ht p hp)

theorem integral_derivative :
    HasDerivAt (fun t => ∫ p, ‖value m degree j α β ell r b c P t p‖^2 ∂jointMeasure)
      (∫ p, response m degree j α β ell r b c P 0 p ∂jointMeasure) 0 := by
  obtain ⟨D,hDi,_,hD⟩ := finite_envelope m degree j α β ell r b c P hβ hA hC
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t p => ‖value m degree j α β ell r b c P t p‖^2)
    (F' := response m degree j α β ell r b c P) (bound := D)
    (Icc_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun t =>
      ((value_continuous m degree j α β ell r b c P t).norm.pow 2).aestronglyMeasurable))
    (density_integrable m degree j α β ell r b c P hβ hA hC 0 (by constructor <;> norm_num))
    (response_continuous m degree j α β ell r b c P 0).aestronglyMeasurable
    ?_ hDi (Eventually.of_forall (fun p t _ => density_pointwise_derivative m degree j α β ell r b c P t p))
  · exact hd.2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    intro t ht
    exact (KFCausalCorrelatedClusteredBounds.cross_bound _ _).trans (hD t ht p hp)

#print axioms value_derivative
#print axioms value_continuous
#print axioms slope_continuous
#print axioms response_continuous
#print axioms density_pointwise_derivative
#print axioms finite_envelope
#print axioms density_integrable
#print axioms integral_derivative
end
end UnifiedTheory.Audit.KFCausalCorrelatedDilationDifferentiation
