/- The original finite charged response has the exact cooling-kernel
half-plane marginal. Cross terms and all half-line boundary terms are
included in the evaluated moments. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingMarginalDerivative
import UnifiedTheory.Audit.KFCausalChargedCoolingResponseMoments
import UnifiedTheory.Audit.KFCausalCorrelatedFourierCoolingResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingResponseMarginal
noncomputable section
open MeasureTheory Matrix
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingPhysicalMarginal
open KFCausalChargedCoolingResponseMoments
open KFCausalChargedCoolingMarginalDerivative (coolingForm marginalSlope)
open KFCausalChargedFourierPolynomialGram (atom width)
open KFCausalChargedCoolingFixedV (dissipation)
open KFCausalChargedCoolingWidthPositive (widthSum coolingB coolingC)
open KFCausalReciprocalWedgeGeometry (gamma chart)
open KFCausalQuarticPlaneDomination (potential potentialSlope)

def atomSlope (p q : ℂ) (w u v Y : ℝ) : ℂ :=
  -(w:ℂ)*(q*((u:ℂ)^2+(v:ℂ)^2)+conj q*(Y:ℂ))*atom p w 0 0 u v Y

def packetSlope (n : ℕ) (p q : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (u v Y : ℝ) : ℂ := ∑ i, c i*atomSlope p q (w i) u v Y

def packetResponse (n : ℕ) (p q : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (u v Y : ℝ) : ℝ :=
  2*(conj (packetSum n p w c u v Y)*packetSlope n p q w c u v Y).re

def crossResponse (p q : ℂ) (w z v : ℝ) : (ℝ × ℝ) → ℂ :=
  responseDensity (width p w z) (conj (width p w z))
    (width q w z) (conj (width q w z)) v

theorem response_density_factor (S T Sd Td : ℂ) (u v Y : ℝ) :
    responseDensity S T Sd Td v (u,Y) =
      -(Sd*((u:ℂ)^2+(v:ℂ)^2)+Td*(Y:ℂ))*planeMoment S T 0 0 v (u,Y) := by
  unfold responseDensity planeMoment KFCausalComplexGaussianMoments.moment laplaceMoment
  simp only [pow_zero,pow_one,one_mul]
  ring

theorem plane_moment_atom (p : ℂ) (w z u v Y : ℝ) :
    planeMoment (width p w z) (conj (width p w z)) 0 0 v (u,Y) =
      conj (atom p w 0 0 u v Y)*atom p z 0 0 u v Y := by
  have he := KFCausalChargedFourierPolynomialGram.atom_cross p w z 0 0 0 u v Y
  simpa only [KFCausalChargedFourierGaussianMoments.density,
    KFCausalShiftedComplexGaussianMoments.moment,planeMoment,
    KFCausalComplexGaussianMoments.moment,laplaceMoment,zero_add,pow_zero,
    one_mul,Complex.ofReal_zero,zero_mul,add_zero] using he.symm

theorem atom_response_cross (p q : ℂ) (w z u v Y : ℝ) :
    conj (atom p w 0 0 u v Y)*atomSlope p q z u v Y+
      conj (atomSlope p q w u v Y)*atom p z 0 0 u v Y =
      crossResponse p q w z v (u,Y) := by
  rw [crossResponse,response_density_factor,plane_moment_atom]
  unfold atomSlope width
  simp only [map_mul,map_neg,map_add,map_pow,starRingEnd_self_apply,Complex.conj_ofReal]
  ring

theorem packet_response_expansion (n : ℕ) (p q : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (u v Y : ℝ) :
    (packetResponse n p q w c u v Y:ℂ) =
      ∑ i, ∑ j, (conj (c i)*c j)*crossResponse p q (w i) (w j) v (u,Y) := by
  have he : (packetResponse n p q w c u v Y:ℂ) =
      conj (packetSum n p w c u v Y)*packetSlope n p q w c u v Y+
      conj (packetSlope n p q w c u v Y)*packetSum n p w c u v Y := by
    unfold packetResponse
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  rw [he]
  unfold packetSum packetSlope
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← atom_response_cross]
  ring

theorem cross_response_integrable (p q : ℂ) (w z v : ℝ) (hp : 0 < p.re)
    (hw : 0 < w) (hz : 0 < z) : Integrable (crossResponse p q w z v) planeMeasure := by
  have hS := KFCausalChargedFourierPolynomialGram.width_positive p w z hp hw hz
  exact response_density_integrable _ _ _ _ hS (by simpa only [Complex.conj_re] using hS) v

theorem cross_response_integral (p q : ℂ) (w z v : ℝ) (hp : 0 < p.re)
    (hw : 0 < w) (hz : 0 < z) :
    (∫ t, crossResponse p q w z v t ∂planeMeasure) =
      -(Real.sqrt Real.pi:ℂ)*dissipation (conj p) (conj q) w z v := by
  have hS := KFCausalChargedFourierPolynomialGram.width_positive p w z hp hw hz
  rw [crossResponse,response_density_integral _ _ _ _ hS (by simpa only [Complex.conj_re] using hS) v]
  unfold dissipation coolingB coolingC widthSum width
  simp only [map_add,map_mul,Complex.conj_ofReal,starRingEnd_self_apply,Complex.ofReal_pow]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev]
  ring

theorem packet_response_integrable (n : ℕ) (p q : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Integrable (fun t : ℝ × ℝ => packetResponse n p q w c t.1 v t.2) planeMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (cross_response_integrable p q (w i) (w j) v hp (hw i) (hw j)).const_mul (conj (c i)*c j)))
  have hc : Integrable (fun t : ℝ × ℝ => (packetResponse n p q w c t.1 v t.2:ℂ)) planeMeasure :=
    hi.congr (Filter.Eventually.of_forall (fun t => (packet_response_expansion n p q w c t.1 v t.2).symm))
  exact hc.re

theorem packet_response_integral (n : ℕ) (p q : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    (∫ t : ℝ × ℝ, packetResponse n p q w c t.1 v t.2 ∂planeMeasure) =
      -Real.sqrt Real.pi*(star c ⬝ᵥ ((fun i j => dissipation (conj p) (conj q) (w i) (w j) v) *ᵥ c)).re := by
  have he : (∫ t : ℝ × ℝ, (packetResponse n p q w c t.1 v t.2:ℂ) ∂planeMeasure) =
      -(Real.sqrt Real.pi:ℂ)*(star c ⬝ᵥ ((fun i j => dissipation (conj p) (conj q) (w i) (w j) v) *ᵥ c)) := by
    simp_rw [packet_response_expansion]
    rw [integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ =>
        (cross_response_integrable p q (w i) (w j) v hp (hw i) (hw j)).const_mul (conj (c i)*c j)))]
    simp only [Matrix.mulVec,dotProduct,Pi.star_apply,Complex.star_def,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum Finset.univ (fun j _ =>
      (cross_response_integrable p q (w i) (w j) v hp (hw i) (hw j)).const_mul (conj (c i)*c j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,cross_response_integral p q (w i) (w j) v hp (hw i) (hw j)]
    ring
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re,Complex.mul_re,Complex.neg_re,Complex.ofReal_im,
    Complex.neg_im,neg_zero,zero_mul,sub_zero] using hr

#print axioms response_density_factor
#print axioms plane_moment_atom
#print axioms atom_response_cross
#print axioms packet_response_expansion
#print axioms cross_response_integrable
#print axioms cross_response_integral
#print axioms packet_response_integrable
#print axioms packet_response_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingResponseMarginal
