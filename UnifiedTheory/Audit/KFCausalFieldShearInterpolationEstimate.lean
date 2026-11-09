/- Field-weighted interpolation for finite complex Gaussian superpositions.
The commutator cost is retained, integrated, and finite. The lower bound
does not assert positivity or Hamiltonian-energy control of the endpoints. -/
import UnifiedTheory.Audit.KFCausalFieldShearPathGraphs
import UnifiedTheory.Audit.KFCausalScalarIntegratingFactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFieldShearInterpolationEstimate
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed graph_sum)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator)
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2) {n : ℕ} (s : Fin n → Seed) (z : Fin n → ℂ)

def field (t : ℝ) : Hilbert := ∑ k, z k • state ε h hε hb (s k) (fieldWeight l i) t
def first (t : ℝ) : Hilbert := ∑ k, z k • firstState ε h hε hb (s k) (fieldWeight l i) t
def derivativeField (t : ℝ) : Hilbert := ∑ k, z k • state ε h hε hb (s k) (slopeWeight l i) t
def shear (t : ℝ) : Hilbert := ∑ k, z k • fieldShear ε h hε hb (s k) l i t
def firstOutput (t : Interval) : Hilbert := ∑ k, z k • firstShear ε h hε hb (s k) l i t

local notation "U" => field ε h hε hb l i s z
local notation "V" => first ε h hε hb l i s z
local notation "E" => derivativeField ε h hε hb l i s z
local notation "J" => shear ε h hε hb l i s z
local notation "K" => firstOutput ε h hε hb l i s z

theorem field_graph_sum (t : Interval) :
    (KFCausalImaginaryShearSuperposition.sumInput ε h hε hb s z t,U t) ∈ (fieldPower l i).graph := by
  have hs := (fieldPower l i).graph.sum_mem (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    (fieldPower l i).graph.smul_mem (z k) (field_graph ε h hε hb (s k) l i t))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

theorem curves_continuous : Continuous U ∧ Continuous J ∧ Continuous E := by
  refine ⟨?_,?_,?_⟩
  · exact continuous_finset_sum _ (fun k _ =>
      (KFCausalActualPolynomialShearCurve.input_continuous (fieldWeight l i) ε (s k).a (s k).p h (s k).α (s k).β
        hε (s k).ha (s k).hα (s k).hβ (s k).hw hb (s k).b).const_smul (z k))
  · exact continuous_finset_sum _ (fun k _ =>
      (fieldShear_continuous ε h hε hb (s k) l i).const_smul (z k))
  · exact continuous_finset_sum _ (fun k _ =>
      (KFCausalActualPolynomialShearCurve.input_continuous (slopeWeight l i) ε (s k).a (s k).p h (s k).α (s k).β
        hε (s k).ha (s k).hα (s k).hβ (s k).hw hb (s k).b).const_smul (z k))

theorem shear_identity (t : ℝ) : J t = V t+(-Complex.I*(h:ℂ)) • E t := by
  unfold shear fieldShear first derivativeField
  simp only [smul_add,Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (z k)]

variable (hh : h ≠ 0)
local notation "C" => coefficientOperator ε h hε hb hh

include hh in
theorem shear_graph_sum (t : Interval) : (U t,J t) ∈ (shearMomentum h).graph :=
  graph_sum h z _ _ (fun k => field_shear_graph ε h hε hb (s k) l i hh t)

include hh in
theorem first_graph_sum (t : Interval) : (V t,K t) ∈ (shearMomentum h).graph :=
  graph_sum h z _ _ (fun k => first_shear_graph ε h hε hb (s k) l i hh t)

theorem field_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt U (C (V t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    (KFCausalActualPolynomialShearCurve.input_strong_derivative (fieldWeight l i) ε (s k).a (s k).p h (s k).α (s k).β
      hε (s k).ha (s k).hα (s k).hβ (s k).hw hb (s k).b hh t ht).const_smul (z k))
  simpa only [field,first,state,firstState,map_sum,map_smul] using hd

theorem shear_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt J (C (K ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    (fieldShear_derivative ε h hε hb (s k) l i hh t ht).const_smul (z k))
  simpa only [shear,firstOutput,map_sum,map_smul] using hd

variable (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
  (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hW in
theorem expectation_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (expectation W U J) (2*(inner ℂ (W (J t)) (C (W (V t)))).re) t :=
  KFCausalForcedShearVariation.forced_expectation_derivative ε h hε hb hh W w hW U J (V t)
    (K ⟨t,ht.1.le,ht.2.le⟩) t (field_derivative ε h hε hb l i s z hh t ht)
    (shear_derivative ε h hε hb l i s z hh t ht)
    (shear_graph_sum ε h hε hb l i s z hh ⟨t,ht.1.le,ht.2.le⟩)
    (first_graph_sum ε h hε hb l i s z hh ⟨t,ht.1.le,ht.2.le⟩)

include hh hW in
theorem expectation_derivative_lower (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    -(h^2/(4*ε))*‖W (E t)‖^2 ≤ deriv (expectation W U J) t := by
  apply KFCausalForcedShearVariation.forced_expectation_lower ε h hε hb hh W w hW U J (V t)
    (K ⟨t,ht.1.le,ht.2.le⟩) (E t) t (field_derivative ε h hε hb l i s z hh t ht)
    (shear_derivative ε h hε hb l i s z hh t ht)
    (shear_graph_sum ε h hε hb l i s z hh ⟨t,ht.1.le,ht.2.le⟩)
    (first_graph_sum ε h hε hb l i s z hh ⟨t,ht.1.le,ht.2.le⟩)
  rw [shear_identity,add_assoc,← add_smul]
  simp only [show -Complex.I*(h:ℂ)+Complex.I*(h:ℂ) = 0 by ring,zero_smul,add_zero]

omit hh w hW in
theorem cost_continuous : Continuous (fun t => ‖W (E t)‖^2) :=
  (W.continuous.comp (curves_continuous ε h hε hb l i s z).2.2).norm.pow 2

include hh hW in
theorem endpoint_comparison :
    expectation W U J 0-(h^2/(4*ε))*(∫ t in (0:ℝ)..1, ‖W (E t)‖^2) ≤ expectation W U J 1 := by
  let M : ℝ → ℝ := fun t => ‖W (E t)‖^2
  have hM : Continuous M := cost_continuous ε h hε hb l i s z W
  let B := KFCausalScalarIntegratingFactor.primitive M
  have hB (t : ℝ) : HasDerivAt B (M t) t := KFCausalScalarIntegratingFactor.primitive_derivative M hM t
  have hBc : Continuous B := (show Differentiable ℝ B from fun t => (hB t).differentiableAt).continuous
  have hQ := KFCausalClockShearPositiveVariation.expectation_continuous W U J
    (curves_continuous ε h hε hb l i s z).1 (curves_continuous ε h hε hb l i s z).2.1
  have hmon : MonotoneOn (fun t => expectation W U J t+(h^2/(4*ε))*B t) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (hQ.add (continuous_const.mul hBc)).continuousOn
      (f' := fun t => deriv (expectation W U J) t+(h^2/(4*ε))*M t)
    · intro t ht
      rw [interior_Icc] at ht
      have hd := expectation_derivative ε h hε hb l i s z hh W w hW t ht
      rw [← hd.deriv] at hd
      exact (hd.add ((hB t).const_mul (h^2/(4*ε)))).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hl := expectation_derivative_lower ε h hε hb l i s z hh W w hW t ht
      change -(h^2/(4*ε))*M t ≤ _ at hl
      linarith
  have he := hmon (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num : (0:ℝ) ≤ 1)
  change expectation W U J 0+(h^2/(4*ε))*(∫ t in (0:ℝ)..0, M t) ≤
    expectation W U J 1+(h^2/(4*ε))*(∫ t in (0:ℝ)..1, M t) at he
  rw [intervalIntegral.integral_same,mul_zero,add_zero] at he
  linarith only [he]

#print axioms field_graph_sum
#print axioms curves_continuous
#print axioms shear_identity
#print axioms shear_graph_sum
#print axioms first_graph_sum
#print axioms field_derivative
#print axioms shear_derivative
#print axioms expectation_derivative
#print axioms expectation_derivative_lower
#print axioms cost_continuous
#print axioms endpoint_comparison
end
end UnifiedTheory.Audit.KFCausalFieldShearInterpolationEstimate
