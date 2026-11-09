/- A positive joint integral represents the entire neutral/reciprocal
Gram form, retaining all finite interference. General integrability
hypotheses are discharged for the actual packet family separately. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveForm
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralKernel (neutral planeDensity kernel)
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure jointDensity weight)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalReciprocalWedgeGeometry (chart)
open KFCausalReciprocalWedgeLaplace (laplaceSum)

def profileSum (n : ℕ) (w : Fin n → ℝ) (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ)
    (z ζ : ℂ) : ℂ := laplaceSum n w (fun i => c i*F i ζ) z

def positiveDensity (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ) (p : Joint) : ℝ :=
  weight β r p*‖profileSum n w c F (chart α r (p.1.1^2+(p.1.2 0)^2) p.2)
    (neutral r (p.1.2 0) (p.1.2 1))‖^2

def pairing (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c d : Fin n → ℂ) (F : Fin n → ℂ → ℂ) : ℂ :=
  ∑ i, ∑ j, (conj (c i)*d j)*kernel α β (w i) (w j) r (F i) (F j)

theorem positiveDensity_nonneg (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ) (p : Joint) :
    0 ≤ positiveDensity n α β w r c F p :=
  mul_nonneg (KFCausalReciprocalNeutralLaplace.weight_positive β r p).le (sq_nonneg _)

theorem density_expansion (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ) (p : Joint) :
    (positiveDensity n α β w r c F p:ℂ) =
      ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
        jointDensity β (B α (w i) (w j) r) (C α β (w i) (w j) r) r (F i) (F j) p := by
  unfold positiveDensity profileSum
  rw [Complex.ofReal_mul,KFCausalReciprocalWedgeLaplace.laplaceSum_norm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [KFCausalReciprocalNeutralLaplace.joint_factor]
  simp only [map_mul]
  ring

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
  (c : Fin n → ℂ) (F : Fin n → ℂ → ℂ)
  (hB : ∀ i j, 0 < (B α (w i) (w j) r).re)
  (hi : ∀ i j, Integrable (planeDensity β (C α β (w i) (w j) r) r (F i) (F j)))

include hB hi in
theorem positiveDensity_integrable : Integrable (positiveDensity n α β w r c F) jointMeasure := by
  have ht (i j : Fin n) : Integrable (fun p => ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
      jointDensity β (B α (w i) (w j) r) (C α β (w i) (w j) r) r (F i) (F j) p) jointMeasure :=
    (KFCausalReciprocalNeutralLaplace.joint_integrable _ _ _ _ _ _ (hB i j) (hi i j)).const_mul _
  have hs := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => ht i j))
  have he : Integrable (fun p => (positiveDensity n α β w r c F p:ℂ)) jointMeasure :=
    hs.congr (Filter.Eventually.of_forall (fun p => (density_expansion n α β w r c F p).symm))
  exact he.re

include hB hi in
theorem density_integral :
    (∫ p, (positiveDensity n α β w r c F p:ℂ) ∂jointMeasure) =
      ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
        ∫ p, jointDensity β (B α (w i) (w j) r) (C α β (w i) (w j) r) r (F i) (F j) p ∂jointMeasure := by
  have ht (i j : Fin n) : Integrable (fun p => ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
      jointDensity β (B α (w i) (w j) r) (C α β (w i) (w j) r) r (F i) (F j) p) jointMeasure :=
    (KFCausalReciprocalNeutralLaplace.joint_integrable _ _ _ _ _ _ (hB i j) (hi i j)).const_mul _
  simp_rw [density_expansion]
  rw [integral_finset_sum Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => ht i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => ht _ j),integral_const_mul]

include hB hi in
theorem pairing_integral (hw : ∀ i, w i ≠ 0) (hA : ∀ i j, 0 < (A α (w i) (w j) r).re) :
    pairing n α β w r c c F =
      ((Real.pi/4*(∫ p, positiveDensity n α β w r c F p ∂jointMeasure):ℝ):ℂ) := by
  rw [Complex.ofReal_mul,← integral_complex_ofReal,density_integral n α β w r c F hB hi]
  unfold pairing
  simp_rw [KFCausalReciprocalNeutralLaplace.kernel_joint α β _ _ (hw _) (hw _) r _ _ (hA _ _) (hB _ _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

include hB hi in
theorem pairing_nonnegative (hw : ∀ i, w i ≠ 0) (hA : ∀ i j, 0 < (A α (w i) (w j) r).re) :
    0 ≤ (pairing n α β w r c c F).re := by
  rw [pairing_integral n α β w r c F hB hi hw hA,Complex.ofReal_re]
  exact mul_nonneg (by positivity) (integral_nonneg (positiveDensity_nonneg n α β w r c F))

#print axioms positiveDensity_nonneg
#print axioms density_expansion
#print axioms positiveDensity_integrable
#print axioms density_integral
#print axioms pairing_integral
#print axioms pairing_nonnegative
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveForm
