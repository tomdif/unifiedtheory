/- The complete original Joint integral for arbitrary finite charged widths
and neutral exponential sources is an explicit quartic Wick kernel. All
cross terms and the original measure normalization are retained. Polynomial
source differentiation and the uniform response inequality are not asserted. -/
import UnifiedTheory.Audit.KFCausalGaussianSourcePlaneKernel
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveForm
import UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianSourceJointKernel
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalCrossGeometry (B C)
open KFCausalReciprocalNeutralKernel (neutral planeDensity)
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure jointDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalGaussianSourcePlaneKernel (formula)

def sourceV (r si sj : ℂ) : ℂ := (2*r.im:ℝ)*Complex.I*(sj-conj si)
def sourceX (si sj : ℂ) : ℂ := conj si+sj

def pairKernel (α β w v : ℝ) (r si sj : ℂ) : ℂ :=
  gaussianValue (B α w v r)*
    formula (C α β w v r) (2*(β:ℂ)) (sourceV r si sj) (sourceX si sj) (fieldSlope r)/
      conj (B α w v r)

def familyForm (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (b c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    pairKernel α β (w i) (w j) r (b i) (b j)

theorem plane_identity (β : ℝ) (H r si sj : ℂ) (u : Fin 2 → ℝ) :
    planeDensity β H r (exponentialProfile si 1 1) (exponentialProfile sj 1 1) u =
      KFCausalGaussianSourcePlaneKernel.density H (2*(β:ℂ))
        (sourceV r si sj) (sourceX si sj) (fieldSlope r) u := by
  simp only [planeDensity,exponentialProfile,Polynomial.eval_one,mul_one,one_mul,
    ← Complex.exp_conj,map_mul,neutral,sourceV,sourceX,
    KFCausalGaussianSourcePlaneKernel.density]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat,
    mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem plane_integrable (β : ℝ) (H r si sj : ℂ) (hβ : 0 < β) (hH : 0 < H.re) :
    Integrable (planeDensity β H r (exponentialProfile si 1 1) (exponentialProfile sj 1 1)) := by
  change Integrable (fun u => planeDensity β H r
    (exponentialProfile si 1 1) (exponentialProfile sj 1 1) u)
  simp_rw [plane_identity]
  exact KFCausalGaussianSourcePlaneKernel.density_integrable _ _ _ _ hH
    (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hβ)) _

theorem pair_integral (α β w v : ℝ) (r si sj : ℂ) (hβ : 0 < β)
    (hB : 0 < (B α w v r).re) (hC : 0 < (C α β w v r).re) :
    (∫ p, jointDensity β (B α w v r) (C α β w v r) r
      (exponentialProfile si 1 1) (exponentialProfile sj 1 1) p ∂jointMeasure) =
        pairKernel α β w v r si sj := by
  rw [KFCausalReciprocalNeutralLaplace.joint_integral _ _ _ _ _ _ hB]
  simp_rw [plane_identity]
  rw [KFCausalGaussianSourcePlaneKernel.density_integral _ _ _ _ hC
    (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hβ))]
  rfl

theorem pair_floors (α β w v : ℝ) (r : ℂ) (hβ : 0 < β)
    (hw : 0 < (w*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2)
    (hv : 0 < (v*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    0 < (B α w v r).re ∧ 0 < (C α β w v r).re := by
  have hp : 0 ≤ 8*β*r.im^2 := mul_nonneg (by positivity) (sq_nonneg _)
  rw [KFCausalReciprocalCrossGeometry.B_re]
  simp only [C,Complex.sub_re,Complex.ofReal_re,KFCausalReciprocalCrossGeometry.B_re]
  constructor <;> nlinarith

theorem family_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (b c : Fin n → ℂ) (hβ : 0 < β)
    (hw : ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    Integrable (positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 1)) jointMeasure := by
  apply KFCausalReciprocalNeutralPositiveForm.positiveDensity_integrable
  · intro i j
    exact (pair_floors α β (w i) (w j) r hβ (hw i) (hw j)).1
  · intro i j
    exact plane_integrable β _ r (b i) (b j) hβ
      (pair_floors α β (w i) (w j) r hβ (hw i) (hw j)).2

theorem family_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (b c : Fin n → ℂ) (hβ : 0 < β)
    (hw : ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    (∫ p, (positiveDensity n α β w r c
      (fun i => exponentialProfile (b i) 1 1) p:ℂ) ∂jointMeasure) =
        familyForm n α β w r b c := by
  have hf (i j : Fin n) := pair_floors α β (w i) (w j) r hβ (hw i) (hw j)
  rw [KFCausalReciprocalNeutralPositiveForm.density_integral n α β w r c
    (fun i => exponentialProfile (b i) 1 1) (fun i j => (hf i j).1)
    (fun i j => plane_integrable β _ r (b i) (b j) hβ (hf i j).2)]
  unfold familyForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pair_integral α β (w i) (w j) r (b i) (b j) hβ (hf i j).1 (hf i j).2]

theorem familyForm_nonnegative (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (b c : Fin n → ℂ) (hβ : 0 < β)
    (hw : ∀ i, 0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area r-8*β*r.im^2) :
    0 ≤ (familyForm n α β w r b c).re := by
  rw [← family_integral n α β w r b c hβ hw,integral_complex_ofReal,Complex.ofReal_re]
  exact integral_nonneg
    (KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg n α β w r c _)

#print axioms plane_identity
#print axioms plane_integrable
#print axioms pair_integral
#print axioms pair_floors
#print axioms family_integrable
#print axioms family_integral
#print axioms familyForm_nonnegative
end
end UnifiedTheory.Audit.KFCausalGaussianSourceJointKernel
