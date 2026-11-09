/- Coefficients of the literal physical clock metric on the canonical
complex Euclidean basis. Contractions retain the bilinear transpose
already proved for the actual shear. -/
import UnifiedTheory.Audit.KFCausalPhysicalClockMetric

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPhysicalClockMetricCoefficients
noncomputable section
open scoped ComplexConjugate
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalPhysicalComplexShearMetric (transposeFlow gram)
open KFCausalPhysicalClockMetric (metric shiftedClock)
open KFCausalPairedModeCoordinates (scale)

def basis (j : Fin 5) : Space := WithLp.toLp 2 (Pi.single j 1)

def flowLinear (σ : ℝ) (δ : ℂ) : Space →ₗ[ℂ] Space where
  toFun := flow σ δ
  map_add' x y := by
    ext i
    fin_cases i <;> simp [flow] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [flow] <;> ring

def transposeLinear (σ : ℝ) (δ : ℂ) : Space →ₗ[ℂ] Space where
  toFun := transposeFlow σ δ
  map_add' x y := by
    ext i
    fin_cases i <;> simp [transposeFlow] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [transposeFlow] <;> ring

def metricLinear (ε s : ℝ) (δ : ℂ) : Space →ₗ[ℂ] Space :=
  (shiftedClock ε s δ)⁻¹ •
    ((flowLinear (2*scale) (-δ)).comp (transposeLinear (2*scale) (-δ)))

theorem metricLinear_apply (ε s : ℝ) (δ : ℂ) (x : Space) :
    metricLinear ε s δ x=metric ε s δ x := rfl

theorem basis_expansion (x : Space) : x=∑j:Fin 5,x j • basis j := by
  ext i
  simp [basis,Pi.single_apply]

def coefficient (ε s : ℝ) (δ : ℂ) (i j : Fin 5) : ℂ := metric ε s δ (basis j) i

theorem metric_apply (ε s : ℝ) (δ : ℂ) (x : Space) (i : Fin 5) :
    metric ε s δ x i=∑j:Fin 5,coefficient ε s δ i j*x j := by
  have he := congrArg (metricLinear ε s δ) (basis_expansion x)
  rw [map_sum] at he
  simp only [map_smul,metricLinear_apply] at he
  have hi := congrArg (fun y:Space=>y i) he
  simpa only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,mul_comm,coefficient] using hi

theorem inner_contraction (ε s : ℝ) (δ : ℂ) (u v : Space) :
    (∑ij:Fin 5×Fin 5,coefficient ε s δ ij.1 ij.2*conj (u ij.1)*v ij.2)=
      inner ℂ u (metric ε s δ v) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,metric_apply,Finset.sum_mul,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms metricLinear_apply
#print axioms basis_expansion
#print axioms metric_apply
#print axioms inner_contraction
end
end UnifiedTheory.Audit.KFCausalPhysicalClockMetricCoefficients
