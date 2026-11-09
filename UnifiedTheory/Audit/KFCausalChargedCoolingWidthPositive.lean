/- Positive semidefiniteness of the actual correlated-width cooling kernels. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingWidthGeometry
import UnifiedTheory.Audit.KFCausalChargedCoolingActualPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingWidthPositive
noncomputable section
open scoped Topology BigOperators ComplexOrder
open KFCausalChargedCoolingWidthGeometry KFCausalChargedCoolingCoshRatio
open KFCausalPositiveKernelExponential KFCausalChargedCoolingActualPhase

variable {n : Type*} [Fintype n]

theorem exponential_diagonal_positive (c d : ℝ) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => (Real.exp (c-d*(x i+x j)):ℂ)) := by
  have he (i j : n) : starRingEnd ℂ (Real.exp (c/2-d*x i):ℂ)*
      (Real.exp (c/2-d*x j):ℂ) = (Real.exp (c-d*(x i+x j)):ℂ) := by
    rw [Complex.conj_ofReal,← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  simpa only [Matrix.vecMulVec,Pi.star_apply,Complex.star_def,he] using
    Matrix.posSemidef_vecMulVec_star_self (fun i => (Real.exp (c/2-d*x i):ℂ))

theorem phase_widthB_positive (ρ σ θ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => widthB ρ σ θ (x i) (x j)) := by
  have h := schur_positive (exponential_diagonal_positive (normalization false ρ σ θ) (1/2) x)
    (ratioB_positive θ hθ (fun i => -x i))
  convert h using 1
  ext i j
  rw [widthB_transport ρ σ θ (x i) (x j) hρ hσ hθ]
  congr 2 <;> ring

theorem phase_widthC_positive (ρ σ θ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => widthC ρ σ θ (x i) (x j)) := by
  have h := schur_positive (exponential_diagonal_positive (normalization true ρ σ θ) (3/2) x)
    (ratioC_positive θ hθ (fun i => -x i))
  convert h using 1
  ext i j
  rw [widthC_transport ρ σ θ (x i) (x j) hρ hσ hθ]
  congr 2 <;> ring

def widthSum (p : ℂ) (w z : ℝ) : ℂ := p*(w:ℂ)+starRingEnd ℂ p*(z:ℂ)
def coolingB (p q : ℂ) (w z : ℝ) : ℂ :=
  widthSum q w z/(widthSum p w z ^ (1/2:ℂ)*widthSum (starRingEnd ℂ p) w z)
def coolingC (p q : ℂ) (w z : ℝ) : ℂ :=
  widthSum (starRingEnd ℂ q) w z/
    (widthSum p w z ^ (1/2:ℂ)*widthSum (starRingEnd ℂ p) w z ^ 2)

theorem widthSum_phase (ρ θ w z : ℝ) (hw : 0 < w) (hz : 0 < z) :
    widthSum ((ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) w z =
      phaseKernel ρ θ (Real.log w/2) (Real.log z/2) := by
  simp only [widthSum,phaseKernel,map_mul,← Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I]
  rw [show 2*(Real.log w/2)=Real.log w by ring,
    show 2*(Real.log z/2)=Real.log z by ring,Real.exp_log hw,Real.exp_log hz]
  congr 2
  congr 2
  ring

theorem phase_conjugate (ρ θ : ℝ) :
    starRingEnd ℂ ((ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) =
      (ρ:ℂ)*Complex.exp ((-θ:ℝ)*Complex.I) := by
  simp only [map_mul,← Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
  congr 2
  ring

theorem actual_coolingB_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => coolingB ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)) := by
  have hp := radii_positive α r hα hr
  have ht := phase_widthB_positive (radius α r) (slopeRadius α r) (angle r)
    hp.1 hp.2 (angle_strip r hr) (fun i => Real.log (w i)/2)
  convert ht using 1
  ext i j
  unfold coolingB widthB
  rw [gamma_polar,slope_polar,
    show (angle r:ℂ)*Complex.I/2 = ((angle r/2:ℝ):ℂ)*Complex.I by push_cast; ring,
    phase_conjugate,widthSum_phase _ _ _ _ (hw i) (hw j),
    widthSum_phase _ _ _ _ (hw i) (hw j),widthSum_phase _ _ _ _ (hw i) (hw j)]

theorem actual_coolingC_positive (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (w : n → ℝ) (hw : ∀ i, 0 < w i) :
    Matrix.PosSemidef (fun i j => coolingC ((α:ℂ)*r^2/2) ((α:ℂ)*r) (w i) (w j)) := by
  have hp := radii_positive α r hα hr
  have ht := phase_widthC_positive (radius α r) (slopeRadius α r) (angle r)
    hp.1 hp.2 (angle_strip r hr) (fun i => Real.log (w i)/2)
  convert ht using 1
  ext i j
  unfold coolingC widthC
  rw [gamma_polar,slope_polar,
    show (angle r:ℂ)*Complex.I/2 = ((angle r/2:ℝ):ℂ)*Complex.I by push_cast; ring,
    phase_conjugate,phase_conjugate,widthSum_phase _ _ _ _ (hw i) (hw j),
    widthSum_phase _ _ _ _ (hw i) (hw j),widthSum_phase _ _ _ _ (hw i) (hw j)]
  rw [neg_div]

#print axioms exponential_diagonal_positive
#print axioms phase_widthB_positive
#print axioms phase_widthC_positive
#print axioms widthSum_phase
#print axioms phase_conjugate
#print axioms actual_coolingB_positive
#print axioms actual_coolingC_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingWidthPositive
