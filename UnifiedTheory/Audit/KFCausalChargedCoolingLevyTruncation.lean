/- Concrete positive Levy densities for the two charged cooling kernels.
Their compactly truncated paired exponents give positive finite kernels.
Identification of the full improper exponent with the log-cosh ratio
is a separate obligation, not a hypothesis concealed in this result. -/
import UnifiedTheory.Audit.KFCausalPositiveKernelExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingLevyTruncation
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexOrder
open KFCausalPositiveKernelExponential (phase compound_poisson_positive schur_positive)

def numeratorB (s : ℝ) : ℝ := Real.exp (2*s)/2+Real.exp (-2*s)-Real.exp s
def numeratorC (s : ℝ) : ℝ := Real.exp (2*s)/2+2*Real.exp (-2*s)-Real.exp (-s)

theorem numeratorB_positive (s : ℝ) : 0 < numeratorB s := by
  let z := Real.exp s
  have hz : 0 < z := Real.exp_pos s
  have hexp : Real.exp (2*s) = z^2 := by
    dsimp [z]
    rw [two_mul, Real.exp_add, pow_two]
  have he : numeratorB s*z^2 = z^4/2-z^3+1 := by
    simp only [numeratorB, show -2*s = -(2*s) by ring, Real.exp_neg,
      hexp]
    change (z^2/2+(z^2)⁻¹-z)*z^2 = _
    field_simp [ne_of_gt hz]
    ring
  have hp : 0 < z^4/2-z^3+1 := by
    rw [show z^4/2-z^3+1 = (z-3/2)^2*(z^2/2+z/2+3/8)+5/32 by ring]
    positivity
  exact (mul_pos_iff_of_pos_right (sq_pos_of_pos hz)).mp (he.symm ▸ hp)

theorem numeratorC_positive (s : ℝ) : 0 < numeratorC s := by
  let z := Real.exp s
  have hz : 0 < z := Real.exp_pos s
  have hexp : Real.exp (2*s) = z^2 := by
    dsimp [z]
    rw [two_mul, Real.exp_add, pow_two]
  have he : numeratorC s*z^2 = z^4/2-z+2 := by
    simp only [numeratorC, show -2*s = -(2*s) by ring, Real.exp_neg,
      hexp]
    change (z^2/2+2*(z^2)⁻¹-z⁻¹)*z^2 = _
    field_simp [ne_of_gt hz]
    ring
  have hp : 0 < z^4/2-z+2 := by
    rw [show z^4/2-z+2 = (z-1)^2*(z^2+2*z+3)/2+z+1/2 by ring]
    positivity
  exact (mul_pos_iff_of_pos_right (sq_pos_of_pos hz)).mp (he.symm ▸ hp)

def numerator (kind : Bool) (s : ℝ) : ℝ := if kind then numeratorC s else numeratorB s
def levyA (kind : Bool) (s : ℝ) : ℝ :=
  if kind then (5/2)*Real.cosh (2*s)-Real.cosh s
  else (3/2)*Real.cosh (2*s)-Real.cosh s
def levyB (kind : Bool) (s : ℝ) : ℝ :=
  if kind then -(3/2)*Real.sinh (2*s)+Real.sinh s
  else -(1/2)*Real.sinh (2*s)-Real.sinh s
def density (kind : Bool) (θ t : ℝ) : ℝ := numerator kind (θ*t)/(2*t*Real.sinh (Real.pi*t))

theorem numerator_hyperbolic (kind : Bool) (s : ℝ) :
    numerator kind s = levyA kind s + levyB kind s := by
  cases kind <;> simp only [numerator, levyA, levyB, Bool.false_eq_true, if_false, if_true,
    numeratorB, numeratorC, Real.cosh_eq, Real.sinh_eq] <;> ring

theorem reflected_numerator_hyperbolic (kind : Bool) (s : ℝ) :
    numerator kind (-s) = levyA kind s - levyB kind s := by
  rw [numerator_hyperbolic]
  cases kind <;> simp only [levyA, levyB, Bool.false_eq_true, if_false, if_true,
    show 2*(-s) = -(2*s) by ring, Real.cosh_neg, Real.sinh_neg] <;> ring

theorem density_positive (kind : Bool) (θ t : ℝ) (ht : 0 < t) :
    0 < density kind θ t := by
  apply div_pos
  · cases kind
    · exact numeratorB_positive (θ*t)
    · exact numeratorC_positive (θ*t)
  · exact mul_pos (mul_pos (by norm_num) ht) (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))

theorem density_continuousOn (kind : Bool) (θ : ℝ) :
    ContinuousOn (density kind θ) (Ioi 0) := by
  unfold density
  apply ContinuousOn.div
  · cases kind <;> simp only [numerator, Bool.false_eq_true, if_false, if_true,
      numeratorB, numeratorC] <;> fun_prop
  · fun_prop
  · intro t ht
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) ht)
      (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)))

theorem density_integrableOn (kind : Bool) (θ ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (density kind θ) (Icc ε R) :=
  ((density_continuousOn kind θ).mono (fun _ ht => lt_of_lt_of_le hε ht.1)).integrableOn_Icc

private theorem weighted_compound_positive {n : Type*} [Fintype n]
    (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Integrable f μ) (hn : ∀ᵐ t ∂μ, 0 ≤ f t)
    (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (∫ t,
      (f t:ℂ)*(phase (x j-x i) t-1) ∂μ)) := by
  let ρ := μ.withDensity (fun t => ENNReal.ofReal (f t))
  letI : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hf.2
  have he (z : ℝ) : (∫ t, phase z t-1 ∂ρ) =
      ∫ t, (f t:ℂ)*(phase z t-1) ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hf.1.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [hn] with t ht
    simp only [ENNReal.toReal_ofReal ht, Complex.real_smul]
  simpa only [he] using compound_poisson_positive ρ x

def truncatedExponent (kind : Bool) (θ ε R z : ℝ) : ℂ :=
  (∫ t in Icc ε R, (density kind (-θ) t:ℂ)*(phase (2*z) t-1))+
  (∫ t in Icc ε R, (density kind θ t:ℂ)*(phase (-2*z) t-1))

theorem truncated_kernel_positive {n : Type*} [Fintype n]
    (kind : Bool) (θ ε R : ℝ) (hε : 0 < ε) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (truncatedExponent kind θ ε R (x j-x i))) := by
  have hn (η : ℝ) : ∀ᵐ t ∂volume.restrict (Icc ε R), 0 ≤ density kind η t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (density_positive kind η t (lt_of_lt_of_le hε ht.1)).le
  have hp := weighted_compound_positive (volume.restrict (Icc ε R)) (density kind (-θ))
    (density_integrableOn kind (-θ) ε R hε) (hn (-θ)) (fun i => 2*x i)
  have hm := weighted_compound_positive (volume.restrict (Icc ε R)) (density kind θ)
    (density_integrableOn kind θ ε R hε) (hn θ) (fun i => -2*x i)
  convert schur_positive hp hm using 1
  funext i j
  simp only [truncatedExponent, Complex.exp_add,
    show 2*(x j-x i) = 2*x j-2*x i by ring,
    show -2*(x j-x i) = -2*x j-(-2*x i) by ring]

#print axioms numeratorB_positive
#print axioms numeratorC_positive
#print axioms numerator_hyperbolic
#print axioms reflected_numerator_hyperbolic
#print axioms density_positive
#print axioms density_continuousOn
#print axioms density_integrableOn
#print axioms truncated_kernel_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingLevyTruncation
