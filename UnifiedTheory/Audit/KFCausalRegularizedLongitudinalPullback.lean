/- The regularized differential expression is conjugate to a derivative
on the whole real q-axis. The Jacobian-weighted pullback preserves the
L2 norm of complex functions. This does not yet identify a quantum
Hamiltonian domain or prove a regulator-removal limit. -/
import UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedLongitudinalPullback
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

def pullback (ε : ℝ) (φ : ℝ → ℂ) (s : ℝ) : ℂ :=
  (Real.sqrt (Real.exp s+ε) : ℂ)*φ (chart ε s)

def differential (ε : ℝ) (ψ : ℝ → ℂ) (s : ℝ) : ℂ :=
  deriv ψ s/(Real.exp s+ε : ℂ)-
    (Real.exp s : ℂ)*ψ s/(2*(Real.exp s+ε : ℂ)^2)

theorem pullback_derivative (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) (s : ℝ)
    (hφ : DifferentiableAt ℝ φ (chart ε s)) :
    HasDerivAt (pullback ε φ)
      (((Real.exp s/(2*Real.sqrt (Real.exp s+ε)) : ℝ) : ℂ)*φ (chart ε s)+
       (Real.sqrt (Real.exp s+ε) : ℂ)*((Real.exp s+ε) • deriv φ (chart ε s))) s := by
  have hw : Real.exp s+ε ≠ 0 := by positivity
  have hs := (((Real.hasDerivAt_exp s).add_const ε).sqrt hw).ofReal_comp
  have hp := hφ.hasDerivAt.scomp s (chart_derivative ε s)
  exact hs.mul hp

/-- Exact intertwining, with the symmetric-order derivative correction. -/
theorem differential_pullback (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) (s : ℝ)
    (hφ : DifferentiableAt ℝ φ (chart ε s)) :
    differential ε (pullback ε φ) s=pullback ε (deriv φ) s := by
  have hw : 0 < Real.exp s+ε := by positivity
  have hs : (Real.sqrt (Real.exp s+ε) : ℂ)^2=(Real.exp s+ε : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hw.le
  have hwc : (Real.exp s+ε : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  have hsc : (Real.sqrt (Real.exp s+ε) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  rw [differential,(pullback_derivative ε hε φ s hφ).deriv]
  simp only [pullback,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.real_smul,
    Complex.ofReal_add]
  field_simp
  linear_combination -(Real.exp s : ℂ)*φ (chart ε s)*hs

theorem pullback_density (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) (s : ℝ) :
    ‖pullback ε φ s‖^2=(Real.exp s+ε)*‖φ (chart ε s)‖^2 := by
  simp only [pullback,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (by positivity : 0 ≤ Real.exp s+ε)]

theorem pullback_square_integrable_iff (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) :
    Integrable (fun s => ‖pullback ε φ s‖^2) ↔ Integrable (fun q => ‖φ q‖^2) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun s (_ : s ∈ (univ : Set ℝ)) => (chart_derivative ε s).hasDerivWithinAt)
    (chart_strictMono ε hε).injective.injOn (fun q => ‖φ q‖^2)
  have hw (s : ℝ) : |Real.exp s+ε|=Real.exp s+ε := abs_of_pos (by positivity)
  simpa only [image_univ,(chart_surjective ε hε).range_eq,integrableOn_univ,
    hw,smul_eq_mul,pullback_density ε hε φ] using h.symm

theorem pullback_square_integral (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) :
    (∫ s, ‖pullback ε φ s‖^2)=∫ q, ‖φ q‖^2 := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun s (_ : s ∈ (univ : Set ℝ)) => (chart_derivative ε s).hasDerivWithinAt)
    (chart_strictMono ε hε).injective.injOn (fun q => ‖φ q‖^2)
  have hw (s : ℝ) : |Real.exp s+ε|=Real.exp s+ε := abs_of_pos (by positivity)
  simpa only [image_univ,(chart_surjective ε hε).range_eq,setIntegral_univ,
    hw,smul_eq_mul,pullback_density ε hε φ] using h.symm

/-- The pullback is onto all complex-valued functions; together with the
integrability equivalence and norm identity this supplies the L2 change
of variables. No completeness of a guessed eigenbasis is assumed. -/
theorem pullback_surjective (ε : ℝ) (hε : 0 < ε) : Function.Surjective (pullback ε) := by
  intro ψ
  let φ : ℝ → ℂ := fun q =>
    ψ ((chartIso ε hε).symm q)/(Real.sqrt (Real.exp ((chartIso ε hε).symm q)+ε) : ℂ)
  refine ⟨φ,?_⟩
  funext s
  have hi : (chartIso ε hε).symm (chart ε s)=s := (chartIso ε hε).symm_apply_apply s
  have hs : (Real.sqrt (Real.exp s+ε) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < Real.exp s+ε)).ne'
  simp only [pullback,φ,hi]
  field_simp

theorem pullback_injective (ε : ℝ) (hε : 0 < ε) : Function.Injective (pullback ε) := by
  intro φ ψ h
  funext q
  obtain ⟨s,hs⟩ := chart_surjective ε hε q
  have he := congrFun h s
  have hn : (Real.sqrt (Real.exp s+ε) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < Real.exp s+ε)).ne'
  apply mul_left_cancel₀ hn
  simpa only [pullback,hs] using he

theorem pullback_measurable_iff (ε : ℝ) (hε : 0 < ε) (φ : ℝ → ℂ) :
    Measurable (pullback ε φ) ↔ Measurable φ := by
  have hw : Measurable (fun s : ℝ => (Real.sqrt (Real.exp s+ε) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp (Real.continuous_exp.add continuous_const).measurable)
  constructor
  · intro hp
    have hi := (chartIso ε hε).symm.toHomeomorph.continuous.measurable
    have hq := (hp.comp hi).div (hw.comp hi)
    have he : (fun q => pullback ε φ ((chartIso ε hε).symm q)/
        (Real.sqrt (Real.exp ((chartIso ε hε).symm q)+ε) : ℂ))=φ := by
      funext q
      have hn : (Real.sqrt (Real.exp ((chartIso ε hε).symm q)+ε) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by positivity :
          0 < Real.exp ((chartIso ε hε).symm q)+ε)).ne'
      have hs : chart ε ((chartIso ε hε).symm q)=q := (chartIso ε hε).apply_symm_apply q
      simp only [pullback,hs]
      field_simp
    change Measurable (fun q => pullback ε φ ((chartIso ε hε).symm q)/
      (Real.sqrt (Real.exp ((chartIso ε hε).symm q)+ε) : ℂ)) at hq
    rwa [he] at hq
  · intro hφ
    exact hw.mul (hφ.comp (chart_continuous ε).measurable)

#print axioms pullback_derivative
#print axioms differential_pullback
#print axioms pullback_density
#print axioms pullback_square_integrable_iff
#print axioms pullback_square_integral
#print axioms pullback_surjective
#print axioms pullback_injective
#print axioms pullback_measurable_iff

end
end UnifiedTheory.Audit.KFCausalRegularizedLongitudinalPullback
