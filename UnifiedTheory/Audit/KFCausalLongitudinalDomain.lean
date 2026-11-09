/- The differential expression of the exponential longitudinal datum.
The change to c=exp(s) exposes half-line momentum. This file proves the
coordinate and deficiency-profile calculations, not an unbounded-operator
self-adjoint-extension theorem. Domain identification is stated separately. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLongitudinalDomain
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- Real differential part of sym(exp(-s) P_s), before multiplication
by -i*hbar. The -1/2 term is forced by symmetric ordering. -/
def longitudinalDifferential (ψ : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-s)*(deriv ψ s-ψ s/2)

def logPullback (φ : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (s/2)*φ (Real.exp s)

theorem logPullback_derivative (φ : ℝ → ℝ) (s : ℝ) (hφ : DifferentiableAt ℝ φ (Real.exp s)) :
    HasDerivAt (logPullback φ)
      (Real.exp (s/2)*φ (Real.exp s)/2+
       Real.exp (s/2)*(deriv φ (Real.exp s)*Real.exp s)) s := by
  have he := ((hasDerivAt_id s).div_const 2).exp
  have h := he.mul (hφ.hasDerivAt.comp s (Real.hasDerivAt_exp s))
  convert h using 1; dsimp [logPullback]; ring

/-- The longitudinal derivative becomes d/dc on c>0 with the correct
Jacobian weight. This is a differential-expression identity. -/
theorem longitudinal_logPullback (φ : ℝ → ℝ) (s : ℝ)
    (hφ : DifferentiableAt ℝ φ (Real.exp s)) :
    longitudinalDifferential (logPullback φ) s=logPullback (deriv φ) s := by
  rw [longitudinalDifferential,(logPullback_derivative φ s hφ).deriv]
  unfold logPullback
  have he : Real.exp (-s)*Real.exp s=1 := by rw [← Real.exp_add]; simp
  calc
    _ = Real.exp (s/2)*deriv φ (Real.exp s)*(Real.exp (-s)*Real.exp s) := by ring
    _ = _ := by rw [he,mul_one]

/-- Pointwise density/Jacobian identity for the same transformation. -/
theorem logPullback_density (φ : ℝ → ℝ) (s : ℝ) :
    logPullback φ s^2=Real.exp s*φ (Real.exp s)^2 := by
  rw [logPullback,mul_pow,← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

def halfLineProfile (k c : ℝ) : ℝ := Real.exp (-k*c)
def deficiencyProfile (k s : ℝ) : ℝ := Real.exp (s/2-k*Real.exp s)

theorem deficiency_is_pullback (k : ℝ) : deficiencyProfile k=logPullback (halfLineProfile k) := by
  funext s
  simp [deficiencyProfile,logPullback,halfLineProfile,sub_eq_add_neg,Real.exp_add,neg_mul]

theorem halfLineProfile_derivative (k c : ℝ) :
    HasDerivAt (halfLineProfile k) (-k*halfLineProfile k c) c := by
  convert ((hasDerivAt_id c).const_mul (-k)).exp using 1; simp [halfLineProfile,mul_comm]

theorem deficiency_differential (k s : ℝ) :
    longitudinalDifferential (deficiencyProfile k) s= -k*deficiencyProfile k s := by
  rw [deficiency_is_pullback,longitudinal_logPullback _ s
    (halfLineProfile_derivative k (Real.exp s)).differentiableAt]
  simp only [logPullback,(halfLineProfile_derivative k (Real.exp s)).deriv]
  ring

theorem halfLineProfile_square (k c : ℝ) : halfLineProfile k c^2=Real.exp ((-2*k)*c) := by
  rw [halfLineProfile,← Real.exp_nat_mul]
  congr 1
  ring

theorem decaying_profile_square_integrable (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun c => halfLineProfile k c^2) (Ioi 0) := by
  simp only [halfLineProfile_square]
  exact integrableOn_exp_mul_Ioi (by linarith) 0

theorem decaying_profile_square_integral (k : ℝ) (hk : 0 < k) :
    (∫ c in Ioi (0 : ℝ), halfLineProfile k c^2)=1/(2*k) := by
  simp only [halfLineProfile_square]
  rw [integral_exp_mul_Ioi (by linarith : -2*k < 0) 0]
  simp

/-- The opposite-sign deficiency profile is not square integrable on
the positive half-line; it dominates the nonintegrable constant one. -/
theorem growing_profile_not_square_integrable (k : ℝ) (hk : 0 < k) :
    ¬IntegrableOn (fun c => halfLineProfile (-k) c^2) (Ioi 0) := by
  intro hi
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
    apply hi.mono' (measurable_const.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    simp only [Real.norm_eq_abs,abs_one,halfLineProfile_square]
    apply Real.one_le_exp
    have hc' : 0 < c := hc
    nlinarith
  simp [integrableOn_const_iff,Real.volume_Ioi] at hone

/-- No everywhere-positive clock can obey the global canonical
translation law. An infinitesimal commutator on a core alone does not
imply this global law; invariant-domain hypotheses cannot be omitted. -/
theorem no_global_positive_translation (c : ℝ → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hd : ∀ t, HasDerivAt c 1 t) : False := by
  have hz (t : ℝ) : HasDerivAt (fun s => c s-s) 0 t := by
    simpa using (hd t).sub (hasDerivAt_id t)
  have he := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
    (fun t => (hz t).deriv)
  have hv : c (-(c 0+1))= -1 := by
    have h := he (-(c 0+1)) 0
    linarith
  have hpos := hc (-(c 0+1))
  linarith

#print axioms logPullback_derivative
#print axioms longitudinal_logPullback
#print axioms logPullback_density
#print axioms deficiency_is_pullback
#print axioms deficiency_differential
#print axioms decaying_profile_square_integrable
#print axioms decaying_profile_square_integral
#print axioms growing_profile_not_square_integrable
#print axioms no_global_positive_translation

end
end UnifiedTheory.Audit.KFCausalLongitudinalDomain
