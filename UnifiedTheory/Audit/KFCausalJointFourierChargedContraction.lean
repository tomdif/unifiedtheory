/- Charged cooling contracts the original three-channel Fourier energy,
with all field/Fourier coefficients and the exponential tilt frozen at r.
The complete clock response also moves those frozen parameters. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingEnergyContraction
import UnifiedTheory.Audit.KFCausalJointFourierMatrixIntegral
import UnifiedTheory.Audit.KFCausalChargedCoolingActualPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierChargedContraction
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedFourierPolynomialGram (family atom)
open KFCausalJointFourierMomentMatrix (source amplitude channelCoefficients matrixEnergy)
open KFCausalChargedCoolingEnergyContraction (energy energy_contraction)
open KFCausalChargedCoolingFixedV (actual_gamma_re_positive)
open KFCausalChargedCoolingContraction (translated_sector)
open KFCausalNeutralFourierQuadraticJet (packetMoment)
open KFCausalReciprocalWedgeGeometry (gamma)
open KFCausalClockFloorRelativeShift (scale)

local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def density (α : ℝ) (r : ℂ) (h : ℝ) (q : Charged × ℝ) : ℝ :=
  ‖family n (gamma α (r+(h:ℂ))) w (source r q.2)
    (channelCoefficients n β w b c P r q.2 0) q.1.1.1 q.1.1.2 q.1.2‖^2+
  ‖family n (gamma α (r+(h:ℂ))) w (source r q.2)
    (channelCoefficients n β w b c P r q.2 1) q.1.1.1 q.1.1.2 q.1.2‖^2/2+
  ‖family n (gamma α (r+(h:ℂ))) w (source r q.2)
    (channelCoefficients n β w b c P r q.2 2) q.1.1.1 q.1.1.2 q.1.2‖^2/4

def marginal (α : ℝ) (r : ℂ) (h k : ℝ) : ℝ :=
  ∫ q : Charged, density n β w b c P α r h (q,k) ∂chargedMeasure

theorem density_continuous (hβ : 0 < β) (α : ℝ) (r : ℂ) (h : ℝ) :
    Continuous (density n β w b c P α r h) := by
  have hf (i : Fin n) (j : ℕ) : Continuous (𝓕 (packetMoment β (b i) (P i) j)) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner
      (KFCausalNeutralFourierQuadraticJet.packetMoment_integrable β hβ (b i) (P i) j)
  have ha (j : Fin 3) (i : Fin n) (d : Fin 3) :
      Continuous (fun k => channelCoefficients n β w b c P r k j i d) := by
    fin_cases j <;> fin_cases d <;> norm_num [channelCoefficients,amplitude] <;> fun_prop
  unfold density family atom source
  fun_prop

theorem density_nonnegative (α : ℝ) (r : ℂ) (h : ℝ) (q : Charged × ℝ) :
    0 ≤ density n β w b c P α r h q := by unfold density; positivity

theorem zero_density (α : ℝ) (r : ℂ) :
    density n β w b c P α r 0 = KFCausalJointFourierMatrixIntegral.density n β w b c P α r := by
  funext q
  simpa only [density,Complex.ofReal_zero,add_zero] using
    (KFCausalJointFourierMomentMatrix.slice_density n β w b c P α r q.2 q.1.1.1 q.1.1.2 q.1.2).symm

theorem charged_integrable (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (h k : ℝ) (hh : 0 ≤ h) :
    Integrable (fun q : Charged => density n β w b c P α r h (q,k)) chargedMeasure := by
  have hi (j : Fin 3) : Integrable (fun q : Charged =>
      ‖family n (gamma α (r+(h:ℂ))) w (source r k)
        (channelCoefficients n β w b c P r k j) q.1.1 q.1.2 q.2‖^2) chargedMeasure :=
    (KFCausalChargedFourierPolynomialGram.family_square_integrable
    n (gamma α (r+(h:ℂ))) w (source r k) (channelCoefficients n β w b c P r k j)
    (actual_gamma_re_positive α _ hα (translated_sector r hr h hh)) hw).re
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

theorem marginal_energy (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (h k : ℝ) (hh : 0 ≤ h) :
    marginal n β w b c P α r h k =
      energy n (gamma α (r+(h:ℂ))) w (source r k) (channelCoefficients n β w b c P r k 0)+
      energy n (gamma α (r+(h:ℂ))) w (source r k) (channelCoefficients n β w b c P r k 1)/2+
      energy n (gamma α (r+(h:ℂ))) w (source r k) (channelCoefficients n β w b c P r k 2)/4 := by
  have hi (j : Fin 3) : Integrable (fun q : Charged =>
      ‖family n (gamma α (r+(h:ℂ))) w (source r k)
        (channelCoefficients n β w b c P r k j) q.1.1 q.1.2 q.2‖^2) chargedMeasure :=
    (KFCausalChargedFourierPolynomialGram.family_square_integrable
    n (gamma α (r+(h:ℂ))) w (source r k) (channelCoefficients n β w b c P r k j)
    (actual_gamma_re_positive α _ hα (translated_sector r hr h hh)) hw).re
  have h01 : Integrable (fun q : Charged =>
      ‖family n (gamma α (r+(h:ℂ))) w (source r k)
        (channelCoefficients n β w b c P r k 0) q.1.1 q.1.2 q.2‖^2+
      ‖family n (gamma α (r+(h:ℂ))) w (source r k)
        (channelCoefficients n β w b c P r k 1) q.1.1 q.1.2 q.2‖^2/2) chargedMeasure :=
    (hi 0).add ((hi 1).div_const 2)
  unfold marginal density energy
  rw [integral_add h01 ((hi 2).div_const 4),
    integral_add (hi 0) ((hi 1).div_const 2),integral_div,integral_div]

theorem marginal_contraction (α : ℝ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (h k : ℝ) (hh : 0 ≤ h) :
    marginal n β w b c P α r h k ≤ matrixEnergy n β w b c P α r k := by
  rw [marginal_energy n β w b c P α r hα hr hw h k hh]
  have he (j : Fin 3) := energy_contraction n α r w (source r k)
    (channelCoefficients n β w b c P r k j) hα hr hw h hh
  have hg (j : Fin 3) := KFCausalJointFourierMomentMatrix.real_gram_integral
    n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k j)
    (actual_gamma_re_positive α r hα hr) hw
  change ∀ j : Fin 3, energy n (gamma α r) w (source r k) (channelCoefficients n β w b c P r k j) = _ at hg
  unfold matrixEnergy
  rw [← hg 0,← hg 1,← hg 2]
  exact add_le_add (add_le_add (he 0) (div_le_div_of_nonneg_right (he 1) (by norm_num)))
    (div_le_div_of_nonneg_right (he 2) (by norm_num))

variable (α ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) (h : ℝ) (hh : 0 ≤ h)
local notation "r" => scale ε y s
include hα hβ hwidth hε hy hw hh

theorem marginal_integrable : Integrable (marginal n β w b c P α r h) := by
  have hi := KFCausalJointFourierMatrixIntegral.matrix_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw
  apply hi.mono' (density_continuous n β w b c P hβ α r h).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  filter_upwards [] with k
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun q => density_nonnegative n β w b c P α r h (q,k)))]
  exact marginal_contraction n β w b c P α r hα
    (KFCausalChargedCoolingActualPhase.actual_sector ε y s hε hy)
    (fun i => lt_of_lt_of_le (by norm_num) (hw i)) h k hh

theorem full_density_integrable :
    Integrable (density n β w b c P α r h) (chargedMeasure.prod volume) := by
  apply (integrable_prod_iff' (density_continuous n β w b c P hβ α r h).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun k => charged_integrable n β w b c P α r hα
    (KFCausalChargedCoolingActualPhase.actual_sector ε y s hε hy)
    (fun i => lt_of_lt_of_le (by norm_num) (hw i)) h k hh),?_⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative n β w b c P α r h _)] using
    marginal_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw h hh

theorem full_energy_contraction :
    Real.pi/4*(∫ q : Charged × ℝ, density n β w b c P α r h q ∂chargedMeasure.prod volume) ≤
      KFCausalJointFourierQuadraticJet.energy n β w b c P α r := by
  rw [KFCausalJointFourierMatrixIntegral.energy_matrix_integral n β w b c P α ε y s hα hβ hwidth hε hy hw,
    integral_prod_symm _ (full_density_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw h hh)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact integral_mono
    (marginal_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw h hh)
    (KFCausalJointFourierMatrixIntegral.matrix_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw)
    (fun k => marginal_contraction n β w b c P α r hα
      (KFCausalChargedCoolingActualPhase.actual_sector ε y s hε hy)
      (fun i => lt_of_lt_of_le (by norm_num) (hw i)) h k hh)

#print axioms density_continuous
#print axioms density_nonnegative
#print axioms zero_density
#print axioms charged_integrable
#print axioms marginal_energy
#print axioms marginal_contraction
#print axioms marginal_integrable
#print axioms full_density_integrable
#print axioms full_energy_contraction
end
end UnifiedTheory.Audit.KFCausalJointFourierChargedContraction
