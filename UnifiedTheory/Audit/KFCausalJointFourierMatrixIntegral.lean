/- The original complete physical energy is the frequency integral of
the evaluated charged moment matrix. The interchange of all four variables
uses actual absolute integrability, with every interference term retained. -/
import UnifiedTheory.Audit.KFCausalChargedProductFubini
import UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalJointFourierMatrixIntegral
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralFourierQuadraticJet (packetMoment jetEnergy)
open KFCausalJointFourierQuadraticJet (chargedJet jetSlice energy)
open KFCausalJointFourierMomentMatrix (matrixEnergy)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalReciprocalWedgeGeometry (gamma chart)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

def density (α : ℝ) (r : ℂ) (q : Charged × ℝ) : ℝ :=
  jetSlice n β w b c P r (chart α r (q.1.1.1^2+q.1.1.2^2) q.1.2) q.1.1.2 q.2

theorem density_continuous (hβ : 0 < β) (α : ℝ) (r : ℂ) :
    Continuous (density n β w b c P α r) := by
  have hf (i : Fin n) (j : ℕ) : Continuous (𝓕 (packetMoment β (b i) (P i) j)) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner
      (KFCausalNeutralFourierQuadraticJet.packetMoment_integrable β hβ (b i) (P i) j)
  have hj (j : ℕ) : Continuous (fun q : Charged × ℝ =>
      chargedJet n β w b c P j (chart α r (q.1.1.1^2+q.1.1.2^2) q.1.2) q.2) := by
    unfold chargedJet KFCausalNeutralJointCurvatureForm.coefficients chart
    fun_prop
  unfold density jetSlice jetEnergy
  fun_prop

theorem density_nonnegative (α : ℝ) (r : ℂ) (q : Charged × ℝ) :
    0 ≤ density n β w b c P α r q :=
  KFCausalJointFourierQuadraticJet.jetSlice_nonnegative n β w b c P r _ _ _

theorem neutral_marginal (hβ : 0 < β) (α : ℝ) (r : ℂ) (q : Charged) :
    (∫ k : ℝ, density n β w b c P α r (q,k)) =
      ∫ x : ℝ, positiveDensity n α β w r c
        (fun i => exponentialProfile (b i) 1 (P i)) ((q.1.1,![q.1.2,x]),q.2) := by
  simp_rw [KFCausalJointNeutralFourierIntegral.density_slice]
  rw [KFCausalJointNeutralFourierIntegral.slice_plancherel n β w b c P hβ]
  simp_rw [KFCausalJointFourierQuadraticJet.frequencySlice_jet n β w b c P hβ]
  rfl

variable (α ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i)
local notation "r" => scale ε y s
include hα hβ hwidth hε hy hw

theorem neutral_marginal_integrable :
    Integrable (fun q : Charged => ∫ k : ℝ, density n β w b c P α r (q,k)) chargedMeasure := by
  apply KFCausalChargedProductFubini.integrable_of_ordered
  · exact (density_continuous n β w b c P hβ α r).stronglyMeasurable.integral_prod_right'
  · intro q
    exact integral_nonneg (fun k => density_nonnegative n β w b c P α r (q,k))
  · unfold KFCausalChargedProductFubini.OrderedIntegrable
    simp_rw [neutral_marginal n β w b c P hβ]
    exact KFCausalJointNeutralFourierOuterFubini.joint_marginals_integrable _
      (KFCausalReciprocalNeutralActualPositive.positive_integrable
        n α β ε y s w b c P hα hβ hwidth hε hy hw)

theorem density_integrable :
    Integrable (density n β w b c P α r) (chargedMeasure.prod volume) := by
  apply (integrable_prod_iff (density_continuous n β w b c P hβ α r).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun q => ?_),?_⟩
  · change Integrable (jetSlice n β w b c P r
      (chart α r (q.1.1^2+q.1.2^2) q.2) q.1.2)
    exact KFCausalJointFourierQuadraticJet.jetSlice_integrable n β w b c P hβ r _ _
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative n β w b c P α r _)] using
      neutral_marginal_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw

omit n β w b c P hβ hwidth hw in
theorem gamma_positive : 0 < (gamma α r).re := by
  have ha := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have he : (gamma α r).re = α*((r).re^2-(r).im^2)/2 := by
    simp only [gamma,pow_two,Complex.div_ofNat_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  rw [he]
  exact div_pos (mul_pos hα (by linarith)) (by norm_num)

theorem matrix_integrable : Integrable (matrixEnergy n β w b c P α r) := by
  apply (density_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw).integral_prod_right.congr
  filter_upwards [] with k
  exact KFCausalJointFourierMomentMatrix.slice_matrix_integral n β w b c P α r k
    (gamma_positive α ε y s hα hε hy) (fun i => lt_of_lt_of_le (by norm_num) (hw i))

theorem energy_matrix_integral :
    energy n β w b c P α r = Real.pi/4*(∫ k : ℝ, matrixEnergy n β w b c P α r k) := by
  have hi := density_integrable n β w b c P α ε y s hα hβ hwidth hε hy hw
  unfold energy
  congr 1
  change (∫ Y in Set.Ioi (0:ℝ), ∫ u : ℝ, ∫ v : ℝ, ∫ k : ℝ,
    density n β w b c P α r (((u,v),Y),k)) = _
  rw [← KFCausalChargedProductFubini.integral_order _ hi.integral_prod_left,
    ← integral_prod _ hi,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with k
  exact KFCausalJointFourierMomentMatrix.slice_matrix_integral n β w b c P α r k
    (gamma_positive α ε y s hα hε hy) (fun i => lt_of_lt_of_le (by norm_num) (hw i))

theorem total_matrix_integral :
    KFCausalReciprocalNeutralClockDerivative.totalEnergy n ε y α β w b P (fun _ => c) s =
      Real.pi/4*(∫ k : ℝ, matrixEnergy n β w b c P α r k) := by
  rw [← KFCausalJointFourierQuadraticJet.energy_eq_total n β w b c P ε y α hε hy hα hβ hwidth hw s]
  exact energy_matrix_integral n β w b c P α ε y s hα hβ hwidth hε hy hw

theorem matrix_energy_derivative :
    HasDerivAt (fun t => Real.pi/4*(∫ k : ℝ, matrixEnergy n β w b c P α (scale ε y t) k))
      (KFCausalReciprocalNeutralClockDerivative.totalResponse n ε y α β w b P (fun _ => c) s) s := by
  have he : (fun t => Real.pi/4*(∫ k : ℝ, matrixEnergy n β w b c P α (scale ε y t) k)) =
      fun t => energy n β w b c P α (scale ε y t) :=
    funext (fun t => (energy_matrix_integral n β w b c P α ε y t hα hβ hwidth hε hy hw).symm)
  rw [he]
  exact KFCausalJointFourierQuadraticJet.energy_derivative n β w b c P ε y α hε hy hα hβ hwidth hw s

#print axioms density_continuous
#print axioms density_nonnegative
#print axioms neutral_marginal
#print axioms neutral_marginal_integrable
#print axioms density_integrable
#print axioms gamma_positive
#print axioms matrix_integrable
#print axioms energy_matrix_integral
#print axioms total_matrix_integral
#print axioms matrix_energy_derivative
end
end UnifiedTheory.Audit.KFCausalJointFourierMatrixIntegral
