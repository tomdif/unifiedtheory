/- Polynomial charged moments of the actual spatial Fourier fields.
Gaussian domination is derived for arbitrary finite packets and moments;
the constants here may depend on the packet family. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalJointFourierSpatialMoments
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalCorrelatedDilationPolynomials (prefactor packet)
open KFCausalCorrelatedDilationDifferentiation (value)
open KFCausalJointFourierDilationRepresentation (fieldDensity)
open KFCausalJointCompactPolynomialBounds (Controlled controlled_const controlled_coordinate coords)
open KFCausalClusteredClockFactors (E)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (r : ℂ)

theorem weighted_value_integrable (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (m j : ℕ) :
    Integrable (fun p : Joint => ‖(p.1.2 0:ℂ)^m*
      value n (fun _ => 0) j (fun i => w i*α) β 0 r b (fun i => c i*(w i:ℂ)) P 0 p‖^2)
      jointMeasure := by
  let f : Fin n → ℝ → Joint → ℂ := fun i t p =>
    (c i*(w i:ℂ))*(p.1.2 0:ℂ)^m*prefactor 0 j (w i*α) 0 r (P i) t p
  have hf (i : Fin n) : Controlled (Set.Icc (-1:ℝ) 1) (f i) := by
    have hv : Controlled (Set.Icc (-1:ℝ) 1) (fun (_ : ℝ) (p : Joint) => (p.1.2 0:ℂ)) := by
      simpa only [coords,Matrix.cons_val_succ,Matrix.cons_val_zero] using
        controlled_coordinate (Set.Icc (-1:ℝ) 1) 1
    exact ((controlled_const _ (c i*(w i:ℂ))).mul (hv.pow m)).mul
      (KFCausalCorrelatedDilationPolynomials.prefactors_controlled 0 j (w i*α) β 0 r (b i) (P i)).1
  obtain ⟨D,hDi,_,hD⟩ := KFCausalCorrelatedDilationEnvelope.finite_pair_envelope
    n (fun i => w i*α) β 0 r b hβ hA hC f f hf hf
  have he (p : Joint) : (p.1.2 0:ℂ)^m*
      value n (fun _ => 0) j (fun i => w i*α) β 0 r b (fun i => c i*(w i:ℂ)) P 0 p =
      ∑ i, Complex.exp (E (w i*α) β (KFCausalCorrelatedDilationEnvelope.geometry 0 r 0) (b i) p)*f i 0 p := by
    unfold value packet f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : Continuous (fun p : Joint => (p.1.2 0:ℂ)^m*
      value n (fun _ => 0) j (fun i => w i*α) β 0 r b (fun i => c i*(w i:ℂ)) P 0 p) := by
    have hv : Continuous (fun p : Joint => (p.1.2 0:ℂ)^m) := by fun_prop
    exact hv.mul (KFCausalCorrelatedDilationDifferentiation.value_continuous _ _ _ _ _ _ _ _ _ _ _)
  apply hDi.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),he]
  exact (le_add_of_nonneg_right (sq_nonneg _)).trans
    (hD 0 (by constructor <;> norm_num) p hp)

theorem field_moment_integrable (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) (m j : ℕ) :
    Integrable (fun p : Joint => (p.1.2 0)^(2*m)*fieldDensity n α β w b c P r 0 0 j p)
      jointMeasure := by
  have hi := weighted_value_integrable n α β w b c P r hβ hA hC m j
  apply hi.congr
  filter_upwards [] with p
  rw [KFCausalJointFourierDilationRepresentation.density_eq,norm_mul,mul_pow,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,← pow_mul,Nat.mul_comm m 2,pow_mul,sq_abs]
  rw [pow_mul]

#print axioms weighted_value_integrable
#print axioms field_moment_integrable
end
end UnifiedTheory.Audit.KFCausalJointFourierSpatialMoments
