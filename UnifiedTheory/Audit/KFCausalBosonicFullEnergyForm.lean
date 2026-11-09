/- The full closed energy form of the completed Bose particle sum,
with exact domain, Hamiltonian identification and number-weighted estimate. -/
import UnifiedTheory.Audit.KFCausalDirectSumFormHamiltonian
import UnifiedTheory.Audit.KFCausalClosedFormLowerBound
import UnifiedTheory.Audit.KFCausalBosonicEnergyGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicFullEnergyForm
noncomputable section
open scoped ENNReal
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalTensorSumEnergyFloor

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev EnergyFock (D : Data H K) := lp (fun n => (sector D n).Energy) 2

def fullFormData (D : Data H K) : Data (BosonFock D) (EnergyFock D) :=
  KFCausalDirectSumEnergyForm.formData (fun n => (sector D n).form)

def coordinate (D : Data H K) (u : FormSpace (fullFormData D)) (n : ℕ) :
    FormSpace (sector D n).form :=
  KFCausalDirectSumEnergyForm.coordinate (fun n => (sector D n).form) u n

theorem coordinate_embedding (D : Data H K) (u : FormSpace (fullFormData D)) (n : ℕ) :
    embedding (sector D n).form (coordinate D u n) = embedding (fullFormData D) u n := rfl

theorem coordinate_output (D : Data H K) (u : FormSpace (fullFormData D)) (n : ℕ) :
    energyOutput (sector D n).form (coordinate D u n) = energyOutput (fullFormData D) u n := rfl

theorem hamiltonian_identification (D : Data H K) :
    hamiltonian (fullFormData D) = fullHamiltonian D :=
  KFCausalDirectSumFormHamiltonian.hamiltonian_eq (fun n => (sector D n).form)

theorem form_domain_iff (D : Data H K) (x : BosonFock D) :
    (∃ u : FormSpace (fullFormData D), embedding (fullFormData D) u = x) ↔
      ∃ (hx : ∀ n, x n ∈ (sector D n).form.operator.domain),
        Summable (fun n => ‖(sector D n).form.operator ⟨x n, hx n⟩‖ ^ 2) :=
  KFCausalDirectSumEnergyForm.form_domain_iff (fun n => (sector D n).form) x

theorem energy_hasSum (D : Data H K) (u : FormSpace (fullFormData D)) :
    HasSum (fun n => ‖energyOutput (sector D n).form (coordinate D u n)‖ ^ 2)
      (‖energyOutput (fullFormData D) u‖ ^ 2) :=
  KFCausalDirectSumEnergyForm.energy_hasSum (fun n => (sector D n).form) u

theorem component_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) (n : ℕ) :
    ((n : ℝ) * δ) * ‖embedding (fullFormData D) u n‖ ^ 2 ≤
      ‖energyOutput (sector D n).form (coordinate D u n)‖ ^ 2 :=
  KFCausalClosedFormLowerBound.lower_bound (sector D n).form ((n : ℝ) * δ)
    (KFCausalBosonicEnergyGap.sector_lower D δ hD n) (coordinate D u n)

theorem weighted_summable (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    Summable (fun n : ℕ => ((n : ℝ) * δ) * ‖embedding (fullFormData D) u n‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ) (sq_nonneg _))
    (component_lower D δ hD u) (energy_hasSum D u).summable

theorem number_energy_lower (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    (∑' n : ℕ, ((n : ℝ) * δ) * ‖embedding (fullFormData D) u n‖ ^ 2) ≤
      ‖energyOutput (fullFormData D) u‖ ^ 2 := by
  rw [← (energy_hasSum D u).tsum_eq]
  exact Summable.tsum_le_tsum (component_lower D δ hD u)
    (weighted_summable D δ hδ hD u) (energy_hasSum D u).summable

theorem number_summable (D : Data H K) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    Summable (fun n : ℕ => (n : ℝ) * ‖embedding (fullFormData D) u n‖ ^ 2) := by
  have hs := (weighted_summable D δ hδ.le hD u).mul_left δ⁻¹
  convert hs using 1
  funext n
  field_simp [ne_of_gt hδ]

theorem vacuum_form_gap (D : Data H K) (δ : ℝ) (hδ : 0 ≤ δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) (hu : embedding (fullFormData D) u 0 = 0) :
    δ * ‖embedding (fullFormData D) u‖ ^ 2 ≤ ‖energyOutput (fullFormData D) u‖ ^ 2 := by
  have hn : HasSum (fun n => ‖embedding (fullFormData D) u n‖ ^ 2)
      (‖embedding (fullFormData D) u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (embedding (fullFormData D) u)
  apply hasSum_le _ (hn.mul_left δ) (energy_hasSum D u)
  intro n
  by_cases hzero : n = 0
  · subst n
    simpa only [hu, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      sq_nonneg (‖energyOutput (sector D 0).form (coordinate D u 0)‖)
  · have hc : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    have hm : δ ≤ (n : ℝ) * δ := by nlinarith
    exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans (component_lower D δ hD u n)

theorem operator_form_dense (D : Data H K) : DenseRange (formLift (fullFormData D)) :=
  KFCausalDirectSumFormHamiltonian.operator_form_dense (fun n => (sector D n).form)

end
end UnifiedTheory.Audit.KFCausalBosonicFullEnergyForm
