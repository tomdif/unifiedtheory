/- Annihilation defined on the full closed energy form of the actual
Bose particle sum, with the gap-based energy estimate ||a(f)u||^2 <= ||f||^2 q(u)/δ. -/
import UnifiedTheory.Audit.KFCausalBosonicFullEnergyForm
import UnifiedTheory.Audit.KFCausalBosonicSectorLadders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicAnnihilationEnergy
noncomputable section
open scoped ENNReal
open KFCausalClosedGraphForm KFCausalBosonicFock KFCausalBosonicFullEnergyForm
open KFCausalBosonicSectorLadders KFCausalTensorSumEnergyFloor

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem component_bound (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) (n : ℕ) :
    ‖annihilator D f n (embedding (fullFormData D) u (n + 1))‖ ^ 2 ≤
      (‖f‖ ^ 2 / δ) * ‖energyOutput (sector D (n + 1)).form (coordinate D u (n + 1))‖ ^ 2 := by
  have hq := component_lower D δ hD u (n + 1)
  have hc : 0 ≤ ‖f‖ ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  calc
    _ ≤ ‖f‖ ^ 2 * ((n : ℝ) + 1) * ‖embedding (fullFormData D) u (n + 1)‖ ^ 2 :=
      annihilator_square_bound D f n _
    _ = (‖f‖ ^ 2 / δ) * (((n + 1 : ℕ) : ℝ) * δ *
        ‖embedding (fullFormData D) u (n + 1)‖ ^ 2) := by
      push_cast
      field_simp [ne_of_gt hδ]
    _ ≤ _ := mul_le_mul_of_nonneg_left hq hc

theorem squares_summable (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ)
    (hD : LowerBound D δ) (u : FormSpace (fullFormData D)) :
    Summable (fun n => ‖annihilator D f n (embedding (fullFormData D) u (n + 1))‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (component_bound D f δ hδ hD u)
  exact ((energy_hasSum D u).summable.comp_injective Nat.succ_injective).mul_left (‖f‖ ^ 2 / δ)

def annihilationLinear (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ) :
    FormSpace (fullFormData D) →ₗ[ℂ] BosonFock D where
  toFun u := ⟨fun n => annihilator D f n (embedding (fullFormData D) u (n + 1)),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using squares_summable D f δ hδ hD u)⟩
  map_add' u v := by
    apply lp.ext
    funext n
    simp only [map_add, lp.coeFn_add, Pi.add_apply]
  map_smul' c u := by
    apply lp.ext
    funext n
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]

theorem square_bound (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    ‖annihilationLinear D f δ hδ hD u‖ ^ 2 ≤
      (‖f‖ ^ 2 / δ) * ‖energyOutput (fullFormData D) u‖ ^ 2 := by
  have hn : HasSum (fun n => ‖annihilator D f n (embedding (fullFormData D) u (n + 1))‖ ^ 2)
      (‖annihilationLinear D f δ hδ hD u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (annihilationLinear D f δ hδ hD u)
  exact hasSum_le_inj (fun n : ℕ => n + 1) Nat.succ_injective
    (fun n _ => mul_nonneg (div_nonneg (sq_nonneg _) hδ.le) (sq_nonneg _))
    (component_bound D f δ hδ hD u) hn ((energy_hasSum D u).mul_left (‖f‖ ^ 2 / δ))

theorem form_norm_bound (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    ‖annihilationLinear D f δ hδ hD u‖ ≤ Real.sqrt (‖f‖ ^ 2 / δ) * ‖u‖ := by
  have hc : 0 ≤ ‖f‖ ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  have he : ‖energyOutput (fullFormData D) u‖ ≤ ‖u‖ := WithLp.norm_snd_le _ u.val
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hc]
  exact (square_bound D f δ hδ hD u).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he 2) hc)

def annihilationForm (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ) :
    FormSpace (fullFormData D) →L[ℂ] BosonFock D :=
  (annihilationLinear D f δ hδ hD).mkContinuous (Real.sqrt (‖f‖ ^ 2 / δ))
    (form_norm_bound D f δ hδ hD)

theorem annihilationForm_apply (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ)
    (hD : LowerBound D δ) (u : FormSpace (fullFormData D)) (n : ℕ) :
    annihilationForm D f δ hδ hD u n = annihilator D f n (embedding (fullFormData D) u (n + 1)) := rfl

theorem energy_bound (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ) (hD : LowerBound D δ)
    (u : FormSpace (fullFormData D)) :
    ‖annihilationForm D f δ hδ hD u‖ ^ 2 ≤
      (‖f‖ ^ 2 / δ) * ‖energyOutput (fullFormData D) u‖ ^ 2 :=
  square_bound D f δ hδ hD u

theorem energy_norm_bound (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ)
    (hD : LowerBound D δ) (u : FormSpace (fullFormData D)) :
    ‖annihilationForm D f δ hδ hD u‖ ≤
      Real.sqrt (‖f‖ ^ 2 / δ) * ‖energyOutput (fullFormData D) u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg (sq_nonneg _) hδ.le)]
  exact energy_bound D f δ hδ hD u

theorem annihilation_vacuum (D : Data H K) (f : H) (δ : ℝ) (hδ : 0 < δ)
    (hD : LowerBound D δ) (u : FormSpace (fullFormData D))
    (hu : embedding (fullFormData D) u = vacuum D) : annihilationForm D f δ hδ hD u = 0 := by
  apply lp.ext
  funext n
  rw [annihilationForm_apply, hu]
  simp [vacuum, lp.single_apply]

end
end UnifiedTheory.Audit.KFCausalBosonicAnnihilationEnergy
