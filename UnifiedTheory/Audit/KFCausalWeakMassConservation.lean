/- Physical norm conservation for a locally bounded weak form curve.
The hypotheses describe its weak differential equation and estimates;
neither norm conservation nor a cutoff representation is assumed. This
allows the theorem to be applied to differences of constructed solutions. -/
import UnifiedTheory.Audit.KFCausalMassEnergyIdentities
import UnifiedTheory.Audit.KFCausalLocalWeakContinuity
import UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeakMassConservation
noncomputable section
open Filter Set
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalMassGram
open UnifiedTheory.Audit.KFCausalMassRegularization
open UnifiedTheory.Audit.KFCausalMassEnergyIdentities
open UnifiedTheory.Audit.KFCausalWeakQuadraticDerivative
open UnifiedTheory.Audit.KFCausalLocalWeakContinuity
open UnifiedTheory.Audit.KFCausalRegularizedEnergyLimit
open UnifiedTheory.Audit.KFCausalShiftedForm

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_square_conserved (J : E →L[ℂ] H) (hj : Function.Injective J)
    (u d : ℝ → E) (R K : ℝ → ℝ) (hK : ∀ T, 0 ≤ K T)
    (hu : ∀ T z, 0 ≤ T → |z| ≤ T → ‖u z‖ ≤ R T)
    (hd : ∀ T z, 0 ≤ T → |z| ≤ T → ‖d z‖ ≤ K T)
    (hw : ∀ y, Continuous (fun z => inner ℂ (d z) y))
    (hl : ∀ T x y, 0 ≤ T → |x| ≤ T → |y| ≤ T →
      ‖gram J (u y)-gram J (u x)‖ ≤ K T*|y-x|)
    (heq : ∀ z y, HasDerivAt (fun t => inner ℂ (gram J (u t)) y) (inner ℂ (d z) y) z)
    (hz : ∀ z, (inner ℂ (d z) (u z)).re = 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (s t : ℝ) : ‖J (u t)‖^2 = ‖J (u s)‖^2 := by
  have hp (x : E) : 0 ≤ (inner ℂ (gram J x) x).re := by
    rw [gram_left_pairing,complex_inner_square,Complex.ofReal_re]
    positivity
  have hs := gram_inner_symm J
  have hgc : Continuous (fun z => gram J (u z)) :=
    continuous_of_window_lipschitz _ K (fun T _ => hK T) hl
  let A : ℕ → ℝ → ℝ := fun n z => energy (massInverse (gram J) (δ n)) (gram J (u z))
  let D : ℕ → ℝ → ℝ := fun n z => 2*(inner ℂ (d z)
    (massInverse (gram J) (δ n) (gram J (u z)))).re
  have herr (n : ℕ) (z : ℝ) : D n z = -2*(inner ℂ (d z) (damping (gram J) (δ n) (u z))).re :=
    regularized_slope_error (gram J) hs hp _ (hδ n) (u z) (d z) (hz z)
  apply conserved_of_regularized_energies A D (fun z => ‖J (u z)‖^2) s t
    (2*K (max |s| |t|)*R (max |s| |t|))
  · intro n z
    apply energy_derivative_of_weak _ (massInverse_symmetric (gram J) hs hp _ (hδ n))
      (fun z => gram J (u z)) (d z) z (K (|z|+1)) (hK _)
    · have he : ∀ᶠ h in 𝓝 (0:ℝ), |h| < 1 := by
        simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually
          (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hh
      have hsum : |z+h| ≤ |z|+|h| := by
        simpa only [sub_zero,zero_sub,sub_neg_eq_add,abs_neg,zero_add] using abs_sub_le z 0 (-h)
      simpa only [add_sub_cancel_left] using hl (|z|+1) z (z+h) (by positivity)
        (by linarith) (hsum.trans (by linarith))
    · exact heq z
  · intro n
    have hc := weak_strong_pairing_continuous d
      (fun z => massInverse (gram J) (δ n) (gram J (u z))) K hd hw
      ((massInverse (gram J) (δ n)).continuous.comp hgc)
    exact continuous_const.mul (Complex.continuous_re.comp hc)
  · intro n z hzt
    have hT : 0 ≤ max |s| |t| := le_max_of_le_left (abs_nonneg s)
    have hsz : |z| ≤ max |s| |t| := by
      rcases mem_uIcc.mp hzt with h | h
      · exact abs_le.mpr ⟨by have := neg_abs_le s; linarith [le_max_left |s| |t|],
          by have := le_abs_self t; linarith [le_max_right |s| |t|]⟩
      · exact abs_le.mpr ⟨by have := neg_abs_le t; linarith [le_max_right |s| |t|],
          by have := le_abs_self s; linarith [le_max_left |s| |t|]⟩
    rw [herr]
    apply (energy_error_norm_bound _ _).trans
    have hy := (damping_contraction (gram J) hs hp _ (hδ n) (u z)).trans (hu _ _ hT hsz)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hd _ _ hT hsz) (by norm_num)) hy
      (norm_nonneg _) (by have := hK (max |s| |t|); positivity)
  · intro z
    exact embedded_energy_limit J hj δ hδ hlim (u z)
  · intro z
    simpa only [herr] using embedded_damping_pairing_limit J hj δ hδ hlim (u z) (d z)

#print axioms norm_square_conserved

end
end UnifiedTheory.Audit.KFCausalWeakMassConservation
