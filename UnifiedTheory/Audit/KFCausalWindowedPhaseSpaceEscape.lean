/- Weak escape implies loss of windowed phase-space mass on every
finite-volume raw region, hence on every bounded physical phase region.
The probability law is the existing tensor/shear/Fourier construction. -/
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceProbe
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceEscape
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceState
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceProbe
open UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceLaw

variable (n : ℕ)

theorem local_integral_decay (f : ℝ → BlockHilbert n) (g : BlockHilbert n)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hw : ∀ z : BlockHilbert n, Tendsto (fun t => inner ℂ (f t) z) atTop (𝓝 0))
    (A : Set (Block n × Block n)) (hA : volume A < ∞) :
    Tendsto (fun t => ∫ z in A, ‖amplitude n (f t) g z‖^2) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hA.ne
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict A) (F := fun t z => ‖amplitude n (f t) g z‖^2)
    (f := fun _ => (0 : ℝ)) (fun _ => (C*‖g‖)^2)
    (Eventually.of_forall (fun t => ((amplitude_measurable n (f t) g).norm.pow 2).restrict))
    (Eventually.of_forall (fun t => Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) ((amplitude_bound n (f t) g z).trans
        (mul_le_mul_of_nonneg_right (hC t) (norm_nonneg g))) 2)))
    (integrable_const _) (Eventually.of_forall (fun z => by
      have hp := ((hw (probe n g z)).norm).pow 2
      simpa only [amplitude,norm_inner_symm (probe n g z),norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hp))
  simpa only [integral_zero] using ht

theorem raw_law_decay (f : ℝ → BlockHilbert n) (g : BlockHilbert n)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hw : ∀ z : BlockHilbert n, Tendsto (fun t => inner ℂ (f t) z) atTop (𝓝 0))
    (A : Set (Block n × Block n)) (hAm : MeasurableSet A) (hA : volume A < ∞) :
    Tendsto (fun t => KFCausalL2BornLaw.law volume (state n (f t) g) A) atTop (𝓝 0) := by
  have he (t : ℝ) : KFCausalL2BornLaw.law volume (state n (f t) g) A =
      ENNReal.ofReal (∫ z in A, ‖amplitude n (f t) g z‖^2) := by
    rw [KFCausalL2BornLaw.law_apply volume _ A hAm]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (state_coe n (f t) g)] with z hz
    rw [hz]
  simp_rw [he]
  simpa only [ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (local_integral_decay n f g C hC hw A hA)

def phaseHomeomorph (h : ℝ) (hne : h ≠ 0) :
    (Block n × Block n) ≃ₜ (Block n × Block n) where
  toFun := phaseCoordinates n h
  invFun z := ((2*Real.pi*h)⁻¹ • z.2,z.1)
  left_inv z := by
    have hc : 2*Real.pi*h ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hne
    simp only [phaseCoordinates,smul_smul,inv_mul_cancel₀ hc,one_smul,Prod.mk.eta]
  right_inv z := by
    have hc : 2*Real.pi*h ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hne
    simp only [phaseCoordinates,smul_smul,mul_inv_cancel₀ hc,one_smul,Prod.mk.eta]
  continuous_toFun := by unfold phaseCoordinates; fun_prop
  continuous_invFun := by fun_prop

theorem law_region_decay (h : ℝ) (f : ℝ → BlockHilbert n) (g : BlockHilbert n)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hw : ∀ z : BlockHilbert n, Tendsto (fun t => inner ℂ (f t) z) atTop (𝓝 0))
    (A : Set (Block n × Block n)) (hAm : MeasurableSet A)
    (hA : volume ((phaseCoordinates n h) ⁻¹' A) < ∞) :
    Tendsto (fun t => law n h (f t) g A) atTop (𝓝 0) := by
  have ht := raw_law_decay n f g C hC hw ((phaseCoordinates n h) ⁻¹' A)
    (hAm.preimage (phaseCoordinates_measurable n h)) hA
  simpa only [law,Measure.map_apply (phaseCoordinates_measurable n h) hAm] using ht

theorem law_compact_decay (h : ℝ) (hne : h ≠ 0)
    (f : ℝ → BlockHilbert n) (g : BlockHilbert n) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hw : ∀ z : BlockHilbert n, Tendsto (fun t => inner ℂ (f t) z) atTop (𝓝 0))
    (A : Set (Block n × Block n)) (hA : IsCompact A) :
    Tendsto (fun t => law n h (f t) g A) atTop (𝓝 0) := by
  apply law_region_decay n h f g C hC hw A hA.measurableSet
  exact ((phaseHomeomorph n h hne).isCompact_preimage.mpr hA).measure_lt_top

theorem law_bounded_decay (h : ℝ) (hne : h ≠ 0)
    (f : ℝ → BlockHilbert n) (g : BlockHilbert n) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hw : ∀ z : BlockHilbert n, Tendsto (fun t => inner ℂ (f t) z) atTop (𝓝 0))
    (A : Set (Block n × Block n)) (hA : Bornology.IsBounded A) :
    Tendsto (fun t => law n h (f t) g A) atTop (𝓝 0) := by
  have ht := law_compact_decay n h hne f g C hC hw (closure A)
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hA.closure)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) (fun _ => measure_mono subset_closure)

#print axioms local_integral_decay
#print axioms raw_law_decay
#print axioms law_region_decay
#print axioms law_compact_decay
#print axioms law_bounded_decay

end
end UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceEscape
