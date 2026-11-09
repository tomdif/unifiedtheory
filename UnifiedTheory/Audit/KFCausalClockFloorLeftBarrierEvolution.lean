/- Defect-norm monotonicity implies bounded negative-clock barrier
monotonicity under the actual quantum propagator, by inverse order. -/
import UnifiedTheory.Audit.KFCausalUnitaryInverseOrder
import UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
import UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hh m g k

theorem inverse_pairing (b : ℝ) (hb : 0 < b) (f : Hilbert) :
    (inner ℂ f (((b:ℂ)⁻¹ • barrier ε hε b hb) f)).re =
      b⁻¹*(inner ℂ f (barrier ε hε b hb f)).re := by
  rw [ContinuousLinearMap.smul_apply,inner_smul_right,← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem expectation_le_initial (b : ℝ) (hb : 0 < b) (s t : ℝ) (hst : s ≤ t)
    (f : Hilbert) :
    (inner ℂ (U s t f) (barrier ε hε b hb (U s t f))).re ≤
      (inner ℂ f (barrier ε hε b hb f)).re := by
  have hi := KFCausalUnitaryInverseOrder.inverse_unitary_order
    (shifted ε hε b) ((b:ℂ)⁻¹ • barrier ε hε b hb)
    (shifted_symmetric ε hε b) (shifted_nonnegative ε hε b hb)
    (inverse_equation ε hε b hb) (U s t) (fun x => by
      rw [shifted_quadratic,shifted_quadratic,evolution_norm]
      have hd := evolution_defect_le_initial ε hε h hne hh m g k s t hst x
      have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
      linarith) f
  rw [inverse_pairing,inverse_pairing] at hi
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hb)).mp hi

theorem expectation_antitone (b : ℝ) (hb : 0 < b) (s : ℝ) (f : Hilbert) :
    Antitone (fun t => (inner ℂ (U s t f) (barrier ε hε b hb (U s t f))).re) := by
  intro r t hrt
  have hi := expectation_le_initial ε hε h hne hh m g k b hb r t hrt (U s r f)
  have hc : U r t (U s r f) = U s t f :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
      (evolution_compose ε hε h hne hh m g k s r t)
  simpa only [hc] using hi

theorem low_probability_le_initial_barrier (b : ℝ) (hb : 0 < b) (S : ℝ)
    (hS : 2*Real.exp S ≤ b*ε) (s t : ℝ) (hst : s ≤ t) (f : Hilbert) :
    ‖KFCausalClockFloorDefectLocalization.lowProjection S (U s t f)‖^2 ≤
      2*(inner ℂ f (barrier ε hε b hb f)).re :=
  (low_probability_bound ε hε b hb S hS (U s t f)).trans
    (mul_le_mul_of_nonneg_left
      (expectation_le_initial ε hε h hne hh m g k b hb s t hst f) (by norm_num))

#print axioms inverse_pairing
#print axioms expectation_le_initial
#print axioms expectation_antitone
#print axioms low_probability_le_initial_barrier
end
end UnifiedTheory.Audit.KFCausalClockFloorLeftBarrierEvolution
