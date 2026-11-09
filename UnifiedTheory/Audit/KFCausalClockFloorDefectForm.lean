/- Cubic control of the squared-defect form pairing for the actual
longitudinal exponential on the constructed analytic coherent family. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectCommutator
import UnifiedTheory.Audit.KFCausalClockFloorDefectShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
open UnifiedTheory.Audit.KFCausalClockFloorDefectShift
open UnifiedTheory.Audit.KFCausalClockFloorExponential

variable (ε a α β p : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
  (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

theorem shifted_square_commutator_bound (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    ‖state ε a α β p b hε ha hα hβ hw (n+2) (-hbar/2) hs -
      defectOperator ε hε (defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs))‖ ≤
    (6*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε (defectOperator ε hε
      (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs)))‖ := by
  let g := state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs
  let gDD := state ε a α β p b hε ha hα hβ hw (n+2) (-hbar/2) hs
  change ‖gDD-defectOperator ε hε (defectOperator ε hε g)‖ ≤
    (6*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε (defectOperator ε hε g))‖
  rw [← (straightening ε hε).norm_map (gDD-defectOperator ε hε (defectOperator ε hε g)),
    ← (straightening ε hε).norm_map (defectOperator ε hε (defectOperator ε hε (defectOperator ε hε g))),map_sub]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (straightening ε hε gDD) (straightening ε hε (defectOperator ε hε (defectOperator ε hε g))),
    state_coe ε a α β p b hε ha hα hβ hw (n+2) (-hbar/2) hs,
    state_coe ε a α β p b hε ha hα hβ hw n (-hbar/2) hs,
    straightening_defect_coe ε hε g,
    straightening_defect_coe ε hε (defectOperator ε hε g),
    straightening_defect_coe ε hε (defectOperator ε hε (defectOperator ε hε g))] with x hsub hD hg hd hdd hddd
  change (straightening ε hε gDD) x = _ at hD
  change (straightening ε hε g) x = _ at hg
  rw [hsub,Pi.sub_apply,hddd,hdd,hd,hD,hg]
  let z := complexDefect ε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)
  let d := realDefect ε hε (x 0)
  let v := profile ε a α β p b (-hbar/2) x
  change ‖z^(n+2)*v-(d:ℂ)*((d:ℂ)*(z^n*v))‖ ≤
    (6*|hbar|/ε)*‖(d:ℂ)*((d:ℂ)*((d:ℂ)*(z^n*v)))‖
  have he : z^(n+2)*v-(d:ℂ)*((d:ℂ)*(z^n*v)) = (z^2-(d:ℂ)^2)*(z^n*v) := by
    rw [pow_add]
    ring
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < d from realDefect_positive ε hε (x 0))]
  have hb := mul_le_mul_of_nonneg_right (half_exponential_square_difference ε hbar (x 0) hε hh)
    (norm_nonneg (z^n*v))
  change ‖z^2-(d:ℂ)^2‖ * ‖z^n*v‖ ≤ (6*|hbar|/ε)*d^3*‖z^n*v‖ at hb
  simpa only [norm_mul,pow_succ,pow_zero,one_mul,mul_assoc] using hb


theorem defect_inner (f g : Hilbert) :
    inner ℂ (defectOperator ε hε f) g = inner ℂ f (defectOperator ε hε g) := by
  have h := KFCausalClockFloorFourierMultiplier.real_multiplier_inner
    (fun x => realDefect ε hε (x 0))
    (straightening ε hε f) (straightening ε hε (defectOperator ε hε f))
    (straightening ε hε g) (straightening ε hε (defectOperator ε hε g))
    (straightening_defect_coe ε hε f) (straightening_defect_coe ε hε g)
  simpa only [LinearIsometryEquiv.inner_map_map] using h

theorem defect_square_inner_im_zero (g : Hilbert) :
    (inner ℂ g (defectOperator ε hε (defectOperator ε hε g))).im = 0 := by
  rw [← defect_inner ε hε g (defectOperator ε hε g)]
  exact inner_self_im (𝕜 := ℂ) _

theorem defect_pairing_bound (g h : Hilbert) :
    |(inner ℂ g h).im| ≤ ‖g‖*‖h-defectOperator ε hε (defectOperator ε hε g)‖ := by
  have hi := Complex.abs_im_le_norm (inner ℂ g (h-defectOperator ε hε (defectOperator ε hε g)))
  have hb := norm_inner_le_norm (𝕜 := ℂ) g (h-defectOperator ε hε (defectOperator ε hε g))
  rw [inner_sub_right,Complex.sub_im,defect_square_inner_im_zero ε hε g,sub_zero] at hi
  rw [inner_sub_right] at hb
  exact hi.trans hb

theorem shifted_square_form_bound (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    |(inner ℂ (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs)
      (state ε a α β p b hε ha hα hβ hw (n+2) (-hbar/2) hs)).im| ≤
      (6*|hbar|/ε)*‖state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs‖ *
      ‖defectOperator ε hε (defectOperator ε hε (defectOperator ε hε
        (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs)))‖ := by
  apply (defect_pairing_bound ε hε _ _).trans
  have hb := mul_le_mul_of_nonneg_left
    (shifted_square_commutator_bound ε a α β p b hε ha hα hβ hw n hbar hh hs)
    (norm_nonneg (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs))
  simpa only [mul_assoc,mul_left_comm] using hb

/-- The cubic estimate applies to the actual form pairing <A f,A(D^2 f)>.
This does not claim the full Hamiltonian propagator preserves this family. -/
theorem exponential_defect_square_form (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) :
    ∃ g gDD : Hilbert,
      (state ε a α β p b hε ha hα hβ hw n 0 h0,g) ∈
        (longitudinalExponential ε hε hbar (1/2)).graph ∧
      (defectOperator ε hε (defectOperator ε hε
        (state ε a α β p b hε ha hα hβ hw n 0 h0)),gDD) ∈
        (longitudinalExponential ε hε hbar (1/2)).graph ∧
      |(inner ℂ g gDD).im| ≤ (6*|hbar|/ε)*‖g‖*
        ‖defectOperator ε hε (defectOperator ε hε (defectOperator ε hε g))‖ := by
  have hs : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  refine ⟨_,_,state_half_graph ε a α β p b hε ha hα hβ hw n hbar hh h0 hs,?_,
    shifted_square_form_bound ε a α β p b hε ha hα hβ hw n hbar hh hs⟩
  rw [← state_zero_successor ε a α β p b hε ha hα hβ hw n h0,
    ← state_zero_successor ε a α β p b hε ha hα hβ hw (n+1) h0]
  exact state_half_graph ε a α β p b hε ha hα hβ hw (n+2) hbar hh h0 hs

#print axioms shifted_square_commutator_bound
#print axioms defect_inner
#print axioms defect_square_inner_im_zero
#print axioms defect_pairing_bound
#print axioms shifted_square_form_bound
#print axioms exponential_defect_square_form

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectForm
