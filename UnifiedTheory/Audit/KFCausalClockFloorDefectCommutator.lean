/- An actual half-exponential/defect commutator bound on the constructed
coherent family and all its finite defect powers. This proves both required
graph memberships; it does not assume a commutator domain or a propagated
state remains in this family. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
import UnifiedTheory.Audit.KFCausalClockFloorDefectShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectCommutator
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

/-- The two images are the already proved graph outputs of A(D f) and A f,
where A is the actual exp(L/2). The right side retains two defect factors. -/
theorem shifted_commutator_bound (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    ‖state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs -
      defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs)‖ ≤
    (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε
      (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs))‖ := by
  let g := state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs
  let gD := state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs
  change ‖gD-defectOperator ε hε g‖ ≤ (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε g)‖
  rw [← (straightening ε hε).norm_map (gD-defectOperator ε hε g),
    ← (straightening ε hε).norm_map (defectOperator ε hε (defectOperator ε hε g)),map_sub]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (straightening ε hε gD) (straightening ε hε (defectOperator ε hε g)),
    state_coe ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs,
    state_coe ε a α β p b hε ha hα hβ hw n (-hbar/2) hs,
    straightening_defect_coe ε hε g,
    straightening_defect_coe ε hε (defectOperator ε hε g)] with x hsub hD hg hd hdd
  change (straightening ε hε gD) x = _ at hD
  change (straightening ε hε g) x = _ at hg
  rw [hsub,Pi.sub_apply,hdd,hd,hD,hg]
  let z := complexDefect ε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)
  let d := realDefect ε hε (x 0)
  let v := profile ε a α β p b (-hbar/2) x
  change ‖z^(n+1)*v-(d:ℂ)*(z^n*v)‖ ≤ (2*|hbar|/ε)*‖(d:ℂ)*((d:ℂ)*(z^n*v))‖
  have he : z^(n+1)*v-(d:ℂ)*(z^n*v) = (z-(d:ℂ))*(z^n*v) := by rw [pow_succ]; ring
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < d from realDefect_positive ε hε (x 0))]
  have hb := mul_le_mul_of_nonneg_right (half_exponential_shift_difference ε hbar (x 0) hε hh)
    (norm_nonneg (z^n*v))
  change ‖z-(d:ℂ)‖ * ‖z^n*v‖ ≤ (2*|hbar|/ε)*d^2*‖z^n*v‖ at hb
  simpa only [norm_mul,pow_two,mul_assoc] using hb

/-- Multiplication by the defect also has a graph-norm estimate on this
family. The small real defect is retained on the exponential output. -/
theorem shifted_defect_bound (n : ℕ) (hbar : ℝ)
    (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    ‖state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs‖ ≤
      2*‖defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs)‖ := by
  let g := state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs
  let gD := state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs
  change ‖gD‖ ≤ 2*‖defectOperator ε hε g‖
  rw [← (straightening ε hε).norm_map gD,
    ← (straightening ε hε).norm_map (defectOperator ε hε g)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [state_coe ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs,
    state_coe ε a α β p b hε ha hα hβ hw n (-hbar/2) hs,
    straightening_defect_coe ε hε g] with x hD hg hd
  change (straightening ε hε gD) x = _ at hD
  change (straightening ε hε g) x = _ at hg
  rw [hD,hd,hg,pow_succ']
  rw [mul_assoc]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (realDefect_positive ε hε (x 0))]
  have hb := complexDefect_norm_bound ε hε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)
    (by simpa using hs)
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero] at hb
  have ht := mul_le_mul_of_nonneg_right hb (mul_nonneg
    (norm_nonneg (complexDefect ε ((x 0:ℂ)+(-hbar/2:ℝ)*Complex.I)^n))
    (norm_nonneg (profile ε a α β p b (-hbar/2) x)))
  simpa only [mul_assoc] using ht

/-- Domain-checked formulation: both exponentials exist and their commutator
is controlled by D squared applied to the actual exponential output. -/
theorem exponential_defect_commutator (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) :
    ∃ g gD : Hilbert,
      (state ε a α β p b hε ha hα hβ hw n 0 h0,g) ∈
        (longitudinalExponential ε hε hbar (1/2)).graph ∧
      (defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n 0 h0),gD) ∈
        (longitudinalExponential ε hε hbar (1/2)).graph ∧
      ‖gD-defectOperator ε hε g‖ ≤
        (2*|hbar|/ε)*‖defectOperator ε hε (defectOperator ε hε g)‖ := by
  have hs : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact ⟨_,_,state_half_graph ε a α β p b hε ha hα hβ hw n hbar hh h0 hs,
    defect_state_half_graph ε a α β p b hε ha hα hβ hw n hbar hh h0 hs,
    shifted_commutator_bound ε a α β p b hε ha hα hβ hw n hbar hh hs⟩

#print axioms shifted_commutator_bound
#print axioms shifted_defect_bound
#print axioms exponential_defect_commutator

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectCommutator
