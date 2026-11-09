/- The normalized neutral-position commutator of the kinetic part alone
is controlled by physical norm times full energy-output norm. This is not
the full Hamiltonian commutator: the matter rows are deliberately absent. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionKineticCommutator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (action action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralPositionKineticGraph
open UnifiedTheory.Audit.KFCausalNeutralPositionAveragedKinetics
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem modulateOutput_inverse (v : ℝ) (y : Outputs) :
    modulateOutput (-v) (modulateOutput v y) = y := by
  apply PiLp.ext
  intro i
  exact action_inverse v (y i)

theorem modulateOutput_dual (v : ℝ) (x y : Outputs) :
    inner ℂ x (modulateOutput v y) = inner ℂ (modulateOutput (-v) x) y := by
  have hinner (a b : Outputs) :
      inner ℂ (modulateOutput v a) (modulateOutput v b) = inner ℂ a b := by
    simp only [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (action v).inner_map_map (a i) (b i)
  have he := hinner (modulateOutput (-v) x) y
  have hi : modulateOutput v (modulateOutput (-v) x) = x := by
    simpa only [neg_neg] using modulateOutput_inverse (-v) x
  rwa [hi] at he

theorem modulateLp_dual (v : ℝ) (x y : OutputSpace) :
    inner ℂ x ((modulateOutput v).compLp y) = inner ℂ ((modulateOutput (-v)).compLp x) y := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(modulateOutput v).coeFn_compLp y,(modulateOutput (-v)).coeFn_compLp x] with θ hx hy
  rw [hx,hy,modulateOutput_dual]

def commutator (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ)
    (f g : Hilbert) (x y : OutputSpace) : ℂ :=
  inner ℂ x (transformed ε hε h hne v g y)-inner ℂ (transformed ε hε h hne (-v) f x) y

theorem commutator_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ)
    (f g : Hilbert) (x y : OutputSpace) :
    ‖commutator ε hε h hne v f g x y‖ ≤
      |h| *responseConstant ε v*(‖x‖*‖g‖+‖f‖*‖y‖) := by
  have he : commutator ε hε h hne v f g x y =
      inner ℂ x (transformed ε hε h hne v g y-(modulateOutput v).compLp y)-
        inner ℂ (transformed ε hε h hne (-v) f x-(modulateOutput (-v)).compLp x) y := by
    rw [inner_sub_right,inner_sub_left,modulateLp_dual]
    unfold commutator
    ring
  have hm : ‖transformed ε hε h hne (-v) f x-(modulateOutput (-v)).compLp x‖ ≤
      |h| *responseConstant ε v*‖f‖ := by
    simpa only [responseConstant,abs_neg] using transformed_correction_bound ε hε h hne (-v) f x
  rw [he]
  calc
    _ ≤ ‖inner ℂ x (transformed ε hε h hne v g y-(modulateOutput v).compLp y)‖+
        ‖inner ℂ (transformed ε hε h hne (-v) f x-(modulateOutput (-v)).compLp x) y‖ := norm_sub_le _ _
    _ ≤ ‖x‖*‖transformed ε hε h hne v g y-(modulateOutput v).compLp y‖+
        ‖transformed ε hε h hne (-v) f x-(modulateOutput (-v)).compLp x‖*‖y‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x‖*(|h| *responseConstant ε v*‖g‖)+(|h| *responseConstant ε v*‖f‖)*‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (transformed_correction_bound ε hε h hne v g y) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hm (norm_nonneg _))
    _ = _ := by ring

theorem normalized_commutator_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (v : ℝ)
    (f g : Hilbert) (x y : OutputSpace) :
    ‖commutator ε hε h hne v f g x y‖/|h| ≤
      responseConstant ε v*(‖x‖*‖g‖+‖f‖*‖y‖) := by
  apply (div_le_iff₀ (abs_pos.mpr hne)).mpr
  exact (commutator_bound ε hε h hne v f g x y).trans_eq (by ring)

open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k t
local notation "J" => embedding ε hε h hne hh m g k t
local notation "E" => energyOutput ε hε h hne hh m g k t

theorem completed_form_graph (u : V) :
    AveragedGraph ε h hne t (J u) (select.compLp (E u)) := by
  obtain ⟨w,rfl⟩ := graphFormVector_surjective ε hε h hne hh m g k t u
  exact full_averaged_graph ε hε h (hamiltonian_bound ε h hh) hne m g k t w

theorem completed_form_normalized_bound (v : ℝ) (u : V) :
    ‖commutator ε hε h hne v (J u) (J u)
      (select.compLp (E u)) (select.compLp (E u))‖/|h| ≤
      2*responseConstant ε v*‖J u‖*‖E u‖ := by
  have hs : ‖select.compLp (E u)‖ ≤ ‖E u‖ := by
    obtain ⟨w,rfl⟩ := graphFormVector_surjective ε hε h hne hh m g k t u
    exact selected_output_bound ε hε h (hamiltonian_bound ε h hh) hne m g k t w
  apply (normalized_commutator_bound ε hε h hne v (J u) (J u) _ _).trans
  have hb := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (responseConstant_nonneg ε v)) (norm_nonneg (J u)))
  nlinarith only [hb]

#print axioms modulateOutput_inverse
#print axioms modulateOutput_dual
#print axioms modulateLp_dual
#print axioms commutator_bound
#print axioms normalized_commutator_bound
#print axioms completed_form_graph
#print axioms completed_form_normalized_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionKineticCommutator
