/- All eight first-factor energies and form responses have physical
strong-limit representatives. The five clock/kinetic factors have an
absolute relative bound independent of the correlated family. This
does not supply a general potential response estimate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllFactorLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredKineticResponseLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockCompositionLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFormBounds
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredAllFactorLimit (output momentumOutput output_tendsto momentumOutput_tendsto)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "U" => output f ε h a p hε hh hb ha
local notation "V" => momentumOutput f ε h a p hε hh hb ha
local notation "F" => KFCausalCorrelatedClusteredPhysicalCauchy.finiteOutput f ε h a p hε hh hb ha
local notation "G" => KFCausalCorrelatedClusteredMomentumPotentialProfiles.finiteMomentumOutput f ε h a p hε hh hb ha

def factorEnergy (j : Fin 8) : ℝ := ‖U j‖^2
def factorResponse (j : Fin 8) : ℝ := (-2/h)*(inner ℂ (U j) (V j)).im

theorem energy_tendsto (j : Fin 8) :
    Tendsto (fun δ => ‖F δ j‖^2) (𝓝[>] 0) (𝓝 (factorEnergy f ε h a p hε hh hb ha j)) :=
  (output_tendsto f ε h a p hε hh hb ha j).norm.pow 2

theorem response_tendsto (j : Fin 8) :
    Tendsto (fun δ => (-2/h)*(inner ℂ (F δ j) (G δ j)).im) (𝓝[>] 0)
      (𝓝 (factorResponse f ε h a p hε hh hb ha j)) := by
  have hp := (output_tendsto f ε h a p hε hh hb ha j).inner (𝕜 := ℂ)
    (momentumOutput_tendsto f ε h a p hε hh hb ha j)
  exact ((Complex.continuous_im.tendsto _).comp hp).const_mul (-2/h)

theorem weighted_energy_tendsto (w : Fin 8 → ℝ) :
    Tendsto (fun δ => ∑ j, w j*‖F δ j‖^2) (𝓝[>] 0)
      (𝓝 (∑ j, w j*factorEnergy f ε h a p hε hh hb ha j)) :=
  tendsto_finset_sum Finset.univ (fun j _ => (energy_tendsto f ε h a p hε hh hb ha j).const_mul (w j))

theorem weighted_response_tendsto (w : Fin 8 → ℝ) :
    Tendsto (fun δ => ∑ j, w j*((-2/h)*(inner ℂ (F δ j) (G δ j)).im)) (𝓝[>] 0)
      (𝓝 (∑ j, w j*factorResponse f ε h a p hε hh hb ha j)) :=
  tendsto_finset_sum Finset.univ (fun j _ => (response_tendsto f ε h a p hε hh hb ha j).const_mul (w j))

def clockKineticIndex (j : Fin 5) : Fin 8 := ⟨j.val,by omega⟩

theorem clockKinetic_abs_bound (j : Fin 5) :
    |factorResponse f ε h a p hε hh hb ha (clockKineticIndex j)| ≤
      (1/(4*ε))*factorEnergy f ε h a p hε hh hb ha (clockKineticIndex j) := by
  fin_cases j
  · have hx : -(1/(4*ε))*‖U 0‖^2 ≤ (-2/h)*(inner ℂ (U 0) (V 0)).im ∧
        (-2/h)*(inner ℂ (U 0) (V 0)).im ≤ 0 :=
      KFCausalCorrelatedClusteredClockCompositionLimit.clock_response_bounds f ε h a p hε hh hb ha
    change |(-2/h)*(inner ℂ (U 0) (V 0)).im| ≤ (1/(4*ε))*‖U 0‖^2
    rw [abs_of_nonpos hx.2]
    linarith [hx.1]
  · have hx := KFCausalCorrelatedClusteredKineticResponseLimit.response_bounds f ε h a p hε hh ha 0
    exact (abs_of_nonneg hx.1).trans_le hx.2
  · have hx := KFCausalCorrelatedClusteredKineticResponseLimit.response_bounds f ε h a p hε hh ha 1
    exact (abs_of_nonneg hx.1).trans_le hx.2
  · have hx := KFCausalCorrelatedClusteredKineticResponseLimit.response_bounds f ε h a p hε hh ha 2
    exact (abs_of_nonneg hx.1).trans_le hx.2
  · have hx := KFCausalCorrelatedClusteredKineticResponseLimit.response_bounds f ε h a p hε hh ha 3
    exact (abs_of_nonneg hx.1).trans_le hx.2

theorem weighted_clockKinetic_bound (w : Fin 5 → ℝ) (hw : ∀ j, 0 ≤ w j) :
    |∑ j, w j*factorResponse f ε h a p hε hh hb ha (clockKineticIndex j)| ≤
      (1/(4*ε))*(∑ j, w j*factorEnergy f ε h a p hε hh hb ha (clockKineticIndex j)) := by
  calc
    _ ≤ ∑ j, |w j*factorResponse f ε h a p hε hh hb ha (clockKineticIndex j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, w j*((1/(4*ε))*factorEnergy f ε h a p hε hh hb ha (clockKineticIndex j)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (hw j)]
      exact mul_le_mul_of_nonneg_left (clockKinetic_abs_bound f ε h a p hε hh hb ha j) (hw j)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

#print axioms energy_tendsto
#print axioms response_tendsto
#print axioms weighted_energy_tendsto
#print axioms weighted_response_tendsto
#print axioms clockKinetic_abs_bound
#print axioms weighted_clockKinetic_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFormBounds
