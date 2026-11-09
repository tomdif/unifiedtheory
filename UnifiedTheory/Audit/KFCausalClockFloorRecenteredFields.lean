/- The ordered physical field is evaluated at the real recentered position.
Its displaced centre survives the limit. Polynomial field growth is absorbed
by a weaker, fixed Gaussian, uniformly on bounded centre orbits. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedExponentialSymbol

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow flow_compose flow_initial)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition rescaledPosition_tendsto)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity (recenter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (grouped)
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (fieldLine)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates (energy energy_lower energy_nonnegative)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant (gaussianEnvelope)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (rotate physicalTail)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

theorem fieldLine_recenter (ε : ℝ) (hε : 0 < ε) (u h : ℝ) (Q ξ : Transverse)
    (l : Transverse →L[ℝ] ℝ) :
    fieldLine ε hε l (u,recenter ε hε u h Q ξ) = l (rescaledPosition h Q ξ) := by
  have hv (X : Transverse) : ![X 0,X 1,X 2,X 3,X 4] = X := by
    funext i
    fin_cases i <;> rfl
  let s := (KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm u
  change l (flow s ![flow (-s) (rescaledPosition h Q ξ) 0,
    flow (-s) (rescaledPosition h Q ξ) 1,flow (-s) (rescaledPosition h Q ξ) 2,
    flow (-s) (rescaledPosition h Q ξ) 3,flow (-s) (rescaledPosition h Q ξ) 4]) = _
  rw [hv,flow_compose,neg_add_cancel,flow_initial]

def fieldPower (j : Fin 2) (l : Transverse →L[ℝ] ℝ) (X : Transverse) : ℝ := (l X)^(j.val+1)

theorem fieldPower_tendsto (j : Fin 2) (l : Transverse →L[ℝ] ℝ) (Q ξ : Transverse)
    (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => fieldPower j l (rescaledPosition (h n) Q ξ)) atTop (𝓝 (fieldPower j l Q)) :=
  (l.continuous.continuousAt.tendsto.comp ((rescaledPosition_tendsto Q ξ).comp hz)).pow (j.val+1)

theorem field_square_bound (l : Transverse →L[ℝ] ℝ) (X : Transverse) :
    (l X)^2 ≤ 64*‖l‖^2*energy X := by
  have hs : 0 ≤ ∑ i : Fin 5, (X i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖X‖ ≤ Real.sqrt (∑ i : Fin 5, (X i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  have hsq := pow_le_pow_left₀ (norm_nonneg X) hn 2
  rw [Real.sq_sqrt hs] at hsq
  have hl := pow_le_pow_left₀ (norm_nonneg (l X)) (l.le_opNorm X) 2
  simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hl
  have he : ‖X‖^2 ≤ 64*energy X := by linarith [energy_lower X]
  exact hl.trans (by simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left he (sq_nonneg ‖l‖))

def fieldBound (l : Transverse →L[ℝ] ℝ) (Q : Transverse) : ℝ :=
  1+2*(l Q)^2+128*‖l‖^2

theorem rescaled_field_bound (h : ℝ) (h1 : |h| ≤ 1) (Q ξ : Transverse) (l : Transverse →L[ℝ] ℝ) :
    (l (rescaledPosition h Q ξ))^2 ≤ fieldBound l Q*(1+energy ξ) := by
  have he : l (rescaledPosition h Q ξ) = l Q+scale h*l ξ := by
    change l (Q+scale h • ξ) = _
    rw [map_add,map_smul,smul_eq_mul]
  have hs : (scale h)^2 ≤ 1 := by rw [scale,Real.sq_sqrt (abs_nonneg h)]; exact h1
  have hf := field_square_bound l ξ
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (l ξ))
  rw [he]
  unfold fieldBound
  nlinarith [sq_nonneg (l Q-scale h*l ξ),energy_nonnegative ξ,
    mul_nonneg (sq_nonneg (l Q)) (energy_nonnegative ξ)]

theorem fieldPower_square_bound (j : Fin 2) (h : ℝ) (h1 : |h| ≤ 1)
    (Q ξ : Transverse) (l : Transverse →L[ℝ] ℝ) :
    (fieldPower j l (rescaledPosition h Q ξ))^2 ≤ (fieldBound l Q)^2*(1+energy ξ)^2 := by
  have hb := rescaled_field_bound h h1 Q ξ l
  have hD : 1 ≤ fieldBound l Q := by unfold fieldBound; nlinarith [sq_nonneg (l Q),sq_nonneg ‖l‖]
  have hE : 1 ≤ 1+energy ξ := by linarith [energy_nonnegative ξ]
  have hp : 1 ≤ fieldBound l Q*(1+energy ξ) := one_le_mul_of_one_le_of_one_le hD hE
  have hsq := pow_le_pow_left₀ (sq_nonneg (l (rescaledPosition h Q ξ))) hb 2
  fin_cases j
  · simp only [fieldPower,zero_add,pow_one]
    nlinarith [sq_nonneg (fieldBound l Q*(1+energy ξ)-1)]
  · simpa only [fieldPower,Fin.val_one,show (1:ℕ)+1=2 from rfl,mul_pow] using hsq

theorem polynomial_absorption (ξ : Transverse) :
    (1+energy ξ)^2*gaussianEnvelope (1/4) ξ ≤ 256*gaussianEnvelope (1/8) ξ := by
  have he : 1+energy ξ ≤ 16*Real.exp (energy ξ/16) := by
    linarith [Real.add_one_le_exp (energy ξ/16)]
  have hsq := pow_le_pow_left₀ (by linarith [energy_nonnegative ξ] : 0 ≤ 1+energy ξ) he 2
  have hm := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-energy ξ/4)).le
  have hid : (16*Real.exp (energy ξ/16))^2*Real.exp (-energy ξ/4) =
      256*Real.exp (-energy ξ/8) := by
    rw [mul_pow,← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
    norm_num only [Nat.cast_ofNat,show (16:ℝ)^2 = 256 by norm_num]
    rw [show (2:ℝ)*(energy ξ/16)+(-energy ξ/4) = -energy ξ/8 by ring]
  simpa only [gaussianEnvelope,show -(1/4:ℝ)*energy ξ = -energy ξ/4 by ring,
    show -(1/8:ℝ)*energy ξ = -energy ξ/8 by ring,hid] using hm

def orbitCentre (p : Configuration) (θ : ℝ) : Transverse :=
  physicalTail (rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)).1

theorem fieldBound_orbit (l : Transverse →L[ℝ] ℝ) (p : Configuration) :
    ∃ D : ℝ, ∀ θ, (fieldBound l (orbitCentre p θ))^2 ≤ D := by
  let z : KFCausalClassicalChargePhase.Phase := (0,KFCausalClassicalPhysicalPhase.toPaired p)
  have hQ : Continuous (fun θ => physicalTail (rotate θ z).1) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [physicalTail,KFCausalPairedModeCoordinates.backward,rotate] <;> fun_prop
  have hc : Continuous (fun θ => (fieldBound l (physicalTail (rotate θ z).1))^2) := by
    unfold fieldBound
    have hl := l.continuous.comp hQ
    fun_prop
  have hp : Function.Periodic (fun θ => (fieldBound l (physicalTail (rotate θ z).1))^2) (2*Real.pi) := by
    intro θ
    dsimp only
    rw [KFCausalDisplacedClassicalAverage.rotate_period]
  obtain ⟨D,hD⟩ := (hp.compact_of_continuous (by positivity) hc).bddAbove
  exact ⟨D,fun θ => hD ⟨-θ,rfl⟩⟩

#print axioms fieldLine_recenter
#print axioms fieldPower_tendsto
#print axioms field_square_bound
#print axioms rescaled_field_bound
#print axioms fieldPower_square_bound
#print axioms polynomial_absorption
#print axioms fieldBound_orbit

end
end UnifiedTheory.Audit.KFCausalClockFloorRecenteredFields
