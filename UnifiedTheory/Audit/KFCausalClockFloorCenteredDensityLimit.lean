/- Pointwise convergence of the full centred transverse density. Exact
width rescaling and the vanishing complex displacement error supply the
Gaussian part; the previous phase theorem supplies clock and neutral shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian
open UnifiedTheory.Audit.KFCausalClockFloorRescaledDisplacement
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive scale_groundWidth scale_neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase (phaseRatio)
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)

theorem quadratic_scale (α β c : ℝ) (v : Fin 5 → ℂ) :
    quadratic α β (fun i => (c:ℂ)*v i) = quadratic (c^2*α) (c^2*β) v := by
  simp [quadratic,weight,Fin.sum_univ_succ]
  ring

theorem quadratic_real (α β : ℝ) (x : Transverse) :
    quadratic α β (fun i => (x i:ℂ)) = (realQuadratic α β x:ℂ) := by
  simp [quadratic,realQuadratic,Fin.sum_univ_succ]

theorem quadratic_rescaled (ε q h : ℝ) (hh : h ≠ 0) (Q ξ : Transverse) :
    quadratic (groundWidth h) (neutralWidth h)
      (fun i => shiftedPosition ε q h (rescaledPosition h Q ξ) i-(Q i:ℂ)) =
      quadratic (groundWidth 1) (neutralWidth 1) (fluctuation ε q h Q ξ) := by
  have hs := Complex.ofReal_ne_zero.mpr (scale_positive h hh).ne'
  have he : (fun i => shiftedPosition ε q h (rescaledPosition h Q ξ) i-(Q i:ℂ)) =
      fun i => (scale h:ℂ)*fluctuation ε q h Q ξ i := by
    funext i
    unfold fluctuation
    field_simp
  rw [he,quadratic_scale,scale_groundWidth h hh,scale_neutralWidth h hh]

def gaussianFactor (ε q h : ℝ) (Q ξ : Transverse) : ℂ :=
  Complex.exp (-quadratic (groundWidth h) (neutralWidth h)
    (fun i => shiftedPosition ε q h (rescaledPosition h Q ξ) i-(Q i:ℂ)))

theorem gaussianFactor_tendsto (ε q : ℝ) (hε : 0 < ε) (Q ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => gaussianFactor ε q (h n) Q ξ) atTop
      (𝓝 (Complex.exp (-(realQuadratic (groundWidth 1) (neutralWidth 1) ξ:ℂ)))) := by
  have hf := tendsto_pi_nhds.mpr (fun i => fluctuation_tendsto ε q hε Q ξ h hh hz i)
  have hc : Continuous (fun v : Fin 5 → ℂ => Complex.exp (-quadratic (groundWidth 1) (neutralWidth 1) v)) := by
    unfold quadratic
    fun_prop
  have ht := hc.continuousAt.tendsto.comp hf
  simp_rw [gaussianFactor,quadratic_rescaled ε q _ (hh _)]
  simpa only [quadratic_real] using ht

theorem packet_phase_factor (α β ε q h : ℝ) (Q P X : Transverse) :
    packet α β Q (fun i => P i/h) (shiftedPosition ε q h X) =
      Complex.exp (-quadratic α β (fun i => shiftedPosition ε q h X i-(Q i:ℂ))) *
        (Complex.exp (Complex.I*linear (fun i => P i/h) (fun i => (X i:ℂ))) *
          transverseRatio ε q h X P) := by
  unfold packet transverseRatio
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [linear,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Complex.ofReal_div]
  ring

theorem real_phase_norm (R X : Transverse) :
    ‖Complex.exp (Complex.I*linear R (fun i => (X i:ℂ)))‖ = 1 := by
  simp [Complex.norm_exp,linear,Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im]

def density (ε q h r : ℝ) (Q P ξ : Transverse) : ℝ :=
  ‖phaseRatio ε r q h * packet (groundWidth h) (neutralWidth h) Q (fun i => P i/h)
    (shiftedPosition ε q h (rescaledPosition h Q ξ))‖^2

theorem density_factor (ε q h r : ℝ) (Q P ξ : Transverse) :
    density ε q h r Q P ξ = ‖gaussianFactor ε q h Q ξ‖^2 *
      ‖phaseRatio ε r q h*transverseRatio ε q h (rescaledPosition h Q ξ) P‖^2 := by
  rw [density,packet_phase_factor]
  simp only [norm_mul,real_phase_norm,one_mul,gaussianFactor,mul_pow]
  ring

theorem density_tendsto (ε q r : ℝ) (hε : 0 < ε) (Q P ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => density ε q (h n) r Q P ξ) atTop
      (𝓝 (Real.exp (-2*realQuadratic (groundWidth 1) (neutralWidth 1) ξ) *
        Real.exp ((r+shear Q P)/realClock ε hε q))) := by
  have hg := (gaussianFactor_tendsto ε q hε Q ξ h hh hz).norm.pow 2
  rw [Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,← Real.exp_nat_mul] at hg
  have he : (2:ℝ)*(-realQuadratic (groundWidth 1) (neutralWidth 1) ξ) =
      -2*realQuadratic (groundWidth 1) (neutralWidth 1) ξ := by ring
  norm_num only [Nat.cast_ofNat] at hg
  rw [he] at hg
  simp_rw [density_factor]
  exact hg.mul (rescaled_phase_energy_tendsto ε q r hε Q P ξ h hh hz)

#print axioms quadratic_scale
#print axioms quadratic_real
#print axioms quadratic_rescaled
#print axioms gaussianFactor_tendsto
#print axioms packet_phase_factor
#print axioms real_phase_norm
#print axioms density_factor
#print axioms density_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit
