/- The phase weight also converges at the sqrt(abs(hbar))-rescaled
fluctuations around each displaced centre. This supplies the physical
clock-plus-shear exponential, not yet the full Gaussian or energy limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
import UnifiedTheory.Audit.KFCausalDisplacedClassicalAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase (phaseRatio phaseRatio_energy_tendsto)

theorem relativeScale_slope (ε q : ℝ) (hε : 0 < ε) :
    Tendsto (fun h : ℝ => (h:ℂ)⁻¹*(relativeScale ε q h-1)) (𝓝[≠] (0:ℝ))
      (𝓝 (-Complex.I/(4*(realClock ε hε q:ℂ)))) := by
  convert (relativeScale_derivative ε q hε).tendsto_slope using 1
  funext h
  simp only [slope_def_module,sub_zero,Complex.real_smul,Complex.ofReal_inv,relativeScale_zero]

theorem transverseRatio_eq (ε q h : ℝ) (Q P : Transverse) :
    transverseRatio ε q h Q P =
      Complex.exp (2*Complex.I*((h:ℂ)⁻¹*(relativeScale ε q h-1))*(shear Q P:ℂ)) := by
  unfold transverseRatio
  congr 1
  simp [shiftedPosition,shear,velocity,Fin.sum_univ_succ]
  ring

theorem shear_continuous : Continuous (fun z : Transverse × Transverse => shear z.1 z.2) := by
  simp [shear,velocity,Fin.sum_univ_succ]
  fun_prop

theorem varying_ratio_tendsto (ε q : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (Q P : ℕ → Transverse) (Q₀ P₀ : Transverse)
    (hQ : Tendsto Q atTop (𝓝 Q₀)) (hP : Tendsto P atTop (𝓝 P₀)) :
    Tendsto (fun n => transverseRatio ε q (h n) (Q n) (P n)) atTop
      (𝓝 (Complex.exp ((shear Q₀ P₀/(2*realClock ε hε q):ℝ):ℂ))) := by
  have hn : Tendsto h atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => hh n)⟩
  have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (shear_continuous.continuousAt.tendsto.comp (hQ.prodMk_nhds hP))
  have ht := (((relativeScale_slope ε q hε).comp hn).const_mul (2*Complex.I)).mul hs
  have he := Complex.continuous_exp.continuousAt.tendsto.comp ht
  simp_rw [transverseRatio_eq]
  convert he using 1
  congr 2
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

def rescaledPosition (h : ℝ) (Q ξ : Transverse) : Transverse :=
  fun i => Q i+Real.sqrt |h| * ξ i

theorem rescaledPosition_tendsto (Q ξ : Transverse) :
    Tendsto (fun h => rescaledPosition h Q ξ) (𝓝 (0:ℝ)) (𝓝 Q) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hi : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0) := tendsto_id
  have ht := ((hi.abs).sqrt.mul_const (ξ i)).const_add (Q i)
  simpa only [rescaledPosition,abs_zero,Real.sqrt_zero,zero_mul,add_zero] using ht

theorem rescaled_phase_energy_tendsto (ε q r : ℝ) (hε : 0 < ε) (Q P ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖phaseRatio ε r q (h n)*
      transverseRatio ε q (h n) (rescaledPosition (h n) Q ξ) P‖^2) atTop
      (𝓝 (Real.exp ((r+shear Q P)/realClock ε hε q))) := by
  have hn : Tendsto h atTop (𝓝[≠] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall (fun n => hh n)⟩
  have hp := (phaseRatio_energy_tendsto ε r q hε).comp hn
  have ht := (varying_ratio_tendsto ε q hε h hh hz
    (fun n => rescaledPosition (h n) Q ξ) (fun _ => P) Q P
    ((rescaledPosition_tendsto Q ξ).comp hz) tendsto_const_nhds).norm.pow 2
  rw [Complex.norm_exp,Complex.ofReal_re,← Real.exp_nat_mul] at ht
  have he : (2:ℝ)*(shear Q P/(2*realClock ε hε q)) = shear Q P/realClock ε hε q := by ring
  norm_num only [Nat.cast_ofNat] at ht
  rw [he] at ht
  simpa only [norm_mul,mul_pow,← Real.exp_add,← add_div] using hp.mul ht

theorem physical_shear (z : KFCausalClassicalChargePhase.Phase) :
    shear (KFCausalClassicalChargePhase.physicalTail z.1) (KFCausalClassicalChargePhase.physicalTail z.2) =
      KFCausalClassicalChargePhase.shear z := rfl

theorem boosted_orbit_phase_energy_tendsto (ε q : ℝ) (hε : 0 < ε)
    (p : KFCausalCoupledLongitudinalFlow.Configuration) (θ : ℝ) (ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n =>
      let z := KFCausalDisplacedPhysicalPhase.phase (h n)
        (KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostQ (h n) ((h n)⁻¹ • p)))
        (KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostK ((h n)⁻¹ • p)))
      ‖phaseRatio ε p.1 q (h n)*transverseRatio ε q (h n)
        (rescaledPosition (h n) (KFCausalClassicalChargePhase.physicalTail z.1) ξ)
        (KFCausalClassicalChargePhase.physicalTail z.2)‖^2) atTop
      (𝓝 (Real.exp ((p.1+KFCausalClassicalChargePhase.shear
        (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/
          realClock ε hε q))) := by
  have he (n : ℕ) := KFCausalDisplacedPhysicalPhase.phase_boost_orbit (h n) (hh n) p θ
  simp_rw [he]
  exact rescaled_phase_energy_tendsto ε q p.1 hε _ _ ξ h hh hz

#print axioms relativeScale_slope
#print axioms transverseRatio_eq
#print axioms shear_continuous
#print axioms varying_ratio_tendsto
#print axioms rescaledPosition_tendsto
#print axioms rescaled_phase_energy_tendsto
#print axioms physical_shear
#print axioms boosted_orbit_phase_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit
