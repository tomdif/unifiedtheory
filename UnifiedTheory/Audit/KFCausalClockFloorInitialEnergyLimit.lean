/- The full eight-factor initial energy converges on the explicit trial.
This is an initial unbounded-energy result, not propagation by a classical
flow and not a simultaneous small-clock-floor limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit
import UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay
import UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay
open UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit

theorem normalized_bound (ε a hbar r B : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (g : Hilbert) (hg : ‖g‖^2 ≤ r*B*gaussianMass (groundWidth hbar) (neutralWidth hbar)) :
    ‖g‖^2/‖trialState ε a hbar hε ha hh‖^2 ≤ r*B/clockMass ε a := by
  rw [trial_norm_square]
  exact (div_le_div_of_nonneg_right hg (mul_pos (clockMass_positive ε a hε ha)
    (gaussianMass_positive _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh))).le).trans_eq
    (mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive hbar hh)
      (neutralWidth_positive hbar hh)).ne')

theorem normalized_rate_tendsto (ε a B : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h r : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hr : Tendsto r atTop (𝓝 0))
    (g : ℕ → Hilbert)
    (hg : ∀ n, ‖g n‖^2 ≤ r n*B*gaussianMass (groundWidth (h n)) (neutralWidth (h n))) :
    Tendsto (fun n => ‖g n‖^2/‖trialState ε a (h n) hε ha (hh n)‖^2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => r n*B/clockMass ε a) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_div] using (hr.mul_const B).div_const (clockMass ε a)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun n => normalized_bound ε a (h n) (r n) B hε ha (hh n) (g n) (hg n))

def factorLimit (ε a : ℝ) : Fin 8 → ℝ :=
  ![halfMass ε a/clockMass ε a,0,0,0,0,0,0,dampedMass ε a/clockMass ε a]

def factorRatio (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : ℝ :=
  ‖factorValue ε hε hbar v l (trialCommon ε a hbar hε ha hh hb v l) i‖^2 /
    ‖trialState ε a hbar hε ha hh‖^2

theorem trial_factor_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (trialState ε a hbar hε ha hh,
      factorValue ε hε hbar v l (trialCommon ε a hbar hε ha hh hb v l) i) ∈
        (energyFactor ε hε hbar v l i).graph :=
  (energyFactor ε hε hbar v l i).mem_graph
    ⟨_,(Submodule.mem_iInf _).mp (trialCommon ε a hbar hε ha hh hb v l).property i⟩

theorem clock_factor_ratio (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    factorRatio ε a hbar hε ha hh hb v l 0 = halfMass ε a/clockMass ε a := by
  rw [factorRatio,trial_clockHalf_mass ε a hbar hε ha hh _ (trial_factor_graph ε a hbar hε ha hh hb v l 0),
    trial_norm_square]
  exact mul_div_mul_right _ _ (gaussianMass_positive _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh)).ne'

theorem factorRatio_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Tendsto (fun n => factorRatio ε a (h n) hε ha (hh n) (hb n) v l i) atTop
      (𝓝 (factorLimit ε a i)) := by
  have habs : Tendsto (fun n => |h n|) atTop (𝓝 0) := by simpa only [abs_zero] using hz.abs
  have hsq : Tendsto (fun n => (h n)^2) atTop (𝓝 0) := by simpa only [zero_pow (by decide : 2 ≠ 0)] using hz.pow 2
  have hg (n : ℕ) (j : Fin 8) := trial_factor_graph ε a (h n) hε ha (hh n) (hb n) v l j
  fin_cases i
  · change Tendsto (fun n => factorRatio ε a (h n) hε ha (hh n) (hb n) v l 0) atTop
      (𝓝 (halfMass ε a/clockMass ε a))
    simp_rw [clock_factor_ratio]
    exact tendsto_const_nhds
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh habs _
      (fun n => trial_momentum_rate ε a (h n) hε ha (hh n) (v 0) _ (hg n 1))
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh habs _
      (fun n => trial_momentum_rate ε a (h n) hε ha (hh n) (v 1) _ (hg n 2))
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh habs _
      (fun n => trial_momentum_rate ε a (h n) hε ha (hh n) (v 2) _ (hg n 3))
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh habs _
      (fun n => trial_momentum_rate ε a (h n) hε ha (hh n) (v 3) _ (hg n 4))
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh habs _
      (fun n => trial_linearMatter_rate ε a (h n) hε ha (hh n) (hb n) l _ (hg n 5))
  · exact normalized_rate_tendsto ε a _ hε ha h _ hh hsq _
      (fun n => trial_quadraticMatter_rate ε a (h n) hε ha (hh n) (hb n) l _ (hg n 6))
  · exact ordered_output_ratio_tendsto ε a hε ha h hh hb hz _ (fun n => hg n 7)

def initialClassicalEnergy (ε a vacuum t : ℝ) : ℝ :=
  (halfMass ε a/2+Real.exp (2*t)*vacuum*dampedMass ε a)/clockMass ε a

theorem energyPolynomial_tendsto (mass2 quartic vacuum t : ℝ) (F : ℕ → Fin 8 → ℝ)
    (L : Fin 8 → ℝ) (hF : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (L i))) :
    Tendsto (fun n => energyPolynomial mass2 quartic vacuum t (F n)) atTop
      (𝓝 (energyPolynomial mass2 quartic vacuum t L)) :=
  (((hF 0).add (hF 1)).add (hF 2)).div_const 2 |>.add
    (((((hF 3).add (hF 4)).div_const 2).add ((hF 5).const_mul (mass2/2))).add
      ((hF 6).const_mul (quartic/4)) |>.add ((hF 7).const_mul vacuum) |>.const_mul (Real.exp (2*t)))

theorem normalized_seed_energy (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ) :
    seedEnergy ε hε hbar v l mass2 quartic vacuum t (trialCommon ε a hbar hε ha hh hb v l) /
        ‖trialState ε a hbar hε ha hh‖^2 =
      energyPolynomial mass2 quartic vacuum t (factorRatio ε a hbar hε ha hh hb v l) := by
  unfold seedEnergy energyPolynomial factorRatio
  ring

theorem seed_energy_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (mass2 quartic vacuum t : ℝ) :
    Tendsto (fun n => seedEnergy ε hε (h n) v l mass2 quartic vacuum t
      (trialCommon ε a (h n) hε ha (hh n) (hb n) v l)/‖trialState ε a (h n) hε ha (hh n)‖^2)
      atTop (𝓝 (initialClassicalEnergy ε a vacuum t)) := by
  simp_rw [normalized_seed_energy]
  have he : energyPolynomial mass2 quartic vacuum t (factorLimit ε a) = initialClassicalEnergy ε a vacuum t := by
    change (halfMass ε a/clockMass ε a+0+0)/2+
      Real.exp (2*t)*((0+0)/2+mass2/2*0+quartic/4*0+vacuum*(dampedMass ε a/clockMass ε a)) =
        (halfMass ε a/2+Real.exp (2*t)*vacuum*dampedMass ε a)/clockMass ε a
    ring
  rw [← he]
  exact energyPolynomial_tendsto mass2 quartic vacuum t _ _ (factorRatio_tendsto ε a hε ha h hh hb hz v l)

#print axioms normalized_bound
#print axioms normalized_rate_tendsto
#print axioms trial_factor_graph
#print axioms clock_factor_ratio
#print axioms factorRatio_tendsto
#print axioms energyPolynomial_tendsto
#print axioms normalized_seed_energy
#print axioms seed_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit
