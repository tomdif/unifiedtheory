/- The actual ordered linear and quadratic matter outputs of normalized
canonical momentum boosts vanish strongly as h tends to zero, at fixed
positive clock floor and clock width. No evolution statement is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
open UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit (normalized_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

def linearOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹:ℝ) • physicalField l
    ⟨spectralOutput ε a h hε ha hh hb (h⁻¹ • p),
      spectralOutput_physicalField_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩

def quadraticOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹:ℝ) • fieldSquare l
    ⟨spectralOutput ε a h hε ha hh hb (h⁻¹ • p),
      spectralOutput_fieldSquare_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩

theorem linearOutput_field_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    (boostedExponentialOutput ε a h hε ha hh hb p,linearOutput ε a h hε ha hh hb p l) ∈
      (physicalField l).graph :=
  ((physicalField l).graph.restrictScalars ℝ).smul_mem (‖trialState ε a h hε ha hh‖⁻¹)
    ((physicalField l).mem_graph
      ⟨_,spectralOutput_physicalField_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩)

theorem quadraticOutput_field_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    (boostedExponentialOutput ε a h hε ha hh hb p,quadraticOutput ε a h hε ha hh hb p l) ∈
      (fieldSquare l).graph :=
  ((fieldSquare l).graph.restrictScalars ℝ).smul_mem (‖trialState ε a h hε ha hh‖⁻¹)
    ((fieldSquare l).mem_graph
      ⟨_,spectralOutput_fieldSquare_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩)

theorem linearOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),linearOutput ε a h hε ha hh hb p l) ∈
      (matterFactor ε hε h (physicalField l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,boostedExponential_graph ε a h hε ha hh hb p,
    linearOutput_field_graph ε a h hε ha hh hb p l⟩

theorem quadraticOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),quadraticOutput ε a h hε ha hh hb p l) ∈
      (matterFactor ε hε h (fieldSquare l)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,boostedExponential_graph ε a h hε ha hh hb p,
    quadraticOutput_field_graph ε a h hε ha hh hb p l⟩

theorem linearOutput_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    ‖linearOutput ε a h hε ha hh hb p l‖^2 ≤
      |h| *(exponentialMass ε a p+quadraticBudget ε a p l)/clockMass ε a := by
  rw [linearOutput,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul]
  exact normalized_bound ε a h |h| _ hε ha hh _
    (spectralOutput_linear_rate ε a h hε ha hh hb h1 p l _
      ((physicalField l).mem_graph ⟨_,spectralOutput_physicalField_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩))

theorem quadraticOutput_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    ‖quadraticOutput ε a h hε ha hh hb p l‖^2 ≤
      h^2*quadraticBudget ε a p l/clockMass ε a := by
  rw [quadraticOutput,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul]
  exact normalized_bound ε a h (h^2) _ hε ha hh _
    (spectralOutput_quadratic_rate ε a h hε ha hh hb h1 p l _
      ((fieldSquare l).mem_graph ⟨_,spectralOutput_fieldSquare_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩))

theorem linear_output_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (l : Transverse →L[ℝ] ℝ)
    (g : Hilbert) (hg : (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),g) ∈
      (matterFactor ε hε h (physicalField l)).graph) :
    ‖g‖^2 ≤ |h| *(exponentialMass ε a p+quadraticBudget ε a p l)/clockMass ε a := by
  have he := (matterFactor ε hε h (physicalField l)).mem_graph_snd_inj' hg
    (linearOutput_graph ε a h hε ha hh hb p l) rfl
  dsimp only [Prod.snd] at he
  rw [he]
  exact linearOutput_rate ε a h hε ha hh hb h1 p l

theorem quadratic_output_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (l : Transverse →L[ℝ] ℝ)
    (g : Hilbert) (hg : (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),g) ∈
      (matterFactor ε hε h (fieldSquare l)).graph) :
    ‖g‖^2 ≤ h^2*quadraticBudget ε a p l/clockMass ε a := by
  have he := (matterFactor ε hε h (fieldSquare l)).mem_graph_snd_inj' hg
    (quadraticOutput_graph ε a h hε ha hh hb p l) rfl
  dsimp only [Prod.snd] at he
  rw [he]
  exact quadraticOutput_rate ε a h hε ha hh hb h1 p l

theorem linearOutput_strong_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    Tendsto (fun n => linearOutput ε a (h n) hε ha (hh n) (hb n) p l) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => |h n| *(exponentialMass ε a p+quadraticBudget ε a p l)/clockMass ε a)
      atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul,zero_div] using
      (hz.abs.mul_const (exponentialMass ε a p+quadraticBudget ε a p l)).div_const (clockMass ε a)
  have hs := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => sq_nonneg ‖linearOutput ε a (h n) hε ha (hh n) (hb n) p l‖)
    (fun n => linearOutput_rate ε a (h n) hε ha (hh n) (hb n) (h1 n) p l)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

theorem quadraticOutput_strong_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (h1 : ∀ n, |h n| ≤ 1) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    Tendsto (fun n => quadraticOutput ε a (h n) hε ha (hh n) (hb n) p l) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => (h n)^2*quadraticBudget ε a p l/clockMass ε a) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul,zero_div] using
      ((hz.pow 2).mul_const (quadraticBudget ε a p l)).div_const (clockMass ε a)
  have hs := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => sq_nonneg ‖quadraticOutput ε a (h n) hε ha (hh n) (hb n) p l‖)
    (fun n => quadraticOutput_rate ε a (h n) hε ha (hh n) (hb n) (h1 n) p l)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

#print axioms linearOutput_field_graph
#print axioms quadraticOutput_field_graph
#print axioms linearOutput_graph
#print axioms quadraticOutput_graph
#print axioms linearOutput_rate
#print axioms quadraticOutput_rate
#print axioms linear_output_rate
#print axioms quadratic_output_rate
#print axioms linearOutput_strong_zero
#print axioms quadraticOutput_strong_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterLimit
