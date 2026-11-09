/- Nonzero momentum calibration of the actual ordered kinetic operator.
The oscillatory states remain in its natural domain, and their kinetic
energies converge to the shifted classical value. This does not assert
membership in the full matter form or preservation of zero charge. -/
import UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
import UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit (normalized_bound)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates
open UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse

def baseOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹:ℝ) • clockMomentum ε h v
    ⟨trialState ε a h hε ha hh,trialState_clockMomentum_domain ε a h hε ha hh v⟩

def boostedState (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) : Hilbert :=
  modulation (h⁻¹ • l) (unitTrial ε a h hε ha hh)

def boostedOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) : Hilbert :=
  modulation (h⁻¹ • l) (baseOutput ε a h hε ha hh v+
    (l (0,v):ℂ) • normalizedDamped ε a h hε ha hh)

def leadingOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) : Hilbert :=
  (l (0,v):ℂ) • modulation (h⁻¹ • l) (normalizedDamped ε a h hε ha hh)

theorem baseOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) :
    (unitTrial ε a h hε ha hh,baseOutput ε a h hε ha hh v) ∈ (clockMomentum ε h v).graph :=
  ((clockMomentum ε h v).graph.restrictScalars ℝ).smul_mem
    (‖trialState ε a h hε ha hh‖⁻¹)
    ((clockMomentum ε h v).mem_graph
      ⟨_,trialState_clockMomentum_domain ε a h hε ha hh v⟩)

theorem baseOutput_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) :
    ‖baseOutput ε a h hε ha hh v‖^2 ≤ |h| *kineticMass ε a v/clockMass ε a := by
  rw [baseOutput,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul]
  exact normalized_bound ε a h |h| (kineticMass ε a v) hε ha hh _
    (trial_momentum_rate ε a h hε ha hh v _ ((clockMomentum ε h v).mem_graph
      ⟨_,trialState_clockMomentum_domain ε a h hε ha hh v⟩))

theorem baseOutput_tendsto_zero (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) (v : Transverse) :
    Tendsto (fun n => ‖baseOutput ε a (h n) hε ha (hh n) v‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => |h n| *kineticMass ε a v/clockMass ε a) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul,zero_div] using
      (hz.abs.mul_const (kineticMass ε a v)).div_const (clockMass ε a)
  have hs : Tendsto (fun n => ‖baseOutput ε a (h n) hε ha (hh n) v‖^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => sq_nonneg _) (fun n => baseOutput_rate ε a (h n) hε ha (hh n) v)
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

theorem boostedState_norm (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (l : Configuration →L[ℝ] ℝ) : ‖boostedState ε a h hε ha hh l‖ = 1 := by
  rw [boostedState,(modulation (h⁻¹ • l)).norm_map,unitTrial_norm]

theorem boostedOutput_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    (boostedState ε a h hε ha hh l,boostedOutput ε a h hε ha hh v l) ∈
      (clockMomentum ε h v).graph := by
  have he := (inverseL_graph ε hε _ _).mp (normalizedDamped_graph ε a h hε ha hh)
  rw [boostedState,boostedOutput,he]
  exact kinetic_graph_boost ε hε h hh v l _ _ (baseOutput_graph ε a h hε ha hh v)

theorem boostedOutput_error (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    ‖boostedOutput ε a h hε ha hh v l-leadingOutput ε a h hε ha hh v l‖ =
      ‖baseOutput ε a h hε ha hh v‖ := by
  rw [boostedOutput,leadingOutput,map_add,map_smul,add_sub_cancel_right,
    (modulation (h⁻¹ • l)).norm_map]

theorem boostedOutput_strong_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    Tendsto (fun n => ‖boostedOutput ε a (h n) hε ha (hh n) v l-
      leadingOutput ε a (h n) hε ha (hh n) v l‖) atTop (𝓝 0) := by
  simp_rw [boostedOutput_error]
  exact baseOutput_tendsto_zero ε a hε ha h hh hz v

theorem leadingOutput_norm (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    ‖leadingOutput ε a h hε ha hh v l‖ = |l (0,v)| *Real.sqrt (dampedMass ε a/clockMass ε a) := by
  rw [leadingOutput,norm_smul,(modulation (h⁻¹ • l)).norm_map,
    Complex.norm_real,Real.norm_eq_abs,normalizedDamped_norm]

theorem boostedOutput_norm_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    Tendsto (fun n => ‖boostedOutput ε a (h n) hε ha (hh n) v l‖) atTop
      (𝓝 (|l (0,v)| *Real.sqrt (dampedMass ε a/clockMass ε a))) := by
  have hd := boostedOutput_strong_limit ε a hε ha h hh hz v l
  have he (n : ℕ) := norm_sub_norm_le
    (boostedOutput ε a (h n) hε ha (hh n) v l)
    (leadingOutput ε a (h n) hε ha (hh n) v l)
  have hr (n : ℕ) := norm_sub_norm_le
    (leadingOutput ε a (h n) hε ha (hh n) v l)
    (boostedOutput ε a (h n) hε ha (hh n) v l)
  simp only [leadingOutput_norm] at he hr
  have hl := hd.const_sub (|l (0,v)| *Real.sqrt (dampedMass ε a/clockMass ε a))
  have hu := hd.const_add (|l (0,v)| *Real.sqrt (dampedMass ε a/clockMass ε a))
  simp only [sub_zero,add_zero] at hl hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun n => by have := hr n; rw [norm_sub_rev] at this; linarith)
    (fun n => by have := he n; linarith)

theorem boostedOutput_energy_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (v : Transverse) (l : Configuration →L[ℝ] ℝ) :
    Tendsto (fun n => ‖boostedOutput ε a (h n) hε ha (hh n) v l‖^2) atTop
      (𝓝 ((l (0,v))^2*dampedMass ε a/clockMass ε a)) := by
  have ht := (boostedOutput_norm_limit ε a hε ha h hh hz v l).pow 2
  rw [mul_pow,sq_abs,Real.sq_sqrt (div_nonneg (dampedMass_nonnegative ε a)
    (clockMass_positive ε a hε ha).le),← mul_div_assoc] at ht
  exact ht

#print axioms baseOutput_graph
#print axioms baseOutput_rate
#print axioms baseOutput_tendsto_zero
#print axioms boostedState_norm
#print axioms boostedOutput_graph
#print axioms boostedOutput_error
#print axioms boostedOutput_strong_limit
#print axioms leadingOutput_norm
#print axioms boostedOutput_norm_limit
#print axioms boostedOutput_energy_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
