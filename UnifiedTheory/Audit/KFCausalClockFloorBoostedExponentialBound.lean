/- An h-independent L2 bound for the actual ordered longitudinal
exponential on every fixed canonical momentum boost of the normalized
trial. Epsilon and clock width remain fixed and positive. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
import UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (line line_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds (stripMass stripMass_nonnegative)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit (normalized_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)

theorem gaussianState_mass (ε a α β r : ℝ) (b : Fin 5 → ℂ) (y : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    ‖gaussianState ε a α β r b y hε ha hα hβ hw hy‖^2 =
      ∫ z : ℝ × Grouped, ‖line ε a α β r b y z‖^2 := by
  let f := configurationLine ε a α β r b y
  have hf := configurationLine_memLp ε a α β r b y hε ha hα hβ hw hy
  have hn := (coordinates ε hε).norm_map (hf.toLp f)
  exact (congrArg (fun t : ℝ => t^2) hn).trans ((toLp_square_integral f hf).trans
    (grouping_preserves_volume.integral_comp grouping.measurableEmbedding
      (fun z : ℝ × Grouped => ‖line ε a α β r b y z‖^2)))

theorem boostedLine_mass_bound (ε a h α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    (∫ z : ℝ × Grouped, ‖line ε a α β (p.1/h) (imaginarySource (h⁻¹ • p.2)) (-h/2) z‖^2) ≤
      (8*(envelope ε α p)^2*stripMass ε a)*gaussianMass α β := by
  have hs := shift_bound ε h hb
  have hm := line_memLp ε a α β (p.1/h) (imaginarySource (h⁻¹ • p.2)) (-h/2) hε ha hα hβ hw hs
  have ht := KFCausalClockFloorFullGaussian.line_memLp ε a (α/2) (β/2) (-h/2)
    hε ha (by positivity) (by positivity) (by linarith) hs
  calc
    _ ≤ ∫ z : ℝ × Grouped, (envelope ε α p)^2*
        ‖KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) (-h/2) z‖^2 := by
      apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)
        (((memLp_two_iff_integrable_sq_norm ht.1).mp ht).const_mul _)
      intro z
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (boostedLine_bound ε a h α β hε hh hα hβ hw hb p z) 2
    _ = (envelope ε α p)^2*(∫ z : ℝ × Grouped,
        ‖KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) (-h/2) z‖^2) := integral_const_mul _ _
    _ ≤ (envelope ε α p)^2*(stripMass ε a*gaussianMass (α/2) (β/2)) :=
      mul_le_mul_of_nonneg_left
        (KFCausalClockFloorGaussianEnergyBounds.line_mass_bound ε a (α/2) (β/2) (-h/2)
          hε ha (by positivity) (by positivity) (by linarith) hs) (sq_nonneg _)
    _ ≤ (envelope ε α p)^2*(stripMass ε a*(8*gaussianMass α β)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gaussianMass_half_bound α β hα hβ)
        (stripMass_nonnegative ε a)) (sq_nonneg _)
    _ = _ := by ring

def uniformEnvelope (ε : ℝ) (p : Configuration) : ℝ :=
  Real.exp (|p.1|/(2*ε)+momentumSize p.2/(4*ε^2))

theorem ground_envelope_bound (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (h1 : |h| ≤ 1)
    (p : Configuration) : envelope ε (groundWidth h) p ≤ uniformEnvelope ε p := by
  unfold envelope uniformEnvelope
  apply Real.exp_le_exp.mpr
  apply add_le_add (le_refl _)
  have hm : 0 ≤ momentumSize p.2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : momentumSize p.2/(8*groundWidth h*ε^2) = |h| *(momentumSize p.2/(4*ε^2)) := by
    unfold groundWidth
    field_simp
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans_eq (one_mul _)

def exponentialMass (ε a : ℝ) (p : Configuration) : ℝ :=
  8*(uniformEnvelope ε p)^2*stripMass ε a

theorem spectralOutput_mass_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) :
    ‖spectralOutput ε a h hε ha hh hb (h⁻¹ • p)‖^2 ≤
      exponentialMass ε a p*gaussianMass (groundWidth h) (neutralWidth h) := by
  rw [spectralOutput,gaussianState_mass]
  have he : (h⁻¹ • p).1 = p.1/h := by change h⁻¹*p.1 = _; ring
  rw [he]
  apply (boostedLine_mass_bound ε a h _ _ hε ha hh (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hb p).trans
  have hs := pow_le_pow_left₀ (Real.exp_pos _).le (ground_envelope_bound ε h hε hh h1 p) 2
  unfold exponentialMass
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 8))
      (stripMass_nonnegative ε a))
    (gaussianMass_positive _ _ (groundWidth_positive h hh) (neutralWidth_positive h hh)).le

theorem boostedExponential_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) :
    ‖boostedExponentialOutput ε a h hε ha hh hb p‖^2 ≤ exponentialMass ε a p/clockMass ε a := by
  rw [boostedExponentialOutput,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,
    abs_of_nonneg (norm_nonneg _),inv_pow,← div_eq_inv_mul]
  simpa only [one_mul] using normalized_bound ε a h 1 (exponentialMass ε a p) hε ha hh _
    (by simpa only [one_mul] using spectralOutput_mass_bound ε a h hε ha hh hb h1 p)

theorem ordered_boost_output_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (g : Hilbert)
    (hg : (boostedState ε a h hε ha hh (positionFrequency p.1 p.2),g) ∈
      (orderedExponential ε hε h).graph) :
    ‖g‖^2 ≤ exponentialMass ε a p/clockMass ε a := by
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hg
    (boostedExponential_graph ε a h hε ha hh hb p) rfl
  dsimp only [Prod.snd] at he
  rw [he]
  exact boostedExponential_bound ε a h hε ha hh hb h1 p

#print axioms gaussianState_mass
#print axioms boostedLine_mass_bound
#print axioms ground_envelope_bound
#print axioms spectralOutput_mass_bound
#print axioms boostedExponential_bound
#print axioms ordered_boost_output_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
