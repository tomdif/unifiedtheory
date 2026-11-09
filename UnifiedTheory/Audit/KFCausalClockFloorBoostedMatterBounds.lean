/- Quantitative matter-output bounds for every fixed physical momentum
boost, retaining the actual longitudinal exponential and its neutral shear.
The constants are independent of h for fixed epsilon, a and momentum. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (line)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter (quadratic_configuration_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorBoostedStripBounds
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (fieldLine)
open UnifiedTheory.Audit.KFCausalClockFloorFieldBounds (momentBound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (fieldLine_grouping)
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyDecay (scaled_linear_field_bound)

theorem gaussianState_fieldSquare_mass (ε a α β r : ℝ) (b : Fin 5 → ℂ) (y : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (gaussianState ε a α β r b y hε ha hα hβ hw hy,g) ∈ (fieldSquare l).graph) :
    ‖g‖^2 = ∫ z : ℝ × Grouped, ‖(fieldLine ε hε l z:ℂ)^2*line ε a α β r b y z‖^2 := by
  let f : Configuration → ℂ := fun x =>
    (l ((coordinateHomeomorph ε hε).symm x).2:ℂ)^2*configurationLine ε a α β r b y x
  have hf : MemLp f 2 volume := quadratic_configuration_memLp ε a α β r b y hε ha hα hβ hw hy l
  have he : g = coordinates ε hε (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [(fieldSquare_graph l _ _).mp hg,
      gaussianState_coe ε a α β r b y hε ha hα hβ hw hy,
      coordinates_toLp_coe ε hε f hf] with x hx hg hc
    rw [hx,hg,hc]
    simp only [weightedFunction,f,Homeomorph.symm_apply_apply]
    ring
  calc
    _ = ‖coordinates ε hε (hf.toLp f)‖^2 := congrArg (fun u : Hilbert => ‖u‖^2) he
    _ = ∫ x : Configuration, ‖f x‖^2 := by rw [(coordinates ε hε).norm_map,toLp_square_integral]
    _ = ∫ x : Configuration, ‖(fieldLine ε hε l (grouping x):ℂ)^2*line ε a α β r b y (grouping x)‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fieldLine_grouping]
      rfl
    _ = _ := grouping_preserves_volume.integral_comp grouping.measurableEmbedding
      (fun z : ℝ × Grouped => ‖(fieldLine ε hε l z:ℂ)^2*line ε a α β r b y z‖^2)

theorem boostedLine_quadratic_mass_bound (ε a h α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |h| ≤ 2*Real.pi*ε/3)
    (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    (∫ z : ℝ × Grouped, ‖(fieldLine ε hε l z:ℂ)^2*
      line ε a α β (p.1/h) (imaginarySource (h⁻¹ • p.2)) (-h/2) z‖^2) ≤
      (64*(envelope ε α p)^2*(2*‖l‖^2*momentBound (α/2) (β/2))^2*stripMass ε a)*gaussianMass α β := by
  have hs := shift_bound ε h hb
  have hm := KFCausalClockFloorCoherentStrip.quadratic_line_memLp ε a α β (p.1/h)
    (imaginarySource (h⁻¹ • p.2)) (-h/2) hε ha hα hβ hw hs l
  have ht := KFCausalClockFloorFieldMoments.quadratic_line_memLp ε a (α/2) (β/2) (-h/2)
    hε ha (by positivity) (by positivity) (by linarith) hs l
  calc
    _ ≤ ∫ z : ℝ × Grouped, (envelope ε α p)^2*
        ‖(fieldLine ε hε l z:ℂ)^2*KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) (-h/2) z‖^2 := by
      apply integral_mono ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)
        (((memLp_two_iff_integrable_sq_norm ht.1).mp ht).const_mul _)
      intro z
      have hp := mul_le_mul_of_nonneg_left (boostedLine_bound ε a h α β hε hh hα hβ hw hb p z)
        (norm_nonneg ((fieldLine ε hε l z:ℂ)^2))
      have he := pow_le_pow_left₀
        (mul_nonneg (norm_nonneg ((fieldLine ε hε l z:ℂ)^2)) (norm_nonneg _)) hp 2
      simpa only [norm_mul,mul_pow,mul_assoc,mul_left_comm] using he
    _ = (envelope ε α p)^2*(∫ z : ℝ × Grouped,
        ‖(fieldLine ε hε l z:ℂ)^2*KFCausalClockFloorFullGaussian.line ε a (α/2) (β/2) (-h/2) z‖^2) :=
      integral_const_mul _ _
    _ ≤ (envelope ε α p)^2*((8*(2*‖l‖^2*momentBound (α/2) (β/2))^2*stripMass ε a)*
        gaussianMass (α/2) (β/2)) :=
      mul_le_mul_of_nonneg_left (quadratic_mass_bound ε a (α/2) (β/2) (-h/2)
        hε ha (by positivity) (by positivity) (by linarith) hs l) (sq_nonneg _)
    _ ≤ (envelope ε α p)^2*((8*(2*‖l‖^2*momentBound (α/2) (β/2))^2*stripMass ε a)*
        (8*gaussianMass α β)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (gaussianMass_half_bound α β hα hβ)
        (mul_nonneg (by positivity) (stripMass_nonnegative ε a))
    _ = _ := by ring

theorem momentBound_half (α β : ℝ) : momentBound (α/2) (β/2) = 2*momentBound α β := by
  unfold momentBound
  field_simp

def quadraticBudget (ε a : ℝ) (p : Configuration) (l : Transverse →L[ℝ] ℝ) : ℝ :=
  32*(uniformEnvelope ε p)^2*quadraticMass ε a l

theorem quadraticBudget_nonnegative (ε a : ℝ) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    0 ≤ quadraticBudget ε a p l :=
  mul_nonneg (by positivity) (quadraticMass_nonnegative ε a l)

theorem spectralOutput_quadratic_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration)
    (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (spectralOutput ε a h hε ha hh hb (h⁻¹ • p),g) ∈ (fieldSquare l).graph) :
    ‖g‖^2 ≤ h^2*quadraticBudget ε a p l*gaussianMass (groundWidth h) (neutralWidth h) := by
  have he : (h⁻¹ • p).1 = p.1/h := by change h⁻¹*p.1 = _; ring
  rw [gaussianState_fieldSquare_mass ε a _ _ _ _ (-h/2) hε ha
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) (shift_bound ε h hb) l g hg,he]
  have ht := boostedLine_quadratic_mass_bound ε a h _ _ hε ha hh
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hb p l
  have hs := pow_le_pow_left₀ (Real.exp_pos _).le (ground_envelope_bound ε h hε hh h1 p) 2
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 64)) (sq_nonneg (2*‖l‖^2*momentBound (groundWidth h/2) (neutralWidth h/2))))
      (stripMass_nonnegative ε a))
    (gaussianMass_positive _ _ (groundWidth_positive h hh) (neutralWidth_positive h hh)).le
  apply ht.trans (hm.trans_eq _)
  rw [momentBound_half,ground_moment h hh]
  unfold quadraticBudget quadraticMass
  simp only [mul_pow,sq_abs]
  ring

theorem spectralOutput_linear_rate (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration)
    (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (spectralOutput ε a h hε ha hh hb (h⁻¹ • p),g) ∈ (physicalField l).graph) :
    ‖g‖^2 ≤ |h| *(exponentialMass ε a p+quadraticBudget ε a p l)*
      gaussianMass (groundWidth h) (neutralWidth h) := by
  let f := spectralOutput ε a h hε ha hh hb (h⁻¹ • p)
  let q := fieldSquare l ⟨f,spectralOutput_fieldSquare_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩
  have hq := (fieldSquare l).mem_graph
    ⟨f,spectralOutput_fieldSquare_domain ε a h hε ha hh hb (h⁻¹ • p) l⟩
  have hi := scaled_linear_field_bound l f g q hg hq |h| (abs_pos.mpr hh)
  have ht := add_le_add
    (mul_le_mul_of_nonneg_left (spectralOutput_mass_bound ε a h hε ha hh hb h1 p) (abs_nonneg h))
    (div_le_div_of_nonneg_right (spectralOutput_quadratic_rate ε a h hε ha hh hb h1 p l q hq) (abs_nonneg h))
  apply hi.trans (ht.trans_eq _)
  rw [← sq_abs h]
  field_simp

#print axioms gaussianState_fieldSquare_mass
#print axioms boostedLine_quadratic_mass_bound
#print axioms momentBound_half
#print axioms quadraticBudget_nonnegative
#print axioms spectralOutput_quadratic_rate
#print axioms spectralOutput_linear_rate

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedMatterBounds
