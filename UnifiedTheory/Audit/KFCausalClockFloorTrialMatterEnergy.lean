/- Bounds for the actual ordered linear and quadratic matter outputs,
transported through the physical coordinate unitary and exact operator graphs. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (line)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates (coordinates)
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergyBounds
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem gaussianState_fieldSquare_mass (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (gaussianState ε a α β y hε ha hα hβ hw hy,g) ∈ (fieldSquare l).graph) :
    ‖g‖^2 = ∫ z : ℝ × Grouped, ‖(fieldLine ε hε l z:ℂ)^2*line ε a α β y z‖^2 := by
  let p : Configuration → ℂ := fun x =>
    (l ((coordinateHomeomorph ε hε).symm x).2:ℂ)^2*configurationLine ε a α β y x
  have hp : MemLp p 2 volume := quadratic_configuration_memLp ε a α β y hε ha hα hβ hw hy l
  have he : g = coordinates ε hε (hp.toLp p) := by
    apply Lp.ext
    filter_upwards [(fieldSquare_graph l _ _).mp hg,
      gaussianState_coe ε a α β y hε ha hα hβ hw hy,
      coordinates_toLp_coe ε hε p hp] with x hx hf hc
    rw [hx,hf,hc]
    simp only [weightedFunction,p,Homeomorph.symm_apply_apply]
    ring
  calc
    _ = ‖coordinates ε hε (hp.toLp p)‖^2 := congrArg (fun u : Hilbert => ‖u‖^2) he
    _ = ∫ x : Configuration, ‖p x‖^2 := by rw [(coordinates ε hε).norm_map,toLp_square_integral]
    _ = ∫ x : Configuration, ‖(fieldLine ε hε l (grouping x):ℂ)^2*line ε a α β y (grouping x)‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fieldLine_grouping]
      rfl
    _ = _ := grouping_preserves_volume.integral_comp grouping.measurableEmbedding
      (fun z : ℝ × Grouped => ‖(fieldLine ε hε l z:ℂ)^2*line ε a α β y z‖^2)

theorem linear_field_energy_bound (l : Transverse →L[ℝ] ℝ) (f g q : Hilbert)
    (hg : (f,g) ∈ (physicalField l).graph) (hq : (f,q) ∈ (fieldSquare l).graph) :
    ‖g‖^2 ≤ ‖f‖^2+‖q‖^2 := by
  have hf2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f)
  have hg2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
  have hq2 := (memLp_two_iff_integrable_sq_norm (Lp.memLp q).1).mp (Lp.memLp q)
  have hb : (∫ x, ‖g x‖^2) ≤ ∫ x, ‖f x‖^2+‖q x‖^2 := by
    apply integral_mono_ae hg2 (hf2.add hq2)
    filter_upwards [(physicalField_graph l _ _).mp hg,(fieldSquare_graph l _ _).mp hq] with x hx hy
    change ‖g x‖^2 ≤ ‖f x‖^2+‖q x‖^2
    rw [hx,hy]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    have hs : (l x.2)^2 ≤ 1+((l x.2)^2)^2 := by nlinarith only [sq_nonneg ((l x.2)^2-1)]
    nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖f x‖)]
  exact (l2_norm_square volume g).le.trans (hb.trans_eq
    ((integral_add hf2 hq2).trans (congrArg₂ (·+·) (l2_norm_square volume f).symm (l2_norm_square volume q).symm)))

theorem shifted_fieldSquare_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (l : Transverse →L[ℝ] ℝ) (q : Hilbert)
    (hq : (shiftedOutput ε a hbar hε ha hh hbound,q) ∈ (fieldSquare l).graph) :
    ‖q‖^2 ≤ quadraticMass ε a l*gaussianMass (groundWidth hbar) (neutralWidth hbar) :=
  (gaussianState_fieldSquare_mass ε a _ _ (-hbar/2) hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (shift_bound ε hbar hbound) l q hq).le.trans
    (ground_quadratic_mass_bound ε a hbar (-hbar/2) hε ha hh hh1 (shift_bound ε hbar hbound) l)

theorem trial_quadraticMatter_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (l : Transverse →L[ℝ] ℝ) (q : Hilbert)
    (hq : (trialState ε a hbar hε ha hh,q) ∈ (matterFactor ε hε hbar (fieldSquare l)).graph) :
    ‖q‖^2 ≤ quadraticMass ε a l*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  obtain ⟨f,hf,hfq⟩ := (composition_graph _ _ _ _).mp hq
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' hf
    (trialState_shifted_graph ε a hbar hε ha hh hbound) rfl
  dsimp only [Prod.snd] at he
  exact shifted_fieldSquare_bound ε a hbar hε ha hh hbound hh1 l q (he ▸ hfq)

theorem trial_linearMatter_bound (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (hh1 : |hbar| ≤ 1)
    (l : Transverse →L[ℝ] ℝ) (g : Hilbert)
    (hg : (trialState ε a hbar hε ha hh,g) ∈ (matterFactor ε hε hbar (physicalField l)).graph) :
    ‖g‖^2 ≤ (stripMass ε a+quadraticMass ε a l)*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  obtain ⟨f,hf,hfg⟩ := (composition_graph _ _ _ _).mp hg
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj' hf
    (trialState_shifted_graph ε a hbar hε ha hh hbound) rfl
  dsimp only [Prod.snd] at he
  let q := fieldSquare l ⟨shiftedOutput ε a hbar hε ha hh hbound,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound l⟩
  have hq := (fieldSquare l).mem_graph ⟨shiftedOutput ε a hbar hε ha hh hbound,
    shiftedOutput_fieldSquare_domain ε a hbar hε ha hh hbound l⟩
  have hb := linear_field_energy_bound l _ g q (he ▸ hfg) hq
  exact hb.trans ((add_le_add (shiftedOutput_mass_bound ε a hbar hε ha hh hbound)
    (shifted_fieldSquare_bound ε a hbar hε ha hh hbound hh1 l q hq)).trans_eq (add_mul _ _ _).symm)

#print axioms gaussianState_fieldSquare_mass
#print axioms linear_field_energy_bound
#print axioms shifted_fieldSquare_bound
#print axioms trial_quadraticMatter_bound
#print axioms trial_linearMatter_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialMatterEnergy
