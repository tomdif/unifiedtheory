/- Chart phases give a bounded-energy family with fixed clock density
and escape of localized mass to the negative coupled spectrum. This is
a family of states at one fixed time, not a Hamiltonian trajectory. -/
import UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectralSplit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticNegativeEscape
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorChartModulation (modulation modulation_coe)
open KFCausalClockFloorFactorChartModulation (factorScale)
open KFCausalClockFloorClosedChartModulation (outputAction outputAction_apply)
open KFCausalClockFloorGaugeEnergy (rate rate_scale)
open KFCausalClockFloorReferenceChartModulation (formAction formAction_embedding formAction_output)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding energyOutput)
open KFCausalClockFloorWeightedClockControl (weighted weighted_coe weight_positive)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation orbitLift orbit_graph_bound)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit orbit_split)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace coordinate coordinateLp physicalOrbit vacuum vacuum_graph)
open KFCausalClockFloorOrbitVacuumDetection (detector detection)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)

theorem weighted_modulation (ε : ℝ) (hε : 0 < ε) (r : ℝ) (f : Hilbert) :
    weighted ε hε (modulation ε r f) = modulation ε r (weighted ε hε f) := by
  apply Lp.ext
  filter_upwards [weighted_coe ε hε (modulation ε r f),modulation_coe ε r f,
    modulation_coe ε r (weighted ε hε f),weighted_coe ε hε f] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  ring

theorem weighted_injective (ε : ℝ) (hε : 0 < ε) : Function.Injective (weighted ε hε) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [weighted_coe ε hε f,(Lp.eq_zero_iff_ae_eq_zero).mp hf] with x hw hz
  have hp : (KFCausalClockFloorWeightedClockControl.weight ε x.1:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (weight_positive ε hε x.1).ne'
  exact (mul_eq_zero.mp (hw.symm.trans hz)).resolve_left hp

theorem output_contraction (ε h u : ℝ) (hne : h ≠ 0) (hu : 0 ≤ u)
    (g : Output (Fin 8) Hilbert) : ‖outputAction ε h (rate h u) g‖ ≤ ‖g‖ := by
  have hc : Real.exp (Real.pi*h*rate h u) ≤ 1 := by
    rw [rate_scale h u hne]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hi (i : Fin 8) : ‖outputAction ε h (rate h u) g i‖ ≤ ‖g i‖ := by
    rw [outputAction_apply,norm_smul,LinearIsometryEquiv.norm_map]
    by_cases hi : i.val < 5
    · simp only [factorScale,hi,if_true,norm_one,one_mul,le_refl]
    · simp only [factorScale,hi,if_false,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) hc
  have hs : ‖outputAction ε h (rate h u) g‖^2 ≤ ‖g‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hi i) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem coordinate_modulation_norm (ε h r : ℝ) (g : EnergyOutputSpace) :
    ‖coordinateLp ((outputAction ε h r).compLp g)‖ =
      Real.exp (Real.pi*h*r)*‖coordinateLp g‖ := by
  have he : coordinateLp ((outputAction ε h r).compLp g) =
      (Real.exp (Real.pi*h*r):ℂ) • (modulation ε r : Hilbert →L[ℂ] Hilbert).compLp
        (coordinateLp g) := by
    apply Lp.ext
    filter_upwards [coordinate.coeFn_compLp ((outputAction ε h r).compLp g),
      (outputAction ε h r).coeFn_compLp g,coordinate.coeFn_compLp g,
      (modulation ε r : Hilbert →L[ℂ] Hilbert).coeFn_compLp (coordinateLp g),
      Lp.coeFn_smul (Real.exp (Real.pi*h*r):ℂ)
        ((modulation ε r : Hilbert →L[ℂ] Hilbert).compLp (coordinateLp g))]
      with θ h1 h2 h3 h4 h5
    change coordinate.compLp ((outputAction ε h r).compLp g) θ = _
    rw [h1,h2,h5]
    simp only [Pi.smul_apply]
    change coordinateLp g θ = coordinate (g θ) at h3
    rw [h4,h3]
    change outputAction ε h r (g θ) 7 = _
    rw [outputAction_apply]
    rfl
  have hn : ‖(modulation ε r : Hilbert →L[ℂ] Hilbert).compLp (coordinateLp g)‖ =
      ‖coordinateLp g‖ := by
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(modulation ε r : Hilbert →L[ℂ] Hilbert).coeFn_compLp (coordinateLp g)] with θ hθ
      rw [hθ]
      exact ((modulation ε r).norm_map _).le
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(modulation ε r : Hilbert →L[ℂ] Hilbert).coeFn_compLp (coordinateLp g)] with θ hθ
      rw [hθ]
      exact ((modulation ε r).norm_map _).symm.le
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hn]

theorem detection_norm_bound (ε : ℝ) (hε : 0 < ε) (q : OrbitSpace) :
    detection ε hε q ≤ ‖detector ε hε‖*‖q‖^2 := by
  have hp := (Complex.abs_re_le_norm (inner ℂ q (detector ε hε q))).trans
    ((norm_inner_le_norm (𝕜 := ℂ) q (detector ε hε q)).trans
      (mul_le_mul_of_nonneg_left ((detector ε hε).le_opNorm q) (norm_nonneg q)))
  have hn := neg_le_abs (inner ℂ q (detector ε hε q)).re
  unfold detection
  nlinarith only [hp,hn]

theorem orbit_scaled_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (R k : ℝ) (hk : 0 < k) (c : ℂ) (hc : ‖c‖^2 = k)
    (f : Hilbert) (q : OrbitSpace)
    (hfg : (physicalOrbit h hne (c • f),q) ∈
      (KFCausalClockFloorOrbitVacuumGraph.vacuumOperator ε hε h).graph) :
    ‖orbitObservation ε hε h hne R f‖^2 ≤
      (64*ε*Real.exp (-R)*‖detector ε hε‖*‖q‖^2)/k := by
  have he := orbit_graph_bound ε hε h hb R _ _ hfg
  have hs : orbitLift ε hε h R (physicalOrbit h hne (c • f)) =
      c • orbitObservation ε hε h hne R f :=
    (orbitObservation ε hε h hne R).map_smul c f
  rw [hs,norm_smul,mul_pow,hc] at he
  have hd := detection_norm_bound ε hε q
  have hbound := he.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  apply (le_div_iff₀ hk).mpr
  nlinarith only [hbound]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => energyOutput ε hε h hne hb m g k 0
local notation "B" => orbitObservation ε hε h hne
local notation "N" => lowerOrbit ε hε h hne
local notation "H" => weighted ε hε

def family (v : V) (u : ℝ) : V := formAction ε hε h hne hb m g k (rate h u) 0 v

theorem family_norm (v : V) (u : ℝ) :
    ‖J (family ε hε h hne hb m g k v u)‖ = ‖J v‖ := by
  change ‖modulation ε (rate h u) (J v)‖ = _
  exact (modulation ε (rate h u)).norm_map _

theorem family_weighted_norm (v : V) (u : ℝ) :
    ‖H (J (family ε hε h hne hb m g k v u))‖ = ‖H (J v)‖ := by
  change ‖H (modulation ε (rate h u) (J v))‖ = _
  rw [weighted_modulation,LinearIsometryEquiv.norm_map]

theorem family_density (v : V) (u : ℝ) :
    (fun x => ‖J (family ε hε h hne hb m g k v u) x‖) =ᵐ[volume] fun x => ‖J v x‖ :=
  KFCausalClockFloorChartModulation.modulation_density ε (rate h u) (J v)

theorem family_charge_fixed (v : V) (u θ : ℝ)
    (hv : KFCausalPhysicalCircleAction.action h hne θ (J v) = J v) :
    KFCausalPhysicalCircleAction.action h hne θ
      (J (family ε hε h hne hb m g k v u)) =
        J (family ε hε h hne hb m g k v u) := by
  change KFCausalPhysicalCircleAction.action h hne θ (modulation ε (rate h u) (J v)) = _
  rw [← KFCausalClockFloorFactorChartModulation.modulation_charge,hv]
  rfl

theorem family_energy (v : V) (u : ℝ) (hu : 0 ≤ u) :
    ‖A (family ε hε h hne hb m g k v u)‖^2 ≤ ‖A v‖^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  change ‖(outputAction ε h (rate h u)).compLp (A v)‖ ≤ ‖A v‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(outputAction ε h (rate h u)).coeFn_compLp (A v)] with θ hθ
  rw [hθ]
  exact output_contraction ε h u hne hu _

theorem family_vacuum_norm (v : V) (u : ℝ) :
    ‖vacuum ε hε h hne hb m g k 0 (family ε hε h hne hb m g k v u)‖ =
      Real.exp (-u)*‖vacuum ε hε h hne hb m g k 0 v‖ := by
  change ‖coordinateLp ((outputAction ε h (rate h u)).compLp (A v))‖ = _
  rw [coordinate_modulation_norm,rate_scale h u hne]
  rfl

theorem upper_bound (hk : 0 < k) (R : ℝ) (v : V) (u : ℝ) :
    ‖B R (J (family ε hε h hne hb m g k v u))‖^2 ≤
      (64*ε*Real.exp (-R)*‖detector ε hε‖*
        ‖vacuum ε hε h hne hb m g k 0 v‖^2/k)*Real.exp (-2*u) := by
  let w := family ε hε h hne hb m g k v u
  let c := KFCausalPhysicalEnergyFactors.energyWeight m g k 0 7
  have hc : ‖c‖^2 = k := by
    change ‖((Real.exp 0*Real.sqrt k:ℝ):ℂ)‖^2 = k
    simp only [Real.exp_zero,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hk.le]
  have he := orbit_scaled_bound ε hε h hne hb R k hk c hc (J w)
    (vacuum ε hε h hne hb m g k 0 w) (vacuum_graph ε hε h hne hb m g k 0 w)
  change ‖B R (J w)‖^2 ≤ _
  apply he.trans_eq
  change (64*ε*Real.exp (-R)*‖detector ε hε‖*
    ‖vacuum ε hε h hne hb m g k 0 (family ε hε h hne hb m g k v u)‖^2)/k = _
  rw [family_vacuum_norm,mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-u) = -2*u by ring]
  ring

theorem upper_decay (hk : 0 < k) (R : ℝ) (v : V) :
    Tendsto (fun u => ‖B R (J (family ε hε h hne hb m g k v u))‖^2) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-2*u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2:ℝ) < 0))
  apply squeeze_zero (fun _ => sq_nonneg _) (upper_bound ε hε h hne hb m g k hk R v)
  simpa only [mul_zero] using he.const_mul
    (64*ε*Real.exp (-R)*‖detector ε hε‖*‖vacuum ε hε h hne hb m g k 0 v‖^2/k)

theorem lower_mass_limit (hk : 0 < k) (R : ℝ) (v : V) :
    Tendsto (fun u => ‖N R (J (family ε hε h hne hb m g k v u))‖^2)
      atTop (𝓝 (‖H (J v)‖^2)) := by
  have he (u : ℝ) : ‖N R (J (family ε hε h hne hb m g k v u))‖^2 =
      ‖H (J v)‖^2-‖B R (J (family ε hε h hne hb m g k v u))‖^2 := by
    have hs := orbit_split ε hε h hne R (J (family ε hε h hne hb m g k v u))
    rw [family_weighted_norm] at hs
    linarith only [hs]
  simp_rw [he]
  simpa only [sub_zero] using
    (upper_decay ε hε h hne hb m g k hk R v).const_sub (‖H (J v)‖^2)

theorem no_uniform_lower_tail (hk : 0 < k) (v : V) (hv : J v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ w : V,
      ‖J w‖ = ‖J v‖ ∧ ‖A w‖^2 ≤ ‖A v‖^2 ∧
      ‖H (J w)‖ = ‖H (J v)‖ ∧ c ≤ ‖N R (J w)‖^2 := by
  have hn : H (J v) ≠ 0 := by
    intro hz
    exact hv ((weighted_injective ε hε) (hz.trans (map_zero H).symm))
  have hp : 0 < ‖H (J v)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  refine ⟨‖H (J v)‖^2/2,by positivity,fun R => ?_⟩
  have he := (lower_mass_limit ε hε h hne hb m g k hk R v).eventually
    (lt_mem_nhds (show ‖H (J v)‖^2/2 < ‖H (J v)‖^2 by linarith))
  have hex := ((eventually_ge_atTop (0:ℝ)).and he).exists
  let u : ℝ := hex.choose
  have hu : 0 ≤ u := hex.choose_spec.1
  have hl : ‖H (J v)‖^2/2 <
      ‖N R (J (family ε hε h hne hb m g k v u))‖^2 := hex.choose_spec.2
  exact ⟨family ε hε h hne hb m g k v u,family_norm ε hε h hne hb m g k v u,
    family_energy ε hε h hne hb m g k v u hu,family_weighted_norm ε hε h hne hb m g k v u,hl.le⟩

#print axioms weighted_modulation
#print axioms weighted_injective
#print axioms output_contraction
#print axioms coordinate_modulation_norm
#print axioms detection_norm_bound
#print axioms orbit_scaled_bound
#print axioms family_norm
#print axioms family_weighted_norm
#print axioms family_density
#print axioms family_charge_fixed
#print axioms family_energy
#print axioms family_vacuum_norm
#print axioms upper_bound
#print axioms upper_decay
#print axioms lower_mass_limit
#print axioms no_uniform_lower_tail
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticNegativeEscape
