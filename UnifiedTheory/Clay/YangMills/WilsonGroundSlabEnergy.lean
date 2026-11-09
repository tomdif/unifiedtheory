/- Weak-coupling energy control under the actual physical-transfer ground slab.
The temporal gauge variables and both half-spatial potentials are retained.
This is an actual-model concentration estimate, not a continuum survival bound. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds
import UnifiedTheory.Clay.YangMills.WilsonVacuumConvergence
import UnifiedTheory.Clay.YangMills.GibbsFreeEnergyBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundLocalComparison
open WilsonSingleLinkStaples WilsonEnergyDensity UnitaryHaarNeighborhood
open RegulatedGauge LocalGibbsComparison
open scoped NNReal

variable (n : ℕ) [NeZero n]

abbrev Slab := (Slice n × Slice n) × SliceGauge n WilsonSlabOperator.Q

local instance slabBorel : BorelSpace (Slab n) := Prod.borelSpace

def reference : Measure (Slab n) :=
  ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)).prod temporalHaar

instance reference_probability : IsProbabilityMeasure (reference n) := by
  unfold reference
  infer_instance

/-- The actual unscaled slab action, including the temporal gauge variables. -/
def energy (z : Slab n) : ℝ := slabAction character 1 2 z.1.1 z.1.2 z.2

theorem energy_continuous : Continuous (energy n) := by
  have hc : Continuous character := character_continuous
  unfold energy slabAction potential temporalAction spatialHolonomy temporalHolonomy
  fun_prop

theorem energy_nonneg (z : Slab n) : 0 ≤ energy n z :=
  (WilsonSlabBounds.slabAction_bounds n 1 (by norm_num) z.1.1 z.1.2 z.2).1

theorem action_eq (β : ℝ) (z : Slab n) :
    slabAction character β 2 z.1.1 z.1.2 z.2 = β * energy n z := by
  simp only [energy, slabAction, one_mul]

/-- The actual positive ground amplitudes weight the two ends of a single full slab. -/
def weight (β : ℝ) (hβ : 0 ≤ β) (z : Slab n) : ℝ :=
  ground n β hβ z.1.1 * ground n β hβ z.1.2 * Real.exp (-(β * energy n z))

theorem weight_continuous (β : ℝ) (hβ : 0 ≤ β) : Continuous (weight n β hβ) :=
  (((ground n β hβ).continuous.comp (continuous_fst.comp continuous_fst)).mul
    ((ground n β hβ).continuous.comp (continuous_snd.comp continuous_fst))).mul
    (Real.continuous_exp.comp (continuous_const.mul (energy_continuous n)).neg)

theorem weight_pos (β : ℝ) (hβ : 0 ≤ β) (z : Slab n) : 0 < weight n β hβ z :=
  mul_pos (mul_pos (ground_pos n β hβ z.1.1) (ground_pos n β hβ z.1.2)) (Real.exp_pos _)

/-- Integrating actual temporal links gives the original full interacting kernel. -/
theorem weight_temporal_integral (β : ℝ) (hβ : 0 ≤ β) (uv : Slice n × Slice n) :
    (∫ h, weight n β hβ (uv, h) ∂temporalHaar) =
      ground n β hβ uv.1 * ground n β hβ uv.2 * kernelMap n β uv := by
  unfold weight
  dsimp only
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with h
  rw [← action_eq]

/-- The joint slab partition is the constructed top transfer eigenvalue exactly. -/
theorem weight_integral (β : ℝ) (hβ : 0 ≤ β) :
    (∫ z, weight n β hβ z ∂reference n) = ‖transfer n β‖ := by
  have hi := (weight_continuous n β hβ).integrable_of_hasCompactSupport
    (μ := reference n) (HasCompactSupport.of_compactSpace _)
  rw [reference, integral_prod _ hi]
  simp_rw [weight_temporal_integral]
  have hc : Continuous (fun uv : Slice n × Slice n =>
      ground n β hβ uv.1 * ground n β hβ uv.2 * kernelMap n β uv) :=
    (((ground n β hβ).continuous.comp continuous_fst).mul
      ((ground n β hβ).continuous.comp continuous_snd)).mul (kernelMap n β).continuous
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have he (u : Slice n) :
      (∫ v, ground n β hβ u * ground n β hβ v * kernelMap n β (u, v)
        ∂WilsonSlabOperator.measure n) = ‖transfer n β‖ * (ground n β hβ u)^2 := by
    have hf : (fun v => ground n β hβ u * ground n β hβ v * kernelMap n β (u, v)) =
        fun v => ground n β hβ u * (kernelMap n β (u, v) * ground n β hβ v) := by
      funext v
      ring
    have hg := ground_equation n β hβ u
    change (∫ v, kernelMap n β (u, v) * ground n β hβ v
      ∂WilsonSlabOperator.measure n) = _ at hg
    rw [hf, integral_const_mul, hg]
    ring
  simp_rw [he]
  rw [integral_const_mul, ground_square_integral, mul_one]

/-- A probability law of the actual ground-state slab, without fixing temporal gauge. -/
def law (β : ℝ) (hβ : 0 ≤ β) : Measure (Slab n) :=
  weightedLaw (reference n) (weight n β hβ)

instance law_probability (β : ℝ) (hβ : 0 ≤ β) : IsProbabilityMeasure (law n β hβ) :=
  weightedLaw_probability (reference n) (weight n β hβ)
    (weight_continuous n β hβ).measurable
    ((weight_continuous n β hβ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (fun z => (weight_pos n β hβ z).le)
    (by rw [weight_integral]; exact (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1)

theorem law_integral (β : ℝ) (hβ : 0 ≤ β) (F : Slab n → ℝ) :
    (∫ z, F z ∂law n β hβ) =
      (∫ z, weight n β hβ z * F z ∂reference n) / ‖transfer n β‖ := by
  rw [law, weighted_integral (reference n) (weight n β hβ)
    (weight_continuous n β hβ).measurable (fun z => (weight_pos n β hβ z).le)
    (by rw [weight_integral]; exact (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1),
    weight_integral]

/-- The two-slice marginal is the already constructed original-transfer ground edge law. -/
theorem pair_integral (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n × Slice n, ℝ)) :
    (∫ z, F z.1 ∂law n β hβ) =
      ∫ uv, F uv ∂GroundStateDirichlet.edgeLaw (WilsonSlabOperator.measure n)
        (kernelMap n β) (ground n β hβ) ‖transfer n β‖ := by
  rw [law_integral]
  have hc : Continuous (fun z : Slab n => weight n β hβ z * F z.1) :=
    (weight_continuous n β hβ).mul (F.continuous.comp continuous_fst)
  rw [reference, integral_prod _
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_mul_const, weight_temporal_integral]
  rw [GroundStateDirichlet.edge_integral _ _ (kernelMap n β).continuous
    (fun uv => (kernel_positive character character_continuous β 2 uv.1 uv.2).le)
    _ (ground n β hβ).continuous (fun u => (ground_pos n β hβ u).le) _
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [] with uv
  unfold GroundStateDirichlet.edgeDensity
  ring

/-- Exact exponential-moment cancellation under the actual normalized slab law. -/
theorem reciprocal_moment (β : ℝ) (hβ : 0 ≤ β) :
    (∫ z, Real.exp (β * energy n z) ∂law n β hβ) =
      (WilsonVacuumConvergence.overlap n β hβ)^2 / ‖transfer n β‖ := by
  rw [law_integral]
  have he (z : Slab n) : weight n β hβ z * Real.exp (β * energy n z) =
      ground n β hβ z.1.1 * ground n β hβ z.1.2 := by
    unfold weight
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  simp_rw [he]
  rw [reference, integral_fun_fst
    (fun uv : Slice n × Slice n => ground n β hβ uv.1 * ground n β hβ uv.2)]
  simp only [probReal_univ, one_smul]
  rw [integral_prod_mul]
  change (_ * _) / _ = _^2 / _
  rw [pow_two]
  rfl

/-- Unit Haar L2 normalization bounds the ground overlap by one. -/
theorem overlap_le_one (β : ℝ) (hβ : 0 ≤ β) : WilsonVacuumConvergence.overlap n β hβ ≤ 1 := by
  have h := re_inner_le_norm (𝕜 := ℂ) (WilsonVacuumConvergence.vacuum n β hβ)
    (WilsonVacuumConvergence.boundary n)
  rw [WilsonVacuumConvergence.overlap_inner] at h
  change WilsonVacuumConvergence.overlap n β hβ ≤
    ‖WilsonVacuumConvergence.vacuum n β hβ‖ * ‖WilsonVacuumConvergence.boundary n‖ at h
  rw [WilsonVacuumConvergence.vacuum_norm, WilsonVacuumConvergence.boundary_norm, mul_one] at h
  exact h

/-- Jensen uses the physical ground slab itself; the ground state is not
replaced by the periodic Wilson law or supplied as an unknown hypothesis. -/
theorem expected_energy_le_free_energy (β : ℝ) (hβ : 0 < β) :
    (∫ z, energy n z ∂law n β hβ.le) ≤ -Real.log ‖transfer n β‖ / β := by
  have hc : Continuous (fun z : Slab n => β * energy n z) :=
    continuous_const.mul (energy_continuous n)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hc.integrable_of_hasCompactSupport
      (μ := law n β hβ.le) (HasCompactSupport.of_compactSpace _))
    ((Real.continuous_exp.comp hc).integrable_of_hasCompactSupport
      (μ := law n β hβ.le) (HasCompactSupport.of_compactSpace _))
  change Real.exp (∫ z, β * energy n z ∂law n β hβ.le) ≤
    ∫ z, Real.exp (β * energy n z) ∂law n β hβ.le at hj
  rw [integral_const_mul, reciprocal_moment] at hj
  have hl := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ.le).1
  have ho := overlap_le_one n β hβ.le
  have ho0 := WilsonVacuumConvergence.overlap_pos n β hβ.le
  have hs : (WilsonVacuumConvergence.overlap n β hβ.le)^2 ≤ 1 := by nlinarith
  have he := hj.trans (div_le_div_of_nonneg_right hs hl.le)
  have hh := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp, one_div, Real.log_inv] at hh
  exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hh)


/-- Identity neighborhoods on the actual spatial and temporal links. -/
def spatialCap (K : ℕ) : Set (Slice n) :=
  Set.pi Set.univ (fun _ => nearIdentity representation K)

def temporalCap (K : ℕ) : Set (SliceGauge n WilsonSlabOperator.Q) :=
  Set.pi Set.univ (fun _ => nearIdentity representation K)

def cap (K : ℕ) : Set (Slab n) :=
  (spatialCap n K ×ˢ spatialCap n K) ×ˢ temporalCap n K

theorem cap_measurable (K : ℕ) : MeasurableSet (cap n K) := by
  have hs : MeasurableSet (spatialCap n K) :=
    MeasurableSet.pi Set.countable_univ
      (fun _ _ => nearIdentity_measurable representation representation_continuous K)
  have ht : MeasurableSet (temporalCap n K) :=
    MeasurableSet.pi Set.countable_univ
      (fun _ _ => nearIdentity_measurable representation representation_continuous K)
  exact (hs.prod hs).prod ht

/-- Both spatial slices and the temporal links give exactly seven links per spatial site. -/
theorem cap_mass (K : ℕ) :
    (reference n).real (cap n K) =
      ((compactHaar WilsonSlabOperator.Q).real (nearIdentity representation K))^
        (7 * Fintype.card (SpatialVertex n)) := by
  have hs : (WilsonSlabOperator.measure n).real (spatialCap n K) =
      ((compactHaar WilsonSlabOperator.Q).real (nearIdentity representation K))^
        (3 * Fintype.card (SpatialVertex n)) := by
    unfold Measure.real WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar spatialCap
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      ENNReal.toReal_pow, Nat.mul_comm]
  have ht : (temporalHaar (n := n) (G := WilsonSlabOperator.Q)).real (temporalCap n K) =
      ((compactHaar WilsonSlabOperator.Q).real (nearIdentity representation K))^
        Fintype.card (SpatialVertex n) := by
    unfold Measure.real temporalHaar temporalCap
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow]
  unfold Measure.real reference cap
  rw [Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul, ENNReal.toReal_mul]
  change (WilsonSlabOperator.measure n).real (spatialCap n K) *
    (WilsonSlabOperator.measure n).real (spatialCap n K) *
    (temporalHaar (n := n) (G := WilsonSlabOperator.Q)).real (temporalCap n K) = _
  rw [hs, ht, ← pow_add, ← pow_add]
  congr 1
  omega

theorem cap_mass_lower (K : ℕ) (hK : 0 < K) :
    (massLower (Fin 2) K)^(7 * Fintype.card (SpatialVertex n)) ≤
      (reference n).real (cap n K) := by
  rw [cap_mass]
  exact pow_le_pow_left₀ (massLower_pos (Fin 2) K).le
    (nearIdentity_mass_lower representation representation_continuous K hK) _

/-- Every actual spatial plaquette is small on the constructed cap. -/
theorem potential_cap_bound (K : ℕ) (u : Slice n) (hu : u ∈ spatialCap n K) :
    potential character 2 u ≤
      3 * (Fintype.card (SpatialVertex n) : ℝ) * squaredTolerance (Fin 2) K := by
  have hp (x : SpatialVertex n) (p : SpatialPlane) :
      2 - (character (spatialHolonomy u x p.1.1 p.1.2)).re ≤
        squaredTolerance (Fin 2) K := by
    have h := four_link_defect_squared_bound representation K
      (u (x, p.1.1)) (u (spatialStep n x p.1.1, p.1.2))
      (u (spatialStep n x p.1.2, p.1.1)) (u (x, p.1.2))
      (hu _ (Set.mem_univ _)) (hu _ (Set.mem_univ _))
      (hu _ (Set.mem_univ _)) (hu _ (Set.mem_univ _))
    simpa only [UnitaryHolonomyDefect.defect, representation_character, Fintype.card_fin,
      Nat.cast_ofNat, spatialHolonomy] using h
  calc
    _ ≤ ∑ _x : SpatialVertex n, ∑ _p : SpatialPlane, squaredTolerance (Fin 2) K :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun p _ => hp x p))
    _ = _ := by simp [WilsonSlabBounds.spatialPlane_card]; ring

/-- Temporal plaquettes use the actual temporal link variables, with the same cap estimate. -/
theorem temporal_cap_bound (K : ℕ) (z : Slab n) (hz : z ∈ cap n K) :
    temporalAction character 2 z.1.1 z.1.2 z.2 ≤
      3 * (Fintype.card (SpatialVertex n) : ℝ) * squaredTolerance (Fin 2) K := by
  have hp (x : SpatialVertex n) (i : Fin 3) :
      2 - (character (temporalHolonomy z.1.1 z.1.2 z.2 x i)).re ≤
        squaredTolerance (Fin 2) K := by
    have h := four_link_defect_squared_bound representation K
      (z.2 x) (z.1.2 (x, i)) (z.2 (spatialStep n x i)) (z.1.1 (x, i))
      (hz.2 _ (Set.mem_univ _)) (hz.1.2 _ (Set.mem_univ _))
      (hz.2 _ (Set.mem_univ _)) (hz.1.1 _ (Set.mem_univ _))
    simpa only [UnitaryHolonomyDefect.defect, representation_character, Fintype.card_fin,
      Nat.cast_ofNat, temporalHolonomy] using h
  calc
    _ ≤ ∑ _x : SpatialVertex n, ∑ _i : Fin 3, squaredTolerance (Fin 2) K :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun i _ => hp x i))
    _ = _ := by simp; ring

/-- The two half-spatial potentials and one temporal potential total six plaquettes per site. -/
theorem cap_energy_bound (K : ℕ) (z : Slab n) (hz : z ∈ cap n K) :
    energy n z ≤ 6 * (Fintype.card (SpatialVertex n) : ℝ) * squaredTolerance (Fin 2) K := by
  have hu := potential_cap_bound n K z.1.1 hz.1.1
  have hv := potential_cap_bound n K z.1.2 hz.1.2
  have ht := temporal_cap_bound n K z hz
  simp only [energy, slabAction, one_mul]
  linarith

/-- The normalized constant test is a genuine Rayleigh lower bound for the original transfer. -/
theorem average_kernel_le_top (β : ℝ) :
    (∫ uv, kernelMap n β uv
      ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) ≤ ‖transfer n β‖ := by
  let e := ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ))
  have he := WilsonSlabBounds.constant_norm_le_one n
  have ht : ‖transfer n β e‖ ≤ ‖transfer n β‖ := by
    exact ((transfer n β).le_opNorm e).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg (transfer n β)))
  have hi := re_inner_le_norm (𝕜 := ℂ) e (transfer n β e)
  change (inner ℂ (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ)))
    (transfer n β (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ
      (1 : C(Slice n, ℂ))))).re ≤ ‖e‖ * ‖transfer n β e‖ at hi
  rw [transfer_one_pairing, Complex.ofReal_re] at hi
  exact hi.trans (by
    simpa only [one_mul] using mul_le_mul he ht (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

/-- A polynomial-in-coupling trial lower bound for the actual attained top eigenvalue. -/
theorem top_cap_lower (β : ℝ) (hβ : 0 ≤ β) (K : ℕ) (hK : 0 < K) :
    (massLower (Fin 2) K)^(7 * Fintype.card (SpatialVertex n)) *
      Real.exp (-β * (6 * (Fintype.card (SpatialVertex n) : ℝ) *
        squaredTolerance (Fin 2) K)) ≤ ‖transfer n β‖ := by
  have h := GibbsLowEnergyConcentration.partition_lower (reference n) (energy n)
    (energy_continuous n) β hβ
    (6 * (Fintype.card (SpatialVertex n) : ℝ) * squaredTolerance (Fin 2) K)
    ((massLower (Fin 2) K)^(7 * Fintype.card (SpatialVertex n)))
    (cap n K) (cap_measurable n K) (cap_mass_lower n K hK) (cap_energy_bound n K)
  have he : (∫ z, GibbsLowEnergyConcentration.weight (energy n) β z ∂reference n) =
      ∫ uv, kernelMap n β uv
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) := by
    unfold GibbsLowEnergyConcentration.weight
    have hc : Continuous (fun z : Slab n => Real.exp (-β * energy n z)) :=
      Real.continuous_exp.comp (continuous_const.mul (energy_continuous n))
    rw [reference, integral_prod _
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    apply integral_congr_ae
    filter_upwards [] with uv
    change (∫ h, Real.exp (-β * energy n (uv, h)) ∂temporalHaar) = _
    apply integral_congr_ae
    filter_upwards [] with h
    change Real.exp (-β * energy n (uv, h)) =
      Real.exp (-slabAction character β 2 uv.1 uv.2 h)
    simp only [energy, slabAction, one_mul]
    congr 1
    ring
  rw [he] at h
  exact h.trans (average_kernel_le_top n β)

/-- The normalized actual ground-slab energy is uniformly small at weak coupling. -/
theorem energy_density_grid_bound (β : ℝ) (hβ : 0 < β) (K : ℕ) (hK : 0 < K) :
    (∫ z, energy n z ∂law n β hβ.le) / (6 * (Fintype.card (SpatialVertex n) : ℝ)) ≤
      1568 / (K : ℝ)^2 + (28 / (3 * β)) * Real.log ((2 * K + 1 : ℕ) : ℝ) := by
  have hl := top_cap_lower n β hβ.le K hK
  have hp := pow_pos (massLower_pos (Fin 2) K) (7 * Fintype.card (SpatialVertex n))
  have hh := Real.log_le_log (mul_pos hp (Real.exp_pos _)) hl
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hh
  have he := expected_energy_le_free_energy n β hβ
  have he' := (le_div_iff₀ hβ).mp he
  have hv : 0 < (Fintype.card (SpatialVertex n) : ℝ) := by positivity
  apply (div_le_iff₀ (by positivity : 0 < 6 * (Fintype.card (SpatialVertex n) : ℝ))).mpr
  have hmass : Real.log (massLower (Fin 2) K) =
      -8 * Real.log ((2 * K + 1 : ℕ) : ℝ) := by
    simp only [massLower, Fintype.card_fin, one_div, Real.log_inv, Real.log_pow]
    norm_num
  have heps : squaredTolerance (Fin 2) K = 1568 / (K : ℝ)^2 := by
    rw [squaredTolerance_formula]
    norm_num
  rw [hmass, heps] at hh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  apply (mul_le_mul_iff_left₀ hβ).mp
  have heq : (1568 / (K : ℝ)^2 + (28 / (3 * β)) *
      Real.log ((2 * K + 1 : ℕ) : ℝ)) *
      (6 * (Fintype.card (SpatialVertex n) : ℝ)) * β =
      β * (6 * (Fintype.card (SpatialVertex n) : ℝ) * (1568 / (K : ℝ)^2)) +
      56 * (Fintype.card (SpatialVertex n) : ℝ) * Real.log ((2 * K + 1 : ℕ) : ℝ) := by
    field_simp [hβ.ne', (Nat.cast_ne_zero.mpr hK.ne' : (K : ℝ) ≠ 0)]
    ring
  rw [heq]
  nlinarith

/-- Explicit weak-coupling envelope for the actual physical ground slab. -/
def envelope (β : ℝ) : ℝ := 1568 / β^2 + (28 / (3 * β)) * Real.log (2 * β + 5)

theorem energy_density_bound (β : ℝ) (hβ : 0 < β) :
    (∫ z, energy n z ∂law n β hβ.le) / (6 * (Fintype.card (SpatialVertex n) : ℝ)) ≤
      envelope β := by
  apply (energy_density_grid_bound n β hβ (grid β) (grid_pos β)).trans
  unfold envelope
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ hβ.le (beta_le_grid β) 2)
  · exact mul_le_mul_of_nonneg_left (grid_log_le β hβ) (by positivity)


omit [NeZero n] in
/-- The derived actual-transfer energy envelope vanishes at weak coupling. -/
theorem envelope_tendsto : Filter.Tendsto envelope Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun β : ℝ => 1176 / β^2) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by decide : 2 ≠ 0))).const_mul
        (1176 : ℝ)
  have h := (WilsonEnergyDensity.energyEnvelope_tendsto.const_mul (7 / 4 : ℝ)).sub hi
  convert h using 1
  · ext β
    unfold envelope WilsonEnergyDensity.energyEnvelope
    ring
  · norm_num

omit [NeZero n] in
/-- The actual physical ground-slab mean energy density tends to zero for
arbitrary varying spatial periods. The coupling is nonnegative by its type;
no law, ground-state concentration or rate premise is supplied. -/
theorem energy_density_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] (β : ι → ℝ≥0)
    (hβ : Filter.Tendsto (fun i => (β i : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun i =>
      (∫ z, energy (N i) z ∂law (N i) (β i) (β i).coe_nonneg) /
        (6 * (Fintype.card (SpatialVertex (N i)) : ℝ))) l (nhds 0) := by
  apply squeeze_zero' _ _ (envelope_tendsto.comp hβ)
  · exact Filter.Eventually.of_forall (fun i =>
      div_nonneg (integral_nonneg (energy_nonneg (N i))) (by positivity))
  · filter_upwards [hβ.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with i hi
    exact energy_density_bound (N i) (β i) hi

end
end UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy
