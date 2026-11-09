/- Polynomial Haar-cap lower bound for the actual finite-block kernel mass.
The price depends on the block's links and internal plaquettes only. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialCutKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutCap
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonSpatialCutEnergy WilsonSpatialCutKernel WilsonEnergyDensity UnitaryHaarNeighborhood
open WilsonSingleLinkStaples (character character_mul_comm)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def cap (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) : Set (Inside n S) :=
  Set.pi Set.univ (fun _ => nearIdentity representation K)

theorem cap_measurable (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) :
    MeasurableSet (cap n S K) :=
  MeasurableSet.pi Set.countable_univ
    (fun _ _ => nearIdentity_measurable representation representation_continuous K)

omit [NeZero n] in
theorem cap_mass_lower (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) (hK : 0 < K) :
    (massLower (Fin 2) K)^S.card ≤ (insideHaar n S).real (cap n S K) := by
  have he : (insideHaar n S).real (cap n S K) =
      ((RegulatedGauge.compactHaar Q).real (nearIdentity representation K))^S.card := by
    unfold Measure.real insideHaar WilsonBlockMarginal.insideMeasure cap
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ENNReal.toReal_pow]
  rw [he]
  exact pow_le_pow_left₀ (massLower_pos (Fin 2) K).le
    (nearIdentity_mass_lower representation representation_continuous K hK) _

omit [NeZero n] in
theorem cap_field (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) (a : Inside n S)
    (ha : a ∈ cap n S K) (e : SpatialVertex n × Fin 3) (he : e ∈ S) :
    insideField n S a e ∈ nearIdentity representation K := by
  rw [insideField, WilsonBlockMarginal.assemble_inside S _ e he]
  exact ha _ (Set.mem_univ _)

theorem bulk_cap (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) (a : Inside n S)
    (ha : a ∈ cap n S K) :
    bulkPotential n S (insideField n S a) ≤ (bulk n S).card*squaredTolerance (Fin 2) K := by
  have hp (p : Plaquette n) (hp : p ∈ bulk n S) :
      defect n (insideField n S a) p ≤ squaredTolerance (Fin 2) K := by
    have hs := (Finset.mem_filter.mp hp).2
    have h := four_link_defect_squared_bound representation K
      (insideField n S a (p.1,p.2.1.1))
      (insideField n S a (spatialStep n p.1 p.2.1.1,p.2.1.2))
      (insideField n S a (spatialStep n p.1 p.2.1.2,p.2.1.1))
      (insideField n S a (p.1,p.2.1.2))
      (cap_field n S K a ha _ (hs (by simp [support])))
      (cap_field n S K a ha _ (hs (by simp [support])))
      (cap_field n S K a ha _ (hs (by simp [support])))
      (cap_field n S K a ha _ (hs (by simp [support])))
    simpa only [UnitaryHolonomyDefect.defect, representation_character, Fintype.card_fin,
      Nat.cast_ofNat, defect, spatialHolonomy] using h
  have h := Finset.sum_le_sum (s := bulk n S) (fun p hp' => hp p hp')
  simpa only [bulkPotential, partPotential, Finset.sum_const, nsmul_eq_mul] using h

omit [NeZero n] in
theorem kinetic_cap (S : Finset (SpatialVertex n × Fin 3)) (K : ℕ) (a b : Inside n S)
    (ha : a ∈ cap n S K) (hb : b ∈ cap n S K) :
    kineticPart n S (insideField n S a) (insideField n S b) ≤
      S.card*squaredTolerance (Fin 2) K := by
  have h1 : (1 : Q) ∈ nearIdentity representation K := by
    intro i j
    rw [map_one]
    change ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ _
    rw [sub_self, norm_zero]
    unfold entryRadius
    positivity
  have hp (e : SpatialVertex n × Fin 3) (he : e ∈ S) :
      2-(character ((insideField n S a e)⁻¹*insideField n S b e)).re ≤
        squaredTolerance (Fin 2) K := by
    have h := four_link_defect_squared_bound representation K
      1 (insideField n S b e) 1 (insideField n S a e)
      h1 (cap_field n S K b hb e he) h1 (cap_field n S K a ha e he)
    simp only [one_mul, inv_one, mul_one, UnitaryHolonomyDefect.defect,
      representation_character, Fintype.card_fin, Nat.cast_ofNat] at h
    rwa [character_mul_comm] at h
  have h := Finset.sum_le_sum (s := S) (fun e he => hp e he)
  simpa only [kineticPart, Finset.sum_const, nsmul_eq_mul] using h

theorem interior_cap_lower (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (K : ℕ) (a b : Inside n S) (ha : a ∈ cap n S K) (hb : b ∈ cap n S K) :
    Real.exp (-β*(((bulk n S).card : ℝ)+S.card)*squaredTolerance (Fin 2) K) ≤
      interior n β S (a,b) := by
  have h1 := bulk_cap n S K a ha
  have h2 := bulk_cap n S K b hb
  have hk := kinetic_cap n S K a b ha hb
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (show bulkPotential n S (insideField n S a)/2+
      kineticPart n S (insideField n S a) (insideField n S b)+
      bulkPotential n S (insideField n S b)/2 ≤
      (((bulk n S).card : ℝ)+S.card)*squaredTolerance (Fin 2) K by nlinarith) hβ
  change _ ≤ -β*(bulkPotential n S (insideField n S a)/2+
    kineticPart n S (insideField n S a) (insideField n S b)+
    bulkPotential n S (insideField n S b)/2)
  nlinarith

/-- An explicit strictly positive normalization lower bound with no exterior
link count. The squared cap mass accounts for both block endpoints. -/
theorem insideMass_lower (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (K : ℕ) (hK : 0 < K) :
    (massLower (Fin 2) K)^(2*S.card)*
      Real.exp (-β*(((bulk n S).card : ℝ)+S.card)*squaredTolerance (Fin 2) K) ≤
        insideMass n β S := by
  let E := cap n S K ×ˢ cap n S K
  let μ := (insideHaar n S).prod (insideHaar n S)
  let c := Real.exp (-β*(((bulk n S).card : ℝ)+S.card)*squaredTolerance (Fin 2) K)
  have hE : MeasurableSet E := (cap_measurable n S K).prod (cap_measurable n S K)
  have hi := integral_mono ((integrable_const c).indicator hE)
    (CompactDensityEntropy.continuous_integrable μ _ (interior n β S).continuous)
    (fun z => show E.indicator (fun _ => c) z ≤ interior n β S z from by
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz]
        exact interior_cap_lower n β hβ S K z.1 z.2 hz.1 hz.2
      · rw [Set.indicator_of_notMem hz]
        exact (piece_pos n β S _ _).le)
  rw [integral_indicator hE, setIntegral_const] at hi
  change μ.real E*c ≤ insideMass n β S at hi
  have hm : (massLower (Fin 2) K)^(2*S.card) ≤ μ.real E := by
    have h := pow_le_pow_left₀ (pow_pos (massLower_pos (Fin 2) K) S.card).le
      (cap_mass_lower n S K hK) 2
    rw [← pow_mul, Nat.mul_comm S.card 2] at h
    simpa only [μ, E, Measure.real, Measure.prod_prod, ENNReal.toReal_mul, pow_two] using h
  exact (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le).trans hi

/-- At the proved coupling-dependent cap scale the block normalization price
per internal link/plaquette tends to zero. -/
theorem insideMass_exp_lower (β : ℝ) (hβ : 0 < β)
    (S : Finset (SpatialVertex n × Fin 3)) :
    Real.exp (-2*β*(((bulk n S).card : ℝ)+S.card)*WilsonGroundSlabEnergy.envelope β) ≤
      insideMass n β S := by
  let K := grid β
  have hK : 0 < K := grid_pos β
  have hl := insideMass_lower n β hβ.le S K hK
  have hp := pow_pos (massLower_pos (Fin 2) K) (2*S.card)
  have hh := Real.log_le_log (mul_pos hp (Real.exp_pos _)) hl
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hh
  have hm : Real.log (massLower (Fin 2) K) = -8*Real.log ((2*K+1 : ℕ) : ℝ) := by
    simp only [massLower, Fintype.card_fin, one_div, Real.log_inv, Real.log_pow]
    norm_num
  have ht : squaredTolerance (Fin 2) K = 1568/(K : ℝ)^2 := by
    rw [squaredTolerance_formula]
    norm_num
  rw [hm, ht] at hh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  have hg : 1568/(K : ℝ)^2+(28/(3*β))*Real.log ((2*K+1 : ℕ) : ℝ) ≤
      WilsonGroundSlabEnergy.envelope β := by
    unfold WilsonGroundSlabEnergy.envelope
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hβ.le (beta_le_grid β) 2)
    · exact mul_le_mul_of_nonneg_left (grid_log_le β hβ) (by positivity)
  let M : ℝ := (bulk n S).card+S.card
  have hM : 0 ≤ M := by positivity
  have hs : (S.card : ℝ) ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log ((2*K+1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*K+1 by omega))
  have htol : 0 ≤ 1568/(K : ℝ)^2 := by positivity
  have hgm := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*β*M by positivity)
  have he : (2*β*M)*(1568/(K : ℝ)^2+(28/(3*β))*Real.log ((2*K+1 : ℕ) : ℝ)) =
      2*β*M*(1568/(K : ℝ)^2)+(56/3)*M*Real.log ((2*K+1 : ℕ) : ℝ) := by
    field_simp [hβ.ne']
    ring
  rw [he] at hgm
  have hpay : -2*β*M*WilsonGroundSlabEnergy.envelope β ≤ Real.log (insideMass n β S) := by
    change (2*(S.card : ℝ))*(-8*Real.log ((2*K+1 : ℕ) : ℝ))+
      -β*M*(1568/(K : ℝ)^2) ≤ _ at hh
    have h0 := mul_nonneg (mul_nonneg hβ.le hM) htol
    have h1 := mul_nonneg (show 0 ≤ (56/3)*M-16*(S.card : ℝ) by nlinarith) hlog
    nlinarith
  have h := Real.exp_le_exp.mpr hpay
  rwa [Real.exp_log (insideMass_pos n β S)] at h

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutCap
