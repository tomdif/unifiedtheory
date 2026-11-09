/- 4D Hodge Star Involution (`★² = id` on `Λ²(ℝ⁴)`), Self-Dual / Anti-Self-Dual `3 + 3`
Submodule Decomposition, Abstract Hodge-Induced Chiral Grading on the Dressing Sector `ker φ`,
and Anomaly-Driven Fermion Representation & Generation Counting (`2 Nc Nw + Nw + 1 = 15`)
Bridged with Orthogonal Projection & Residual Energy Multi-Packet Decomposition:
1. Formalizes a unified audit bridge for `UnifiedTheory.LayerA.HodgeStarFourD` and
   `UnifiedTheory.LayerA.ChiralityFromHodge`, certifying `hodgeStar.comp hodgeStar = id`,
   idempotency of `sdProj` and `asdProj`, exact decomposition `ω = sdProj ω + asdProj ω`,
   three-component determination and rank `finrank ℝ selfDual = finrank ℝ antiSelfDual = 3`,
   sign formula `(-1)^(2*(4-2)) = 1`, involution-induced complementary `ChiralGrading`,
   absence of nontrivial chiral gradings on the 1D source sector `K`, and nontrivial
   chiral grading on the dressing sector `ker φ` (`chirality_derived_not_identified`).
2. Bridges `UnifiedTheory.LayerA.FermionRepForced` and
   `UnifiedTheory.LayerA.FermionCountFromAnomaly`, certifying `SU(3)³` color parity
   `(n_3 : ℤ) - n_3bar = 0 → n_3 = n_3bar`, minimal chiral fermion count
   `fermionCount_SUN 2 = 15 < 22 = fermionCount_SUN 3`, general anomaly counting formula
   `totalFermions Nc Nw = 2 * Nc * Nw + Nw + 1`, colored/uncolored split `12 + 3 = 15`
   at `(Nc, Nw) = (3, 2)`, vectorlike even count `2 * (Nc + 1)` at `Nw = 1`, and uniqueness
   of `(Nc, Nw) = (3, 2)` among `Nc, Nw ≥ 2` achieving `totalFermions Nc Nw = 15`.
3. Unites the 4D Hodge star `3 + 3` self-dual/anti-self-dual split and `12 + 3 = 15`
   colored/uncolored fermion sector counts with the orthogonal-projection and complementary
   residual-energy multi-packet decomposition from
   `KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition`. -/
import UnifiedTheory.LayerA.HodgeStarFourD
import UnifiedTheory.LayerA.ChiralityFromHodge
import UnifiedTheory.LayerA.FermionRepForced
import UnifiedTheory.LayerA.FermionCountFromAnomaly
import UnifiedTheory.Audit.KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
import UnifiedTheory.Audit.KFCausalSO10SharpenedQuarkLeptonUnificationMagicSquareMultiPacketBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalHodgeStarFourDChiralityFermionRepMultiPacketBridge

noncomputable section

open scoped InnerProduct BigOperators
open UnifiedTheory.LayerA.AnomalyConstraints
open UnifiedTheory.LayerA.HodgeStarFourD
open UnifiedTheory.LayerA.ChiralityFromHodge
open UnifiedTheory.LayerA.FermionRepForced
open UnifiedTheory.LayerA.FermionCountFromAnomaly
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (cauchySchwarzWeightRatio)
open KFCausalSMFrameworkAtomicCrossSectorMultiPacketSynthesis
  (uniformSectorWeights uniformSectorWeights_cauchySchwarzWeightRatio)
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceModeState arbitrarySourceDegreeMPolyState
   antipodalWeights antipodalSources identicalPackets)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyResponse)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
  (IsOrthogonalProjection complementaryProjection hilbertEnergy
   isOrthogonalProjection_complementary
   proj_and_complementaryProjection_annihilate
   inner_proj_complementaryProjection_zero
   hilbertEnergy_orthogonalProjection_pythagorean
   arbitrarySourceDegreeMPolyState_orthogonalProjection_decomposition
   arbitrary_source_orthogonal_projection_residual_energy_master_synthesis)

/-! ### 1. 4D Hodge Star Involution, Self-Dual / Anti-Self-Dual `3 + 3` Split, and Chiral Grading -/

/-- 4D Hodge star involution and self-dual / anti-self-dual projection package on `TwoForm = Fin 6 → ℝ`:
`★ ∘ ★ = id`, `sdProj` and `asdProj` idempotency and eigenspace membership,
`ω = sdProj ω + asdProj ω`, and `(-1)^(2*(4-2)) = 1`. -/
theorem hodge_star_four_d_involution_and_projection_package (ω : TwoForm) :
    hodgeStar.comp hodgeStar = LinearMap.id ∧
    hodgeStar (hodgeStar ω) = ω ∧
    hodgeStar (sdProj ω) = sdProj ω ∧
    hodgeStar (asdProj ω) = -asdProj ω ∧
    ω = sdProj ω + asdProj ω ∧
    sdProj ω ∈ selfDual ∧
    asdProj ω ∈ antiSelfDual ∧
    sdProj (sdProj ω) = sdProj ω ∧
    asdProj (asdProj ω) = asdProj ω ∧
    (-1 : ℤ) ^ (2 * (4 - 2)) = 1 :=
  ⟨hodge_star_sq_eq_id,
   hodge_star_sq ω,
   sdProj_is_selfDual ω,
   asdProj_is_antiSelfDual ω,
   two_forms_eq_sd_plus_asd ω,
   sdProj_mem_selfDual ω,
   asdProj_mem_antiSelfDual ω,
   sdProj_idempotent ω,
   asdProj_idempotent ω,
   hodge_sq_sign_formula⟩

/-- Three-parameter coordinate characterization and `3 + 3` dimension package for the
4D self-dual and anti-self-dual 2-form submodules. -/
theorem hodge_star_four_d_three_plus_three_dimension_package (a b c : ℝ) :
    mkSelfDual a b c ∈ selfDual ∧
    mkAntiSelfDual a b c ∈ antiSelfDual ∧
    Module.finrank ℝ selfDual = 3 ∧
    Module.finrank ℝ antiSelfDual = 3 ∧
    Module.finrank ℝ selfDual + Module.finrank ℝ antiSelfDual = 6 :=
  ⟨mkSelfDual_mem a b c,
   mkAntiSelfDual_mem a b c,
   dim_self_dual_eq_three,
   dim_anti_self_dual_eq_three,
   by rw [dim_self_dual_eq_three, dim_anti_self_dual_eq_three]⟩

/-- Involution-induced chiral grading and K/P dressing-sector chirality package from
`UnifiedTheory.LayerA.ChiralityFromHodge`. -/
theorem chirality_from_hodge_involution_and_kp_sector_package
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (inv : Involution W) (w : W)
    (φ : W →ₗ[ℝ] ℝ) (hφ : φ ≠ 0)
    (K_sub : Submodule ℝ W) (hKP : IsCompl (LinearMap.ker φ) K_sub)
    (hK_dim : Module.finrank ℝ K_sub = 1)
    (star_ker : (LinearMap.ker φ) →ₗ[ℝ] (LinearMap.ker φ))
    (h_star_inv : ∀ x : LinearMap.ker φ, star_ker (star_ker x) = x)
    (h_plus : Involution.plusSpace ⟨star_ker, h_star_inv⟩ ≠ ⊥)
    (h_minus : Involution.minusSpace ⟨star_ker, h_star_inv⟩ ≠ ⊥) :
    (∃ wp wm : W, wp ∈ inv.plusSpace ∧ wm ∈ inv.minusSpace ∧ w = wp + wm) ∧
    inv.plusSpace ⊓ inv.minusSpace = ⊥ ∧
    inv.plusSpace ⊔ inv.minusSpace = ⊤ ∧
    (∃ g : ChiralGrading (LinearMap.ker φ), g.IsNontrivial) ∧
    (∀ g : ChiralGrading K_sub, ¬ g.IsNontrivial) ∧
    LinearMap.ker φ ≠ ⊥ := by
  have hcap := chirality_derived_not_identified φ hφ K_sub hKP hK_dim
    star_ker h_star_inv h_plus h_minus
  exact ⟨involution_decomposition inv w,
         involution_plus_minus_disjoint inv,
         involution_plus_minus_span inv,
         hcap.1, hcap.2.1, hcap.2.2⟩

/-! ### 2. Anomaly-Driven Fermion Representation & Generation Counting (`12 + 3 = 15`) -/

/-- Fermion representation forcing package (`UnifiedTheory.LayerA.FermionRepForced`):
`SU(3)³` cubic anomaly color parity, `fermionCount_SUN 2 = 15`, `fermionCount_SUN 3 = 22`,
minimality of `SU(2)` (`fermionCount_SUN N > 15` for all `N ≥ 3`), and full SM anomaly cancellation. -/
theorem fermion_rep_forced_color_parity_and_su2_minimality_package
    (n_3 n_3bar N : ℕ) (hanom : (n_3 : ℤ) - n_3bar = 0) (hN : N ≥ 3) :
    n_3 = n_3bar ∧
    fermionCount_SUN 1 = 8 ∧
    fermionCount_SUN 2 = 15 ∧
    fermionCount_SUN 3 = 22 ∧
    fermionCount_SUN N > 15 ∧
    (cubicCondition smCharges ∧ linearCondition smCharges ∧
     su2MixedCondition smCharges ∧ su3MixedCondition smCharges) :=
  ⟨su3_cubic_forces_color_parity n_3 n_3bar hanom,
   su2_is_minimal.2.2,
   su2_gives_15,
   su3_gives_22,
   suN_exceeds_sm N hN,
   sm_generation_forced.2.2.2⟩

/-- Fermion counting formula and `(Nc, Nw) = (3, 2)` uniqueness package
(`UnifiedTheory.LayerA.FermionCountFromAnomaly`):
`totalFermions Nc Nw = 2 * Nc * Nw + Nw + 1`, `totalFermions 3 2 = 15`,
`coloredFermions 3 2 = 12`, `uncoloredFermions 2 = 3`, vectorlike `Nw = 1` count
`2 * (Nc + 1)`, and uniqueness of `(Nc, Nw) = (3, 2)` among `Nc, Nw ≥ 2`. -/
theorem fermion_count_from_anomaly_uniqueness_and_sector_split_package
    (Nc Nw : ℕ) (hNc : Nc ≥ 2) (hNw : Nw ≥ 2) :
    UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions Nc Nw =
      2 * Nc * Nw + Nw + 1 ∧
    UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 3 2 = 15 ∧
    coloredFermions 3 2 = 12 ∧
    uncoloredFermions 2 = 3 ∧
    coloredFermions 3 2 + uncoloredFermions 2 = 15 ∧
    coloredFermions Nc Nw > uncoloredFermions Nw ∧
    (cubicAnomalyCoeff Nc Nw = 0 ∧ leftColoredCount Nc Nw = rightColoredCount Nc Nw) ∧
    (UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions Nc 1 = 2 * Nc + 2 ∧
     2 * Nc + 2 = 2 * (Nc + 1)) ∧
    (UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions Nc Nw ≥
       UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 2 2 ∧
     (UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions Nc Nw =
        UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 3 2 →
      Nc = 3 ∧ Nw = 2)) :=
  ⟨totalFermions_eq Nc Nw,
   sm_generation_count,
   colored_sm,
   uncolored_sm,
   by rw [colored_sm, uncolored_sm],
   total_decomposition Nc Nw hNc ( by omega ),
   color_parity_balanced Nc Nw,
   nw1_not_chiral Nc,
   fermion_count_derived Nc Nw hNc hNw⟩

/-! ### 3. Multi-Packet Sector Weight Ratios and Orthogonal Projection Energy Bridge -/

/-- Exact Cauchy–Schwarz uniform sector weight ratios for the 6-component 4D 2-form space
(`3 + 3 = 6`), the 12-state colored SM sector (`coloredFermions 3 2 = 12`), the 3-state
uncolored SM sector (`uncoloredFermions 2 = 3`), and the 15-state SM generation
(`totalFermions 3 2 = 15`). -/
theorem hodge_and_fermion_sector_cauchy_schwarz_weight_ratios :
    cauchySchwarzWeightRatio (uniformSectorWeights 3) = 3 ∧
    cauchySchwarzWeightRatio (uniformSectorWeights 6) = 6 ∧
    cauchySchwarzWeightRatio (uniformSectorWeights 12) = 12 ∧
    cauchySchwarzWeightRatio (uniformSectorWeights 15) = 15 ∧
    cauchySchwarzWeightRatio (uniformSectorWeights (coloredFermions 3 2)) +
      cauchySchwarzWeightRatio (uniformSectorWeights (uncoloredFermions 2)) =
      cauchySchwarzWeightRatio
        (uniformSectorWeights
          (UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 3 2)) := by
  have h3 := uniformSectorWeights_cauchySchwarzWeightRatio 3 (by decide)
  have h6 := uniformSectorWeights_cauchySchwarzWeightRatio 6 (by decide)
  have h12 := uniformSectorWeights_cauchySchwarzWeightRatio 12 (by decide)
  have h15 := uniformSectorWeights_cauchySchwarzWeightRatio 15 (by decide)
  refine ⟨by norm_num [h3], by norm_num [h6], by norm_num [h12], by norm_num [h15], ?_⟩
  rw [colored_sm, uncolored_sm, sm_generation_count]
  norm_num [h12, h3, h15]

/-- Master 4D Hodge Star Involution, Abstract Chiral Grading, Anomaly-Driven Fermion
Generation Counting (`12 + 3 = 15`), and Orthogonal-Projection Multi-Packet Energy Synthesis. -/
theorem hodge_star_four_d_chirality_fermion_rep_multi_packet_master_synthesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P : E →L[ℂ] E} (hP : IsOrthogonalProjection P)
    (M : ℕ) (c : Fin (M + 2) → ℂ) (c₁ : Fin 2 → ℂ) (ψ : E)
    (ω : TwoForm) (Nc Nw : ℕ) (hNc : Nc ≥ 2) (hNw : Nw ≥ 2) :
    (hodgeStar.comp hodgeStar = LinearMap.id ∧
     ω = sdProj ω + asdProj ω ∧
     Module.finrank ℝ selfDual = 3 ∧
     Module.finrank ℝ antiSelfDual = 3) ∧
    (fermionCount_SUN 2 = 15 ∧
     coloredFermions 3 2 = 12 ∧
     uncoloredFermions 2 = 3 ∧
     UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 3 2 = 15 ∧
     (UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions Nc Nw =
        UnifiedTheory.LayerA.FermionCountFromAnomaly.totalFermions 3 2 →
      Nc = 3 ∧ Nw = 2)) ∧
    (IsOrthogonalProjection (complementaryProjection P) ∧
     hilbertEnergy ψ = hilbertEnergy (P ψ) + hilbertEnergy (complementaryProjection P ψ) ∧
     hilbertEnergy
        (arbitrarySourceDegreeMPolyState (M + 1) antipodalWeights antipodalSources c
          (identicalPackets ψ)) =
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse P (M + 1) antipodalWeights antipodalSources c
          (identicalPackets ψ)) +
      hilbertEnergy
        (arbitrarySourceDegreeMPolyResponse (complementaryProjection P) (M + 1)
          antipodalWeights antipodalSources c (identicalPackets ψ)) ∧
     ‖arbitrarySourceDegreeMPolyResponse P 1 antipodalWeights antipodalSources c₁
        (identicalPackets ψ)‖ = 2 * ‖c₁ 1‖ * ‖P ψ‖) := by
  have horth := arbitrary_source_orthogonal_projection_residual_energy_master_synthesis
    hP M c c₁ ψ
  exact ⟨⟨hodge_star_sq_eq_id,
          two_forms_eq_sd_plus_asd ω,
          dim_self_dual_eq_three,
          dim_anti_self_dual_eq_three⟩,
         ⟨su2_gives_15,
          colored_sm,
          uncolored_sm,
          sm_generation_count,
          (fermion_count_derived Nc Nw hNc hNw).2⟩,
         ⟨horth.1.1, horth.1.2.2.2.2, horth.2.1.2, horth.2.2.2⟩⟩

#print axioms hodge_star_four_d_involution_and_projection_package
#print axioms hodge_star_four_d_three_plus_three_dimension_package
#print axioms chirality_from_hodge_involution_and_kp_sector_package
#print axioms fermion_rep_forced_color_parity_and_su2_minimality_package
#print axioms fermion_count_from_anomaly_uniqueness_and_sector_split_package
#print axioms hodge_and_fermion_sector_cauchy_schwarz_weight_ratios
#print axioms hodge_star_four_d_chirality_fermion_rep_multi_packet_master_synthesis

end

end UnifiedTheory.Audit.KFCausalHodgeStarFourDChiralityFermionRepMultiPacketBridge
