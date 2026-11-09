/- Bridge connecting `SU(3)_c` color group forcing (`ColorGroupForced`), full
`SU(3) × SU(2) × U(1)` gauge group derivation (`GaugeGroupDerived`), chiral
representation forcing and colored-sector global minimality (`RepStructureForced`),
the hypercharge-neutral adjoint unification obstruction (`AdjointUnificationObstruction`),
trace-hypercharge geometric exile from the connection sector (`TraceHyperchargeExile`),
arrow-chiral vector-like fermion mass protection (`VLMassProtection`), and the
transfer-matrix spectral mass and Higgs quartic theorem (`SpectralMassTheorem`)
to multi-packet sector superpositions on `Fin 11`, `Fin 12`, and `Fin 15`,
Cauchy-Schwarz weight ratios, and dominant anchor-mode bounds. -/
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
import UnifiedTheory.Audit.KFCausalDiscreteAmbroseSingerHolonomyMultiPacketBridge
import UnifiedTheory.LayerA.ColorGroupForced
import UnifiedTheory.LayerA.GaugeGroupDerived
import UnifiedTheory.LayerA.RepStructureForced
import UnifiedTheory.LayerA.AdjointUnificationObstruction
import UnifiedTheory.LayerA.TraceHyperchargeExile
import UnifiedTheory.LayerA.VLMassProtection
import UnifiedTheory.LayerA.SpectralMassTheorem

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaugeSelectionAdjointObstructionHyperchargeExileMultiPacketBridge
noncomputable section
open UnifiedTheory.LayerA.ColorGroupForced
  (cubicForNc cubic_factors cubic_solutions
   cubic_nc3_solutions cubic_nc3_sm_match
   fermionCountColor su2_color_count su3_color_count
   count_increasing su3_minimal_distinct sm_gauge_group_forced
   swapProd swap_incompatible_with_grading full_sm_derived)
open UnifiedTheory.LayerA.GaugeGroupDerived
  (freeParameters nw2_uniquely_determined sm_gauge_group_derived)
open UnifiedTheory.LayerA.RepStructureForced
  (FermionAssignment hasColorParity isChiral chargeVars
   smAssignment sm_color_parity sm_is_chiral
   forced_singlets both_multiplets_not_chiral
   colored_sector_globally_minimal sm_colored_sector_achieves_minimum
   anomalyCount charge_determinacy_forces_Nw2 nw1_overconstrained
   representation_structure_forced)
open UnifiedTheory.LayerA.ConnectionDefectAdjoint (adjointSMspectrum)
open UnifiedTheory.LayerA.AdjointUnificationObstruction
  (b1Contribution adjoint_b1_contribution_zero)
open UnifiedTheory.LayerA.AdjointDimension (slMatrix)
open UnifiedTheory.LayerA.TraceHyperchargeExile
  (abelian_direction_dim_one adjoint_fixes_scalar)
open UnifiedTheory.LayerA.VertexMassTension (leverArm)
open UnifiedTheory.LayerA.VLMassProtection
  (dirac_bare_forbidden_iff_arrowChiral
   majorana_bare_allowed_iff_neutral
   protectedMassScale vl_at_v_neutrino_at_MP vl_arrowchiral_runs)
open UnifiedTheory.LayerA.SpectralMassTheorem
  (transferEigenvalue transferEigenvalue_bounds
   neg_log_eigenvalue_eq_gap spectral_decay
   higgsMassFromGap quarticFromMass
   quartic_eq_half_gap_squared quartic_d4 quartic_complete)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (cauchySchwarzWeightRatio)
open KFCausalSMFrameworkAtomicCrossSectorMultiPacketSynthesis
  (uniformSectorWeights uniformSectorWeights_cauchySchwarzWeightRatio)
open KFCausalArbitrarySourceSharpNeutralCancellationCounterexampleAndBounds
  (arbitrarySourceModeState arbitrarySourceDegreeMPolyState isNeutralArbitrarySource)
open KFCausalArbitrarySourceMultiModeOrthogonalDecompositionAndResponseBounds
  (arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral
   arbitrarySourceDegreeMPolyState_dominant_anchor_mode_norm_ge)
open KFCausalDiscreteAmbroseSingerHolonomyMultiPacketBridge
  (discrete_ambrose_singer_eq_bridge)

/-! ### 1. Color Group Forcing, Gauge Group Derivation, and Chiral Representation Structure -/

theorem cubic_factors_bridge (Nc : ℕ) (r : ℝ) :
    cubicForNc Nc r = 6 * Nc * ((Nc : ℝ) - r - 1) * ((Nc : ℝ) + r + 1) :=
  cubic_factors Nc r

theorem cubic_solutions_bridge (Nc : ℕ) (hNc : (Nc : ℝ) ≠ 0) (r : ℝ)
    (hcubic : cubicForNc Nc r = 0) :
    r = (Nc : ℝ) - 1 ∨ r = -((Nc : ℝ) + 1) :=
  cubic_solutions Nc hNc r hcubic

theorem cubic_nc3_solutions_bridge (r : ℝ) (h : cubicForNc 3 r = 0) :
    r = 2 ∨ r = -4 :=
  cubic_nc3_solutions r h

theorem cubic_nc3_sm_match_bridge :
    cubicForNc 3 2 = 0 ∧ cubicForNc 3 (-4) = 0 :=
  cubic_nc3_sm_match

theorem su2_and_su3_color_counts_bridge :
    fermionCountColor 2 = 11 ∧ fermionCountColor 3 = 15 :=
  ⟨su2_color_count, su3_color_count⟩

theorem fermionCountColor_increasing_bridge (N M : ℕ) (h : N < M) :
    fermionCountColor N < fermionCountColor M :=
  count_increasing N M h

theorem su3_minimal_distinct_bridge :
    (3 : ℕ) ≠ 2 ∧
      (∀ N : ℕ, N ≥ 3 → N ≠ 2 → fermionCountColor 3 ≤ fermionCountColor N) :=
  su3_minimal_distinct

theorem sm_gauge_group_forced_bridge :
    ((3 : ℕ) ≠ 2) ∧
    (fermionCountColor 3 = 15) ∧
    (-(3 + 1 : ℝ) = -4 ∧ (3 - 1 : ℝ) = 2 ∧ (-(3 : ℝ) = -3) ∧ (2 * 3 : ℝ) = 6) :=
  sm_gauge_group_forced

theorem swap_incompatible_with_grading_bridge {α : Type*} [DecidableEq α]
    (g1 g2 : α) (h : g1 ≠ g2) :
    swapProd (g1, g2) ≠ (g1, g2) :=
  swap_incompatible_with_grading g1 g2 h

theorem full_sm_derived_bridge :
    (∀ N : ℕ, N ≥ 3 → 7 * N + 1 > 7 * 2 + 1) ∧
    ((3 : ℕ) ≠ 2) ∧
    (fermionCountColor 3 = 15) ∧
    (-(3 + 1 : ℝ) = -4 ∧ (3 - 1 : ℝ) = 2) :=
  full_sm_derived

theorem nw2_uniquely_determined_bridge :
    freeParameters 2 = 1 ∧
    freeParameters 1 = 0 ∧
    (∀ Nw, Nw ≥ 3 → freeParameters Nw > 1) :=
  nw2_uniquely_determined

theorem sm_gauge_group_derived_bridge :
    (freeParameters 2 = 1 ∧ (∀ Nw, Nw ≥ 3 → freeParameters Nw > 1)) ∧
    ((3 : ℕ) ≠ 2) ∧
    (UnifiedTheory.LayerA.FermionCountDerived.totalFermions 3 2 = 15) ∧
    (∀ Nc, Nc ≥ 4 → UnifiedTheory.LayerA.FermionCountDerived.totalFermions Nc 2 > 15) :=
  sm_gauge_group_derived

theorem sm_color_parity_and_chiral_bridge (Nw : ℕ) :
    hasColorParity (smAssignment Nw) Nw ∧
    (Nw ≥ 2 → isChiral (smAssignment Nw)) :=
  ⟨sm_color_parity Nw, sm_is_chiral Nw⟩

theorem forced_singlets_bridge (f : FermionAssignment) (Nw : ℕ) (hNw : Nw ≥ 1)
    (h_parity : hasColorParity f Nw)
    (h_one_mult : f.n_NcNw = 1) (h_no_anti_mult : f.n_NcbNw = 0)
    (h_no_extra_Nc : f.n_Nc1 = 0) :
    f.n_Ncb1 = Nw :=
  forced_singlets f Nw hNw h_parity h_one_mult h_no_anti_mult h_no_extra_Nc

theorem both_multiplets_not_chiral_bridge (f : FermionAssignment) (Nw : ℕ)
    (h_parity : hasColorParity f Nw)
    (h_no_sing1 : f.n_Nc1 = 0) (h_no_sing2 : f.n_Ncb1 = 0)
    (hNw : Nw ≥ 1) :
    ¬isChiral f :=
  both_multiplets_not_chiral f Nw h_parity h_no_sing1 h_no_sing2 hNw

theorem colored_sector_globally_minimal_bridge :
    (∀ f : FermionAssignment,
      hasColorParity f 2 → isChiral f →
        UnifiedTheory.LayerA.RepStructureForced.coloredFermions f 3 2 ≥ 12) ∧
    UnifiedTheory.LayerA.RepStructureForced.coloredFermions (smAssignment 2) 3 2 = 12 :=
  ⟨colored_sector_globally_minimal, sm_colored_sector_achieves_minimum⟩

theorem charge_determinacy_forces_Nw2_bridge :
    chargeVars (smAssignment 2) = anomalyCount + 1 ∧
    chargeVars (smAssignment 1) = anomalyCount :=
  ⟨charge_determinacy_forces_Nw2, nw1_overconstrained⟩

theorem representation_structure_forced_bridge :
    (∀ Nw, hasColorParity (smAssignment Nw) Nw) ∧
    (∀ Nw, Nw ≥ 2 → isChiral (smAssignment Nw)) ∧
    (∀ f Nw, hasColorParity f Nw → f.n_Nc1 = 0 → f.n_Ncb1 = 0 →
        Nw ≥ 1 → ¬isChiral f) ∧
    (chargeVars (smAssignment 2) = anomalyCount + 1) ∧
    (∀ Nw, Nw ≥ 3 → chargeVars (smAssignment Nw) > anomalyCount + 1) ∧
    (UnifiedTheory.LayerA.RepStructureForced.totalFermions (smAssignment 2) 3 2 = 15) :=
  representation_structure_forced

/-! ### 2. Adjoint Obstruction, Trace-Hypercharge Exile, VL Protection, and Spectral Mass -/

theorem adjoint_b1_contribution_zero_bridge :
    b1Contribution adjointSMspectrum = 0 :=
  adjoint_b1_contribution_zero

theorem abelian_direction_dim_one_bridge (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℝ) -
      Module.finrank ℝ (slMatrix n) = 1 :=
  abelian_direction_dim_one n hn

theorem adjoint_fixes_scalar_bridge {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : IsUnit W.det) (c : ℝ) :
    W * (c • (1 : Matrix (Fin n) (Fin n) ℝ)) * W⁻¹ =
      c • (1 : Matrix (Fin n) (Fin n) ℝ) :=
  adjoint_fixes_scalar W hW c

theorem dirac_bare_forbidden_iff_arrowChiral_bridge (qL qR : ℤ) :
    qR - qL ≠ 0 ↔ qL ≠ qR :=
  dirac_bare_forbidden_iff_arrowChiral qL qR

theorem majorana_bare_allowed_iff_neutral_bridge (q : ℤ) :
    2 * q = 0 ↔ q = 0 :=
  majorana_bare_allowed_iff_neutral q

theorem vl_at_v_neutrino_at_MP_bridge (v MP : ℝ) :
    protectedMassScale v MP true = v ∧
    protectedMassScale v MP false = MP :=
  vl_at_v_neutrino_at_MP v MP

theorem vl_arrowchiral_runs_bridge (MGUT v : ℝ) (hv : 0 < v) (h : v < MGUT) :
    0 < leverArm MGUT v :=
  vl_arrowchiral_runs MGUT v hv h

theorem transferEigenvalue_bounds_bridge (d : ℕ) (hd : 3 ≤ d) :
    0 < transferEigenvalue d ∧ transferEigenvalue d < 1 :=
  transferEigenvalue_bounds d hd

theorem neg_log_eigenvalue_eq_gap_bridge (d : ℕ) (hd : 3 ≤ d) :
    -Real.log (transferEigenvalue d) =
      UnifiedTheory.LayerB.PSectorMass.spectralGap d :=
  neg_log_eigenvalue_eq_gap d hd

theorem spectral_decay_bridge (d : ℕ) (hd : 3 ≤ d) (k : ℕ) :
    (transferEigenvalue d) ^ k =
      Real.exp (-(UnifiedTheory.LayerB.PSectorMass.spectralGap d * (k : ℝ))) :=
  spectral_decay d hd k

theorem quartic_eq_half_gap_squared_bridge (d : ℕ) (v : ℝ) (hv : v ≠ 0) :
    quarticFromMass (higgsMassFromGap d v) v =
      (UnifiedTheory.LayerB.PSectorMass.spectralGap d) ^ 2 / 2 :=
  quartic_eq_half_gap_squared d v hv

theorem quartic_d4_bridge (v : ℝ) (hv : v ≠ 0) :
    quarticFromMass (higgsMassFromGap 4 v) v =
      (Real.log (5 / 3)) ^ 2 / 2 :=
  quartic_d4 v hv

theorem quartic_complete_bridge (v : ℝ) (hv : 0 < v) :
    0 < higgsMassFromGap 4 v ∧
    quarticFromMass (higgsMassFromGap 4 v) v = (Real.log (5 / 3)) ^ 2 / 2 ∧
    0 < quarticFromMass (higgsMassFromGap 4 v) v ∧
    quarticFromMass (higgsMassFromGap 4 v) v < 1 / 2 ∧
    (higgsMassFromGap 4 v) ^ 2 =
      2 * quarticFromMass (higgsMassFromGap 4 v) v * v ^ 2 :=
  quartic_complete v hv

/-! ### 3. Multi-Packet Bridges for Fermion Sector Multiplicities and Anchor-Mode Dominance -/

theorem colored_fermions_sm_weight_ratio_eq_twelve :
    cauchySchwarzWeightRatio
      (uniformSectorWeights
        (UnifiedTheory.LayerA.RepStructureForced.coloredFermions (smAssignment 2) 3 2)) = 12 := by
  rw [sm_colored_sector_achieves_minimum]
  simpa using uniformSectorWeights_cauchySchwarzWeightRatio 12 (by decide)

theorem total_fermions_sm_weight_ratio_eq_fifteen :
    cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 3)) = 15 := by
  rw [su3_color_count]
  simpa using uniformSectorWeights_cauchySchwarzWeightRatio 15 (by decide)

theorem su2_color_fermions_weight_ratio_eq_eleven :
    cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 2)) = 11 := by
  rw [su2_color_count]
  simpa using uniformSectorWeights_cauchySchwarzWeightRatio 11 (by decide)

theorem su3_exceeds_su2_color_weight_ratio :
    cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 2)) <
      cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 3)) := by
  rw [su2_color_fermions_weight_ratio_eq_eleven, total_fermions_sm_weight_ratio_eq_fifteen]
  norm_num

theorem colored_sector_sm_neutral_eq_higher_modes
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ)
    (w b : Fin (UnifiedTheory.LayerA.RepStructureForced.coloredFermions (smAssignment 2) 3 2) → ℂ)
    (c : Fin (M + 1) → ℂ)
    (P : Fin (UnifiedTheory.LayerA.RepStructureForced.coloredFermions (smAssignment 2) 3 2) → E)
    (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceDegreeMPolyState M w b c P =
      ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P :=
  arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral M w b c P hneutral

theorem total_fermions_sm_neutral_eq_higher_modes
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ)
    (w b : Fin (fermionCountColor 3) → ℂ)
    (c : Fin (M + 1) → ℂ)
    (P : Fin (fermionCountColor 3) → E)
    (hneutral : isNeutralArbitrarySource w b P) :
    arbitrarySourceDegreeMPolyState M w b c P =
      ∑ r : Fin M, c r.succ • arbitrarySourceModeState w b ((r : ℕ) + 1) P :=
  arbitrarySourceDegreeMPolyState_eq_higher_modes_of_neutral M w b c P hneutral

theorem sm_fermion_sector_dominant_anchor_mode_norm_ge
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (M : ℕ)
    (w b : Fin (fermionCountColor 3) → ℂ)
    (c : Fin (M + 1) → ℂ)
    (P : Fin (fermionCountColor 3) → E)
    (k₀ : Fin (M + 1)) (θ : ℝ)
    (hdom : ∑ k ∈ Finset.univ.erase k₀, ‖c k‖ * ‖arbitrarySourceModeState w b (k : ℕ) P‖ ≤
      θ * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖)) :
    (1 - θ) * (‖c k₀‖ * ‖arbitrarySourceModeState w b (k₀ : ℕ) P‖) ≤
      ‖arbitrarySourceDegreeMPolyState M w b c P‖ :=
  arbitrarySourceDegreeMPolyState_dominant_anchor_mode_norm_ge M w b c P k₀ θ hdom

theorem gauge_selection_adjoint_obstruction_hypercharge_exile_master_synthesis
    {Γ : UnifiedTheory.LayerA.DiscreteBundles.DirectedGraph} {G : Type*} [Group G]
    [UnifiedTheory.LayerA.DiscreteAmbroseSinger.HasReversal Γ]
    (conn : UnifiedTheory.LayerA.DiscreteBundles.DiscreteConnection Γ G)
    [UnifiedTheory.LayerA.DiscreteAmbroseSinger.ReversibleConnection Γ G conn]
    (v₀ : Γ.Vertex) (MGUT v : ℝ) (hv : 0 < v) (hMGUT : v < MGUT) :
    (freeParameters 2 = 1 ∧ (3 : ℕ) ≠ 2 ∧ fermionCountColor 3 = 15) ∧
    (UnifiedTheory.LayerA.RepStructureForced.coloredFermions (smAssignment 2) 3 2 = 12) ∧
    (b1Contribution adjointSMspectrum = 0) ∧
    (∀ n : ℕ, 0 < n →
      Module.finrank ℝ (Matrix (Fin n) (Fin n) ℝ) -
        Module.finrank ℝ (slMatrix n) = 1) ∧
    (0 < leverArm MGUT v) ∧
    (0 < higgsMassFromGap 4 v ∧
      quarticFromMass (higgsMassFromGap 4 v) v = (Real.log (5 / 3)) ^ 2 / 2) ∧
    (cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 2)) <
      cauchySchwarzWeightRatio (uniformSectorWeights (fermionCountColor 3))) ∧
    (UnifiedTheory.LayerA.DiscreteAmbroseSinger.holonomySubgroup conn v₀ =
      Subgroup.closure (UnifiedTheory.LayerA.DiscreteAmbroseSinger.basedCurvatureSet conn v₀)) :=
  ⟨⟨nw2_uniquely_determined_bridge.1, by decide, su3_color_count⟩,
   sm_colored_sector_achieves_minimum,
   adjoint_b1_contribution_zero_bridge,
   abelian_direction_dim_one_bridge,
   vl_arrowchiral_runs_bridge MGUT v hv hMGUT,
   ⟨(quartic_complete_bridge v hv).1, (quartic_complete_bridge v hv).2.1⟩,
   su3_exceeds_su2_color_weight_ratio,
   discrete_ambrose_singer_eq_bridge conn v₀⟩

#print axioms cubic_factors_bridge
#print axioms cubic_solutions_bridge
#print axioms cubic_nc3_solutions_bridge
#print axioms cubic_nc3_sm_match_bridge
#print axioms su2_and_su3_color_counts_bridge
#print axioms fermionCountColor_increasing_bridge
#print axioms su3_minimal_distinct_bridge
#print axioms sm_gauge_group_forced_bridge
#print axioms swap_incompatible_with_grading_bridge
#print axioms full_sm_derived_bridge
#print axioms nw2_uniquely_determined_bridge
#print axioms sm_gauge_group_derived_bridge
#print axioms sm_color_parity_and_chiral_bridge
#print axioms forced_singlets_bridge
#print axioms both_multiplets_not_chiral_bridge
#print axioms colored_sector_globally_minimal_bridge
#print axioms charge_determinacy_forces_Nw2_bridge
#print axioms representation_structure_forced_bridge
#print axioms adjoint_b1_contribution_zero_bridge
#print axioms abelian_direction_dim_one_bridge
#print axioms adjoint_fixes_scalar_bridge
#print axioms dirac_bare_forbidden_iff_arrowChiral_bridge
#print axioms majorana_bare_allowed_iff_neutral_bridge
#print axioms vl_at_v_neutrino_at_MP_bridge
#print axioms vl_arrowchiral_runs_bridge
#print axioms transferEigenvalue_bounds_bridge
#print axioms neg_log_eigenvalue_eq_gap_bridge
#print axioms spectral_decay_bridge
#print axioms quartic_eq_half_gap_squared_bridge
#print axioms quartic_d4_bridge
#print axioms quartic_complete_bridge
#print axioms colored_fermions_sm_weight_ratio_eq_twelve
#print axioms total_fermions_sm_weight_ratio_eq_fifteen
#print axioms su2_color_fermions_weight_ratio_eq_eleven
#print axioms su3_exceeds_su2_color_weight_ratio
#print axioms colored_sector_sm_neutral_eq_higher_modes
#print axioms total_fermions_sm_neutral_eq_higher_modes
#print axioms sm_fermion_sector_dominant_anchor_mode_norm_ge
#print axioms gauge_selection_adjoint_obstruction_hypercharge_exile_master_synthesis
end
end UnifiedTheory.Audit.KFCausalGaugeSelectionAdjointObstructionHyperchargeExileMultiPacketBridge
