/- Haag-Ruelle Scattering Wavepacket Construction, Kugo-Ojima BRST Physical-State
Characterization and Quartet Decoupling, Chamber Confinement Function u(0) Evaluation
and Trace-Inverse Resolvent Shift 55/3, Slavnov-Taylor Ward Identities, and Arbitrary-
Coupling Two-Time Iterated Clock-Floor Resolvent and Yosida Synthesis:
1. Re-exports and connects the explicit Haag-Ruelle chamber wavepacket bijection
   ChamberState ≃ ℝ, exact reconstruction inWavePacket_chamber (chamber_state_to_real ψ) = ψ,
   explicit ScatteringConstruction inhabitant, and chamber asymptotic completeness (W7)
   (LayerB.Clay2_HaagRuelleConstruction).
2. Synthesizes the Kugo-Ojima BRST physical-state characterization KO_Physical X ↔
   (X.c = 0 ∧ X.B = 0), doublet/quartet BRST exactness, ghost-number raising by Q,
   chamber-spectral observable BRST invariance, and positive-semidefinite gauge-sector
   inner product physInner (LayerB.Clay4_KugoOjima).
3. Combines the explicit chamber longitudinal resolvent trace Δ_L^chamber(0) = 55/3,
   B-propagator D_BB^chamber(0) = 0, and Kugo-Ojima function u^chamber(0) = 0 ≠ -1
   (LayerB.Clay4_KOConfinement) with the chamber Slavnov-Taylor identities STsum n O = 0
   and observable-level BRST nilpotency δ_BRST² = 0 (LayerB.Clay4_SlavnovTaylor).
4. Bridges the chamber trace-inverse shift chamberInverseTraceShift = 55/3 > 0 and
   chamber eigenvalue shifts (5-√7)/30, (13-√7)/30, 3/5 to the infinite-dimensional
   clock-floor 5-operator resolvents, two-time iterated Hamiltonian resolvent and
   Yosida differences, 5-domain time-independent stability, and two-time strong
   iteratedYosida and Gaussian core convergence. -/
import UnifiedTheory.LayerB.Clay2_HaagRuelleConstruction
import UnifiedTheory.LayerB.Clay4_KugoOjima
import UnifiedTheory.LayerB.Clay4_KOConfinement
import UnifiedTheory.LayerB.Clay4_SlavnovTaylor
import UnifiedTheory.Audit.KFCausalClockFloorOsterwalderSchraderWightmanReconstructionBridge
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHaagRuelleKugoOjimaConfinementBridge

noncomputable section

open Real Filter Topology
open scoped BigOperators Topology InnerProduct

open UnifiedTheory.LayerA.CausalFoundation
open UnifiedTheory.LayerB.CL1_BathSector
open UnifiedTheory.LayerB.CL1_ContinuumLimit
open UnifiedTheory.LayerB.CL2_LorentzianWightmanDirect
open UnifiedTheory.LayerB.CL3_ClusterDecomposition
open UnifiedTheory.LayerB.Clay2_HaagRuelleConstruction
open UnifiedTheory.LayerB.Clay4_BRSTSchwingerConstruction
open UnifiedTheory.LayerB.Clay4_KugoOjima
open UnifiedTheory.LayerB.Clay4_KOConfinement
open UnifiedTheory.LayerB.Clay4_SlavnovTaylor

open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorPotentialClockApproximation (cutoff)
open KFCausalClockFloorIteratedResolventSecondPowerCore
  (hamiltonianSecondPowerDomain)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_mem_radial_domain)
open KFCausalClockFloorFullFiveResolventChainSynthesis
  (five_resolvent_norm_sum_le)
open KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
  (unconditionalCoreDomain growingClockCoreDomain coreApproxSeq)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_mem_ten_domains)
open KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation
  (iteratedYosida unconditional_coreApproxSeq_with_resolvent_identities)
open KFCausalClockFloorOsterwalderSchraderWightmanReconstructionBridge
  (chamberBottomShift chamberMiddleShift chamberAdditiveGapShift chamberTopShift
   chamber_spectral_shifts_pos_and_strict_order)
open KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis
  (twoTimeIteratedHamiltonianResolventDiff
   twoTimeIteratedHamiltonianYosidaDiff
   twoTimeIteratedHamiltonianResolventDiff_telescope_eq
   twoTimeIteratedHamiltonianYosidaDiff_eq_sq_smul
   twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
   twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains
   twoTimeIteratedHamiltonianResolventDiff_norm_le
   twoTimeIteratedHamiltonianYosidaDiff_norm_le
   twoTimeIteratedHamiltonianResolventDiff_radial_norm_le
   twoTimeIteratedHamiltonianResolventDiff_radialRoot_norm_le
   twoTimeIteratedHamiltonianResolventDiff_via_residual_eq
   twoTimeIteratedHamiltonianYosida_sequence_strong_limit)

/-! ### 1. Haag-Ruelle Scattering Wavepacket Construction (`Clay2_HaagRuelleConstruction`) -/

/-- Set-theoretic cardinality identity `#(Fin 3 → ℝ) = 𝔠 = #ℝ` underlying the chamber
Haag-Ruelle wavepacket bijection. -/
theorem haag_ruelle_chamber_cardinality_and_equipotence :
    Cardinal.mk (Fin 3 → ℝ) = Cardinal.continuum ∧
    Cardinal.mk (Fin 3 → ℝ) = Cardinal.mk ℝ :=
  ⟨chamber_state_cardinality, chamber_state_equipotent_real⟩

/-- Exact left-inverse reconstruction and asymptotic span of `inWavePacket_chamber`
and `outWavePacket_chamber` on `ChamberState`. -/
theorem haag_ruelle_in_out_wavepacket_invertible_and_span (ψ : ChamberState) :
    inWavePacket_chamber (chamber_state_to_real ψ) = ψ ∧
    outWavePacket_chamber (chamber_state_to_real ψ) = ψ ∧
    (∃ t : ℝ, inWavePacket_chamber t = ψ) ∧
    (∃ t : ℝ, outWavePacket_chamber t = ψ) :=
  ⟨inWavePacket_chamber_invertible ψ,
   outWavePacket_chamber_invertible ψ,
   inWavePacket_chamber_span ψ,
   outWavePacket_chamber_span ψ⟩

/-- Both `inWavePacket_chamber` and `outWavePacket_chamber` attain the chamber vacuum
`Ω_chamber` at a real asymptotic time parameter. -/
theorem haag_ruelle_in_out_vacuum_limit :
    (∃ t : ℝ, inWavePacket_chamber t = Ω_chamber) ∧
    (∃ t : ℝ, outWavePacket_chamber t = Ω_chamber) :=
  ⟨inWavePacket_chamber_vacuum_limit, outWavePacket_chamber_vacuum_limit⟩

/-- Unconditional discharge of `(W7)` on the chamber sector via the explicit
`chamberScatteringConstruction C` inhabitant. -/
theorem haag_ruelle_w7_chamber_unconditional_and_scattering_inhabitant
    (C : CausalSet) [Fintype C.Event] :
    Nonempty (ScatteringConstruction C) ∧
    ((∀ ψ : ChamberState, ∃ t : ℝ,
        (chamberScatteringConstruction C).inWavePacket t = ψ) ∧
     (∀ ψ : ChamberState, ∃ t : ℝ,
        (chamberScatteringConstruction C).outWavePacket t = ψ) ∧
     (∃ t : ℝ, (chamberScatteringConstruction C).inWavePacket t = Ω_chamber) ∧
     (∃ t : ℝ, (chamberScatteringConstruction C).outWavePacket t = Ω_chamber)) ∧
    W7_chamber_status_proved = true :=
  ⟨chamberScatteringConstruction_exists C,
   W7_chamber_unconditional C,
   W7_chamber_status_proved_eq⟩

/-- Full-spectrum lift of the chamber Haag-Ruelle scattering construction under
`ChamberIsLowestSector B`. -/
theorem haag_ruelle_w7_full_hilbert_lift_under_lowest_sector
    (C : CausalSet) [Fintype C.Event]
    (B : BathSpectrum) (hB : ChamberIsLowestSector B) :
    (∀ ψ : ChamberState, ∃ t : ℝ,
        (chamberScatteringConstruction C).inWavePacket t = ψ) ∧
    (∀ lam ∈ FullSpectrum B, μ_vac ≤ lam) ∧
    (∀ lam ∈ FullSpectrum B, lam ≠ μ_vac → μ_first ≤ lam) ∧
    (∀ lam ∈ B.eigs, μ_top ≤ lam) :=
  W7_full_under_lowest_sector C B hB

/-- Complete Haag-Ruelle `(W7)` chamber master package from `Clay2_HaagRuelleConstruction`. -/
theorem haag_ruelle_w7_chamber_master_synthesis
    (C : CausalSet) [Fintype C.Event] (B : BathSpectrum) :
    Cardinal.mk (Fin 3 → ℝ) = Cardinal.mk ℝ ∧
    (∀ ψ : ChamberState, inWavePacket_chamber (chamber_state_to_real ψ) = ψ) ∧
    (∃ t : ℝ, inWavePacket_chamber t = Ω_chamber) ∧
    (∃ t : ℝ, outWavePacket_chamber t = Ω_chamber) ∧
    (∀ ψ : ChamberState, ∃ t : ℝ, inWavePacket_chamber t = ψ) ∧
    (∀ ψ : ChamberState, ∃ t : ℝ, outWavePacket_chamber t = ψ) ∧
    (∀ ψ : ChamberState, ∃ t : ℝ,
        (chamberScatteringConstruction C).inWavePacket t = ψ) ∧
    (ChamberIsLowestSector B →
        (∀ lam ∈ FullSpectrum B, μ_vac ≤ lam) ∧
        (∀ lam ∈ FullSpectrum B, lam ≠ μ_vac → μ_first ≤ lam)) :=
  Haag_Ruelle_W7_chamber_proved C B

/-! ### 2. Kugo-Ojima BRST Physical-State Characterization & Quartet Decoupling (`Clay4_KugoOjima`) -/

/-- Kugo-Ojima physical-state characterization: the vacuum `0` is `KO_Physical`,
`KO_Physical X ↔ (X.c = 0 ∧ X.B = 0)`, and every `BRSTExact` state is `KO_Physical`. -/
theorem kugo_ojima_physical_state_vacuum_and_no_ghost_no_nl (X : BRSTConfig) :
    KO_Physical (0 : BRSTConfig) ∧
    (KO_Physical X ↔ X.c = (fun _ => 0) ∧ X.B = (fun _ => 0)) ∧
    (BRSTExact X → KO_Physical X) :=
  ⟨KO_Physical_vacuum,
   KO_Physical_iff_no_ghost_no_NL X,
   BRSTExact_is_KO_Physical X⟩

/-- Ghost-number raising by `Q` (`gh(Q_target) - gh = 1` on `gaugeField` and `antighost`)
and characterization of the ghost-number-zero physical sector `KO_PhysicalSectorGh0`. -/
theorem kugo_ojima_ghost_number_and_physical_sector_gh0 (X : BRSTConfig) :
    ghostNumber (Q_target .gaugeField) - ghostNumber .gaugeField = 1 ∧
    ghostNumber (Q_target .antighost) - ghostNumber .antighost = 1 ∧
    (KO_PhysicalSectorGh0 X ↔
      X.c = (fun _ => 0) ∧ X.cbar = (fun _ => 0) ∧ X.B = (fun _ => 0)) :=
  ⟨Q_raises_ghostNumber_gaugeField,
   Q_raises_ghostNumber_antighost,
   KO_PhysicalSectorGh0_iff X⟩

/-- Explicit BRST doublets `doublet_I_quartet` `(A, c)` and `doublet_II_quartet` `(c̄, B)`
and quartet decoupling `quartet_decouple` for `(a, 0, b, 0)`. -/
theorem kugo_ojima_doublet_and_quartet_decoupling (a b : Fin 3 → ℝ) :
    BRSTExact { A := a, c := fun _ => 0, cbar := fun _ => 0, B := fun _ => 0 } ∧
    BRSTExact { A := fun _ => 0, c := fun _ => 0, cbar := b, B := fun _ => 0 } ∧
    (KO_Physical { A := a, c := fun _ => 0, cbar := b, B := fun _ => 0 } ∧
     BRSTExact { A := a, c := fun _ => 0, cbar := b, B := fun _ => 0 }) :=
  ⟨doublet_I_quartet a,
   doublet_II_quartet b,
   quartet_decoupling_configuration a b⟩

/-- Every chamber-spectral observable `chamberSpectralObservable F` (including `3/5`,
`(13 - √7)/30`, and `√7 / 15`) is a Kugo-Ojima physical observable (`KO_PhysicalObservable`). -/
theorem kugo_ojima_chamber_spectral_observables_physical (F : ℝ) :
    KO_PhysicalObservable (chamberSpectralObservable (3 / 5)) ∧
    KO_PhysicalObservable (chamberSpectralObservable ((13 - Real.sqrt 7) / 30)) ∧
    KO_PhysicalObservable (chamberSpectralObservable (Real.sqrt 7 / 15)) ∧
    KO_PhysicalObservable (chamberSpectralObservable F) :=
  ⟨chamber_top_KO_Physical,
   chamber_additive_gap_KO_Physical,
   chamber_vacuum_gap_KO_Physical,
   chamberSpectral_is_KO_PhysicalObservable F⟩

/-- Reflexivity of `PhysicallyEquivalent`, BRST-orbit constancy of `KO_PhysicalObservable`,
and invariance of `chamberSpectralObservable F` across physically equivalent configurations. -/
theorem kugo_ojima_cohomology_invariance_and_equivalence
    (F : ℝ) (O : BRSTConfig → ℝ) (X X' Y : BRSTConfig) :
    PhysicallyEquivalent X X ∧
    (KO_PhysicalObservable O → O (X + Q Y) = O X) ∧
    (PhysicallyEquivalent X X' →
      chamberSpectralObservable F X = chamberSpectralObservable F X') :=
  ⟨PhysicallyEquivalent.refl X,
   fun hO => KO_Physical_constant_on_BRST_orbit O hO X Y,
   KO_Physical_agree_on_equivalent_chamberSpectral F X X'⟩

/-- Symmetry, positive semidefiniteness, bi-additivity, and quartet-direction vanishing
of the configuration-space physical inner product `physInner`. -/
theorem kugo_ojima_physical_inner_product_properties
    (X Y X' Y' : BRSTConfig) (c₀ cbar₀ b₀ : Fin 3 → ℝ) :
    physInner X X' = physInner X' X ∧
    0 ≤ physInner X X ∧
    physInner (X + Y) X' = physInner X X' + physInner Y X' ∧
    physInner X (X' + Y') = physInner X X' + physInner X Y' ∧
    physInner { A := fun _ => 0, c := c₀, cbar := cbar₀, B := b₀ } X' = 0 :=
  ⟨physInner_symm X X',
   physInner_self_nonneg X,
   physInner_add_left X Y X',
   physInner_add_right X X' Y',
   physInner_quartet_decouple c₀ cbar₀ b₀ X'⟩

/-- Kugo-Ojima 7-entry status ledger verification (`3 Proved + 2 ChamberAbelian + 2 OpenResearch = 7`). -/
theorem kugo_ojima_status_ledger_verification :
    ko_ledger.length = 7 ∧
    (ko_ledger.filter (fun c => c.status = KOStatus.Proved)).length = 3 ∧
    (ko_ledger.filter (fun c => c.status = KOStatus.ChamberAbelian)).length = 2 ∧
    (ko_ledger.filter (fun c => c.status = KOStatus.OpenResearch)).length = 2 ∧
    (ko_ledger.filter (fun c => c.status = KOStatus.Proved)).length +
      (ko_ledger.filter (fun c => c.status = KOStatus.ChamberAbelian)).length +
      (ko_ledger.filter (fun c => c.status = KOStatus.OpenResearch)).length = 7 :=
  KO_ledger_report

/-- Complete chamber-sector Kugo-Ojima discharge (`KO-1` cohomology and `KO-2` quartet decoupling). -/
theorem kugo_ojima_chamber_master_synthesis :
    (∀ X : BRSTConfig, KO_Physical X ↔ BRSTClosed X) ∧
    (∀ X : BRSTConfig, BRSTExact X → KO_Physical X) ∧
    (∀ a b : Fin 3 → ℝ, BRSTExact
      { A := a, c := fun _ => 0, cbar := b, B := fun _ => 0 }) ∧
    (∀ F : ℝ, KO_PhysicalObservable (chamberSpectralObservable F)) :=
  KO_chamber_discharge

/-! ### 3. Kugo-Ojima Confinement Criterion (`Clay4_KOConfinement`) & Slavnov-Taylor Identities (`Clay4_SlavnovTaylor`) -/

/-- Positivity of all three chamber eigenvalues `chamberEigenvalue (√7) i` and exact
evaluation of the chamber longitudinal resolvent trace `Delta_L_chamber (√7) 0 = 55 / 3`. -/
theorem ko_confinement_chamber_eigenvalues_and_resolvent_trace :
    (∀ i : Fin 3, 0 < chamberEigenvalue (Real.sqrt 7) i) ∧
    Delta_L_chamber (Real.sqrt 7) 0 = 55 / 3 :=
  ⟨chamberEigenvalue_pos (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   Delta_L_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos⟩

/-- Explicit evaluation of the chamber B-field propagator `D_BB_chamber (√7) 0 = 0` and
Kugo-Ojima function `u_chamber (√7) 0 = 0 ≠ -1` at zero momentum. -/
theorem ko_confinement_chamber_propagator_and_u_at_zero :
    D_BB_chamber (Real.sqrt 7) 0 = 0 ∧
    u_chamber (Real.sqrt 7) 0 = 0 ∧
    u_chamber (Real.sqrt 7) 0 ≠ -1 :=
  ⟨D_BB_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   u_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos,
   u_chamber_ne_neg_one (Real.sqrt 7) sqrt7_sq sqrt7_pos⟩

/-- Soft-mode residue formula `u_aug (√7) R k2 = -R - k2 * Delta_L_chamber (√7) k2` for `k2 ≠ 0`,
residue reduction `R = 1 ↔ -R = -1`, and 6-entry `kc_ledger` verification. -/
theorem ko_confinement_augmented_residue_formula_and_verdict (R k2 : ℝ) :
    (k2 ≠ 0 → u_aug (Real.sqrt 7) R k2 = - R - k2 * Delta_L_chamber (Real.sqrt 7) k2) ∧
    (R = 1 ↔ - R = -1) ∧
    kc_ledger.length = 6 ∧
    (kc_ledger.filter (fun c => c.status = KOConfStatus.Proved)).length = 4 :=
  ⟨u_aug_at_pos_k2 (Real.sqrt 7) R k2,
   (KO_confinement_reduces_to_residue (Real.sqrt 7) sqrt7_sq sqrt7_pos R).2,
   kc_ledger_length,
   kc_ledger_proved_count⟩

/-- Master chamber-sector Kugo-Ojima confinement status theorem at `s = √7`. -/
theorem ko_confinement_chamber_status_master :
    Delta_L_chamber (Real.sqrt 7) 0 = 55 / 3 ∧
    D_BB_chamber (Real.sqrt 7) 0 = 0 ∧
    u_chamber (Real.sqrt 7) 0 = 0 ∧
    u_chamber (Real.sqrt 7) 0 ≠ -1 ∧
    (∀ i : Fin 3, 0 < chamberEigenvalue (Real.sqrt 7) i) ∧
    (∀ R k2 : ℝ, k2 ≠ 0 →
      u_aug (Real.sqrt 7) R k2 = - R - k2 * Delta_L_chamber (Real.sqrt 7) k2) ∧
    (∀ R : ℝ, R = 1 ↔ - R = -1) ∧
    (∃ verdict : ChamberKOVerdict (Real.sqrt 7),
      verdict.resolvent_finite =
        Delta_L_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos ∧
      verdict.required_residue = 1) :=
  KO_confinement_chamber_status (Real.sqrt 7) sqrt7_sq sqrt7_pos

/-- Observable-level BRST variation identities: `deltaBRST zeroObs = zeroObs`,
`deltaBRST (chamberSpectralObservable F) = zeroObs`, nilpotency `deltaBRST (deltaBRST O) = zeroObs`,
and configuration-level nilpotency `Q (Q X) = 0`. -/
theorem slavnov_taylor_brst_variation_and_squared_zero
    (F : ℝ) (O : BRSTConfig → ℝ) (X : BRSTConfig) :
    deltaBRST zeroObs = zeroObs ∧
    deltaBRST (chamberSpectralObservable F) = zeroObs ∧
    deltaBRST (deltaBRST O) = zeroObs ∧
    Q (Q X) = 0 :=
  ⟨deltaBRST_zero,
   deltaBRST_chamberSpectral F,
   deltaBRST_squared_general O,
   M_Q_squared_zero X⟩

/-- Agreement of `correlator_vac` with `continuum_Schwinger_n` on chamber-spectral
observables, individual vanishing of every Slavnov-Taylor term `STterm n O i = 0`,
and vanishing of the full Slavnov-Taylor sum `STsum n O = 0`. -/
theorem slavnov_taylor_chamber_correlator_and_term_vanishing
    (n : ℕ) (β : ℝ) (F : Fin n → ℝ) (i : Fin n) :
    correlator_vac n (fun j => chamberSpectralObservable (F j)) =
      continuum_Schwinger_n n β F ∧
    STterm n (fun j => chamberSpectralObservable (F j)) i = 0 ∧
    STsum n (fun j => chamberSpectralObservable (F j)) = 0 :=
  ⟨correlator_vac_chamberSpectral n β F,
   STterm_chamberSpectral_zero n F i,
   ST_chamber_sector n F⟩

/-- Chamber Slavnov-Taylor identities at the spectral constants `3/5`, `(13 - √7)/30`,
and `√7 / 15`, together with BRST-shift invariance `M_INV_chamber_sector` of `correlator_vac`. -/
theorem slavnov_taylor_chamber_spectral_identities_and_measure_invariance
    (n : ℕ) (F : Fin n → ℝ) :
    STsum n (fun _ : Fin n => chamberSpectralObservable (3 / 5 : ℝ)) = 0 ∧
    STsum n (fun _ : Fin n =>
      chamberSpectralObservable ((13 - Real.sqrt 7) / 30)) = 0 ∧
    STsum n (fun _ : Fin n =>
      chamberSpectralObservable (Real.sqrt 7 / 15)) = 0 ∧
    correlator_vac n
      (fun j => fun X =>
        chamberSpectralObservable (F j) X +
        deltaBRST (chamberSpectralObservable (F j)) X) =
      correlator_vac n (fun j => chamberSpectralObservable (F j)) :=
  ⟨ST_chamber_top n,
   ST_chamber_additive_gap n,
   ST_chamber_vacuum_gap n,
   M_INV_chamber_sector n F⟩

/-- Chamber Slavnov-Taylor residue discharge and 8-entry `st_ledger` verification
(`5 Proved + 2 ChamberOnly + 1 OpenContinuum = 8`). -/
theorem slavnov_taylor_chamber_master_and_ledger :
    (∀ (n : ℕ) (F : Fin n → ℝ),
      STsum n (fun j => chamberSpectralObservable (F j)) = 0) ∧
    (∀ X : BRSTConfig, Q (Q X) = 0) ∧
    (∀ O : BRSTConfig → ℝ, deltaBRST (deltaBRST O) = zeroObs) ∧
    st_ledger.length = 8 ∧
    (st_ledger.filter (fun c => c.status = STStatus.Proved)).length = 5 ∧
    (st_ledger.filter (fun c => c.status = STStatus.ChamberOnly)).length = 2 ∧
    (st_ledger.filter (fun c => c.status = STStatus.OpenContinuum)).length = 1 :=
  ⟨ST_chamber_sector,
   M_Q_squared_zero,
   deltaBRST_squared_general,
   st_ledger_length,
   st_ledger_proved_count,
   st_ledger_chamber_count,
   st_ledger_open_count⟩

/-! ### 4. Clock-Floor Operator-Core & Two-Time Iterated Resolvent Bridge at `chamberInverseTraceShift = 55 / 3` and Chamber Spectral Shifts -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- The positive chamber inverse-trace spectral shift `55 / 3 = Tr(H_chamber⁻¹) = Δ_L^chamber(0) > 0`. -/
def chamberInverseTraceShift : ℝ := 55 / 3

/-- Positivity of `chamberInverseTraceShift = 55 / 3` and identity with `Delta_L_chamber (√7) 0`. -/
theorem chamberInverseTraceShift_pos_and_eq_Delta_L_zero :
    0 < chamberInverseTraceShift ∧
    chamberInverseTraceShift = 55 / 3 ∧
    Delta_L_chamber (Real.sqrt 7) 0 = chamberInverseTraceShift := by
  refine ⟨by unfold chamberInverseTraceShift; norm_num, rfl, ?_⟩
  exact Delta_L_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos

/-- Collective 5-operator clock-floor resolvent norm sum bound evaluated at
`chamberInverseTraceShift = 55 / 3 > 0`. -/
theorem clock_floor_five_resolvents_at_chamberInverseTraceShift_norm_sum_le
    (t : ℝ) (f : Hilbert) :
    ‖RT chamberInverseTraceShift f‖ + ‖RP chamberInverseTraceShift f‖ +
      ‖RG chamberInverseTraceShift f‖ + ‖RS t chamberInverseTraceShift f‖ +
      ‖RH t chamberInverseTraceShift f‖ ≤
      5 * chamberInverseTraceShift⁻¹ * ‖f‖ :=
  five_resolvent_norm_sum_le ε hε h hh hb m g k t
    chamberInverseTraceShift chamberInverseTraceShift_pos_and_eq_Delta_L_zero.1 f

/-- Unconditional 10-domain membership and `hamiltonianSecondPowerDomain` regularity of
`squaredHamiltonianResolvent t chamberInverseTraceShift f` at `chamberInverseTraceShift = 55 / 3 > 0`. -/
theorem clock_floor_iterated_resolvent_at_chamberInverseTraceShift_mem_ten_domains
    (t : ℝ) (f : Hilbert) :
    let x := squaredHamiltonianResolvent ε hε h hh hb m g k t chamberInverseTraceShift f
    x ∈ hamiltonianSecondPowerDomain ε hε h hh hb m g k t ∧
    x ∈ (H t).domain ∧
    x ∈ (K).domain ∧
    x ∈ (S t).domain ∧
    x ∈ (Eavg t).domain ∧
    x ∈ (Tstat).domain ∧
    x ∈ (Kroot).domain ∧
    x ∈ (Tpot).domain ∧
    x ∈ (Tgrow).domain ∧
    x ∈ (Tres t).domain ∧
    x ∈ (clockHalf ε).domain := by
  have hpos := chamberInverseTraceShift_pos_and_eq_Delta_L_zero.1
  exact iteratedHamiltonianResolvent_mem_ten_domains
    ε hε h hh hb m g k t t chamberInverseTraceShift chamberInverseTraceShift hpos hpos f

/-- Telescoping decomposition and unconditional 5-domain time-independent stability for
`twoTimeIteratedHamiltonianResolventDiff s t chamberBottomShift chamberTopShift f` across
all real couplings `m, g, k, s, t ∈ ℝ`. -/
theorem clock_floor_two_time_iterated_diff_at_chamberBottom_Top_telescope_and_domains
    (s t : ℝ) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianResolventDiff
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift f
    d = (RH t chamberBottomShift (RH t chamberTopShift f) -
          RH s chamberBottomShift (RH t chamberTopShift f)) +
        RH s chamberBottomShift (RH t chamberTopShift f - RH s chamberTopShift f) ∧
    (d ∈ (K).domain ∧
     d ∈ (Tstat).domain ∧
     d ∈ (Kroot).domain ∧
     d ∈ (Tpot).domain ∧
     d ∈ (clockHalf ε).domain) := by
  intro d
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have htop : 0 < chamberTopShift := ((hord.1.trans hord.2.1).trans hord.2.2.1).trans hord.2.2.2
  exact ⟨twoTimeIteratedHamiltonianResolventDiff_telescope_eq
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift f,
    twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift hord.1 htop f⟩

/-- Hilbert norm bound and radial (`K`) / radial-root (`Kroot`) triangle bounds for
`twoTimeIteratedHamiltonianResolventDiff s t chamberBottomShift chamberTopShift f`. -/
theorem clock_floor_two_time_iterated_diff_at_chamberBottom_Top_norm_and_radial_bounds
    (s t : ℝ) (f : Hilbert) :
    let hord := chamber_spectral_shifts_pos_and_strict_order
    let htop : 0 < chamberTopShift := ((hord.1.trans hord.2.1).trans hord.2.2.1).trans hord.2.2.2
    let d := twoTimeIteratedHamiltonianResolventDiff
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift f
    let hd := (twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift hord.1 htop f)
    let ht := (iteratedHamiltonianResolvent_mem_ten_domains
      ε hε h hh hb m g k t 0 chamberBottomShift chamberTopShift hord.1 htop f)
    let hs := (iteratedHamiltonianResolvent_mem_ten_domains
      ε hε h hh hb m g k s 0 chamberBottomShift chamberTopShift hord.1 htop f)
    ‖d‖ ≤ 2 * (chamberBottomShift⁻¹ * (chamberTopShift⁻¹ * ‖f‖)) ∧
    ‖K ⟨d, hd.1⟩‖ ≤
      ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f,
        ht.2.2.1⟩‖ +
      ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s chamberBottomShift chamberTopShift f,
        hs.2.2.1⟩‖ ∧
    ‖Kroot ⟨d, hd.2.2.1⟩‖ ≤
      ‖Kroot ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t chamberBottomShift chamberTopShift f,
        ht.2.2.2.2.2.2.1⟩‖ +
      ‖Kroot ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s chamberBottomShift chamberTopShift f,
        hs.2.2.2.2.2.2.1⟩‖ := by
  intro hord htop d hd ht hs
  exact ⟨twoTimeIteratedHamiltonianResolventDiff_norm_le
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift hord.1 htop f,
    twoTimeIteratedHamiltonianResolventDiff_radial_norm_le
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift hord.1 htop f,
    twoTimeIteratedHamiltonianResolventDiff_radialRoot_norm_le
      ε hε h hh hb m g k s t chamberBottomShift chamberTopShift hord.1 htop f⟩

/-- Unconditional 5-domain time-independent stability, squared-shift scaling identity, and
`2 * ‖f‖` norm bound for `twoTimeIteratedHamiltonianYosidaDiff s t chamberAdditiveGapShift f`. -/
theorem clock_floor_two_time_iterated_yosida_diff_at_chamberAdditiveGapShift_properties
    (s t : ℝ) (f : Hilbert) :
    let dy := twoTimeIteratedHamiltonianYosidaDiff
      ε hε h hh hb m g k s t chamberAdditiveGapShift f
    dy = ((chamberAdditiveGapShift ^ 2 : ℝ) : ℂ) •
      twoTimeIteratedHamiltonianResolventDiff
        ε hε h hh hb m g k s t chamberAdditiveGapShift chamberAdditiveGapShift f ∧
    (dy ∈ (K).domain ∧
     dy ∈ (Tstat).domain ∧
     dy ∈ (Kroot).domain ∧
     dy ∈ (Tpot).domain ∧
     dy ∈ (clockHalf ε).domain) ∧
    ‖dy‖ ≤ 2 * ‖f‖ := by
  intro dy
  have hord := chamber_spectral_shifts_pos_and_strict_order
  have hgap : 0 < chamberAdditiveGapShift := (hord.1.trans hord.2.1).trans hord.2.2.1
  exact ⟨twoTimeIteratedHamiltonianYosidaDiff_eq_sq_smul
      ε hε h hh hb m g k s t chamberAdditiveGapShift f,
    twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t chamberAdditiveGapShift hgap f,
    twoTimeIteratedHamiltonianYosidaDiff_norm_le
      ε hε h hh hb m g k s t chamberAdditiveGapShift hgap f⟩

/-- Exact two-time residual second-resolvent identity for
`twoTimeIteratedHamiltonianResolventDiff s t chamberInverseTraceShift chamberInverseTraceShift f`
evaluated at `chamberInverseTraceShift = 55 / 3 > 0`. -/
theorem clock_floor_two_time_iterated_diff_at_chamberInverseTraceShift_residual_eq
    (s t : ℝ) (f : Hilbert) :
    let hpos := chamberInverseTraceShift_pos_and_eq_Delta_L_zero.1
    twoTimeIteratedHamiltonianResolventDiff
      ε hε h hh hb m g k s t chamberInverseTraceShift chamberInverseTraceShift f =
      (RS t chamberInverseTraceShift (RH t chamberInverseTraceShift f) -
        RS s chamberInverseTraceShift (RH s chamberInverseTraceShift f)) -
        (Real.exp (2 * t) : ℂ) •
          RS t chamberInverseTraceShift
            (K ⟨iteratedHamiltonianResolvent
              ε hε h hh hb m g k t chamberInverseTraceShift chamberInverseTraceShift f,
              resolvent_mem_radial_domain
                ε hε h hh hb m g k t chamberInverseTraceShift hpos
                (RH t chamberInverseTraceShift f)⟩) +
        (Real.exp (2 * s) : ℂ) •
          RS s chamberInverseTraceShift
            (K ⟨iteratedHamiltonianResolvent
              ε hε h hh hb m g k s chamberInverseTraceShift chamberInverseTraceShift f,
              resolvent_mem_radial_domain
                ε hε h hh hb m g k s chamberInverseTraceShift hpos
                (RH s chamberInverseTraceShift f)⟩) :=
  twoTimeIteratedHamiltonianResolventDiff_via_residual_eq
    ε hε h hh hb m g k s t chamberInverseTraceShift chamberInverseTraceShift
    chamberInverseTraceShift_pos_and_eq_Delta_L_zero.1 f

/-- Joint bridge combining Haag-Ruelle wavepacket surjectivity (`inWavePacket_chamber_span`),
Kugo-Ojima physical-state characterization (`KO_Physical_iff_no_ghost_no_NL`), and
two-time strong `iteratedYosida` sequence convergence on `(H t).domain × (H s).domain`. -/
theorem haag_ruelle_kugo_ojima_and_two_time_iterated_yosida_convergence_bridge
    (s t : ℝ) (ψ : ChamberState) (X : BRSTConfig)
    (ut : (H t).domain) (us : (H s).domain) :
    (∃ τ : ℝ, inWavePacket_chamber τ = ψ) ∧
    (KO_Physical X ↔ X.c = (fun _ => 0) ∧ X.B = (fun _ => 0)) ∧
    Tendsto
      (fun n : ℕ =>
        (iteratedYosida (RH t (cutoff n)) (cutoff n) (ut : Hilbert),
         iteratedYosida (RH s (cutoff n)) (cutoff n) (us : Hilbert)))
      atTop
      (nhds ((ut : Hilbert), (us : Hilbert))) :=
  ⟨inWavePacket_chamber_span ψ,
   KO_Physical_iff_no_ghost_no_NL X,
   twoTimeIteratedHamiltonianYosida_sequence_strong_limit ε hε h hh hb m g k s t ut us⟩

/-- Joint bridge combining the chamber Kugo-Ojima confinement evaluation
`Delta_L_chamber (√7) 0 = 55 / 3 = chamberInverseTraceShift` and `u_chamber (√7) 0 = 0`,
chamber Slavnov-Taylor identities `ST_chamber_sector`, and Gaussian clock-core sequence
approximation `coreApproxSeq ε x` at `chamberInverseTraceShift = 55 / 3`. -/
theorem ko_confinement_slavnov_taylor_and_clock_floor_core_approx_bridge
    (n : ℕ) (F : Fin n → ℝ) (t : ℝ) (x : Hilbert)
    (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    Delta_L_chamber (Real.sqrt 7) 0 = chamberInverseTraceShift ∧
    u_chamber (Real.sqrt 7) 0 = 0 ∧
    u_chamber (Real.sqrt 7) 0 ≠ -1 ∧
    STsum n (fun j => chamberSpectralObservable (F j)) = 0 ∧
    (∀ j : ℕ, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
    (∀ j : ℕ, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k) ∧
    Tendsto (fun j : ℕ => coreApproxSeq ε x j) atTop (nhds x) := by
  have hseq := unconditional_coreApproxSeq_with_resolvent_identities
    ε hε h hh hb m g k t chamberInverseTraceShift
    chamberInverseTraceShift_pos_and_eq_Delta_L_zero.1 x hx
  exact ⟨chamberInverseTraceShift_pos_and_eq_Delta_L_zero.2.2,
    u_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos,
    u_chamber_ne_neg_one (Real.sqrt 7) sqrt7_sq sqrt7_pos,
    ST_chamber_sector n F,
    hseq.1,
    hseq.2.1,
    hseq.2.2.2⟩

/-- Grand synthesis theorem uniting Haag-Ruelle `(W7)` chamber scattering completeness,
Kugo-Ojima BRST cohomology and quartet decoupling, Kugo-Ojima confinement evaluation
`Δ_L^chamber(0) = 55/3` and `u^chamber(0) = 0 ≠ -1`, Slavnov-Taylor Ward identities and
observable BRST nilpotency, Osterwalder-Schrader/Wightman/cluster continuum properties,
and arbitrary-coupling two-time clock-floor iterated resolvent and Yosida synthesis. -/
theorem haag_ruelle_kugo_ojima_slavnov_taylor_clock_floor_master_bridge
    (C : CausalSet) [Fintype C.Event]
    (n : ℕ) (F : Fin n → ℝ)
    (s t : ℝ) (f : Hilbert) (ut : (H t).domain) (us : (H s).domain) :
    ((∀ ψ : ChamberState, ∃ τ : ℝ,
        (chamberScatteringConstruction C).inWavePacket τ = ψ) ∧
     (∀ ψ : ChamberState, ∃ τ : ℝ,
        (chamberScatteringConstruction C).outWavePacket τ = ψ)) ∧
    (KO_Physical (0 : BRSTConfig) ∧
     (∀ a b : Fin 3 → ℝ, BRSTExact
       { A := a, c := fun _ => 0, cbar := b, B := fun _ => 0 }) ∧
     (∀ X : BRSTConfig, 0 ≤ physInner X X)) ∧
    (Delta_L_chamber (Real.sqrt 7) 0 = 55 / 3 ∧
     u_chamber (Real.sqrt 7) 0 = 0 ∧
     u_chamber (Real.sqrt 7) 0 ≠ -1) ∧
    (STsum n (fun j => chamberSpectralObservable (F j)) = 0 ∧
     (∀ O : BRSTConfig → ℝ, deltaBRST (deltaBRST O) = zeroObs)) ∧
    (Tendsto chamber_gap_at atTop (𝓝 ((13 - Real.sqrt 7) / 30)) ∧
     0 < γ_cluster (Real.sqrt 7)) ∧
    (twoTimeIteratedHamiltonianResolventDiff
        ε hε h hh hb m g k s t chamberBottomShift chamberTopShift f ∈ (K).domain ∧
     ‖RT chamberInverseTraceShift f‖ + ‖RP chamberInverseTraceShift f‖ +
       ‖RG chamberInverseTraceShift f‖ + ‖RS t chamberInverseTraceShift f‖ +
       ‖RH t chamberInverseTraceShift f‖ ≤
       5 * chamberInverseTraceShift⁻¹ * ‖f‖ ∧
     Tendsto
       (fun j : ℕ =>
         (iteratedYosida (RH t (cutoff j)) (cutoff j) (ut : Hilbert),
          iteratedYosida (RH s (cutoff j)) (cutoff j) (us : Hilbert)))
       atTop
       (nhds ((ut : Hilbert), (us : Hilbert)))) :=
  ⟨⟨(W7_chamber_unconditional C).1, (W7_chamber_unconditional C).2.1⟩,
   ⟨KO_Physical_vacuum, quartet_decouple, physInner_self_nonneg⟩,
   ⟨Delta_L_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos,
    u_chamber_at_zero (Real.sqrt 7) sqrt7_sq sqrt7_pos,
    u_chamber_ne_neg_one (Real.sqrt 7) sqrt7_sq sqrt7_pos⟩,
   ⟨ST_chamber_sector n F, deltaBRST_squared_general⟩,
   ⟨chamber_gap_continuum_limit,
    γ_cluster_pos (Real.sqrt 7) sqrt7_sq sqrt7_pos⟩,
   ⟨(clock_floor_two_time_iterated_diff_at_chamberBottom_Top_telescope_and_domains
       ε hε h hh hb m g k s t f).2.1,
    clock_floor_five_resolvents_at_chamberInverseTraceShift_norm_sum_le ε hε h hh hb m g k t f,
    twoTimeIteratedHamiltonianYosida_sequence_strong_limit ε hε h hh hb m g k s t ut us⟩⟩

#print axioms haag_ruelle_chamber_cardinality_and_equipotence
#print axioms haag_ruelle_in_out_wavepacket_invertible_and_span
#print axioms haag_ruelle_in_out_vacuum_limit
#print axioms haag_ruelle_w7_chamber_unconditional_and_scattering_inhabitant
#print axioms haag_ruelle_w7_full_hilbert_lift_under_lowest_sector
#print axioms haag_ruelle_w7_chamber_master_synthesis
#print axioms kugo_ojima_physical_state_vacuum_and_no_ghost_no_nl
#print axioms kugo_ojima_ghost_number_and_physical_sector_gh0
#print axioms kugo_ojima_doublet_and_quartet_decoupling
#print axioms kugo_ojima_chamber_spectral_observables_physical
#print axioms kugo_ojima_cohomology_invariance_and_equivalence
#print axioms kugo_ojima_physical_inner_product_properties
#print axioms kugo_ojima_status_ledger_verification
#print axioms kugo_ojima_chamber_master_synthesis
#print axioms ko_confinement_chamber_eigenvalues_and_resolvent_trace
#print axioms ko_confinement_chamber_propagator_and_u_at_zero
#print axioms ko_confinement_augmented_residue_formula_and_verdict
#print axioms ko_confinement_chamber_status_master
#print axioms slavnov_taylor_brst_variation_and_squared_zero
#print axioms slavnov_taylor_chamber_correlator_and_term_vanishing
#print axioms slavnov_taylor_chamber_spectral_identities_and_measure_invariance
#print axioms slavnov_taylor_chamber_master_and_ledger
#print axioms chamberInverseTraceShift_pos_and_eq_Delta_L_zero
#print axioms clock_floor_five_resolvents_at_chamberInverseTraceShift_norm_sum_le
#print axioms clock_floor_iterated_resolvent_at_chamberInverseTraceShift_mem_ten_domains
#print axioms clock_floor_two_time_iterated_diff_at_chamberBottom_Top_telescope_and_domains
#print axioms clock_floor_two_time_iterated_diff_at_chamberBottom_Top_norm_and_radial_bounds
#print axioms clock_floor_two_time_iterated_yosida_diff_at_chamberAdditiveGapShift_properties
#print axioms clock_floor_two_time_iterated_diff_at_chamberInverseTraceShift_residual_eq
#print axioms haag_ruelle_kugo_ojima_and_two_time_iterated_yosida_convergence_bridge
#print axioms ko_confinement_slavnov_taylor_and_clock_floor_core_approx_bridge
#print axioms haag_ruelle_kugo_ojima_slavnov_taylor_clock_floor_master_bridge

end

end UnifiedTheory.Audit.KFCausalClockFloorHaagRuelleKugoOjimaConfinementBridge
