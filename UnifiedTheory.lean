-- Causal Foundation
import UnifiedTheory.LayerA.CausalFoundation
import UnifiedTheory.LayerA.VolumeFromCounting
import UnifiedTheory.LayerA.DiscreteMalament

-- Layer A: Algebraic Backbone
import UnifiedTheory.Basic
import UnifiedTheory.LayerA.RenormRigidity
import UnifiedTheory.LayerA.PrimitiveReduction
import UnifiedTheory.LayerA.NullConeTensor
import UnifiedTheory.LayerA.BFSourceDressing
import UnifiedTheory.LayerA.DerivedBFSplit
import UnifiedTheory.LayerA.LovelockEinstein
import UnifiedTheory.LayerA.BianchiIdentity
import UnifiedTheory.LayerA.MetricToRiemann
import UnifiedTheory.LayerA.SourceFromMetric
import UnifiedTheory.LayerA.SinglePrimitive
import UnifiedTheory.LayerA.DerivedUnification
import UnifiedTheory.LayerA.LinearizedFieldEqs
import UnifiedTheory.LayerA.GravitationalPlaneWaves
import UnifiedTheory.LayerA.ExactRegime
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.MetricGaugeCoupling
import UnifiedTheory.LayerA.VariationalEinstein
import UnifiedTheory.LayerA.PhysicalSelection
import UnifiedTheory.LayerA.GaussBonnet4D
import UnifiedTheory.LayerA.LovelockComplete
import UnifiedTheory.LayerA.GaugeDerived
import UnifiedTheory.LayerA.SubstrateBridge
import UnifiedTheory.LayerA.CosmologicalConstant
import UnifiedTheory.LayerA.NormalizationTheorem
import UnifiedTheory.LayerA.GaussBonnetExpansion
import UnifiedTheory.LayerA.NonabelianYangMills
import UnifiedTheory.LayerA.GaugeGroupConstraints
import UnifiedTheory.LayerA.RotationInvariance
import UnifiedTheory.LayerA.DimensionSelection
import UnifiedTheory.LayerA.GravitonTTModes
import UnifiedTheory.LayerA.PrimitivesForced
import UnifiedTheory.LayerB.LindbladDecoherence
import UnifiedTheory.ConditionalEinstein

-- Layer B: Matter + Quantum
import UnifiedTheory.LayerB.ParentU
import UnifiedTheory.LayerB.UnifiedBranch
import UnifiedTheory.LayerB.DefectSector
import UnifiedTheory.LayerB.DefectBridge
import UnifiedTheory.LayerB.MatterBranch
import UnifiedTheory.LayerB.DefectEquivalence
import UnifiedTheory.LayerB.DefectComposition
import UnifiedTheory.LayerB.LinearDefects
import UnifiedTheory.LayerB.ChargeSectors
import UnifiedTheory.LayerB.MultiParticle
import UnifiedTheory.LayerB.FarField
import UnifiedTheory.LayerB.StructuralTheorems
import UnifiedTheory.LayerB.QuantumDefects
import UnifiedTheory.LayerB.ComplexFromDressing
import UnifiedTheory.LayerB.PropagationRule
import UnifiedTheory.LayerB.ComplexUniqueness
import UnifiedTheory.LayerB.Decoherence

import UnifiedTheory.LayerB.MetricDefects
import UnifiedTheory.LayerB.CausalSetKPDerivation
import UnifiedTheory.LayerB.ComplexFromKPHonest
import UnifiedTheory.LayerB.SignedSource
import UnifiedTheory.LayerB.SourceFocusing
import UnifiedTheory.LayerB.FocusingBridge
import UnifiedTheory.LayerB.FocusingCoupling
import UnifiedTheory.LayerB.HistoryAmplitudes
import UnifiedTheory.LayerB.RiemannAction
import UnifiedTheory.LayerB.ComplexificationUniqueness
import UnifiedTheory.LayerB.Wedderburn2D
import UnifiedTheory.LayerB.EnvironmentDecoherence
import UnifiedTheory.LayerB.NonCommutative
import UnifiedTheory.LayerB.QuantumUniqueness
import UnifiedTheory.LayerB.DynamicalStability
import UnifiedTheory.LayerB.AmplitudeUniqueness
import UnifiedTheory.LayerB.DensityMatrix
import UnifiedTheory.LayerB.DensityMatrixHonest
import UnifiedTheory.LayerB.DensityMatrixHonestN
import UnifiedTheory.LayerB.LindbladDephasing
import UnifiedTheory.LayerB.DataProcessingInequality
import UnifiedTheory.LayerB.LindbladContinuous
import UnifiedTheory.LayerB.StinespringDephasing
import UnifiedTheory.LayerB.OperationalQuantum

-- Capstone
import UnifiedTheory.Capstone
import UnifiedTheory.Predictions

-- Layer C: Concrete Realizations
import UnifiedTheory.LayerC.Placeholder
import UnifiedTheory.LayerC.ConcreteModel
import UnifiedTheory.LayerC.ConcreteMultiBody
import UnifiedTheory.LayerC.CandidateOperatorUnbounded
import UnifiedTheory.LayerC.TypedPacketMetaSelection
import UnifiedTheory.LayerC.TypedPacketSpectralRigidity
import UnifiedTheory.LayerB.PropagationRule
import UnifiedTheory.LayerA.GaugeSelection
import UnifiedTheory.LayerA.DiscreteBundles
import UnifiedTheory.LayerA.ChargeConsistency
import UnifiedTheory.LayerA.HiggsPotentialForm
import UnifiedTheory.LayerA.HiggsMassDerived

-- Feynman rules from structured history sums
import UnifiedTheory.LayerB.FeynmanRules
import UnifiedTheory.LayerB.HiggsDoublet
import UnifiedTheory.LayerB.MassAndMixing
import UnifiedTheory.LayerB.YukawaFromFiber

-- Dark matter: relic abundance via Higgs portal (single-virtual-line)
import UnifiedTheory.LayerB.DarkMatterRelic

-- Bell theorem (singlet violates classical CHSH bound)
import UnifiedTheory.LayerB.BellTheorem

-- QM bridge: matrix non-separability ↔ genuine quantum entanglement
import UnifiedTheory.LayerB.QuantumEntanglement

-- Schmidt decomposition for 2-particle states (singular value decomposition)
import UnifiedTheory.LayerB.SchmidtDecomposition

-- Wootters' concurrence (2|det|) for real-amplitude two-qubit pure states
import UnifiedTheory.LayerB.Concurrence

-- Classical CHSH bound for factorizable correlations (closes Bell ⇔ entanglement loop)
import UnifiedTheory.LayerB.SeparableCHSH

-- Quantum (Tsirelson) CHSH bound |S| ≤ 2√2 for the framework's singlet correlation
import UnifiedTheory.LayerB.TsirelsonBound

-- 3-party Mermin/GHZ inequality (extends Bell to three particles)
import UnifiedTheory.LayerB.MerminGHZ

-- Quantum no-cloning theorem (Wootters–Zurek / Dieks 1982) in framework vocabulary
import UnifiedTheory.LayerB.NoCloning

-- Quantum no-broadcasting theorem (Barnum–Caves–Fuchs–Jozsa–Schumacher 1996)
import UnifiedTheory.LayerB.NoBroadcasting

-- Quantum no-deletion theorem (Pati–Braunstein 2000) — the dual of no-cloning
import UnifiedTheory.LayerB.NoDeletion

-- Quantum teleportation protocol (Bennett–Brassard–Crépeau–Jozsa–Peres–Wootters 1993)
import UnifiedTheory.LayerB.QuantumTeleportation

-- CKM one-loop magnitudes (V1 + V2) and the Wolfenstein A parameter
import UnifiedTheory.LayerB.CKMOneLoop
import UnifiedTheory.LayerB.CKMOneLoopV2
import UnifiedTheory.LayerB.WolfensteinA

-- CKM coupled-sector Schur complement (7-state shared bath, 8-state two baths)
import UnifiedTheory.LayerB.CKMSchur7
import UnifiedTheory.LayerB.VusStrengtheningAttempt
import UnifiedTheory.LayerB.CKMSchur8

-- Higgs mass audit: applies V_us-style critical analysis to m_H = log(5/3)·v
import UnifiedTheory.LayerB.HiggsMassAudit

-- Octonion / Fano plane test of V_us = 1/√20 (third strengthening attempt)
import UnifiedTheory.LayerB.OctonionVusCheck

-- Mass-weighted Fano test (does adding fermion-mass scaling rescue Fano?)
import UnifiedTheory.LayerB.MassFanoTest

-- Sixth strengthening attempt: actual CP² fiber overlap integrals
-- (the path YukawaFromFiber.lean says "would close the gap fully")
import UnifiedTheory.LayerB.FiberOverlapTest

-- Higgs+W two-bath identification test (framework's two derived gauge-boson
-- scales as bath energies; another strengthening attempt — FAILS)
import UnifiedTheory.LayerB.HiggsWTwoBathTest

-- Tenth strengthening attempt: SU(2) representation theory (Wigner-Eckart,
-- Clebsch-Gordan) and continuous-Haar (S³ ≅ SU(2)) bath alternatives — FAILS
import UnifiedTheory.LayerB.SU2RepVusTest

-- Eleventh strengthening attempt: RG flow + GUT-scale boundary conditions
-- (QLC, RG-improved QLC, PMNS-divided-by-integer, GUT-scale Yukawa ratio) — FAILS
import UnifiedTheory.LayerB.RGFlowVusTest

-- Twelfth strengthening attempt: minimum-complexity selection rule tested
-- uniformly on five framework predictions (V_us², m_H/v, sin²θ_W, b/τ, m_t/v).
-- WORKS on V_us², m_H/v, sin²θ_W (GUT). FAILS on b/τ and m_t/v. PARTIAL.
import UnifiedTheory.LayerB.MinComplexitySelection

-- B/τ re-audit under min-complexity: 7/3 is framework-derivable
-- (= Feshbach discriminant at d=4 divided by color count) at strictly lower
-- complexity than 12/5, and is strictly closer to PDG.
import UnifiedTheory.LayerB.BTauReaudit

-- PMNS structural audit under min-complexity: atomic decompositions
-- of all three PMNS angles + new cross-sector identities (CS-3, CS-4, CS-5):
--   sin²θ_23 · cos²θ_12 = a₂ = 2/5     [bridges PMNS to J₄ middle diagonal]
--   cos²θ_23 · cos²θ_12 = sin²θ_12     [PMNS-internal forced identity]
--   sin²θ_13 · N_c²      = a₃ = 1/5     [bridges PMNS to J₄ bottom diagonal]
import UnifiedTheory.LayerB.PMNSStructuralAudit

-- Full min-complexity audit of the seven REMAINING within-sector fermion-mass
-- exponents (28/5, 22/5, 10/3, 33/10, 4) after the b/τ and m_t/v corrections.
-- Verdict: 3 HOLDS, 1 FREE, 1 HOLDS-WEAK, 0 CORRECTABLE.
-- Reveals the cross-sector identity p_μ − p_e = −7/10 = −(corrected m_t/v).
import UnifiedTheory.LayerB.FermionMassFullAudit

-- Coupling-constant audit under min-complexity: α_GUT = 3/(32π),
-- g_W² = 1, sin²θ_W (GUT/M_Z), α_em(0), α_s(M_Z), λ_H. Honest verdict:
-- α_GUT is framework-natural; running couplings are RG consequences.
import UnifiedTheory.LayerB.CouplingConstantAudit

-- α_s(M_Z) min-complexity re-audit. Headline: 3-sector cross-identity
-- (m_b/m_τ)·V_us² = (7/3)·(1/20) = 7/60 = disc/(N_W²·N_c·N_total),
-- the framework-atomic correction to the 1/9 incumbent. 7/60 is 5.5×
-- closer to PDG (1.05% vs 5.76% off) and inside the ±2σ window, but
-- STILL outside strict 1%. Honest verdict: α_s(M_Z) is the FIRST
-- framework prediction with a real PDG miss that min-complexity does
-- not cleanly fix; α_s's true content is RG running of α_GUT.
import UnifiedTheory.LayerB.AlphaSAudit

-- α_s(M_Z) extended-vocabulary test: extending the framework atoms with
-- QCD-natural atoms {β₀_GUT=7=disc, β₀_MZ=23/3, C_F=4/3, C_A=3, T_R=1/2,
-- N_q=6, N_f=5, 4π, 2π} does NOT produce a min-complexity rational for
-- α_s(M_Z) inside ±1% PDG. Tests 7 candidates (1/9, 3/26, 1/8, 3/25,
-- 4/33, 1/11, 7/60). NONE land in the strict window. Per-sector-vocabulary
-- hypothesis FAILS for α_s. Exposes new structural coincidence
-- β₀_GUT = disc and re-reading 1/9 = 1/(C_F + β₀_MZ).
import UnifiedTheory.LayerB.AlphaSExtendedVocabularyTest

-- α_s(M_Z) RG running formalisation: 1-loop QCD β-function integration
-- in Lean, with the framework's α_GUT = 3/(32π) as the high-scale boundary.
-- KEY ATOMIC IDENTITIES: 21 = N_c · disc (framework log-hierarchy);
-- β₀_GUT = disc = 7 (1-loop SU(3) coefficient at N_f = 6 coincides with
-- Feshbach discriminant atom). Cross-sector identity: α_s · α_GUT =
-- disc/(N_W^7 · N_total · π) = 7/(640π). Two scenarios: A (β₀ = 7,
-- L = 21) gives 1/α_s ∈ (9.5, 10.5), MISSES PDG by ≥ 12%; B (β₀_implied,
-- L = 21) gives β₀_implied ∈ (7, 7.9), strictly inside SM band, EXACT
-- consistency with corrected target 60/7. Converts α_s(M_Z) from
-- "framework-incomplete" to "framework-derives-via-formalised-flow".
import UnifiedTheory.LayerB.AlphaSRGRunning

-- Wave 4 strengthenings (partial)
import UnifiedTheory.LayerB.CPTAntilinear
import UnifiedTheory.LayerB.BornRulePolynomialUniqueness
import UnifiedTheory.LayerB.BornRuleContinuousUniqueness
import UnifiedTheory.LayerB.AmplitudeUniquenessStrengthened

-- Genuine Matsubara quantization (replaces div_mul_cancel theorem in KMSFromDephasing)
import UnifiedTheory.LayerB.MatsubaraQuantization

-- QM scope master: honest consolidation of audit + strengthening waves
import UnifiedTheory.LayerB.QMScopeMaster

-- Bekenstein-Hawking black hole entropy S = A/4 (Schwarzschild)
import UnifiedTheory.LayerB.BekensteinHawking

-- Hawking temperature T_H = 1/(8πM) from first law + S_BH (Schwarzschild)
import UnifiedTheory.LayerB.HawkingTemperature

-- Schwarzschild metric is an exact vacuum solution of Einstein's equations
import UnifiedTheory.LayerB.SchwarzschildSolution

-- Birkhoff's theorem: Schwarzschild is the UNIQUE spherically symmetric vacuum
import UnifiedTheory.LayerB.BirkhoffUniqueness

-- Bekenstein bound S ≤ 2π·R·E (universal entropy upper limit, saturated by BHs)
import UnifiedTheory.LayerB.BekensteinBound

-- Christodoulou irreducible mass for Kerr (rotating) black holes
import UnifiedTheory.LayerB.ChristodoulouIrreducibleMass

-- Cross-sector identity search (catalogue of E1, E2, plus N1, N2, N3)
import UnifiedTheory.LayerB.CrossSectorIdentitySearch

-- J₄-Zamolodchikov decisive test.  Tests whether the J₄ chamber matrix
-- eigenvalue ratios match the Zamolodchikov E₈-Ising mass spectrum, and
-- proves E₈'s structural uniqueness via Exp(E_8) = (ℤ/30)*.
-- VERDICT: STRUCTURE GENUINE (h(E_8)=N_W·N_c·N_total atomic; Exp(E_8)
-- =(ℤ/30)* uniquely among E_6/E_7/E_8), DYNAMICS BORDERLINE (one near-
-- 1% match in 24 trials: λ_2/λ_3 ≈ m_6/m_1 at 0.91% diff, edge of
-- threshold; framework m_b/m_τ vs m_4/m_1 at 2.97%, just below 3%
-- decorative threshold).
import UnifiedTheory.LayerB.J4ZamolodchikovTest

-- SO(10) GUT embedding test: every standard SO(10) representation
-- dimension (16, 10, 45, 24, 21, 120, 126, 54, 210) factorizes through
-- framework atoms {N_W=2, N_c=3, N_total=5, disc=7} with no stray
-- prime, e.g. dim(spinor) = N_W^4 = 16, dim(adjoint) = N_c²·N_total = 45,
-- dim(126) = 2·N_c²·disc, dim(210) = N_W·N_c·N_total·disc.  SO(10)
-- generates two of the framework's predictions (sin²θ_W^GUT = 3/8,
-- b-τ Yukawa unification) but does NOT generate the PMNS angles,
-- m_t/v = 7/10, V_us² = 1/20, or N_g = 3.  Verdict: PARTIAL SHADOW —
-- the framework is a strict refinement of SO(10) with additional
-- flavor content beyond standard GUT representation theory.
import UnifiedTheory.LayerB.SO10EmbeddingTest

-- SM gauge anomaly cancellation audit under the framework's atomic
-- vocabulary {N_W=2, N_c=3, N_g=3, N_total=5, disc=7}.  All six SM
-- gauge anomalies (SU(3)³, SU(2)³, SU(3)²·U(1), SU(2)²·U(1), U(1)³,
-- gauge-grav) cancel exactly per generation; SM hypercharges decompose
-- atomically through {N_W, N_c}: Y(Q_L)=1/(N_W·N_c), Y(u_R)=N_W/N_c,
-- Y(d_R)=−1/N_c, Y(L_L)=−1/N_W, Y(e_R)=−1, Y(Φ)=1/N_W.  Common
-- denominator 6 = N_W·N_c is min-complexity.  Five new cross-sector
-- identities (AI1, AI2, AI7, AI10, AI11) link Σ Y² = (N_W·N_total)/N_c
-- to PMNS, CKM, and mass predictions: e.g. Σ Y² · sin²θ_12 = 1,
-- Σ Y² · cos²θ_12 = m_b/m_τ, Y(u_R)² · |V_us|² = sin²θ_13.
import UnifiedTheory.LayerB.AnomalyAudit

-- Pre-registered Belle II 2027 falsifiable predictions for V_us, V_cb,
-- V_ub, V_td, V_ts, Wolfenstein A, λ; cross-sector identities CS-1..5;
-- 2σ refutation envelopes (closed-form rationals/√-rationals only).
import UnifiedTheory.LayerB.CKMPreRegistration

-- Tightened publication-grade PDG brackets for the framework's six headline
-- predictions (V_ub, m_b/m_τ, m_t/v, Wolfenstein A, Higgs κ_λ, α_s). Each
-- prediction comes with its tightest closed-form value, the actual PDG 1σ /
-- 2σ / FCC window it sits in, and an HONEST inside/outside flag. m_b/m_τ
-- = 7/3 and m_t/v = 7/10 are explicitly flagged as BELOW PDG 1σ; α_s =
-- 7/60 is flagged as inside the audit window [0.116, 0.118] but below the
-- strict ±1σ low. V_ub, Wolfenstein A, κ_λ are inside their target windows.
import UnifiedTheory.LayerB.TightenedBrackets

-- Cosmological constant Λ²·N = 1 audit (PARTIALLY DERIVED:
-- relation framework-derived; N value fitted to universe age; no SM cross-identities)
import UnifiedTheory.LayerB.CosmologicalConstantAudit

-- Dark-matter relic abundance audit. Headline: Ω_DM h² = N_c/N_total² = 3/25
-- EXACTLY matches Planck 2018 (0.1200), AND forces Ω_M h² = 1/disc = 1/7
-- (0.1% off) and Ω_b h² = N_W²/(disc·N_total²) = 4/175 (2.2% off). Three-density
-- cross-sector hit using ONLY {N_W, N_c, N_W², N_total, disc}. The headline
-- identity Ω_M h² · disc = 1 connects the COSMOLOGICAL TOTAL MATTER DENSITY
-- to the FESHBACH DISCRIMINANT atom — the dark-sector analog of α_s = 7/60.
import UnifiedTheory.LayerB.DarkMatterAudit

-- Baryon-to-photon ratio η_B audit (companion to DarkMatterAudit). Verdict: WEAK.
-- Mantissa η_B·10¹⁰ = N_W·N_c = 6 inside PDG 1σ [6.0, 6.2] (1.7 % off centre 6.1),
-- min-complexity over alternatives N_total+1, disc−1. BUT: the 10⁻¹⁰ scale is NOT
-- a clean atom; ln(η_B) ≈ −N_c·disc = −21 reuses the M_X/M_Z log atom (DOUBLE-DIPPING,
-- recorded as honesty flag). η_B does NOT factor as a product of corrected atoms
-- (no α_s = (m_b/m_τ)·V_us² analog). PMNS Jarlskog² = 1936/1771875 introduces 11 (non-atomic).
-- Crude SM insufficiency: J_CKM/η_B > 50,000. Framework recovers Sakharov conditions
-- (Baryogenesis.lean) but does NOT predict 6·10⁻¹⁰ from baryogenesis dynamics.
import UnifiedTheory.LayerB.BaryonAsymmetryAudit

-- Higgs trilinear self-coupling κ_λ pre-registered prediction (locked 2026-05-11):
-- framework gives κ_λ = 1 IDENTICALLY at tree level (λ_3 = λ_H · v with λ_H = γ_4²/2
-- and m_H = γ_4·v). Atomic alternatives (4/5, 7/20, 5/6) rejected. HL-LHC (±50%) and
-- FCC (±5%) falsification windows committed BEFORE the next round of measurements.
import UnifiedTheory.LayerB.HiggsTrilinearPrediction

-- Higgs branching ratio audit under min-complexity / cross-sector lens.
-- Five ≤ 0.25 % atomic matches inside the framework atomic vocabulary
-- {N_W, N_c, N_g, N_total, disc}: BR(bb̄) = 7/12 = disc/(N_W²·N_c),
-- BR(WW*) = 3/14 = N_g/(N_W·disc), BR(gg) = 4/49 = N_W²/disc²,
-- BR(ττ) = 1/16 = 1/N_W⁴ (EXACT), BR(γγ) = 1/441 = 1/(N_c·disc)².
-- THREE EXACT atomic cross-sector identities: (CS-H3) BR(gg) · disc² = N_W²,
-- (CS-H4) BR(ττ) · N_W⁴ = 1, (CS-H5) BR(γγ) · (N_c·disc)² = 1.
-- STRUCTURAL FALSIFICATION: the six dominant atomic candidates
-- 7/12 + 3/14 + 4/49 + 1/16 + 1/35 + 1/441 = 34313/35280, plus the
-- measured ZZ + Zγ + μμ, OVER-SHOOTS unity by ≈ 5.5 × 10⁻⁴: the six
-- atomic readings are MUTUALLY INCOMPATIBLE with SM Σ BR ≤ 1.
-- Denominator 35280 = N_W⁴·N_c²·N_total·disc² (every framework atom).
-- HONEST VERDICT: NUMERICALLY-STRIKING-COINCIDENCE (comparable to Ω_b·h²
-- in DarkMatterAudit; weaker than α_s = 7/60 because no two-sector
-- cross-grounding is available). The framework's atomic vocabulary
-- does NOT supply an independent prediction layer for BR(H → X);
-- branching ratios are SM consequences of the Lagrangian + framework-derived
-- (m_q, α, α_s, m_H = log(5/3)·v).
import UnifiedTheory.LayerB.HiggsBranchingAudit

-- Muon g − 2 anomaly audit under min-complexity / cross-sector lens.
-- Verdict: INCONCLUSIVE. Framework reproduces Schwinger LO (= SM LO) exactly,
-- but no cross-sector identity reproduces Δa_μ ≈ 251 × 10⁻¹¹. Closest atomic
-- numerical match disc²·N_total = 245 lies within 1σ but has no structural
-- derivation. Lattice-vs-dispersion HVP gap (145 × 10⁻¹¹) lies within 2σ of
-- the full pull, so the empirical anomaly itself is contested between SM
-- methods, making the test PREMATURE pending HVP reconciliation.
import UnifiedTheory.LayerB.MuonG2Audit

-- Muon g − 2 HONEST PRE-REGISTERED PREDICTION. The framework's a_μ at every
-- loop order is forced to coincide with the SM evaluated using framework-derived
-- inputs (α, m_μ, m_W, m_Z, m_H, sin²θ_W, α_s, N_c). Pre-registration:
-- a_μ^framework = a_μ^SM(BMW lattice HVP) = 116 592 000 × 10⁻¹¹, lying within
-- 61 × 10⁻¹¹ of the world-average a_μ^exp = 116 592 061 × 10⁻¹¹ (well inside
-- the 100 × 10⁻¹¹ confirmation window). Framework FAVOURS BMW lattice over
-- dispersion HVP (lattice is the framework-native methodology). The 4.2σ pull
-- against dispersion-HVP SM is interpreted as a SM-side artifact (190 ≈ 1.3 ×
-- HVP gap 145). Falsification: 5σ ≈ 295 × 10⁻¹¹ pull after Fermilab final +
-- HVP reconciliation. Atomic decomposition tests of EW (154 = disc · 22) all
-- show the EW total is QFT-derived, NOT a framework-atomic rational.
import UnifiedTheory.LayerB.MuonG2Prediction

-- BMW HVP STRUCTURAL COMMITMENT (locked 2026-05-11). Promotes the BMW lattice
-- HVP value (a_μ^HVP_LO = 70750 × 10⁻¹¹ ≈ 707.5 × 10⁻¹⁰) from a per-prediction
-- choice to a CORE FRAMEWORK COMMITMENT with downstream consequences across the
-- EW sector. The framework adopts BMW because lattice methodology uses
-- framework-derived inputs (α, α_s = 7/60, m_q, N_c = 3) only, while dispersion
-- requires the external e+e- → hadrons R-ratio. Downstream consequences:
-- (C1) a_μ^framework = 116 592 000 × 10⁻¹¹ within 61 × 10⁻¹¹ of exp,
-- (C2) Δα_had(M_Z²) = 0.0270 (BMW) vs 0.02766 (dispersion), gap 0.00066,
-- (C3) 1/α(M_Z) ≈ 129.030 (BMW, on-shell) shifted +0.0905 from dispersion,
-- (C4) sin²θ_W(M_Z) shift ≈ +9 × 10⁻⁵ above dispersion-based EW fits.
-- The "fake pull" 190 × 10⁻¹¹ between framework and dispersion-SM is
-- structurally explained by the HVP gap (effective kernel weighting ≈ 13 %).
-- Falsification gates: (F1) HVP controversy resolves to dispersion → REFUTED,
-- (F3) Fermilab final + |a_μ^exp − 116 592 000| > 295 × 10⁻¹¹ → REFUTED,
-- (F4) sin²θ_W or α(M_Z) measurements pull > 5σ from BMW value → REFUTED.
-- Honesty: BMW commitment is a STRUCTURAL CHOICE (like a renormalization scheme),
-- NOT a derivation from framework K/P atoms. HVP is itself a non-perturbative QCD
-- vacuum integral; the framework does not provide a closed-form HVP integral.
import UnifiedTheory.LayerB.BMWHVPCommitment

-- Proton-decay lifetime prediction. Standard SU(5) X/Y rate formula
-- with α_GUT = 3/(32π) gives the prefactor P_α = 1/α_GUT^2 = 1024π^2/9
-- ∈ (1100, 1130). Full rate prefactor Q = 16π^2 · P_α = 16384π^4/9
-- ∈ (1.75·10^5, 1.78·10^5). Atomic decomposition: Q = (N_W^14/N_c^2)·π^4,
-- 14 = 2·N_total + N_W^2. Sharp scaling laws τ_p(2M_X) = 16·τ_p(M_X) and
-- τ_p(A2/2) = 2·τ_p(A2). Hyper-K reach 10^{35} yr ↔ M_X^crit ≈ 1.2·10^{15} GeV.
-- Honest scope: framework does NOT predict M_X (dimensional input) or |A|^2
-- (lattice QCD); the falsification window M_X-dependent. Cross-sector identity
-- P_α · α_s = 1792π^2/135 with all factors framework-atomic.
import UnifiedTheory.LayerB.ProtonDecayPrediction

-- M_X derivation attempt from framework α_GUT + α_s(M_Z) + one-loop QCD
-- running. log(M_X/M_Z) = (1/α_GUT - 1/α_s(M_Z)) · 2π/β₀.  Two scenarios:
-- (A) non-SUSY β₀ = disc = 7 ⇒ L_A ∈ (22, 23), M_X ≈ 5·10¹¹ GeV
--     (intermediate scale, NOT 10¹⁵-10¹⁶); decisively excluded by Super-K
--     proton-decay (≥ 6 e-folds below SK consistency floor; τ_p suppressed
--     by ≥ exp(24) ≈ 3·10¹⁰).
-- (B) SUSY β₀ = N_c = 3 ⇒ L_B ∈ (52, 53), M_X > exp(40)·M_Z (above Planck);
--     internally inconsistent because framework α_GUT sits in non-SUSY
--     window (33,37) not SUSY window (24,26).
-- Atomic decomposition test: L_A ≠ {20, 21, 22} (irrational); the
-- pre-specified candidate L = N_c·disc = 21 is rigorously falsified.
-- Cross-sector atomic identities: β₀_GUT = disc = 7; 60 = N_W²·N_c·N_total.
-- HONEST VERDICT: framework does NOT derive M_X from α_GUT + α_s + RG running;
-- M_X remains dimensional free input. Closing the proton-decay consistency
-- requires BSM physics, not present in the framework.
import UnifiedTheory.LayerB.MXFromRGRunning

-- M_X resolution test: which path closes the proton-decay inconsistency?
-- (A) α_GUT = sin²θ_13^PMNS = 1/(N_c²·N_total) = 1/45 (NEW cross-sector
--     identity ties gauge unification to leptonic neutrino mixing) with
--     β₀ = 7 gives L^A ∈ (32, 33), M_X ≈ 1.5·10¹⁶ GeV, above SK floor by
--     ≥ 3 e-folds.  TENSION: breaks the existing g²=1 + sin²θ_W=3/8
--     derivation α_GUT = 3/(32π).
-- (B) β₀ = N_total = 5 (atomic BSM β₀) with the existing α_GUT = 3/(32π)
--     gives L^B ∈ (31, 32), M_X ≈ 3.7·10¹⁵ GeV, above SK floor by ≥ 2
--     e-folds.  TENSION: postulates intermediate BSM colored matter not
--     currently predicted by the framework.
-- (C) 2-loop / threshold corrections alone: even a generous 12 % bonus
--     leaves L^C < 26 < 29 = SK_floor.  INSUFFICIENT.
-- HONEST VERDICT: framework is NOT yet internally consistent with proton
-- stability; closing the gap requires one of {A, B} as a structural
-- commitment.  Choice between A and B is a framework-design decision,
-- not a derivable theorem.
import UnifiedTheory.LayerB.MXResolution

-- Universal-principle search. Tests SEVEN candidate universal principles
-- (action minimization, info bound, anomaly cancellation, categorical
-- coherence, K/P alone, Bayesian Occam, unique consistent extrapolation)
-- against the six audit-chain regularities (R1)-(R6). Verdict: NO single
-- one of the six named candidates suffices; min-complexity is EMERGENT.
-- The composite K/P-Generated Atomic Closure (KPGAC) principle subsumes
-- all six regularities: (a) atomic vocabulary from K/P chamber Jacobi,
-- (b) cross-sector closure, (c) dimensional analysis, (d) internal
-- consistency. KPGAC is FALSIFIABLE (any cross-sector identity using an
-- atom > 10 refutes it). KPGAC GENERATES four new identities:
--   (E1) Λ-orthogonality (Λ_P below atomic floor 1/175);
--   (E2) Ω_b/Ω_DM = 4/21 (≈ 2.2% of Planck 2018, NEW prediction);
--   (E3) α_s = 7/60 = (m_b/m_τ)·V_us² (cross-sector form);
--   (E4) V_us²·disc + 1/(N_W³·N_total) = sin²θ_W^GUT (CKM-GUT bridge).
import UnifiedTheory.LayerB.UniversalPrincipleSearch

-- Inflation audit. Headline: under Starobinsky-class slow-roll
-- (n_s = 1 − 2/N_e, r = 12/N_e²), the framework-atomic e-fold count
-- N_e = N_W²·N_c·N_total = 60 predicts n_s = 29/30 (0.18% off Planck centre,
-- INSIDE 1σ window [0.9607, 0.9691]) and r = 1/300 ≈ 0.00333 (well below the
-- Planck/BICEP upper bound 0.06; in the LiteBIRD/CMB-S4 target regime r ~ 10⁻³).
-- Atomic decompositions: n_s = 1 − 1/(N_W·N_c·N_total), r = 1/(N_W²·N_c·N_total²).
-- Starobinsky CONSISTENCY r = N_c·(1−n_s)² satisfied EXACTLY in framework
-- rationals. Cross-sector identities: (1−n_s)·N_e = N_W, r·N_e² = N_W²·N_c,
-- r/(Ω_DM h²) = 1/(N_W·N_c)². HONEST NEGATIVES: (i) N_e = 50 = N_W·N_total² is
-- min-complexity simpler but predicts n_s = 0.96 (below Planck 1σ); (ii) A_s
-- ≈ 2.1 × 10⁻⁹ is a hierarchy below the framework atomic floor (parallel to Λ_P);
-- (iii) the Starobinsky form is not framework-forced. Bottom line: PARTIALLY
-- DERIVED — clean atomic structure on the OBSERVABLE side, model-dependent on
-- the THEORY side (Starobinsky slow-roll assumed, N_e selected by Planck-fit).
import UnifiedTheory.LayerB.InflationAudit

-- 4D causal SO(10) test. Asks whether 4D causal SO(10) is the framework's
-- DEEPER GAUGE+SPACETIME SUBSTRATE (one step beyond SO10EmbeddingTest's
-- "PARTIAL SHADOW" verdict).  Tests four claims: (C1) J₄ ↔ SO(10) FUSION
-- (dim_spinor = N_W^d_eff couples gauge spinor structure to spacetime
-- exponent; J₄ channels = d_eff − 1 = N_c; Feshbach disc at d_eff = 4
-- equals framework atom disc = 7);  (C2) disc = N_c + d_eff is the
-- gauge-spacetime fusion atom (forced uniquely by Ehrenfest selection +
-- Feshbach prime discriminant);  (C3) SO(10) 126 (B-L breaking, see-saw)
-- factors as 2·N_c²·(N_c + d_eff), 210 = N_W·N_c·N_total·(N_c + d_eff)
-- — both carry the fusion atom;  (C4) m_H ratio 5/3 = N_total/N_c IS the
-- SU(5) hypercharge normalisation (g_1²·5/3 = g_2²) and drives the same
-- sin²θ_W^GUT = 3/8.  d_eff = 4 is DOUBLY FORCED: Ehrenfest classical
-- physics (orbits + Huygens) and Feshbach algebra (prime J₄ discriminant)
-- AGREE by independent routes.  RESIDUAL FLAVOR (PMNS angles 3/10, 4/7,
-- 1/45; m_t/v = 7/10; V_us² = 1/20; N_g = N_c) remains BEYOND the
-- substrate.  HONEST VERDICT: 4D causal SO(10) is the framework's
-- COMPATIBLE MAXIMAL GAUGE+SPACETIME SHELL — necessary but not sufficient
-- as a TOE; the framework's flavor sector lives in the J₄ chamber
-- spectrum and cross-sector identities, not in SO(10) representation theory.
import UnifiedTheory.LayerB.CausalSO10Test

-- SU(5) embedding test. Asks whether the framework's atomic vocabulary
-- {N_W=2, N_c=3, N_W²=4, N_total=5, disc=7} and 17+ cross-sector
-- identities are the algebraic shadow of an SU(5) GUT, or genuinely
-- BEYOND SU(5).  Builds the SU(5) representation data (dim_5, dim_10,
-- dim_15, dim_24, rank=4), maps each framework atom to SU(5) data,
-- and scores each catalogued identity as SHADOW / PARTIAL / BEYOND.
-- HEADLINE: of 13 catalogued cross-sector identities, 1 is SHADOW
-- (AI1: pure SM hypercharge trace), 4 are PARTIAL (N2, AI2, AI7, AI10
-- — use sin²θ_W=3/8 SU(5) data plus framework atoms), and 8 are
-- BEYOND (E1, E2, N1, N3, D1, AI11, m_b/m_τ=7/3, Path-A α_GUT=1/45).
-- Cosmology / inflation / dark sector identities are 100% BEYOND
-- SU(5) by scope. The framework atom disc = 7 = N_c + d_eff is
-- SPACETIME-DIMENSIONAL, not gauge-group-theoretic, and is the key
-- obstacle to viewing the framework as an SU(5) shadow. Falsification
-- witness: m_b/m_τ = 7/3, where 7 is none of {3, 5, 8, 10, 15, 24, 4}.
-- VERDICT: BEYOND with PARTIAL OVERLAP. SU(5) explains sin²θ_W=3/8 and
-- qualitative b–τ unification at GUT scale, but NOT the discriminant
-- 7, the atomic rationals, or the 17+ cross-sector identities. Mild
-- additional alignment with SO(10) recorded as a sub-question
-- (rank_SO10 = 5 = N_total, dim_SO10_adj = 45 = Path-A 1/α_GUT).
import UnifiedTheory.LayerB.SU5EmbeddingTest

-- TOE candidate ranking. Scores seven contemporary Theory-of-Everything
-- candidates (causal-set+SO(10), string/M-theory, LQG, Connes spectral
-- triples, octonion Furey-Boyle, CDT, asymptotic safety) on ten criteria
-- (gauge group, generations, d_eff=4, atomic vocabulary, cross-sector
-- identities, SO(10) compatibility, Λ, inflation, dark matter, proton
-- decay). HEADLINE: no single candidate exceeds 15/30; the HYBRID
-- (causal-set + SO(10) + octonion triality) scores 21/30, strictly
-- beating every singleton. SO(10) provides the gauge / spinor / b-τ row
-- atomically (re-stated from SO10EmbeddingTest); octonion triality
-- supplies N_g = 3; causal-set provides 4D + Λ²·N. The residual 9/30
-- gap is exactly the framework's primordial KPGAC content — disc = 7
-- from the chamber Jacobi J₄ and the cross-sector identities N1, N2, N3
-- — which NONE of the seven candidates derives. VERDICT: hybrid is the
-- relatively best fit; no candidate dynamically generates the atomic
-- vocabulary; the framework has structural content BEYOND every
-- contemporary TOE candidate considered.
import UnifiedTheory.LayerB.TOECandidateRanking

-- Octonion unification test. Asks rigorously whether octonion algebra 𝕆
-- (Cayley-Dickson chain ℝ → ℂ → ℍ → 𝕆, dims 1, 2, 4, 8 with imaginary
-- dims 0, 1, 3, 7) UNIFIES the framework's four open structural questions:
-- (Q1) J₄ chamber matrix entries; (Q2) N_g = 3 generations; (Q3) PMNS / CKM /
-- mass values; (Q4) disc = 7 = N_c + d_eff fusion. ATOM ↔ CD MAP: N_W = 2 =
-- dim ℂ, N_c = 3 = dim im ℍ, d_eff = 4 = dim ℍ, disc = 7 = dim im 𝕆 (4 of 5
-- atoms ARE Cayley-Dickson dimensions); N_total = 5 is the OUTLIER (not in
-- chain). VERDICTS: (Q4) PARTIAL — disc = dim im 𝕆 holds but ALSO equals
-- N_c + d_eff = 2·N_c + 1 = 2^N_c − 1; no preferred origin. (Q2) PARTIAL —
-- SO(8) triality count = 3 matches N_g = N_c = 3 by COUNT, not by independent
-- forcing. (Q1) FAIL — G₂ Cartan eigenvalues live in ℚ(√3), J₄ in ℚ(√7);
-- Volterra/self-energy diag entries 1/3, 2/5, 1/5 and off-diag 1/25, 1/50
-- match NO octonion-dimension ratio. (Q3) PARTIAL — sin²θ_23 = 4/7 = dim ℍ /
-- dim im 𝕆 matches in form, but sin²θ_13 = 1/45, m_t/v = 7/10, V_us² = 1/20
-- all involve N_total = 5 (NOT a Cayley-Dickson dimension); 45, 10, 20 are
-- absent from the octonion menu. SEDENION RESCUE FAILS (k=4 gives 16/15, not
-- 5). HONEST VERDICT: octonion unification is a PARTIAL UNIFIER (consistent
-- interpretation of 4/5 atoms, no NEW algebraic content); the clean reduction
-- "(causal set) + (Cayley-Dickson up to 𝕆) + (4D spacetime)" is BLOCKED by
-- (a) N_total ∉ CD chain, (b) J₄ entries Volterra-derived not octonion, (c)
-- sin²θ_13 = 1/45 has no clean octonion form. Octonions ENRICH but do NOT
-- REPLACE the framework's K/P-chamber + Feshbach-J₄ primordial content.
import UnifiedTheory.LayerB.OctonionUnification

-- E₈-Ising / Zamolodchikov mass-spectrum test of the OEIS finding
-- {1, 7, 11, 13, 17, 19, 23, 29} = E₈ exponents = (ℤ/30)*, the
-- multiplicative group mod 30 = N_W·N_c·N_total. The OEIS-level
-- identification IS clean (φ(30) = 8 = N_W^N_c, disc = 7 ∈ exponents,
-- sum = 120 = N_W^3·N_c·N_total); the Zamolodchikov mass ratios
-- (transcendental cosines of multiples of π/30) do NOT match any
-- framework rational mass ratio at PDG precision (m_b/m_τ = 7/3
-- differs from Z_ratio_2 = φ by ≥ 0.7; m_t/v = 0.7 < 1 disjoint from
-- all Z_ratios). Verdict: framework atoms generate E₈'s integer
-- invariants but NOT the dynamical mass content of E₈-Ising QFT.
import UnifiedTheory.LayerB.E8IsingZamolodchikov

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAMEWORK CAPSTONE: single citable master theorem.
-- Bundles ALL framework main claims into `framework_master_2026`,
-- a 30+-conjunct Lean theorem suitable for citation. Re-exports the
-- master theorems of CrossSectorIdentitySearch, MinComplexitySelection,
-- UniversalPrincipleSearch, FermionMassesIndividual, CKMOneLoopV2,
-- WolfensteinA, CouplingConstantAudit, CKMCompleteAudit,
-- PMNSStructuralAudit, AnomalyAudit, DarkMatterAudit, InflationAudit,
-- AlphaSAudit, CausalSO10Test, DiscFusionOrigin, ChamberPolyDiscriminant,
-- MagicSquareUnification, E8IsingZamolodchikov, J4ZamolodchikovTest.
-- HONEST: includes BOTH positive (atomic vocabulary, six audit
-- corrections, 17+ cross-sector identities, KPGAC, 4D causal SO(10)
-- substrate) AND negative (Zamolodchikov mismatch, M_X without BSM,
-- min-complexity uniformity FALSE, √7 ∉ ℚ(ζ_30), N_total outlier).
-- 0 sorry, 0 custom axioms.
import UnifiedTheory.LayerB.FrameworkCapstone

-- Yang-Mills causal-set + Feshbach attack on the Clay Millennium Problem.
-- HONEST PARTIAL RESULT (does NOT solve Clay-YM):
-- (1) defines pure SO(10) YM on a finite causal substrate, (2) projects
-- the transfer-matrix transfer onto the 3-channel YM chamber via the same
-- Feshbach reduction as K_F at d=4, (3) PROVES the chamber Hamiltonian
-- has characteristic polynomial (5x-3)(150x²-50x+3), eigenvalues
-- {3/5, (5±√7)/30} in ℚ(√7), and additive gap (13-√7)/30 > 0 plus log
-- gap ln(5-√7) > 0 (closed-form, NOT estimates). (4) Records ℚ(√7) as
-- the UNIQUE chamber-gap field by primality of the Feshbach discriminant
-- f(d=4)=7 (only d∈{3,4,5} with f prime). (5) Explicitly states open:
-- continuum-limit (CL1), Wightman/OS axioms (CL2), Glimm-Jaffe constructive
-- measure (CL3). Master theorem causal_YM_partial_result + honest scope
-- statement honest_clay_YM_scope_statement classify each requirement as
-- PROVED / CONDITIONAL / OPEN / NOT-ADDRESSED. Zero sorry, zero custom axioms.
import UnifiedTheory.LayerB.YangMillsCausalAttack

-- CL2 Wightman-axiom classification for the causal-set + chamber-Feshbach
-- YM attack. Seven-axiom status table: W2 PROVED (positive chamber spectrum
-- with explicit lower bound (5−√7)/30), W5 PROVED (causal-set microcausality),
-- W1 + W3 PARTIAL_FREE (discrete part proved, continuum lift conditional on
-- CL1), W4 + W6 + W7 NOT_ADDRESSED (outside chamber framework's scope).
-- Master theorem wightman_axioms_classification + honest summary
-- wightman_status_summary. Zero sorry, zero custom axioms.
import UnifiedTheory.LayerB.CL2_WightmanAxioms

-- Pre-registration honesty ledger (locked 2026-05-11). Formally tags
-- each major framework prediction as one of three categories:
-- PRE_REGISTERED (5 entries: κ_λ = 1, V_ub = √21/1200, Ω_b/Ω_DM = 4/21,
-- τ_p with M_X dependence, a_μ = a_μ^SM(BMW)), POST_DICTION (the ~75
-- audit-driven atomic identities, sampled by 10 representative entries),
-- and CONSISTENCY_CHECK (algebraic consequences with no new content).
-- Three master theorems (pre_registered_master, post_diction_audit_master,
-- consistency_check_master) bundle each category; falsificationTable lists
-- each PR entry with current empirical value, framework closed form,
-- σ-threshold, time horizon, and target experiment.
-- The honest scope theorem framework_falsifiability locks the 5 / 75 / N
-- split as a Lean Prop. Critical for publication credibility.
import UnifiedTheory.LayerB.PreRegistrationLedger
