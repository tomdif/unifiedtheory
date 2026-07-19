/-
# ENTROPY AXIOM MANIFEST  (trustworthiness regression check)

Companion to `ENTROPY_AUDIT.md` (auditor's per-file classification, dated 2026-06-02).

PURPOSE.  This file imports every entropy "headline" file and runs `#print axioms`
on each result the audit classifies as **GENUINELY PROVED** (audit buckets A and B).
When this file builds, Lean EMITS the exact axiom dependency set of each claimed
theorem into the build log.  This is a *living regression check*:

  * A genuinely-proved, sorry-free, custom-axiom-free result should print only
    `[propext, Classical.choice, Quot.sound]` (Mathlib's classical core).
  * If any later edit silently introduces a `sorry` or a custom `axiom` into the
    dependency tree of one of these theorems, its printed axiom set will CHANGE
    (e.g. gain `sorryAx`), and the change is visible in `lake build` output.

SCOPE / HONESTY.  Only bucket A (unconditional) and bucket B (PosDef / full-rank,
claimable with caveat) results appear below.  Deliberately ABSENT — because they are
NOT honest closed deliverables — are:

  * bucket C  (conditional `(h : SomeTarget) → …`),
  * bucket D  (named open `*_Target` holes, and `: True := trivial` placeholders),
  * bucket E  (reflexive `(h : T) : T := h` "interface" stubs),
  * every VACUOUS result gated on the PROVABLY-FALSE `LiebTrace_Concavity_Target`
    (see `LiebTargetAudit.liebTrace_concavity_target_is_false`), notably
    `StrongSubadditivity.strong_subadditivity_general`.

So: a name appearing in THIS file is an explicit claim "this is genuinely proved";
a result's ABSENCE here is an explicit refusal to claim it.  See the AUDIT-FLAG
banners in the source files for the vacuity sites.

This file changes NO proof, statement, or `def` — it only `#print axioms` existing
public theorems and imports their files.
-/

-- ## Imports of the headline files (bucket A/B sources)
import UnifiedTheory.LayerB.KleinInequalityFull
import UnifiedTheory.LayerB.KleinInequality
import UnifiedTheory.LayerB.KleinEquality
import UnifiedTheory.LayerB.VonNeumannConcavity
import UnifiedTheory.LayerB.WeakSubadditivity
import UnifiedTheory.LayerB.SubadditivityEquality
import UnifiedTheory.LayerB.ArakiLieb
import UnifiedTheory.LayerB.StrongSubadditivity
import UnifiedTheory.LayerB.LiebTargetAudit
import UnifiedTheory.LayerB.LiebRpowRoute
import UnifiedTheory.LayerB.RpowConcavityClosed
import UnifiedTheory.LayerB.BochnerConcavityLift
import UnifiedTheory.LayerB.OperatorEntropyConvexity
import UnifiedTheory.LayerB.LiebThirring
import UnifiedTheory.LayerB.GibbsVariationalFull
import UnifiedTheory.LayerB.MaxEntropyPrinciple
import UnifiedTheory.LayerB.RelativeEntropyConvexity
import UnifiedTheory.LayerB.Pinsker
import UnifiedTheory.LayerB.QuantumPinsker
import UnifiedTheory.LayerB.HolevoBound
import UnifiedTheory.LayerB.HolevoChi
import UnifiedTheory.LayerB.SpectralHolevoEnsemble
import UnifiedTheory.LayerB.CFCLogTensor
import UnifiedTheory.LayerB.UmegakiTensorAdditivityFull
import UnifiedTheory.LayerB.CoherenceNonneg
import UnifiedTheory.LayerB.CoherentInformation
import UnifiedTheory.LayerB.UmegakiIsometricInvariance
import UnifiedTheory.LayerB.GibbsInequality
import UnifiedTheory.LayerB.WehrlEntropy

namespace EntropyManifest

/-- Trivial anchor so the module always has a buildable declaration of its own. -/
theorem manifest_probe : True := trivial

end EntropyManifest

/- ============================================================================
   ## GENUINELY PROVED — UNCONDITIONAL  (audit bucket A)
   Real propositions; no `*_Target` hypothesis; not PosDef-gated.
   ============================================================================ -/

/- ### A2. Lieb-target falsification (a genuine NEGATIVE result) -/
#print axioms UnifiedTheory.LayerB.LiebTargetAudit.liebTrace_concavity_target_is_false
#print axioms UnifiedTheory.LayerB.LiebTargetAudit.any_consequence_of_liebTrace_concavity_target

/- ### A1. Scalar / diagonal Klein -/
#print axioms UnifiedTheory.LayerB.KleinInequality.klein_scalar
#print axioms UnifiedTheory.LayerB.KleinInequality.klein_scalar_form
#print axioms UnifiedTheory.LayerB.KleinInequality.klein_diagonal_scalar
#print axioms UnifiedTheory.LayerB.KleinEquality.kleinDeficit_strict

/- ### A3. Classical Shannon strong subadditivity + KL-imbalance identity -/
#print axioms UnifiedTheory.LayerB.StrongSubadditivity.shannon_strong_subadditivity
#print axioms UnifiedTheory.LayerB.StrongSubadditivity.klDivergence_jointProductComparison_eq

/- ### A4. Classical Gibbs / KL ≥ 0 -/
#print axioms UnifiedTheory.LayerB.GibbsInequality.klDivergence_nonneg_of_ac

/- ### A5. Classical & binary Pinsker (+ commuting quantum reduction) -/
#print axioms UnifiedTheory.LayerB.QuantumPinsker.binary_pinsker
#print axioms UnifiedTheory.LayerB.QuantumPinsker.binaryPinsker_holds
#print axioms UnifiedTheory.LayerB.QuantumPinsker.classical_pinsker
#print axioms UnifiedTheory.LayerB.QuantumPinsker.Quantum_Pinsker_Commuting

/- ### A6. Classical / spectral Holevo bound + DPI -/
#print axioms UnifiedTheory.LayerB.HolevoChi.holevoChiClassical_nonneg
#print axioms UnifiedTheory.LayerB.HolevoChi.classical_measurement_mutualInformation_le_source_chi
#print axioms UnifiedTheory.LayerB.SpectralHolevo.holevoChiSpectral_nonneg
#print axioms UnifiedTheory.LayerB.SpectralHolevo.spectral_measurement_mutualInformation_le_holevoChi

/- ### A7. Holevo χ closed forms -/
#print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_singleton
#print axioms UnifiedTheory.LayerB.HolevoBound.holevoChi_identical
#print axioms UnifiedTheory.LayerB.HolevoBound.holevo_master

/- ### A8. CFC log-tensor identity  log(ρ⊗τ)=logρ⊗I+I⊗logτ -/
#print axioms UnifiedTheory.LayerB.CFCLogTensor.cfcLogTensorIdentity_holds

/- ### A9. rpow operator/scalar gates + Ando trace-geometric-mean concavity -/
#print axioms UnifiedTheory.LayerB.RpowConcavityClosed.rpow_operator_concavity_target_unconditional
#print axioms UnifiedTheory.LayerB.RpowConcavityClosed.log_as_rpow_limit_target_unconditional
#print axioms UnifiedTheory.LayerB.BochnerConcavityLift.bochner_concavity_lift
#print axioms UnifiedTheory.LayerB.BochnerConcavityLift.bochnerConcavityLift_holds
#print axioms UnifiedTheory.LayerB.LiebRpowRoute.trace_geometricMean_jointly_concave
#print axioms UnifiedTheory.LayerB.LiebRpowRoute.matrix_rpow_monotone

/- ### A10. Lieb–Thirring (commuting / q = 1) -/
#print axioms UnifiedTheory.LayerB.LiebThirring.liebThirring_q_one
#print axioms UnifiedTheory.LayerB.LiebThirring.liebThirring_commuting_target_holds

/- ### A11. Wehrl bounds  0 ≤ S_W ≤ log m -/
#print axioms UnifiedTheory.LayerB.WehrlEntropy.wehrlEntropy_nonneg
#print axioms UnifiedTheory.LayerB.WehrlEntropy.wehrlEntropy_le_log
#print axioms UnifiedTheory.LayerB.WehrlEntropy.uniform_wehrl_eq_log_m

/- ### A12. Araki–Lieb abstract core + diagonal product -/
#print axioms UnifiedTheory.LayerB.ArakiLieb.EntropyData.arakiLieb_abs
#print axioms UnifiedTheory.LayerB.ArakiLieb.araki_lieb_diagonal_product

/- ### A14. Coherent-information WEAK bound  I_c ≤ S(N(ρ))  (sharp bound needs SSA, not claimed) -/
#print axioms UnifiedTheory.LayerB.CoherentInformation.coherentInformation_le_output_entropy

/- ============================================================================
   ## GENUINELY PROVED — PosDef / FULL-RANK ONLY  (audit bucket B, "★")
   Real propositions, but carry PosDef / full-rank hypotheses. Claimable WITH the
   full-rank caveat; NOT a general-states claim.
   ============================================================================ -/

/- ### B15. Klein's inequality (full non-commuting) + relative-entropy nonnegativity -/
#print axioms UnifiedTheory.LayerB.KleinInequalityFull.klein_inequality
#print axioms UnifiedTheory.LayerB.KleinInequalityFull.umegakiRelativeEntropy_nonneg
#print axioms UnifiedTheory.LayerB.KleinInequalityFull.trace_mul_cfc_log_eq_sum_mixed

/- ### B16. Strict Klein faithfulness (full non-commuting) -/
#print axioms UnifiedTheory.LayerB.KleinEquality.umegakiRelativeEntropy_eq_zero_imp
#print axioms UnifiedTheory.LayerB.KleinEquality.umegakiRelativeEntropy_eq_zero_iff
#print axioms UnifiedTheory.LayerB.KleinEquality.umegaki_eq_sum_kleinDeficit

/- ### B17. von Neumann concavity + χ ≥ 0 (PosDef average) -/
#print axioms UnifiedTheory.LayerB.VonNeumannConcavity.vonNeumann_concave
#print axioms UnifiedTheory.LayerB.VonNeumannConcavity.holevoChi_nonneg
#print axioms UnifiedTheory.LayerB.VonNeumannConcavity.vonNeumannConcavity_of_posDef
#print axioms UnifiedTheory.LayerB.VonNeumannConcavity.weighted_umegaki_eq_holevoChi

/- ### B18. Weak subadditivity + mutual-info identities + Araki–Lieb sandwich -/
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.weak_subadditivity
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.mutualInfo_eq_umegaki
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.mutualInfo_nonneg_of_density
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.mutualInfo_eq_relativeEntropy
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.entropyData_subadditivity_of_density
#print axioms UnifiedTheory.LayerB.WeakSubadditivity.arakiLieb_sandwich_unconditional

/- ### B19. Subadditivity equality case -/
#print axioms UnifiedTheory.LayerB.SubadditivityEquality.subadditivity_equality
#print axioms UnifiedTheory.LayerB.SubadditivityEquality.mutualInfo_eq_zero_iff_product
#print axioms UnifiedTheory.LayerB.SubadditivityEquality.strict_subadditivity_iff_not_product

/- ### B20. Operator-entropy convexity (from Klein) -/
#print axioms UnifiedTheory.LayerB.OperatorEntropyConvexity.operatorEntropy_convex
#print axioms UnifiedTheory.LayerB.OperatorEntropyConvexity.operatorEntropyConvexity_holds

/- ### B21. Relative-entropy convexity — FIRST ARGUMENT ONLY (full joint convexity is OPEN) -/
#print axioms UnifiedTheory.LayerB.RelativeEntropyConvexity.relativeEntropy_convex_first_arg

/- ### B22. Umegaki tensor additivity (full PosDef) -/
#print axioms UnifiedTheory.LayerB.UmegakiTensorAdditivityFull.umegakiRelativeEntropy_tensor_additive_full
#print axioms UnifiedTheory.LayerB.UmegakiTensorAdditivityFull.umegakiTensorAdditivityFull_holds

/- ### B23. Gibbs variational principle + uniqueness + gap identity -/
#print axioms UnifiedTheory.LayerB.GibbsVariationalFull.gibbs_variational_principle
#print axioms UnifiedTheory.LayerB.GibbsVariationalFull.gibbs_state_unique
#print axioms UnifiedTheory.LayerB.GibbsVariationalFull.gibbs_free_energy_eq_iff
#print axioms UnifiedTheory.LayerB.GibbsVariationalFull.gibbs_gap_identity

/- ### B24. Maximum-entropy (Jaynes) + uniqueness -/
#print axioms UnifiedTheory.LayerB.MaxEntropyPrinciple.max_entropy
#print axioms UnifiedTheory.LayerB.MaxEntropyPrinciple.gibbs_is_maxEntropy
#print axioms UnifiedTheory.LayerB.MaxEntropyPrinciple.max_entropy_unique

/- ### B25. Relative entropy of coherence: nonneg + faithfulness -/
#print axioms UnifiedTheory.LayerB.CoherenceNonneg.coherence_nonneg_of_posDef
#print axioms UnifiedTheory.LayerB.CoherenceNonneg.coherence_eq_zero_iff

/- ### B26. Umegaki unitary-conjugation (square isometric) invariance -/
#print axioms UnifiedTheory.LayerB.UmegakiIsometricInvariance.umegakiRelativeEntropy_square_isometric_invariant
