# ENTROPY / RELATIVE-ENTROPY FORMALIZATION AUDIT

**Auditor role:** skeptical referee. **Scope:** the quantum-entropy stack in
`UnifiedTheory/LayerB/`. **Date:** 2026-06-02.

## Buckets
- **A** PROVED-UNCONDITIONAL — real proposition, no `*_Target` hypothesis, not PosDef-gated.
- **B** PROVED-POSDEF — same, but carries `PosDef`/full-rank hypotheses (claimable with caveat).
- **C** CONDITIONAL — `(h : Some_Target) → conclusion`; not claimable unconditionally.
- **D** NAMED-TARGET (open hole) — a `def X_Target : Prop` that states the hard content and is
  undischarged, OR a `theorem foo : X_Target` where `X_Target := True`/trivial (vacuous).
- **E** REDUCTION/INTERFACE — `CoreTarget → OtherTarget`, or the reflexive `(h:T):T:=h`
  "canonical interface" pattern. Useful plumbing, not a closed result.

## Verification method (HONEST DISCLOSURE)
Classification is by **source inspection** + grep. Empirical `#print axioms` re-verification was
**NOT possible in this environment**: Mathlib is not prebuilt (`.lake/.../Mathlib/...olean` absent),
so any `lake build` would recompile all of Mathlib (hours). I confirmed:
(1) **no real `sorry`** token anywhere in scope (only doc-comment mentions); (2) **no custom `axiom`**
in scope; (3) the files carry the author's `#print axioms` directives (several live/uncommented in
ArakiLieb, WeakSubadditivity, SubadditivityEquality, GibbsVariationalFull, CoherenceNonneg) reporting
`[propext, Classical.choice, Quot.sound]`. Verdicts assume those directives compile as the author
records; the math-content classification (which bucket) does not depend on the axiom set.

---

# PER-FILE CLASSIFICATION (headline declarations)

### KleinInequalityFull.lean — CANONICAL Klein
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `klein_inequality` | **B** | `A B : Matrix (Fin n) … ℂ`, both `PosDef` | Full **non-commuting** Klein `Re Tr(A−B) ≤ Re Tr(A(log A−log B))`. Two-basis Jensen reduction. Genuine. |
| `umegakiRelativeEntropy_nonneg` | **B** | ρ, σ density matrices, both `.M.PosDef` | `0 ≤ S(ρ‖σ)`. THE Lindblad–Uhlmann deliverable. |
| `trace_mul_cfc_log_eq_sum_mixed` | B | PosDef A,B | mixed-basis trace formula (engine). |

### KleinInequality.lean — scalar + diagonal Klein (subsumed by Full)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `klein_scalar`, `klein_scalar_form` | **A** | `x,y>0` | scalar per-eigenvalue Klein. |
| `klein_diagonal_scalar` | **A** | λ,μ>0 | diagonal-summed Klein. |
| `re_trace_mul_cfc_log_eq_sum` | B | PosDef A | `Re Tr(A log A)=∑λlogλ`. |
| `umegakiRelativeEntropy_nonneg_of_klein` | **E** | takes Klein-shaped hyp | reduction shape only. |

### KleinEquality.lean — strict faithfulness (CANONICAL, full non-commuting)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `umegakiRelativeEntropy_eq_zero_imp` | **B** | ρ,σ PosDef density | `S(ρ‖σ)=0 ⟹ ρ.M=σ.M`. **Full non-commuting** (no shared eigenbasis). |
| `umegakiRelativeEntropy_eq_zero_iff` | **B** | ρ,σ PosDef density | `S(ρ‖σ)=0 ⟺ ρ=σ`. The headline faithfulness `↔`. |
| `umegaki_eq_sum_kleinDeficit` | B | PosDef | exact deficit decomposition (no Jensen). |
| `kleinDeficit_strict`, `_eq_zero_iff` | **A** | a,b>0 | strict scalar deficit. |

### VonNeumannConcavity.lean — concavity + χ≥0 (full-rank locus)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `vonNeumann_concave` | **B** | ∀i (ρi).M.PosDef AND `ρbar.M.PosDef` | `∑pᵢS(ρᵢ) ≤ S(ρ̄)`. Genuine, full-rank only. |
| `holevoChi_nonneg` | **B** | same + PosDef average `hbarpos` | `0 ≤ χ` as a REAL theorem — but requires PosDef average; **NOT fully unconditional**. |
| `vonNeumannConcavity_of_posDef` | B | PosDef component + PosDef ρ̄ | discharges the `VonNeumannConcavity n` gate on full-rank locus. |
| `weighted_umegaki_eq_holevoChi` | B | PosDef | χ-identity. |

### WeakSubadditivity.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `weak_subadditivity` | **B** | ρ_AB PosDef, both marginals PosDef | `S(ρ_AB) ≤ S(ρ_A)+S(ρ_B)`. REAL theorem (mutual-info = relative entropy + Klein). |
| `mutualInfo_eq_umegaki` | B | marginals PosDef | `S(ρ_AB‖ρ_A⊗ρ_B)=S_A+S_B−S_AB`. |
| `mutualInfo_nonneg_of_density`, `mutualInfo_eq_relativeEntropy` | B | PosDef marginals | I(A:B)≥0; identification. |
| `entropyData_subadditivity_of_density` | B | PosDef | discharges ArakiLieb `Subadditivity_Target`. |
| `arakiLieb_sandwich_unconditional` | B | PosDef | full sandwich `|S_A−S_B|≤S_AB≤S_A+S_B`. |

### SubadditivityEquality.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `subadditivity_equality` | **B** | ρ PosDef, marginals PosDef | `S(ρ_AB)=S_A+S_B ⟺ ρ_AB=ρ_A⊗ρ_B`. Real `↔` (mutual-info id + Klein faithfulness). |
| `mutualInfo_eq_zero_iff_product` | **B** | PosDef | `I(A:B)=0 ⟺ product`. |
| `strict_subadditivity_iff_not_product` | **B** | PosDef | strict `<` ⟺ correlated. |

### ArakiLieb.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `arakiLieb_abs` (`EntropyData`) | **A** | abstract `EntropyData` (purity + subadd recorded as fields) | `|S_A−S_B|≤S_AB` from the order-theoretic core. |
| `araki_lieb_master` | **C** | `d.Subadditivity_Target` (named hyp) | sandwich, conditional on the abstract subadd target. |
| `Subadditivity_Target` | **D** | — | named hole at abstract level (discharged downstream by WeakSubadditivity). |
| `araki_lieb_diagonal_product` | **A** | product distribution | fully unconditional sandwich on diagonal vN entropy (product additivity discharges subadd). |

### StrongSubadditivity.lean ⚠ (mixed; the vacuity trap lives here)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `shannon_strong_subadditivity` | **A** | any `ProbabilityVector` on tripartite | **CLASSICAL** Shannon SSA `H(ABC)+H(B)≤H(AB)+H(BC)`. Genuine, unconditional, ~400 lines via Gibbs. |
| `klDivergence_jointProductComparison_eq` | **A** | — | entropy-imbalance identity. |
| `strong_subadditivity_general` | **D/C** | `hLieb : Lieb1973_Target` (= `LiebTrace_Concavity_Target`, **PROVABLY FALSE**) + 3 more named targets | **VACUOUS**: hypothesis unsatisfiable. Also conclusion is `∃ S_AB S_BC S_B, …` (witness-existential — weak). NOT claimable. |
| `conditionalMutualInfo_nonneg`, `partialTraceDPI_from_lieb_gate`, `holevo_bound_general_from_lieb`, `quantumRelativeEntropyMonotonicity_from_lieb_and_stinespring` | **D/C** | gated on the FALSE `Lieb1973_Target` | all VACUOUSLY TRUE (author flags this in header). |
| `strong_subadditivity_general_corrected` (+ `_corrected` siblings) | **C** | `Lieb1973_Corrected_Target` (open, true) + `PartialTrace_Decomposition_Target` + `Tripartite_SSA_Reduction_Target` (both open) | non-vacuous BUT conditional on ≥2 undischarged targets; conclusion still witness-existential. NOT claimable. |
| `Tripartite_SSA_Reduction_Target` | **D** | — | open; conclusion is existential `∃ S_AB…` (does not pin marginals). |
| `Stinespring_for_Measurement_Target` | **D** | — | open. |
| `scopingNote_*` | **D**(vacuous) | — | `: True := trivial`. |

### LiebTargetAudit.lean ⭐ (the falsification result)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `liebTrace_concavity_target_is_false` | **A** | — | **Proves `¬ LiebTrace_Concavity_Target`** via 1×1 counterexample (log2 vs 1.5·log1.5). Genuine, important. |
| `any_consequence_of_liebTrace_concavity_target` | A | hyp = false target | `(hLieb)→False`; documents vacuity. |
| `Lieb1973_Corrected_Target` | **D** | — | the corrected hole (joint convexity of Umegaki at matrix level, Lindblad–Uhlmann). Undischarged. |

### LiebTargetCorrected.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `umegakiRelativeEntropy_jointly_convex_corrected` | **C** | `Lieb1973_Corrected_Target` | `→ JointConvexity_RelEntropy_Target`. Definitional bridge; conditional. |
| `umegaki_dpi_partialTrace_corrected` | **C** | `Lieb1973_Corrected_Target` + `PartialTrace_Decomposition_Target` | conditional. |
| `jointConvexity_corrected_self` | **C** | corrected target | self-case, conditional. |

### LiebRpowRoute.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `scalar_weighted_am_gm` | **A** | a,b>0, s∈[0,1] | weighted AM–GM. |
| `matrix_rpow_monotone` | **A** | A≤B, p∈[0,1] | operator monotonicity of rpow (Mathlib bridge). |
| `trace_geometricMean_jointly_concave` | **A** | PosDef A₁A₂B₁B₂ | UNCONDITIONAL joint concavity of `Tr(A#B)` (Ando). |
| `matrix_rpow_integral_representation`, `matrix_rpow_integrand_monotone` | **A** | PSD | Mathlib rpow-integral bridges. |
| `Rpow_Operator_Concavity_Target`, `Log_As_Rpow_Limit_Target`, `Lieb1973_Tracial_Target`, `Tracial_To_Corrected_Reduction_Target`, `Rpow_Route_Full_Reduction` | **D** | — | named targets/implications (the reduction implications are only NAMED, not proved). |
| `*_target_holds` | **E** | `(h:T)` | reflexive interfaces `:= h`. NOT discharges. |

### RpowConcavityClosed.lean ⭐ (real closures of two rpow gates)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `rpow_operator_concavity_target_unconditional` | **A** | — | **DISCHARGES `Rpow_Operator_Concavity_Target`** (composes per-t concavity + Bochner lift). |
| `log_as_rpow_limit_target_unconditional` | **A** | — | **DISCHARGES `Log_As_Rpow_Limit_Target`** (Mathlib `tendsto_cfc_rpow_sub_one_log`). |

### RpowOperatorConcavity.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `shifted_inv_operator_convex`, `scalar_rpowIntegrand₀₁_concaveOn`, `convexOn_inv_add` | **A** | — | genuine operator/scalar convexity lemmas. |
| `rpow_operator_concavity_target_from_gates` | **E** | per-t concavity + Bochner gates | reduction. |
| `*_target_holds` | E | reflexive | interfaces. |

### BochnerConcavityLift.lean ⭐
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `bochner_concavity_lift` | **A** | pointwise-concave integrand family | genuine: integral of concave is concave. |
| `bochnerConcavityLift_holds` | **A** | — | **DISCHARGES `Bochner_Concavity_Lift_Target`**. |

### OperatorEntropyConvexity.lean ⭐ (closes the OE-convexity gate)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `operatorEntropy_convex` | **B** | A₁,A₂ PosDef | `Tr(B log B)` convex, proved FROM Klein. Genuine. |
| `operatorEntropyConvexity_holds` | **B** | — | **DISCHARGES `OperatorEntropy_Convexity_Target`** (real, PosDef). |

### LiebThirring.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `liebThirring_q_one` (and `_le/_ge/_def`) | **A** | PSD B | `Tr(√B A √B)=Tr(AB)` (trace cyclicity). |
| `liebThirring_commuting_eq`, `liebThirring_commuting_target_holds` | **A** | PSD, **Commute A B** | commuting Lieb–Thirring **equality**, genuine discharge of commuting gate. |
| `LiebThirring_Target`, `_Reverse_Target`, `_NonCommuting_Subgate` | **D** | — | open (the deep non-commuting direction). |
| `lieb_thirring_master(_and)` | **E** | `LiebThirring_NonCommuting_Subgate` | reduction commuting+subgate→target. |

### LiebGoldenThompson.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `GoldenThompson_Target` | **D** | — | open; the irreducible Lie-Trotter/non-commuting residual. |
| `CarlenLieb_Integral_Reduction_Target` | **D** | — | `GT → Lieb-tracial-subgate`, open implication. |
| `lieb_tracial_*_from_GT_route` | **E/C** | GT + reduction targets | reductions. |
| `lieb_tracial_commuting_no_GT_needed`, `lieb_tracial_endpoint_{zero,one}_no_GT_needed` | **B** | PosDef + AllCommute / endpoints | genuine commuting/endpoint tracial concavity. |
| `*_target_holds` | E | reflexive | interfaces. |

### CarlenLiebIntegralReduction.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `CarlenLiebIntegrand_PointwiseConcavity_Target`, `CarlenLieb_Schwartz_Identity_Target` | **D** | — | open Schwartz double-integral gates. |
| `carlenLieb_integral_reduction_holds_modulo_identity`, `lieb_tracial_target_from_CL_*`, `lieb_tracial_target_from_three_routes` | **C/E** | the two CL subgates (+GT) | reductions; conditional. |
| `*_target_holds` | E | reflexive | interfaces. |

### LiebTracialAttack.lean / LiebSubgateProgress.lean / LiebJointConcavityKraus.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `scalar_lieb_concavity`, `cfc_rpow_diagonal`, `lieb_tracial_diagonal_data`, `lieb1973_tracial_target_diagonal_holds` | **A/B** | diagonal/scalar | genuine DIAGONAL/scalar tracial cases. |
| `Lieb1973_Tracial_Target_Diagonal`, `..._From_Half_And_Rpow_Concavity_Target` | D | — | named. |
| `frullaniLogIntegrand_*`, `re_trace_kraus_self_convex`, `lieb1973_kraus_concavity_target_holds` | A / D / E | — | building blocks + Kraus named target + interface. |
| `LieTrotter_NormedExp_Target`, `PerStep_*`, `goldenThompson_*_from_normedExp_*` | D/E | — | Lie-Trotter normed-exp gates + reductions (residual of GT). |

### GibbsVariationalFull.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `gibbs_variational_principle` | **B** | ρ.M PosDef, H Hermitian, 0≤T, T·β=1, Z>0 | `F(ρ_β)≤F(ρ)`. Genuine. |
| `gibbs_state_unique` | **B** | PosDef + above | `F(ρ)=F(ρ_β) ⟹ ρ=ρ_β` (Klein faithfulness). |
| `gibbs_free_energy_eq_iff` | **B** | PosDef | `↔` variational characterisation. |
| `gibbs_gap_identity`, `operatorLog_gibbsDensity`, `freeEnergy_gibbs_eq` | B | PosDef/Hermitian | gap identity `F(ρ)−F(ρ_β)=T·S(ρ‖ρ_β)`. |

### GibbsVariational.lean (thin-vocabulary; mostly defs + reductions)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `freeEnergy_*`, `energy_*`, `gibbsMinimum_eq` | A | — | algebraic identities (linearity, T·log Z). |
| `Gibbs_Variational_Target`, `PeierlsBogoliubov_Target`, `FreeEnergy_RelEntropy_Identity_Target` | **D** | — | named targets (the substantive ones live discharged in `…Full`). |
| `gibbs_variational_of_gap`, `gibbs_master`, `gibbs_variational_attained` | **C/E** | gap-identity hyp | reductions. |

### MaxEntropyPrinciple.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `max_entropy`, `gibbs_is_maxEntropy` | **B** | ρ.M PosDef, H Herm, 0<T, equal energy | Jaynes max-entropy `S(ρ)≤S(ρ_β)`. Genuine. |
| `max_entropy_unique` | **B** | PosDef + equal energy + equal entropy | Gibbs is THE unique maximiser. |
| `max_entropy_eq_iff_relent_zero`, `max_entropy_unique_via_relent` | B | PosDef | equality criteria. |

### RelativeEntropyConvexity.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `relativeEntropy_convex_first_arg` | **B** | ρ₁,ρ₂,ρ̄ PosDef | convexity of `S(·‖σ)` in first arg, full-rank. NOTE: only **first-argument** convexity; full **joint** convexity is the open `JointConvexity_RelEntropy_Target`. |
| `negEntropy_convex_two_point`, `cross_term_two_point` | B | PosDef | building blocks. |

### Pinsker.lean / QuantumPinsker.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `binary_pinsker`, `binaryPinsker_holds` | **A** | p,q∈(0,1)-ish, AC | scalar/binary Pinsker. Genuine. |
| `classical_pinsker` | **A** | P,Q prob vectors, AC | `2·TV² ≤ KL`. Genuine n-point classical Pinsker. |
| `Quantum_Pinsker_Commuting` | **A** | shared-eigenbasis P,Q | commuting quantum Pinsker = classical (honest reduction). |
| `Quantum_Pinsker_General` | **D** | — | named hole: non-commuting quantum Pinsker (needs pinching DPI). UNDISCHARGED. |
| `BinaryPinsker` (Pinsker.lean), `pinsker_of_binaryPinsker` | D / E | — | named binary target + reduction (discharged by `binaryPinsker_holds`). |

### HolevoBound.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `holevoChi_singleton`, `holevoChi_identical`, `holevo_master`, `averageState_M*` | **A** | prob vector | closed-form χ identities. Genuine. |
| `holevoChi_nonneg_of_concave` | **E/C** | `VonNeumannConcavity n` gate | reduces to concavity (discharged on full-rank locus in VonNeumannConcavity.lean). |
| `holevo_bound`, `Holevo_Theorem_Target_holds`, `postMeasurementMI_le_holevoChi` | **C** | `HolevoUmegakiForm` + `QuantumRelativeEntropyMonotonicity` (named hyps) | Holevo bound conditional on Lindblad–Uhlmann monotonicity (open). `Holevo_Theorem_Target` def embeds those hyps. NOT a vacuity trap, but conditional. |

### HolevoChi.lean / SpectralHolevoEnsemble.lean (classical/spectral)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `holevoChiClassical_nonneg`, `holevoChiClassical_eq_mutualInformation`, `classical_measurement_mutualInformation_le_source_chi`, `holevoChiClassical_contracts_under_stochastic` | **A** | classical ensembles | genuine classical Holevo/DPI. |
| `holevoChiSpectral_nonneg`, `spectral_measurement_mutualInformation_le_holevoChi`, `holevoChiSpectral_contracts_under_stochastic` | **A** | spectral ensemble (commuting-diagonalised) | genuine — full Holevo bound for the **spectral/commuting** ensemble class. |

### HolevoUmegakiDischarge.lean / HolevoDiagonalDischarge.lean
| declaration | bucket | notes |
|---|---|---|
| diagonal/Umegaki form discharges | A/B | foundational identities feeding Klein & Holevo (e.g. `mul_operatorLog_eq_operatorXLogX`). Genuine. |

### Umegaki tensor additivity
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `CFCLogTensor.cfcLogTensorIdentity_holds` | **A** | — | **DISCHARGES `CFC_LogTensor_Identity_Target`** (log(ρ⊗τ)=logρ⊗I+I⊗logτ). Unconditional. ⭐ |
| `CFCLogTensor.cfc_log_kronecker_prod`, `cfc_diagonal_entrywise_generic` | A | — | genuine CFC bridges. |
| `UmegakiTensorAdditivityFull.umegakiRelativeEntropy_tensor_additive_full` / `umegakiTensorAdditivityFull_holds` | **B** | ρ,σ PosDef, τ density | `S(ρ⊗τ‖σ⊗τ)=S(ρ‖σ)` — full, no diagonal/commuting restriction. Genuine. |
| `UmegakiTensorAdditivity.umegakiTensorAdditive_self`, `_dim_one_n` | A | special cases | genuine. |
| `umegakiTensorAdditive_dim_one_m_conditional`, `tensorAdditivity_holds` | C/E | conditional/named | reductions. |
| `scopingNote_residualGap` | D(vacuous) | `:True` | — |

### JointConvexityUmegaki.lean ⚠
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `umegakiRelativeEntropy_jointConvex_self` | **A** | α∈[0,1] | trivial self-case `S(ρ‖σ)≤S(ρ‖σ)`. |
| `reTrace_smul_add_log` | A | — | linearity of the easy term. |
| `scopingNote_logIntegralRepr/operatorInvConvex/jointConvexityViaIntegral/partialTraceDPI` | **D**(vacuous) | `:True := trivial` | these are NOT theorems — doc placeholders. The genuine joint convexity is the OPEN `JointConvexity_RelEntropy_Target` (= corrected Lieb). |

### UmegakiMultiConvex.lean ⚠ (vacuity trap)
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `umegakiRelativeEntropy_n_fold_jointly_convex` | **C** | `h2 : JointConvexity_RelEntropy_Target` + PosDef | genuine N-fold statement, conditional on the open binary gate. |
| `multiConvex_holds_unconditional` / `multiConvex_holds_of_2` | **D**(vacuous) | — | prove `JointConvexity_Multi_Target` which **`:= True`** (author flags it). VACUOUS. |
| `convexCombination_two_PosDef` | A/B | PosDef | genuine. |

### CoherenceNonneg.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `coherence_nonneg_of_posDef` | **B** | ρ.M PosDef | `C(ρ)≥0` (Klein corollary). |
| `coherence_eq_zero_iff` | **B** | PosDef | `C(ρ)=0 ⟺ incoherent` (Klein faithfulness). |
| `coherence_eq_umegaki`, `coherence_zero_imp_incoherent` | B | PosDef | genuine. |

### CoherenceResource.lean
| declaration | bucket | notes |
|---|---|---|
| `dephase_*`, `IsIncoherent`, `coherence_incoherent_zero`, `coherence_master` | A | structural dephasing algebra + incoherent⟹zero (unconditional direction). |
| `Coherence_Nonneg_Target`, `_Zero_Iff_Incoherent_Target`, `_Monotone_Target` | D | named (nonneg/faithfulness discharged in CoherenceNonneg; monotone open). |

### CoherentInformation.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `coherentInformation_le_output_entropy` | **A** | — | WEAK bound `I_c≤S(N(ρ))` (sharp `I_c≤S(ρ)` needs SSA — not claimed). |
| `coherentInformation_identity_eq_entropy`, `vonNeumannEntropy_*_eq_zero` | A | unitary/pure cases | genuine pure-state/identity-channel facts. |
| `LSDQuantumCapacityFormula` | D | — | named LSD capacity target. |

### UmegakiIsometricInvariance.lean
| declaration | bucket | hypotheses | notes |
|---|---|---|---|
| `umegakiRelativeEntropy_square_isometric_invariant` / `_isometric_invariant_square` | **B** | square isometry (=unitary) | genuine invariance under unitary conjugation. |
| `umegakiRelativeEntropy_isometric_invariant_Target` | D | — | the rectangular (true isometry) case named/open. |
| `scopingNote_*` | D(vacuous) | `:True` | — |

### Classical/diagonal/spectral leaf files (foundational, genuine)
| file / declaration | bucket | notes |
|---|---|---|
| `GibbsInequality.klDivergence_nonneg_of_ac` + spectral/diagonal/measurement variants | **A** | classical Gibbs (KL≥0). The engine under classical SSA & Pinsker. |
| `DiagonalRelativeEntropy.*`, `SpectralRelativeEntropy.*` | **A** | `S=KL` identities, self=0, product additivity (classical/commuting). |
| `ClassicalEntropy.*`, `ClassicalRelativeEntropy.*` | **A** | Shannon entropy + KL toolbox. |
| `DiagonalVonNeumannEntropy.*` | **A** | diagonal vN entropy + product additivity + nonneg. |
| `WehrlEntropy.wehrlEntropy_nonneg / _le_log / uniform_wehrl_eq_log_m` | **A** | classical-histogram Wehrl bounds `0≤S_W≤log m`. |
| `WehrlEntropy.WehrlLieb_Target / Lieb_Conjecture_Target / Wehrl_ge_vonNeumann_Target` | **D** | named (Wehrl–Lieb conjecture, open). |
| `HolevoBoundQuantum.*` | mix | `holevo_bound_of_monotonicity` is **E/C** (consumes monotonicity gate); χ-definitions A. |
| `UmegakiRelativeEntropy.*`, `OperatorEntropy.*` | A | definitions + basic identities (`vonNeumannEntropy_nonneg`, etc.). |

---

# PAPER-CLAIMABLE (bucket A + B) — MASTER LIST

These are the genuinely-proved results a formalization paper could claim, **sorry-free and
axiom-clean by source inspection** (PosDef caveat marked ★).

### Fully unconditional (A)
1. **Scalar/diagonal Klein** — `klein_scalar`, `klein_scalar_form`, `klein_diagonal_scalar`, `kleinDeficit_strict`.
2. **`¬ LiebTrace_Concavity_Target`** — `liebTrace_concavity_target_is_false` (the original Lieb target is FALSE; clean counterexample). A genuine *negative* result.
3. **Classical Shannon strong subadditivity** — `shannon_strong_subadditivity` (+ KL-imbalance identity).
4. **Classical Gibbs / KL≥0** — `klDivergence_nonneg_of_ac` (+ spectral/diagonal/measurement variants).
5. **Classical & binary Pinsker** — `binary_pinsker`, `classical_pinsker`, `Quantum_Pinsker_Commuting`.
6. **Classical / spectral Holevo bound + DPI** — `holevoChiClassical_nonneg`, `classical_measurement_mutualInformation_le_source_chi`, `holevoChiSpectral_nonneg`, `spectral_measurement_mutualInformation_le_holevoChi` (full Holevo for the commuting/spectral ensemble class).
7. **Holevo χ closed-forms** — `holevoChi_singleton`, `holevoChi_identical`, `holevo_master`.
8. **CFC log-tensor identity** — `cfcLogTensorIdentity_holds` (`log(ρ⊗τ)=logρ⊗I+I⊗logτ`).
9. **rpow gates** — `rpow_operator_concavity_target_unconditional`, `log_as_rpow_limit_target_unconditional`, `bochnerConcavityLift_holds`, `trace_geometricMean_jointly_concave`, `matrix_rpow_monotone`.
10. **Lieb–Thirring (commuting/q=1)** — `liebThirring_q_one`, `liebThirring_commuting_target_holds`.
11. **Wehrl bounds** — `wehrlEntropy_nonneg`, `wehrlEntropy_le_log`, `uniform_wehrl_eq_log_m`.
12. **Araki–Lieb (abstract core + diagonal product)** — `arakiLieb_abs`, `araki_lieb_diagonal_product`.
13. **Coherence (incoherent⟹0; algebra)** — dephasing toolbox, `coherence_incoherent_zero`.
14. **Coherent-information weak bound** — `coherentInformation_le_output_entropy`.

### Proved on the PosDef / full-rank locus (B) ★
15. **Klein's inequality, full non-commuting** ★ — `klein_inequality`; corollary `umegakiRelativeEntropy_nonneg` (`0≤S(ρ‖σ)`).
16. **Strict Klein faithfulness, full non-commuting** ★ — `umegakiRelativeEntropy_eq_zero_iff` (`S(ρ‖σ)=0 ⟺ ρ=σ`).
17. **von Neumann concavity** ★ — `vonNeumann_concave`; and **χ≥0** `holevoChi_nonneg` (requires PosDef average).
18. **Weak subadditivity** ★ — `weak_subadditivity`; mutual-info = relative entropy; Araki–Lieb sandwich (`arakiLieb_sandwich_unconditional`).
19. **Subadditivity equality** ★ — `subadditivity_equality` (`S(AB)=S_A+S_B ⟺ product`); `mutualInfo_eq_zero_iff_product`; strict version.
20. **Operator-entropy convexity** ★ — `operatorEntropy_convex` / `operatorEntropyConvexity_holds`.
21. **Relative-entropy convexity (first argument)** ★ — `relativeEntropy_convex_first_arg` (NOT full joint convexity).
22. **Umegaki tensor additivity, full** ★ — `umegakiRelativeEntropy_tensor_additive_full`.
23. **Gibbs variational principle + uniqueness** ★ — `gibbs_variational_principle`, `gibbs_state_unique`, `gibbs_free_energy_eq_iff`.
24. **Maximum-entropy (Jaynes) + uniqueness** ★ — `max_entropy`, `gibbs_is_maxEntropy`, `max_entropy_unique`.
25. **Relative entropy of coherence: nonneg + faithfulness** ★ — `coherence_nonneg_of_posDef`, `coherence_eq_zero_iff`.
26. **Umegaki unitary-conjugation invariance** ★ — `umegakiRelativeEntropy_square_isometric_invariant`.

---

# SCOPED / OPEN (bucket C + D) — MASTER LIST (the genuine holes)

The single irreducible analytic core per chain:

- **Lieb 1973 / joint convexity chain.** Head hole = `Lieb1973_Corrected_Target` (joint convexity of Umegaki relative entropy at matrix level, Lindblad–Uhlmann). It reduces (`Tracial_To_Corrected_Reduction_Target`, itself only a *named* implication) to `Lieb1973_Tracial_Target`, with the other two antecedents (`Log_As_Rpow_Limit_Target`, `OperatorEntropy_Convexity_Target`) **already closed**. `Lieb1973_Tracial_Target` reduces (Carlen–Lieb) to:
  - **`GoldenThompson_Target`** (the irreducible **Lie–Trotter / non-commuting exp** residual), and
  - **`CarlenLieb_Schwartz_Identity_Target`** + **`CarlenLiebIntegrand_PointwiseConcavity_Target`** (Schwartz double-integral content).
  → **Net irreducible cores for the whole Lieb chain: Golden–Thompson (Lie-Trotter) + the Carlen–Lieb Schwartz-integral concavity.** Everything else on the chain is closed or a reflexive interface.
- **`JointConvexity_RelEntropy_Target`** — the binary form; equals the corrected Lieb head. Open. (`umegakiRelativeEntropy_n_fold_jointly_convex` is conditional on it.)
- **Quantum strong subadditivity** — `strong_subadditivity_general` is VACUOUS (gated on the FALSE `Lieb1973_Target`). The `_corrected` version is conditional on `Lieb1973_Corrected_Target` **and** `Tripartite_SSA_Reduction_Target` **and** `PartialTrace_Decomposition_Target`, with a witness-existential conclusion. Quantum SSA is **NOT proved**.
- **General Holevo bound** (`holevo_bound`) — conditional on `HolevoUmegakiForm` + `QuantumRelativeEntropyMonotonicity` (Lindblad–Uhlmann monotonicity, open for general POVM). Only classical/spectral Holevo is closed.
- **General quantum Pinsker** — `Quantum_Pinsker_General` open (needs pinching-channel DPI). Only commuting/classical closed.
- **Wehrl–Lieb conjecture** — `WehrlLieb_Target`, `Lieb_Conjecture_Target` open.
- **Lieb–Thirring (non-commuting, q≥1)** — `LiebThirring_Target` open (`LiebThirring_NonCommuting_Subgate`).
- **Coherence monotonicity** — `Coherence_Monotone_Target` open.
- **Umegaki isometric invariance (rectangular)** — open; only square (unitary) case closed.

### Vacuity traps explicitly flagged (do NOT claim)
- `StrongSubadditivity.strong_subadditivity_general` and all `Lieb1973_Target`-gated siblings — gated on the **FALSE** `LiebTrace_Concavity_Target`; vacuously true.
- `UmegakiMultiConvex.multiConvex_holds_unconditional` / `_of_2` — prove `JointConvexity_Multi_Target` which is **`:= True`**.
- `JointConvexityUmegaki.scopingNote_*`, `UmegakiTensorAdditivity.scopingNote_residualGap`, `UmegakiIsometricInvariance.scopingNote_*`, `StrongSubadditivity.scopingNote_*` — `: True := trivial` doc placeholders, not theorems.
- All `*_target_holds` of the form `(h : T) : T := h` (LiebRpowRoute, LiebGoldenThompson, LiebThirring's `..._holds` interfaces, CarlenLieb) are **reflexive interfaces, NOT discharges** (E). (Exceptions that ARE real discharges: `liebThirring_commuting_target_holds`, `operatorEntropyConvexity_holds`, `cfcLogTensorIdentity_holds`, `rpow_operator_concavity_target_unconditional`, `log_as_rpow_limit_target_unconditional`, `bochnerConcavityLift_holds`, `umegakiTensorAdditivityFull_holds`, `Holevo_Theorem_Target_holds` [conditional], `tensorAdditivity_holds`.)

---

# DUPLICATES / CONSOLIDATION NEEDED

- **Klein:** `KleinInequalityFull` is canonical (full non-commuting). `KleinInequality` (scalar/diagonal building blocks) and `KleinEquality` (faithfulness) are complementary, not duplicates. `KleinInequality.umegakiRelativeEntropy_nonneg_of_klein` is a stub subsumed by `KleinInequalityFull.umegakiRelativeEntropy_nonneg`.
- **Umegaki tensor:** `UmegakiTensorAdditivityFull` (full PosDef) subsumes the special cases in `UmegakiTensorAdditivity` (`_self`, `_dim_one_n`, `_partial`). Keep Full as canonical.
- **Joint convexity:** `JointConvexityUmegaki` (binary self-case + scoping notes), `UmegakiMultiConvex` (N-fold, conditional), `LiebTargetCorrected` (the bridge). All point at the same open `Lieb1973_Corrected_Target`; consolidate the `True`-placeholders.
- **Gibbs:** `GibbsVariational` (defs + named targets + gap-conditional reductions) is subsumed by `GibbsVariationalFull` (actual discharges). `MaxEntropyPrinciple` builds on Full.
- **Lieb route files:** `LiebRpowRoute`, `RpowConcavityClosed`, `RpowOperatorConcavity`, `BochnerConcavityLift`, `LiebGoldenThompson`, `CarlenLiebIntegralReduction`, `LiebThirring`, `LiebTracialAttack`, `LiebSubgateProgress`, `LiebJointConcavityKraus` form ONE reduction web around Golden–Thompson; many `*_target_holds` reflexive interfaces are redundant.
- **Holevo:** `HolevoBound` (Fin N vocabulary), `HolevoBoundQuantum` (ensemble), `HolevoChi`/`SpectralHolevoEnsemble` (classical/spectral) — layered, not duplicated.
- **Coherence:** `CoherenceResource` (algebra + targets) + `CoherenceNonneg` (the discharges). Keep both.

---

# HONEST VERDICT (paper-readiness)

The genuinely-proved core is **substantial and paper-sized**, but it is a **full-rank (PosDef)
relative-entropy paper**, not a general-states paper, and the **deep Lieb/SSA layer is open**.

What is real and would carry a formalization paper: **Klein's inequality in the full non-commuting
case and its strict faithfulness** (`klein_inequality`, `umegakiRelativeEntropy_eq_zero_iff`,
PosDef) — these are the load-bearing theorems — together with everything Klein bootstraps
**unconditionally on the full-rank locus**: von Neumann concavity, Holevo χ≥0, weak subadditivity +
its equality case, operator-entropy convexity, first-argument relative-entropy convexity, full
Umegaki tensor additivity, the Gibbs variational principle + Jaynes max-entropy with uniqueness, and
the relative entropy of coherence (nonneg + faithfulness). On the fully-unconditional side there is a
clean classical layer (Shannon SSA, classical/spectral Holevo, classical & binary Pinsker, Gibbs
KL≥0, Wehrl bounds) plus genuine analytic infrastructure (CFC log-tensor identity, rpow operator
concavity, Bochner lift, Ando trace-geometric-mean concavity, Lieb–Thirring commuting case) **and a
notable negative result** (`liebTrace_concavity_target_is_false`).

What a referee must NOT let through as "proved": **general (non-full-rank) states** anywhere
PosDef appears; **quantum strong subadditivity** (vacuous on a false gate, or conditional on ≥2 open
targets with a witness-existential conclusion); the **general Holevo bound** (conditional on
Lindblad–Uhlmann monotonicity); **general quantum Pinsker**; **full joint convexity of relative
entropy** (`JointConvexity_RelEntropy_Target` = corrected Lieb, open); and the **Wehrl–Lieb
conjecture**. The entire deep layer funnels into two irreducible analytic cores —
**Golden–Thompson (Lie–Trotter) and the Carlen–Lieb Schwartz-integral joint concavity** — both
genuinely undischarged. The author's scoping is, to their credit, mostly honest (the false-gate
vacuity, the `:= True` placeholders, and the PosDef caveats are all flagged in-file); the audit's
job here is mainly to stop those flagged-but-named items from being read as closed.
