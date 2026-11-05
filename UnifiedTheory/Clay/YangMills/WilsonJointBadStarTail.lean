/- A normalized joint bad-star estimate under the original Wilson law.
Disjoint affected plaquettes make the energy cost additive; the partition
lower bound is the actual Haar grid bound. This proves the energetic input
for dissemination, not a chessboard inequality or a continuum mass gap. -/
import UnifiedTheory.Clay.YangMills.WilsonBadStapleProbability
import UnifiedTheory.Clay.YangMills.WilsonExtensiveSchedule
import UnifiedTheory.Clay.YangMills.WilsonRemainderDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonJointBadStarTail
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples
open WilsonIndependentBlocks SingleLinkWilsonOscillation SU2StarEnergy WilsonEnergyDensity
open UnitaryHaarNeighborhood WilsonIdentityNeighborhood
open scoped Topology

/-- A normalized energy-event estimate, with an explicitly proved partition lower bound. -/
theorem gibbs_event_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A : X → ℝ) (hA : Continuous A) (E : Set X) (T C : ℝ)
    (hE : ∀ x ∈ E, T ≤ A x)
    (hZ : Real.exp (-C) ≤ ∫ x, Real.exp (-A x) ∂μ) :
    (CompactGibbsContinuity.law μ A).real E ≤ Real.exp (C - T) := by
  letI := CompactGibbsContinuity.law_probability μ A hA
  have hsub : E ⊆ {x | Real.exp T ≤ Real.exp (A x)} :=
    fun x hx => Real.exp_le_exp.mpr (hE x hx)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => (Real.exp_pos (A x)).le))
    ((Real.continuous_exp.comp hA).integrable_of_hasCompactSupport
      (μ := CompactGibbsContinuity.law μ A) (HasCompactSupport.of_compactSpace _))
    (Real.exp T)
  rw [GibbsFreeEnergyBound.reciprocal_partition_identity μ A hA] at hm
  have hrec : 1 / (∫ x, Real.exp (-A x) ∂μ) ≤ Real.exp C := by
    calc
      _ ≤ 1 / Real.exp (-C) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hZ
      _ = _ := by rw [Real.exp_neg]; simp
  have h := (mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := CompactGibbsContinuity.law μ A) hsub) (Real.exp_pos T).le).trans hm
  have hh : (CompactGibbsContinuity.law μ A).real E ≤ Real.exp C / Real.exp T := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [mul_comm] using h.trans hrec
  simpa only [Real.exp_sub] using hh

/-- The cost per vertex in the actual SU(2) Haar cap partition lower bound. -/
def entropyCost (β : ℝ) (K : ℕ) : ℝ :=
  6 * β * squaredTolerance (Fin 2) K - 4 * Real.log (massLower (Fin 2) K)

theorem entropyCost_formula (β : ℝ) (K : ℕ) :
    entropyCost β K = 9408 * β / (K : ℝ) ^ 2 +
      32 * Real.log ((2 * K + 1 : ℕ) : ℝ) := by
  unfold entropyCost massLower
  rw [squaredTolerance_formula, one_div, Real.log_inv, Real.log_pow]
  norm_num [Fintype.card_fin]
  ring

theorem entropyCost_grid_le (β : ℝ) (hβ : 0 < β) :
    entropyCost β (grid β) ≤ 6 * β * energyEnvelope β := by
  rw [entropyCost_formula]
  have hk : β ^ 2 ≤ (grid β : ℝ) ^ 2 :=
    pow_le_pow_left₀ hβ.le (beta_le_grid β) 2
  have hp := div_le_div_of_nonneg_left (by positivity : 0 ≤ 9408 * β)
    (by positivity : 0 < β ^ 2) hk
  have hl := mul_le_mul_of_nonneg_left (grid_log_le β hβ) (by norm_num : (0 : ℝ) ≤ 32)
  have he : 9408 * β / β ^ 2 + 32 * Real.log (2 * β + 5) =
      6 * β * energyEnvelope β := by
    unfold energyEnvelope
    field_simp
    ring
  exact he ▸ add_le_add hp hl

variable (n : ℕ) [NeZero n] [Fact (1 < n)]

def action (β : ℝ) (U : Configuration (Vertex n) Q) : ℝ :=
  (6 * β * (Fintype.card (Vertex n) : ℝ)) * energyDensity n U

omit [Fact (1 < n)] in
theorem action_continuous (β : ℝ) : Continuous (action n β) :=
  continuous_const.mul (energyDensity_continuous n)

omit [Fact (1 < n)] in
theorem law_identification (β : ℝ) :
    CompactGibbsContinuity.law (referenceMeasure Q (Vertex n)) (action n β) =
      wilsonLaw n Q character β 2 := by
  have h := law_eq_average_weight n Q representation representation_continuous β
  norm_num only [representation_character, Fintype.card_fin, Nat.cast_ofNat] at h
  rw [h]
  unfold CompactGibbsContinuity.law
  congr 1
  funext U
  unfold GibbsLowEnergyConcentration.weight action energyDensity
  congr 1
  ring

omit [Fact (1 < n)] in
/-- Actual Haar normalization; no concentration of an externally supplied law is assumed. -/
theorem partition_lower (β : ℝ) (hβ : 0 ≤ β) (K : ℕ) (hK : 0 < K) :
    Real.exp (-(Fintype.card (Vertex n) : ℝ) * entropyCost β K) ≤
      ∫ U, Real.exp (-action n β U) ∂referenceMeasure Q (Vertex n) := by
  have hp := massLower_pos (Fin 2) K
  have hh := GibbsLowEnergyConcentration.partition_lower
    (referenceMeasure Q (Vertex n)) (energyDensity n) (energyDensity_continuous n)
    (6 * β * (Fintype.card (Vertex n) : ℝ)) (by positivity)
    (squaredTolerance (Fin 2) K) ((massLower (Fin 2) K) ^ (4 * Fintype.card (Vertex n)))
    (goodEvent n Q (nearIdentity representation K))
    (goodEvent_measurable n Q _
      (nearIdentity_measurable representation representation_continuous K))
    (by
      rw [goodEvent_mass]
      exact pow_le_pow_left₀ hp.le
        (nearIdentity_mass_lower representation representation_continuous K hK) _)
    (fun U hU => goodEvent_small n Q representation _ _
      (fun a ha b hb c hc d hd =>
        four_link_defect_squared_bound representation K a b c d ha hb hc hd) U hU)
  have he : Real.exp (-(Fintype.card (Vertex n) : ℝ) * entropyCost β K) =
      massLower (Fin 2) K ^ (4 * Fintype.card (Vertex n)) *
        Real.exp (-(6 * β * (Fintype.card (Vertex n) : ℝ)) * squaredTolerance (Fin 2) K) := by
    rw [← Real.exp_log (mul_pos (pow_pos hp _) (Real.exp_pos _))]
    congr 1
    rw [Real.log_mul (pow_ne_zero _ hp.ne') (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    unfold entropyCost
    push_cast
    ring
  rw [he]
  simpa only [action, GibbsLowEnergyConcentration.weight, neg_mul] using hh

omit [Fact (1 < n)] in
/-- Disjoint star energies use disjoint nonnegative plaquette terms. -/
theorem independent_energy_bound (S : Finset (Link n)) (hS : Independent n S)
    (U : Configuration (Vertex n) Q) :
    (∑ e ∈ S, starEnergy n e.1 e.2 U) ≤
      (6 * (Fintype.card (Vertex n) : ℝ)) * energyDensity n U := by
  classical
  have hn (p : PlaquetteIndex n) : 0 ≤ plaquetteTerm n Q character 2 U p := by
    rw [← plaquetteDefect_eq_term]
    exact WilsonAverageDefect.plaquette_nonneg n Q representation p U
  rw [energyDensity_eq, mul_div_cancel₀ _ (by positivity :
    (6 * (Fintype.card (Vertex n) : ℝ)) ≠ 0)]
  unfold starEnergy
  rw [← Finset.sum_biUnion hS]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _ => hn p)

def jointBad (S : Finset (Link n)) (δ : ℝ) : Set (Configuration (Vertex n) Q) :=
  {U | ∀ e ∈ S, δ ≤ 6 - ‖stapleField n e.1 e.2 U‖}

theorem jointBad_energy (S : Finset (Link n)) (hS : Independent n S) (δ : ℝ)
    (U : Configuration (Vertex n) Q) (hU : U ∈ jointBad n S δ) :
    2 * δ * S.card ≤ (6 * (Fintype.card (Vertex n) : ℝ)) * energyDensity n U := by
  calc
    _ = ∑ _e ∈ S, 2 * δ := by simp [mul_comm]
    _ ≤ ∑ e ∈ S, starEnergy n e.1 e.2 U := by
      apply Finset.sum_le_sum
      intro e he
      linarith [hU e he, starEnergy_lower n e.1 e.2 U]
    _ ≤ _ := independent_energy_bound n S hS U

/-- The unnormalized additive energy cost survives normalization with an explicit entropy cost. -/
theorem jointBad_probability_bound (S : Finset (Link n)) (hS : Independent n S)
    (β δ : ℝ) (hβ : 0 ≤ β) (K : ℕ) (hK : 0 < K) :
    (wilsonLaw n Q character β 2).real (jointBad n S δ) ≤
      Real.exp ((Fintype.card (Vertex n) : ℝ) * entropyCost β K - 2 * β * δ * S.card) := by
  rw [← law_identification]
  apply gibbs_event_bound (referenceMeasure Q (Vertex n)) (action n β)
    (action_continuous n β) (jointBad n S δ) _ _ _
    (by simpa only [neg_mul] using partition_lower n β hβ K hK)
  intro U hU
  have h := mul_le_mul_of_nonneg_left (jointBad_energy n S hS δ U hU) hβ
  unfold action
  nlinarith

theorem jointBad_probability_grid (S : Finset (Link n)) (hS : Independent n S)
    (β δ : ℝ) (hβ : 0 < β) :
    (wilsonLaw n Q character β 2).real (jointBad n S δ) ≤
      Real.exp (6 * β * (Fintype.card (Vertex n) : ℝ) * energyEnvelope β -
        2 * β * δ * S.card) := by
  apply (jointBad_probability_bound n S hS β δ hβ.le (grid β) (grid_pos β)).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (entropyCost_grid_le β hβ)
    (Nat.cast_nonneg (Fintype.card (Vertex n)) : (0 : ℝ) ≤ _)
  nlinarith

/-- For an extensive independent block the joint event decays exponentially in its cardinality.
The condition on beta eventually holds for each fixed c and positive delta. -/
theorem jointBad_probability_extensive (S : Finset (Link n)) (hS : Independent n S)
    (β δ c : ℝ) (hβ : 0 < β)
    (hsize : (Fintype.card (Vertex n) : ℝ) ≤ c * S.card)
    (hsmall : 6 * c * energyEnvelope β ≤ δ) :
    (wilsonLaw n Q character β 2).real (jointBad n S δ) ≤
      Real.exp (-β * δ * S.card) := by
  apply (jointBad_probability_grid n S hS β δ hβ).trans
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hsize
    (mul_nonneg (by positivity : 0 ≤ 6 * β) (energyEnvelope_nonneg β hβ))
  have h2 := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hβ.le (Nat.cast_nonneg S.card))
  nlinarith

/-- A concrete extensive family from the actual maximal-packing schedule. -/
def packedBlock : Finset (Link n) :=
  (WilsonExtensiveSchedule.wilsonSchedule n 0).image (edgeCoord n)

omit [Fact (1 < n)] in
theorem packedBlock_independent : Independent n (packedBlock n) := by
  classical
  have hi := WilsonExtensiveSchedule.wilsonSchedule_admissible n 0
  change FiniteFactorConditional.Independent (WilsonInducedSupport.plaquetteEdges n)
    (WilsonExtensiveSchedule.wilsonSchedule n 0) at hi
  intro a ha b hb hab
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hab (congrArg (edgeCoord n) (hi p e he d hd
    ((WilsonInducedSupport.mem_plaquetteEdges n p e).mpr hp)
    ((WilsonInducedSupport.mem_plaquetteEdges n p d).mpr hq)))

omit [Fact (1 < n)] in
theorem packedBlock_card_bound :
    4 * Fintype.card (Vertex n) ≤ 25 * (packedBlock n).card := by
  classical
  have hinj : Function.Injective (edgeCoord n) := by
    intro e d h
    rw [← selected_edgeCoord n e, ← selected_edgeCoord n d, h]
  rw [packedBlock, Finset.card_image_of_injective _ hinj]
  simpa only [WilsonExtensiveSchedule.edgeCount, WilsonIdentityNeighborhood.edge_card] using
    WilsonExtensiveSchedule.wilsonSchedule_zero_card_bound n

/-- Explicit joint tail on a proved extensive block, under the displayed coupling test. -/
theorem packedBlock_probability_bound (β δ : ℝ) (hβ : 0 < β)
    (hsmall : (75 / 2) * energyEnvelope β ≤ δ) :
    (wilsonLaw n Q character β 2).real (jointBad n (packedBlock n) δ) ≤
      Real.exp (-β * δ * (packedBlock n).card) := by
  apply jointBad_probability_extensive n (packedBlock n) (packedBlock_independent n)
    β δ (25 / 4) hβ
  · have h : (4 : ℝ) * Fintype.card (Vertex n) ≤ 25 * (packedBlock n).card := by
      exact_mod_cast packedBlock_card_bound n
    linarith
  · nlinarith

theorem packedBlock_probability_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun i => (wilsonLaw (N i) Q character (β i) 2).real
      (jointBad (N i) (packedBlock (N i)) δ)) l (𝓝 0) := by
  have hu : Tendsto (fun i => Real.exp (-(β i * δ))) l (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hβ.atTop_mul_const hδ)
  have he : Tendsto (fun i => (75 / 2) * energyEnvelope (β i)) l (𝓝 0) := by
    simpa only [mul_zero] using (energyEnvelope_tendsto.comp hβ).const_mul (75 / 2 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hβ.eventually (eventually_gt_atTop (0 : ℝ)),
      he.eventually (gt_mem_nhds hδ)] with i hi hsmall
    apply (packedBlock_probability_bound (N i) (β i) δ hi hsmall.le).trans
    apply Real.exp_le_exp.mpr
    have hcard := packedBlock_card_bound (N i)
    have hv := Fintype.card_pos (α := Vertex (N i))
    have hm : (1 : ℝ) ≤ (packedBlock (N i)).card := by
      exact_mod_cast (show 1 ≤ (packedBlock (N i)).card by omega)
    nlinarith [mul_nonneg (mul_nonneg hi.le hδ.le) (sub_nonneg.mpr hm)]

def jointRemainderBad (S : Finset (Link n)) (β ε : ℝ) : Set (Configuration (Vertex n) Q) :=
  {U | ∀ e ∈ S, ε ≤ SU2StableStarRemainder.positiveRemainder β (stapleField n e.1 e.2 U)}

omit [NeZero n] in
theorem jointRemainderBad_subset (S : Finset (Link n)) (β ε : ℝ) (hβ : 0 < β) :
    jointRemainderBad n S β ε ⊆ jointBad n S (Real.sqrt ε / Real.sqrt β) := by
  intro U hU e he
  have h := (Real.sqrt_le_sqrt (hU e he)).trans
    (WilsonRemainderDensity.sqrt_positiveRemainder_bound β hβ (stapleField n e.1 e.2 U)
      (stapleField_norm_le_six n e.1 e.2 U))
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hβ)).mpr (by simpa only [mul_comm] using h)

/-- Simultaneously large positive remainders on the concrete extensive block
have a stretched-exponential coupling rate times the number of selected links. -/
theorem packedRemainder_probability_bound (β ε : ℝ) (hβ : 0 < β)
    (hsmall : (25 / 12) * WilsonRemainderDensity.envelope β ≤ Real.sqrt ε) :
    (wilsonLaw n Q character β 2).real (jointRemainderBad n (packedBlock n) β ε) ≤
      Real.exp (-Real.sqrt β * Real.sqrt ε * (packedBlock n).card) := by
  letI := wilsonLaw_probability n Q character character_continuous β 2
  have hs : (75 / 2) * energyEnvelope β ≤ Real.sqrt ε / Real.sqrt β := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hβ)).mpr
    unfold WilsonRemainderDensity.envelope at hsmall
    nlinarith
  have h := (measureReal_mono (μ := wilsonLaw n Q character β 2)
    (jointRemainderBad_subset n (packedBlock n) β ε hβ)).trans
    (packedBlock_probability_bound n β (Real.sqrt ε / Real.sqrt β) hβ hs)
  have he : -β * (Real.sqrt ε / Real.sqrt β) * (packedBlock n).card =
      -Real.sqrt β * Real.sqrt ε * (packedBlock n).card := by
    have hs0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.mpr hβ).ne'
    field_simp
    rw [Real.sq_sqrt hβ.le]
    ring
  simpa only [he] using h

theorem packedRemainder_probability_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ i, NeZero (N i)] [∀ i, Fact (1 < N i)]
    (β : ι → ℝ) (hβ : Tendsto β l atTop) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun i => (wilsonLaw (N i) Q character (β i) 2).real
      (jointRemainderBad (N i) (packedBlock (N i)) (β i) ε)) l (𝓝 0) := by
  have hu : Tendsto (fun i => Real.exp (-(Real.sqrt (β i) * Real.sqrt ε))) l (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((Real.tendsto_sqrt_atTop.comp hβ).atTop_mul_const (Real.sqrt_pos.mpr hε))
  have he : Tendsto (fun i => (25 / 12) * WilsonRemainderDensity.envelope (β i)) l (𝓝 0) := by
    simpa only [mul_zero] using
      (WilsonRemainderDensity.envelope_tendsto.comp hβ).const_mul (25 / 12 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hβ.eventually (eventually_gt_atTop (0 : ℝ)),
      he.eventually (gt_mem_nhds (Real.sqrt_pos.mpr hε))] with i hi hsmall
    apply (packedRemainder_probability_bound (N i) (β i) ε hi hsmall.le).trans
    apply Real.exp_le_exp.mpr
    have hcard := packedBlock_card_bound (N i)
    have hv := Fintype.card_pos (α := Vertex (N i))
    have hm : (1 : ℝ) ≤ (packedBlock (N i)).card := by
      exact_mod_cast (show 1 ≤ (packedBlock (N i)).card by omega)
    nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg (β i)) (Real.sqrt_nonneg ε))
      (sub_nonneg.mpr hm)]

end
end UnifiedTheory.Clay.YangMills.WilsonJointBadStarTail
